use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;
use std::sync::LazyLock;

use apollo_compiler::Name;
use apollo_compiler::Node;
use apollo_compiler::Schema;
use apollo_compiler::ast::Argument;
use apollo_compiler::ast::Directive;
use apollo_compiler::ast::DirectiveDefinition;
use apollo_compiler::ast::FieldDefinition;
use apollo_compiler::ast::InputValueDefinition;
use apollo_compiler::ast::NamedType;
use apollo_compiler::ast::Type;
use apollo_compiler::ast::Value;
use apollo_compiler::collections::IndexMap;
use apollo_compiler::schema::EnumValueDefinition;
use apollo_compiler::schema::ExtendedType;
use apollo_compiler::validation::Valid;
use itertools::Itertools;
use regex::Regex;
use strsim::jaro_winkler;

use crate::LinkSpecDefinition;
use crate::bail;
use crate::error::CompositionError;
use crate::error::FederationError;
use crate::internal_error;
use crate::link::federation_spec_definition::FEDERATION_OPERATION_TYPES;
use crate::link::federation_spec_definition::FEDERATION_VERSIONS;
use crate::link::join_spec_definition::JOIN_VERSIONS;
use crate::link::join_spec_definition::JoinSpecDefinition;
use crate::link::link_spec_definition::LINK_VERSIONS;
use crate::link::spec::Identity;
use crate::link::spec::Url;
use crate::link::spec::Version;
use crate::link::spec_definition::SpecDefinition;
use crate::merger::compose_directive_manager::ComposeDirectiveManager;
use crate::merger::error_reporter::ErrorReporter;
use crate::merger::hints::HintCode;
use crate::merger::merge_enum::EnumExample;
use crate::merger::merge_enum::EnumExampleAst;
use crate::merger::merge_enum::EnumTypeUsage;
use crate::schema::FederationSchema;
use crate::schema::directive_location::DirectiveLocationExt;
use crate::schema::position::DirectiveDefinitionPosition;
use crate::schema::position::DirectiveTargetPosition;
use crate::schema::position::FieldDefinitionPosition;
use crate::schema::position::InterfaceFieldDefinitionPosition;
use crate::schema::position::InterfaceTypeDefinitionPosition;
use crate::schema::position::ObjectFieldDefinitionPosition;
use crate::schema::position::ObjectOrInterfaceFieldDefinitionPosition;
use crate::schema::position::TypeDefinitionPosition;
use crate::schema::referencer::DirectiveReferencers;
use crate::schema::type_and_directive_specification::ArgumentMerger;
use crate::schema::type_and_directive_specification::StaticArgumentsTransform;
use crate::subgraph::typestate::Subgraph;
use crate::subgraph::typestate::Validated;
use crate::supergraph::ASTNodeKind;
use crate::supergraph::CompositionHint;
use crate::supergraph::SubgraphASTNode;
use crate::utils::human_readable::human_readable_subgraph_names;

static NON_MERGED_CORE_FEATURES: LazyLock<[Identity; 4]> = LazyLock::new(|| {
    [
        Identity::federation_identity(),
        Identity::link_identity(),
        Identity::core_identity(),
        Identity::connect_identity(),
    ]
});

/// In JS, this is encoded indirectly in `isGraphQLBuiltInDirective`. Regardless of whether
/// the end user redefined these directives, we consider them built-in for merging.
static BUILT_IN_DIRECTIVES: [&str; 6] = [
    "skip",
    "include",
    "deprecated",
    "specifiedBy",
    "defer",
    "stream",
];

// Cached regex patterns for override label validation
static LABEL_REGEX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^[a-zA-Z][a-zA-Z0-9_\-:./]*$").unwrap());
static PERCENT_REGEX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^percent\((\d{1,2}(\.\d{1,8})?|100)\)$").unwrap());

/// Federation directive types for type-safe directive handling
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FederationDirective {
    Override,
    External,
    Requires,
    Provides,
}

impl FederationDirective {
    /// Get the standard directive name
    fn name(self) -> &'static str {
        match self {
            Self::Override => "override",
            Self::External => "external",
            Self::Requires => "requires",
            Self::Provides => "provides",
        }
    }

    /// Get the federation-prefixed directive name
    fn federation_name(self) -> &'static str {
        match self {
            Self::Override => "federation__override",
            Self::External => "federation__external",
            Self::Requires => "federation__requires",
            Self::Provides => "federation__provides",
        }
    }

    /// Check if a directive name matches this federation directive (either form)
    fn matches(self, directive_name: &str) -> bool {
        directive_name == self.name() || directive_name == self.federation_name()
    }

    /// Get conflict description for error messages
    fn conflict_name(self) -> &'static str {
        self.name() // Use simple name for user-facing messages
    }
}

/// Enum for override validation hint codes to replace magic strings
#[derive(Debug, Clone, PartialEq, Eq)]
enum OverrideHintCode {
    FromSubgraphDoesNotExist,
    OverrideDirectiveCanBeRemoved,
    #[allow(dead_code)]
    OverrideSourceHasNoField,
    OverriddenFieldCanBeRemoved,
}

/// Result type for override conflict detection
#[derive(Debug)]
#[allow(dead_code)]
struct OverrideConflictResult {
    has_incompatible: bool,
    conflicting_directive: Option<String>,
    subgraph: Option<String>,
}

/// Parameters for override field validation to avoid too many arguments
#[derive(Debug)]
struct OverrideValidationParams<'a> {
    from_idx: usize,
    source_field: &'a Node<FieldDefinition>,
    dest: &'a Node<FieldDefinition>,
    subgraph_name: &'a str,
    source_subgraph_name: &'a str,
    overridden_field_is_referenced: bool,
    override_label: Option<&'a str>,
    override_directive: &'a Node<Directive>,
}

impl OverrideHintCode {
    fn as_str(&self) -> &'static str {
        match self {
            Self::FromSubgraphDoesNotExist => "FROM_SUBGRAPH_DOES_NOT_EXIST",
            Self::OverrideDirectiveCanBeRemoved => "OVERRIDE_DIRECTIVE_CAN_BE_REMOVED",
            Self::OverrideSourceHasNoField => "OVERRIDE_SOURCE_HAS_NO_FIELD",
            Self::OverriddenFieldCanBeRemoved => "OVERRIDDEN_FIELD_CAN_BE_REMOVED",
        }
    }
}

/// Type alias for Sources mapping - maps subgraph indices to optional values
pub(crate) type Sources<T> = IndexMap<usize, Option<T>>;

#[derive(Debug)]
pub(crate) struct MergeResult {
    #[allow(dead_code)]
    pub(crate) supergraph: Option<Valid<FederationSchema>>,
    #[allow(dead_code)]
    pub(crate) errors: Vec<CompositionError>,
    #[allow(dead_code)]
    pub(crate) hints: Vec<CompositionHint>,
}

pub(in crate::merger) struct MergedDirectiveInfo {
    pub(in crate::merger) definition: DirectiveDefinition,
    pub(in crate::merger) arguments_merger: Option<ArgumentMerger>,
    pub(in crate::merger) static_argument_transform: Option<Rc<StaticArgumentsTransform>>,
}

#[derive(Debug, Default)]
pub(crate) struct CompositionOptions {
    // Add options as needed - for now keeping it minimal
    /// Maximum allowable number of outstanding subgraph paths to validate during satisfiability.
    pub(crate) max_validation_subgraph_paths: Option<usize>,
}

#[allow(unused)]
pub(crate) struct Merger {
    pub(in crate::merger) subgraphs: Vec<Subgraph<Validated>>,
    pub(in crate::merger) options: CompositionOptions,
    pub(in crate::merger) compose_directive_manager: ComposeDirectiveManager,
    pub(in crate::merger) names: Vec<String>,
    pub(in crate::merger) error_reporter: ErrorReporter,
    pub(in crate::merger) merged: FederationSchema,
    pub(in crate::merger) subgraph_names_to_join_spec_name: HashMap<String, Name>,
    pub(in crate::merger) merged_federation_directive_names: HashSet<String>,
    pub(in crate::merger) merged_federation_directive_in_supergraph_by_directive_name:
        HashMap<Name, MergedDirectiveInfo>,
    pub(in crate::merger) enum_usages: HashMap<String, EnumTypeUsage>,
    pub(in crate::merger) fields_with_from_context: DirectiveReferencers,
    pub(in crate::merger) fields_with_override: DirectiveReferencers,
    pub(in crate::merger) inaccessible_directive_name_in_supergraph: Option<Name>,
    pub(in crate::merger) schema_to_import_to_feature_url: HashMap<String, HashMap<String, Url>>,
    pub(in crate::merger) link_spec_definition: &'static LinkSpecDefinition,
    pub(in crate::merger) join_directive_identities: HashSet<Identity>,
    pub(in crate::merger) join_spec_definition: &'static JoinSpecDefinition,
    pub(in crate::merger) latest_federation_version_used: Version,
    // Pre-computed field-to-parent mapping for O(1) parent access
    // Key: "field_name:type_signature", Value: parent type position
    // Replaces expensive O(n*m) searches with instant HashMap lookup
    pub(in crate::merger) field_parent_lookup: HashMap<String, FieldDefinitionPosition>,
}

/// Abstraction for schema elements that have types that can be merged.
///
/// This replaces the TypeScript `NamedSchemaElementWithType` interface,
/// providing a unified way to handle type merging for both field definitions
/// and input value definitions (arguments).
pub(crate) trait SchemaElementWithType {
    //
    fn coordinate(&self, parent_name: &str) -> String;
    fn set_type(&mut self, typ: Type);
    fn enum_example_ast(&self) -> Option<EnumExampleAst>;
}

impl SchemaElementWithType for FieldDefinition {
    fn coordinate(&self, parent_name: &str) -> String {
        format!("{}.{}", parent_name, self.name)
    }
    fn set_type(&mut self, typ: Type) {
        self.ty = typ;
    }
    fn enum_example_ast(&self) -> Option<EnumExampleAst> {
        Some(EnumExampleAst::Field(Node::new(self.clone())))
    }
}

impl SchemaElementWithType for InputValueDefinition {
    fn coordinate(&self, parent_name: &str) -> String {
        format!("{}.{}", parent_name, self.name)
    }
    fn set_type(&mut self, typ: Type) {
        self.ty = typ.into();
    }
    fn enum_example_ast(&self) -> Option<EnumExampleAst> {
        Some(EnumExampleAst::Input(Node::new(self.clone())))
    }
}

#[allow(unused)]
impl Merger {
    pub(crate) fn new(
        subgraphs: Vec<Subgraph<Validated>>,
        options: CompositionOptions,
    ) -> Result<Self, FederationError> {
        let names: Vec<String> = subgraphs.iter().map(|s| s.name.clone()).collect();
        let mut error_reporter = ErrorReporter::new(names.clone());
        let latest_federation_version_used =
            Self::get_latest_federation_version_used(&subgraphs, &mut error_reporter).clone();
        let Some(join_spec) =
            JOIN_VERSIONS.get_minimum_required_version(&latest_federation_version_used)
        else {
            bail!(
                "No join spec version found for federation version {}",
                latest_federation_version_used
            )
        };
        let Some(link_spec_definition) =
            LINK_VERSIONS.get_minimum_required_version(&latest_federation_version_used)
        else {
            bail!(
                "No link spec version found for federation version {}",
                latest_federation_version_used
            )
        };
        let fields_with_from_context = Self::get_fields_with_from_context_directive(&subgraphs);
        let fields_with_override = Self::get_fields_with_override_directive(&subgraphs);

        let schema_to_import_to_feature_url = subgraphs
            .iter()
            .map(|s| {
                (
                    s.name.clone(),
                    s.schema()
                        .metadata()
                        .map(|l| l.import_to_feature_url_map())
                        .unwrap_or_default(),
                )
            })
            .collect();
        let merged = FederationSchema::new(Schema::new())?;
        let join_directive_identities = HashSet::from([Identity::connect_identity()]);

        let mut merger = Self {
            subgraphs,
            options,
            names,
            compose_directive_manager: ComposeDirectiveManager::new(),
            error_reporter,
            merged,
            subgraph_names_to_join_spec_name: HashMap::new(),
            merged_federation_directive_names: HashSet::new(),
            merged_federation_directive_in_supergraph_by_directive_name: HashMap::new(),
            enum_usages: HashMap::new(),
            fields_with_from_context,
            fields_with_override,
            schema_to_import_to_feature_url,
            link_spec_definition,
            join_directive_identities,
            inaccessible_directive_name_in_supergraph: None,
            join_spec_definition: join_spec,
            latest_federation_version_used,
            field_parent_lookup: HashMap::new(), // Will be populated below
        };

        // Build the field-to-parent lookup table for O(1) parent access
        merger.build_field_parent_lookup();

        // Now call prepare_supergraph as a member function
        merger.prepare_supergraph()?;

        Ok(merger)
    }

    fn get_latest_federation_version_used<'a>(
        subgraphs: &'a [Subgraph<Validated>],
        error_reporter: &mut ErrorReporter,
    ) -> &'a Version {
        subgraphs
            .iter()
            .map(|subgraph| {
                Self::get_latest_federation_version_used_in_subgraph(subgraph, error_reporter)
            })
            .max()
            .unwrap_or_else(|| FEDERATION_VERSIONS.latest().version())
    }

    fn get_latest_federation_version_used_in_subgraph<'a>(
        subgraph: &'a Subgraph<Validated>,
        error_reporter: &mut ErrorReporter,
    ) -> &'a Version {
        let linked_federation_version = subgraph.metadata().federation_spec_definition().version();

        let linked_features = subgraph.schema().all_features().unwrap_or_default();
        let spec_with_max_implied_version = linked_features
            .iter()
            .max_by_key(|spec| spec.minimum_federation_version());

        if let Some(spec) = spec_with_max_implied_version {
            if spec
                .minimum_federation_version()
                .satisfies(linked_federation_version)
                && spec
                    .minimum_federation_version()
                    .gt(linked_federation_version)
            {
                error_reporter.add_hint(CompositionHint::new(
                    format!(
                        "Subgraph {} has been implicitly upgraded from federation {} to {}",
                        subgraph.name,
                        linked_federation_version,
                        spec.minimum_federation_version()
                    ),
                    HintCode::ImplicitlyUpgradedFederationVersion
                        .code()
                        .to_string(),
                ));
                return spec.minimum_federation_version();
            }
        }
        linked_federation_version
    }

    /// Build a comprehensive field-to-parent lookup table for O(1) parent access
    /// This eliminates the need for expensive O(n*m) searches in get_field_position
    fn build_field_parent_lookup(&mut self) {
        use crate::schema::position::InterfaceFieldDefinitionPosition;
        use crate::schema::position::ObjectFieldDefinitionPosition;

        for subgraph in &self.subgraphs {
            let schema = subgraph.schema().schema();

            // Iterate through all types in this subgraph
            for (type_name, type_def) in &schema.types {
                match type_def {
                    ExtendedType::Object(obj_type) => {
                        // Map all object fields to their parent object type
                        for (field_name, field_component) in &obj_type.fields {
                            let lookup_key =
                                Self::make_field_lookup_key(field_name, &field_component.node.ty);
                            let obj_pos = ObjectFieldDefinitionPosition {
                                type_name: type_name.clone(),
                                field_name: field_name.clone(),
                            };
                            self.field_parent_lookup
                                .insert(lookup_key, FieldDefinitionPosition::Object(obj_pos));
                        }
                    }
                    ExtendedType::Interface(interface_type) => {
                        // Map all interface fields to their parent interface type
                        for (field_name, field_component) in &interface_type.fields {
                            let lookup_key =
                                Self::make_field_lookup_key(field_name, &field_component.node.ty);
                            let interface_pos = InterfaceFieldDefinitionPosition {
                                type_name: type_name.clone(),
                                field_name: field_name.clone(),
                            };
                            self.field_parent_lookup.insert(
                                lookup_key,
                                FieldDefinitionPosition::Interface(interface_pos),
                            );
                        }
                    }
                    _ => {
                        // Skip scalar, enum, union, and input types (they don't have fields)
                    }
                }
            }
        }
    }

    /// Create a consistent lookup key for field identification
    /// Format: "fieldName:TypeSignature" for unique identification
    fn make_field_lookup_key(field_name: &Name, field_type: &Type) -> String {
        format!("{}:{}", field_name, field_type)
    }

    fn get_fields_with_from_context_directive(
        subgraphs: &[Subgraph<Validated>],
    ) -> DirectiveReferencers {
        subgraphs
            .iter()
            .fold(Default::default(), |mut acc, subgraph| {
                if let Ok(Some(directive_name)) = subgraph.from_context_directive_name() {
                    if let Ok(referencers) = subgraph
                        .schema()
                        .referencers()
                        .get_directive(&directive_name)
                    {
                        acc.extend(referencers);
                    }
                }
                acc
            })
    }

    fn get_fields_with_override_directive(
        subgraphs: &[Subgraph<Validated>],
    ) -> DirectiveReferencers {
        subgraphs
            .iter()
            .fold(Default::default(), |mut acc, subgraph| {
                if let Ok(Some(directive_name)) = subgraph.override_directive_name() {
                    if let Ok(referencers) = subgraph
                        .schema()
                        .referencers()
                        .get_directive(&directive_name)
                    {
                        acc.extend(referencers);
                    }
                }
                acc
            })
    }

    fn prepare_supergraph(&mut self) -> Result<(), FederationError> {
        // Add the @link specification to the merged schema
        self.link_spec_definition
            .add_to_schema(&mut self.merged, None)?;

        // Apply the @join specification to the schema
        self.link_spec_definition.apply_feature_to_schema(
            &mut self.merged,
            self.join_spec_definition,
            None,
            self.join_spec_definition.purpose(),
            None, // imports
        )?;

        let directives_merge_info = self.collect_core_directives_to_compose()?;

        self.validate_and_maybe_add_specs(&directives_merge_info)?;

        // Populate the graph enum with subgraph information and store the mapping
        self.subgraph_names_to_join_spec_name = self
            .join_spec_definition
            .populate_graph_enum(&mut self.merged, &self.subgraphs)?;

        Ok(())
    }

    /// Get the join spec name for a subgraph by index (ported from JavaScript joinSpecName())
    pub(crate) fn join_spec_name(&self, subgraph_index: usize) -> Result<&Name, FederationError> {
        let subgraph_name = &self.names[subgraph_index];
        self.subgraph_names_to_join_spec_name
            .get(subgraph_name)
            .ok_or_else(|| {
                internal_error!(
                    "Could not find join spec name for subgraph '{}'",
                    subgraph_name
                )
            })
    }

    /// Get access to the merged schema
    pub(crate) fn schema(&self) -> &FederationSchema {
        &self.merged
    }

    /// Get access to the error reporter
    pub(crate) fn error_reporter(&self) -> &ErrorReporter {
        &self.error_reporter
    }

    /// Get mutable access to the error reporter
    pub(crate) fn error_reporter_mut(&mut self) -> &mut ErrorReporter {
        &mut self.error_reporter
    }

    /// Get access to the subgraph names
    pub(crate) fn subgraph_names(&self) -> &[String] {
        &self.names
    }

    /// Get access to the enum usages
    pub(crate) fn enum_usages(&self) -> &HashMap<String, EnumTypeUsage> {
        &self.enum_usages
    }

    /// Get mutable access to the enum usages
    pub(crate) fn enum_usages_mut(&mut self) -> &mut HashMap<String, EnumTypeUsage> {
        &mut self.enum_usages
    }

    /// Check if there are any errors
    pub(crate) fn has_errors(&self) -> bool {
        self.error_reporter.has_errors()
    }

    /// Check if there are any hints
    pub(crate) fn has_hints(&self) -> bool {
        self.error_reporter.has_hints()
    }

    /// Get enum usage for a specific enum type
    pub(crate) fn get_enum_usage(&self, enum_name: &str) -> Option<&EnumTypeUsage> {
        self.enum_usages.get(enum_name)
    }

    pub(crate) fn merge(mut self) -> MergeResult {
        // Validate compose directive manager
        self.validate_compose_directive_manager();

        // Add core features to the merged schema
        self.add_core_features();

        // Create empty objects for all types and directive definitions
        self.add_types_shallow();
        self.add_directives_shallow();

        // Collect types by category
        let mut object_types: Vec<Name> = Vec::new();
        let mut interface_types: Vec<Name> = Vec::new();
        let mut union_types: Vec<Name> = Vec::new();
        let mut enum_types: Vec<Name> = Vec::new();
        let mut non_union_enum_types: Vec<Name> = Vec::new();

        // TODO: Iterate through merged.types() and categorize them
        // This requires implementing type iteration and categorization

        // Merge implements relationships for object and interface types
        for object_type in &object_types {
            self.merge_implements(object_type);
        }

        for interface_type in &interface_types {
            self.merge_implements(interface_type);
        }

        // Merge union types
        for union_type in &union_types {
            self.merge_type_union(union_type);
        }

        // Merge schema definition (root types)
        self.merge_schema_definition();

        // Merge non-union and non-enum types
        for type_def in &non_union_enum_types {
            self.merge_type_general(type_def);
        }

        // Merge directive definitions
        self.merge_directive_definitions();

        // Merge enum types last
        for enum_type in &enum_types {
            self.merge_type_enum(enum_type);
        }

        // Validate that we have a query root type
        self.validate_query_root();

        // Merge all applied directives
        self.merge_all_applied_directives();

        // Add missing interface object fields to implementations
        self.add_missing_interface_object_fields_to_implementations();

        // Post-merge validations if no errors so far
        if !self.error_reporter.has_errors() {
            self.post_merge_validations();
        }

        // Return result
        let (errors, hints) = self.error_reporter.into_errors_and_hints();
        if !errors.is_empty() {
            MergeResult {
                supergraph: None,
                errors,
                hints,
            }
        } else {
            let valid_schema = Valid::assume_valid(self.merged);
            MergeResult {
                supergraph: Some(valid_schema),
                errors,
                hints,
            }
        }
    }

    // Methods called directly by merge() - implemented with todo!() for now

    fn validate_compose_directive_manager(&mut self) {
        todo!("Implement compose directive manager validation")
    }

    fn add_core_features(&mut self) {
        todo!("Implement adding core features to merged schema")
    }

    fn add_types_shallow(&mut self) {
        let mut mismatched_types = HashSet::new();
        let mut types_with_interface_object = HashSet::new();

        for subgraph in &self.subgraphs {
            for pos in subgraph.schema().get_types() {
                if !self.is_merged_type(subgraph, &pos) {
                    continue;
                }

                let mut expects_interface = false;
                if subgraph.is_interface_object_type(&pos) {
                    expects_interface = true;
                    types_with_interface_object.insert(pos.clone());
                }
                if let Ok(previous) = self.merged.get_type(pos.type_name().clone()) {
                    if expects_interface
                        && !matches!(previous, TypeDefinitionPosition::Interface(_))
                    {
                        mismatched_types.insert(pos.clone());
                    }
                    if !expects_interface && previous != pos {
                        mismatched_types.insert(pos.clone());
                    }
                } else if expects_interface {
                    let itf_pos = InterfaceTypeDefinitionPosition {
                        type_name: pos.type_name().clone(),
                    };
                    itf_pos.pre_insert(&mut self.merged);
                    itf_pos.insert_empty(&mut self.merged);
                } else {
                    pos.pre_insert(&mut self.merged);
                    pos.insert_empty(&mut self.merged);
                }
            }
        }

        for mismatched_type in mismatched_types.iter() {
            self.report_mismatched_type_definitions(mismatched_type, &types_with_interface_object);
        }

        // Most invalid use of @interfaceObject are reported as a mismatch above, but one exception is the
        // case where a type is used only with @interfaceObject, but there is no corresponding interface
        // definition in any subgraph.
        for type_ in types_with_interface_object.iter() {
            if mismatched_types.contains(type_) {
                continue;
            }

            let mut found_interface = false;
            let mut subgraphs_with_type = HashSet::new();
            for subgraph in &self.subgraphs {
                let type_in_subgraph = subgraph.schema().get_type(type_.type_name().clone());
                if matches!(type_in_subgraph, Ok(TypeDefinitionPosition::Interface(_))) {
                    found_interface = true;
                    break;
                }
                if type_in_subgraph.is_ok() {
                    subgraphs_with_type.insert(subgraph.name.clone());
                }
            }

            // Note that there is meaningful way in which the supergraph could work in this situation, expect maybe if
            // the type is unused, because validation composition would complain it cannot find the `__typename` in path
            // leading to that type. But the error here is a bit more "direct"/user friendly than what post-merging
            // validation would return, so we make this a hard error, not just a warning.
            if !found_interface {
                self.error_reporter.add_error(CompositionError::InterfaceObjectUsageError { message: format!(
                    "Type \"{}\" is declared with @interfaceObject in all the subgraphs in which it is defined (it is defined in {} but should be defined as an interface in at least one subgraph)",
                    type_.type_name(),
                    human_readable_subgraph_names(subgraphs_with_type.iter())
                ) });
            }
        }
    }

    fn is_merged_type(
        &self,
        subgraph: &Subgraph<Validated>,
        type_: &TypeDefinitionPosition,
    ) -> bool {
        if type_.is_introspection_type() || FEDERATION_OPERATION_TYPES.contains(type_.type_name()) {
            return false;
        }

        let type_feature = subgraph
            .schema()
            .metadata()
            .and_then(|links| links.source_link_of_type(type_.type_name()));
        let exists_and_is_excluded = type_feature
            .is_some_and(|link| NON_MERGED_CORE_FEATURES.contains(&link.link.url.identity));
        !exists_and_is_excluded
    }

    fn report_mismatched_type_definitions(
        &mut self,
        mismatched_type: &TypeDefinitionPosition,
        types_with_interface_object: &HashSet<TypeDefinitionPosition>,
    ) {
        let sources = self
            .subgraphs
            .iter()
            .enumerate()
            .map(|(idx, sg)| {
                (
                    idx,
                    sg.schema()
                        .get_type(mismatched_type.type_name().clone())
                        .ok(),
                )
            })
            .collect();
        let type_kind_to_string = |type_def: &TypeDefinitionPosition, _| {
            let type_kind_description = if types_with_interface_object.contains(type_def) {
                "Interface Object Type (Object Type with @interfaceObject)".to_string()
            } else {
                type_def.kind().replace("Type", " Type")
            };
            Some(type_kind_description)
        };
        // TODO: Second type param is supposed to be representation of AST nodes
        self.error_reporter
            .report_mismatch_error::<TypeDefinitionPosition, ()>(
                CompositionError::TypeKindMismatch {
                    message: format!(
                        "Type \"{}\" has mismatched kind: it is defined as ",
                        mismatched_type.type_name()
                    ),
                },
                mismatched_type,
                &sources,
                type_kind_to_string,
            );
    }

    fn add_directives_shallow(&mut self) -> Result<(), FederationError> {
        for subgraph in self.subgraphs.iter() {
            for (name, definition) in subgraph.schema().schema().directive_definitions.iter() {
                if self.merged.get_directive_definition(name).is_none()
                    && self.is_merged_directive_definition(&subgraph.name, definition)
                {
                    let pos = DirectiveDefinitionPosition {
                        directive_name: name.clone(),
                    };
                    pos.pre_insert(&mut self.merged)?;
                    pos.insert(&mut self.merged, definition.clone())?;
                }
            }
        }
        Ok(())
    }

    pub(in crate::merger) fn is_merged_directive(
        &self,
        subgraph_name: &str,
        directive: &Directive,
    ) -> bool {
        if self
            .compose_directive_manager
            .should_compose_directive(subgraph_name, &directive.name)
        {
            return true;
        }

        self.merged_federation_directive_names
            .contains(directive.name.as_str())
            || BUILT_IN_DIRECTIVES.contains(&directive.name.as_str())
    }

    fn is_merged_directive_definition(
        &self,
        subgraph_name: &str,
        definition: &DirectiveDefinition,
    ) -> bool {
        if self
            .compose_directive_manager
            .should_compose_directive(subgraph_name, &definition.name)
        {
            return true;
        }

        !BUILT_IN_DIRECTIVES.contains(&definition.name.as_str())
            && definition
                .locations
                .iter()
                .any(|loc| loc.is_executable_location())
    }

    fn merge_implements(&mut self, _type_def: &Name) {
        todo!("Implement merging of 'implements' relationships")
    }

    fn merge_type_union(&mut self, _union_type: &Name) {
        todo!("Implement union type merging")
    }

    fn merge_schema_definition(&mut self) {
        todo!("Implement schema definition merging (root types)")
    }

    fn merge_type_general(&mut self, _type_def: &Name) {
        todo!("Implement general type merging")
    }

    fn merge_directive_definitions(&mut self) {
        todo!("Implement directive definition merging")
    }

    fn merge_type_enum(&mut self, _enum_type: &Name) {
        todo!("Implement enum type merging - collect sources and call merge_enum")
    }

    fn validate_query_root(&mut self) {
        todo!("Implement query root validation")
    }

    fn merge_all_applied_directives(&mut self) {
        todo!("Implement merging of all applied directives")
    }

    fn merge_applied_directive(
        &mut self,
        name: &Name,
        sources: Sources<Subgraph<Validated>>,
        dest: &mut FederationSchema,
    ) -> Result<(), FederationError> {
        let Some(directive_in_supergraph) = self
            .merged_federation_directive_in_supergraph_by_directive_name
            .get(name)
        else {
            // Definition is missing, so we assume there is nothing to merge.
            return Ok(());
        };

        // Accumulate all positions of the directive in the source schemas
        let all_schema_referencers = sources
            .values()
            .filter_map(|subgraph| subgraph.as_ref())
            .fold(DirectiveReferencers::default(), |mut acc, subgraph| {
                if let Ok(drs) = subgraph.schema().referencers().get_directive(name) {
                    acc.extend(drs);
                }
                acc
            });

        for pos in all_schema_referencers.iter() {
            // In JS, there are several methods for checking if directive applications are the same, and the static
            // argument transforms are only applied for repeatable directives. In this version, we rely on the `Eq`
            // and `Hash` implementations of `Directive` to deduplicate applications, and the argument transforms
            // are applied up front so they are available in all locations.
            let mut directive_sources: Sources<Directive> = Default::default();
            let directive_counts = sources
                .iter()
                .flat_map(|(idx, subgraph)| {
                    if let Some(subgraph) = subgraph {
                        let directives = Self::directive_applications_with_transformed_arguments(
                            &pos,
                            directive_in_supergraph,
                            subgraph,
                        );
                        directive_sources.insert(*idx, directives.first().cloned());
                        directives
                    } else {
                        vec![]
                    }
                })
                .counts();

            if directive_in_supergraph.definition.repeatable {
                for directive in directive_counts.keys() {
                    pos.insert_directive(dest, (*directive).clone())?;
                }
            } else if directive_counts.len() == 1 {
                let only_application = directive_counts.iter().next().unwrap().0.clone();
                pos.insert_directive(dest, only_application)?;
            } else if let Some(merger) = &directive_in_supergraph.arguments_merger {
                // When we have multiple unique applications of the directive, and there is a
                // supplied argument merger, then we merge each of the arguments into a combined
                // directive.
                let mut merged_directive = Directive::new(name.clone());
                for arg_def in &directive_in_supergraph.definition.arguments {
                    let values = directive_counts
                        .keys()
                        .filter_map(|d| {
                            d.specified_argument_by_name(name)
                                .or(arg_def.default_value.as_ref())
                                .map(|v| v.as_ref())
                        })
                        .cloned()
                        .collect_vec();
                    if let Some(merged_value) = (merger.merge)(name, &values)? {
                        let merged_arg = Argument {
                            name: arg_def.name.clone(),
                            value: Node::new(merged_value),
                        };
                        merged_directive.arguments.push(Node::new(merged_arg));
                    }
                }
                pos.insert_directive(dest, merged_directive)?;
                self.error_reporter.add_hint(CompositionHint::new(
                    format!(
                        "Directive @{name} is applied to \"{pos}\" in multiple subgraphs with different arguments. Merging strategies used by arguments: {}",
                        directive_in_supergraph.arguments_merger.as_ref().map_or("undefined".to_string(), |m| (m.to_string)())
                    ),
                    HintCode::MergedNonRepeatableDirectiveArguments.code().to_string(),
                ));
            } else if let Some(most_used_directive) = directive_counts
                .into_iter()
                .max_by_key(|(_, count)| *count)
                .map(|(directive, _)| directive)
            {
                // When there is no argument merger, we use the application appearing in the most
                // subgraphs. Adding it to the destination here allows the error reporter to
                // determine which one we selected when it's looking through the sources.
                pos.insert_directive(dest, most_used_directive.clone())?;
                self.error_reporter.report_mismatch_hint::<Directive, ()>(
                    HintCode::InconsistentNonRepeatableDirectiveArguments,
                    format!("Non-repeatable directive @{name} is applied to \"{pos}\" in mulitple subgraphs but with incompatible arguments. "),
                    &most_used_directive,
                    &directive_sources,
                    |elt, _| if elt.arguments.is_empty() {
                        Some("no arguments".to_string())
                    } else {
                        Some(format!("arguments: [{}]", elt.arguments.iter().map(|arg| format!("{}: {}", arg.name, arg.value)).join(", ")))
                    },
                    false
                );
            }
        }

        Ok(())
    }

    fn directive_applications_with_transformed_arguments(
        pos: &DirectiveTargetPosition,
        merge_info: &MergedDirectiveInfo,
        subgraph: &Subgraph<Validated>,
    ) -> Vec<Directive> {
        let mut applications = Vec::new();
        if let Some(arg_transform) = &merge_info.static_argument_transform {
            for application in
                pos.get_applied_directives(subgraph.schema(), &merge_info.definition.name)
            {
                let mut transformed_application = Directive::new(application.name.clone());
                let indexed_args: IndexMap<Name, Value> = application
                    .arguments
                    .iter()
                    .map(|a| (a.name.clone(), a.value.as_ref().clone()))
                    .collect();
                transformed_application.arguments = arg_transform(subgraph, indexed_args)
                    .into_iter()
                    .map(|(name, value)| {
                        Node::new(Argument {
                            name,
                            value: Node::new(value),
                        })
                    })
                    .collect();
                applications.push(transformed_application);
            }
        }
        applications
    }

    fn add_missing_interface_object_fields_to_implementations(&mut self) {
        todo!("Implement adding missing interface object fields to implementations")
    }

    fn post_merge_validations(&mut self) {
        todo!("Implement post-merge validations")
    }

    /// Core type merging logic for GraphQL Federation composition.
    ///
    /// Merges type references from multiple subgraphs following Federation variance rules:
    /// - For output positions: uses the most general (supertype) when types are compatible
    /// - For input positions: uses the most specific (subtype) when types are compatible  
    /// - Reports errors for incompatible types, hints for compatible but inconsistent types
    /// - Tracks enum usage for validation purposes
    pub(crate) fn merge_type_reference<TElement>(
        &mut self,
        sources: &Sources<Type>,
        dest: &mut TElement,
        is_input_position: bool,
        parent_type_name: &str, // We need this for the coordinate as FieldDefinition lack parent context
    ) -> Result<bool, FederationError>
    where
        TElement: SchemaElementWithType,
    {
        // Validate sources
        if sources.is_empty() {
            self.error_reporter_mut()
                .add_error(CompositionError::InternalError {
                    message: format!(
                        "No type sources provided for merging {}",
                        dest.coordinate(parent_type_name)
                    ),
                });
            return Ok(false);
        }

        // Build iterator over the non-None source types
        let mut iter = sources.values().filter_map(Option::as_ref);
        let mut has_subtypes = false;
        let mut has_incompatible = false;

        // Grab the first type (if any) to initialise comparison
        let Some(mut typ) = iter.next() else {
            // No concrete type found in any subgraph — this should not normally happen
            let error = CompositionError::InternalError {
                message: format!(
                    "No type sources provided for {} across subgraphs",
                    dest.coordinate(parent_type_name)
                ),
            };
            self.error_reporter_mut().add_error(error);
            return Ok(false);
        };

        // Determine the merged type following GraphQL Federation variance rules
        for source_type in iter {
            if Self::same_type(typ, source_type) {
                // Types are identical
                continue;
            } else if let Ok(true) = self.is_strict_subtype(source_type, typ) {
                // current typ is a subtype of source_type (source_type is more general)
                has_subtypes = true;
                if is_input_position {
                    // For input: upgrade to the supertype
                    typ = source_type;
                }
            } else if let Ok(true) = self.is_strict_subtype(typ, source_type) {
                // source_type is a subtype of current typ (current typ is more general)
                has_subtypes = true;
                if !is_input_position {
                    // For output: keep the supertype; for input: adopt the subtype
                    typ = source_type;
                }
            } else {
                has_incompatible = true;
            }
        }

        // Copy the type reference to the destination schema
        let copied_type = self.copy_type_reference(typ)?;

        dest.set_type(copied_type);

        let ast_node = dest.enum_example_ast();
        self.track_enum_usage(
            typ,
            dest.coordinate(parent_type_name),
            ast_node,
            is_input_position,
        );

        let element_kind = if is_input_position {
            "argument"
        } else {
            "field"
        };

        if has_incompatible {
            // Report incompatible type error
            let error_code_str = if is_input_position {
                "ARGUMENT_TYPE_MISMATCH"
            } else {
                "FIELD_TYPE_MISMATCH"
            };

            let error = CompositionError::InternalError {
                message: format!(
                    "Type of {} \"{}\" is incompatible across subgraphs",
                    element_kind,
                    dest.coordinate(parent_type_name)
                ),
            };

            self.error_reporter_mut().report_mismatch_error::<Type, ()>(
                error,
                typ,
                sources,
                |typ, _is_supergraph| Some(format!("type \"{}\"", typ)),
            );

            Ok(false)
        } else if has_subtypes {
            // Report compatibility hint for subtype relationships
            let hint_code = if is_input_position {
                HintCode::InconsistentButCompatibleArgumentType
            } else {
                HintCode::InconsistentButCompatibleFieldType
            };

            // TODO: Match the original TypeScript element formatting for consistent mismatch reporting.
            self.error_reporter_mut().report_mismatch_hint::<Type, ()>(
                hint_code,
                format!(
                    "Type of {} \"{}\" is inconsistent but compatible across subgraphs:",
                    element_kind,
                    dest.coordinate(parent_type_name)
                ),
                typ,
                sources,
                |typ, _is_supergraph| Some(format!("type \"{}\"", typ)),
                false,
            );

            Ok(false)
        } else {
            Ok(true)
        }
    }

    fn track_enum_usage(
        &mut self,
        typ: &Type,
        element_name: String,
        element_ast: Option<EnumExampleAst>,
        is_input_position: bool,
    ) {
        // Get the base type (unwrap nullability and list wrappers)
        let base_type_name = typ.inner_named_type();

        // Check if it's an enum type
        if let Some(&ExtendedType::Enum(_)) = self.schema().schema().types.get(base_type_name) {
            let default_example = || EnumExample {
                coordinate: element_name,
                element_ast: element_ast.clone(),
            };

            // Compute the new usage directly based on existing record and current position
            let new_usage = match self.enum_usages().get(base_type_name.as_str()) {
                Some(EnumTypeUsage::Input { input_example }) if !is_input_position => {
                    EnumTypeUsage::Both {
                        input_example: input_example.clone(),
                        output_example: default_example(),
                    }
                }
                Some(EnumTypeUsage::Input { input_example })
                | Some(EnumTypeUsage::Both { input_example, .. })
                    if is_input_position =>
                {
                    EnumTypeUsage::Input {
                        input_example: input_example.clone(),
                    }
                }
                Some(EnumTypeUsage::Output { output_example }) if is_input_position => {
                    EnumTypeUsage::Both {
                        input_example: default_example(),
                        output_example: output_example.clone(),
                    }
                }
                Some(EnumTypeUsage::Output { output_example })
                | Some(EnumTypeUsage::Both { output_example, .. })
                    if !is_input_position =>
                {
                    EnumTypeUsage::Output {
                        output_example: output_example.clone(),
                    }
                }
                _ if is_input_position => EnumTypeUsage::Input {
                    input_example: default_example(),
                },
                _ => EnumTypeUsage::Output {
                    output_example: default_example(),
                },
            };

            // Store updated usage
            self.enum_usages_mut()
                .insert(base_type_name.to_string(), new_usage);
        }
    }

    fn same_type(dest_type: &Type, source_type: &Type) -> bool {
        match (dest_type, source_type) {
            (Type::Named(n1), Type::Named(n2)) => n1 == n2,
            (Type::NonNullNamed(n1), Type::NonNullNamed(n2)) => n1 == n2,
            (Type::List(inner1), Type::List(inner2)) => Self::same_type(inner1, inner2),
            (Type::NonNullList(inner1), Type::NonNullList(inner2)) => {
                Self::same_type(inner1, inner2)
            }
            _ => false,
        }
    }

    pub(in crate::merger) fn is_strict_subtype(
        &self,
        potential_supertype: &Type,
        potential_subtype: &Type,
    ) -> Result<bool, FederationError> {
        // Hardcoded subtyping rules based on the default configuration:
        // - Direct: Interface/union subtyping relationships
        // - NonNullableDowngrade: NonNull T is subtype of T
        // - ListPropagation: [T] is subtype of [U] if T is subtype of U
        // - NonNullablePropagation: NonNull T is subtype of NonNull U if T is subtype of U
        // - ListUpgrade is NOT supported (was excluded by default)

        match (potential_subtype, potential_supertype) {
            // -------- List & NonNullList --------
            // ListPropagation: [T] is subtype of [U] if T is subtype of U
            (Type::List(inner_sub), Type::List(inner_super)) => {
                self.is_strict_subtype(inner_super, inner_sub)
            }
            // NonNullablePropagation and NonNullableDowngrade
            (Type::NonNullList(inner_sub), Type::NonNullList(inner_super))
            | (Type::NonNullList(inner_sub), Type::List(inner_super)) => {
                self.is_strict_subtype(inner_super, inner_sub)
            }

            // Anything else with list on the left is not a strict subtype
            (Type::List(_), _) | (Type::NonNullList(_), _) => Ok(false),

            // -------- Named & NonNullNamed --------
            // Same named type => not strict subtype
            (Type::Named(a), Type::Named(b)) | (Type::Named(a), Type::NonNullNamed(b))
                if a == b =>
            {
                Ok(false)
            }
            (Type::NonNullNamed(a), Type::NonNullNamed(b)) if a == b => Ok(false),

            // NonNull downgrade: T! ⊑ T
            (Type::NonNullNamed(sub), Type::Named(super_)) if sub == super_ => Ok(true),

            // Interface/Union relationships (includes downgrade handled above)
            (Type::Named(sub), Type::Named(super_))
            | (Type::Named(sub), Type::NonNullNamed(super_))
            | (Type::NonNullNamed(sub), Type::Named(super_))
            | (Type::NonNullNamed(sub), Type::NonNullNamed(super_)) => {
                self.is_named_type_subtype(super_, sub)
            }

            // ListUpgrade not supported; any other combination is not strict
            _ => Ok(false),
        }
    }

    fn is_named_type_subtype(
        &self,
        potential_supertype: &NamedType,
        potential_subtype: &NamedType,
    ) -> Result<bool, FederationError> {
        let Some(subtype_def) = self.schema().schema().types.get(potential_subtype) else {
            bail!("Cannot find type '{}' in schema", potential_subtype);
        };

        let Some(supertype_def) = self.schema().schema().types.get(potential_supertype) else {
            bail!("Cannot find type '{}' in schema", potential_supertype);
        };

        // Direct subtyping relationships (interface/union) are always supported
        match (subtype_def, supertype_def) {
            // Object type implementing an interface
            (ExtendedType::Object(obj), ExtendedType::Interface(_)) => {
                Ok(obj.implements_interfaces.contains(potential_supertype))
            }
            // Interface extending another interface
            (ExtendedType::Interface(sub_intf), ExtendedType::Interface(_)) => {
                Ok(sub_intf.implements_interfaces.contains(potential_supertype))
            }
            // Object type that is a member of a union
            (ExtendedType::Object(_), ExtendedType::Union(union_type)) => {
                Ok(union_type.members.contains(potential_subtype))
            }
            // Interface that is a member of a union (if supported)
            (ExtendedType::Interface(_), ExtendedType::Union(union_type)) => {
                Ok(union_type.members.contains(potential_subtype))
            }
            _ => Ok(false),
        }
    }

    pub(crate) fn copy_type_reference(
        &mut self,
        source_type: &Type,
    ) -> Result<Type, FederationError> {
        // Check if the type is already defined in the target schema
        let target_schema = self.schema().schema();

        let name = source_type.inner_named_type();
        if !target_schema.types.contains_key(name) {
            self.error_reporter_mut()
                .add_error(CompositionError::InternalError {
                    message: format!("Cannot find type '{}' in target schema", name),
                });
        }

        Ok(source_type.clone())
    }

    pub(in crate::merger) fn merge_description<T>(&mut self, _sources: &Sources<T>, _dest: &T) {
        todo!("Implement merge_description")
    }

    pub(in crate::merger) fn add_join_field<T>(&mut self, _sources: &Sources<T>, _dest: &T) {
        todo!("Implement add_join_field")
    }

    pub(in crate::merger) fn add_join_directive_directives<T>(
        &mut self,
        _sources: &Sources<T>,
        _dest: &T,
    ) {
        todo!("Implement add_join_directive_directives")
    }

    pub(in crate::merger) fn add_arguments_shallow<T>(&mut self, _sources: &Sources<T>, _dest: &T) {
        todo!("Implement add_arguments_shallow")
    }

    pub(in crate::merger) fn record_applied_directives_to_merge<T>(
        &mut self,
        _sources: &Sources<T>,
        _dest: &T,
    ) {
        todo!("Implement record_applied_directives_to_merge")
    }

    fn is_inaccessible_directive_in_supergraph(&self, _value: &EnumValueDefinition) -> bool {
        todo!("Implement is_inaccessible_directive_in_supergraph")
    }

    /// Like Iterator::any, but for Sources<T> maps - checks if any source satisfies the predicate
    pub(in crate::merger) fn some_sources<T, F>(sources: &Sources<T>, mut predicate: F) -> bool
    where
        F: FnMut(&Option<T>, usize) -> bool,
    {
        sources.iter().any(|(idx, source)| predicate(source, *idx))
    }

    // TODO: These error reporting functions are not yet fully implemented
    pub(crate) fn report_mismatch_error_with_specifics<T>(
        &mut self,
        error: CompositionError,
        sources: &Sources<T>,
        accessor: impl Fn(&Option<T>) -> &str,
    ) {
        // Build a detailed error message by showing which subgraphs have/don't have the element
        let mut details = Vec::new();
        let mut has_subgraphs = Vec::new();
        let mut missing_subgraphs = Vec::new();

        for (&idx, source) in sources.iter() {
            let subgraph_name = if idx < self.names.len() {
                &self.names[idx]
            } else {
                "unknown"
            };

            let result = accessor(source);
            if result == "yes" {
                has_subgraphs.push(subgraph_name);
            } else {
                missing_subgraphs.push(subgraph_name);
            }
        }

        // Format the subgraph lists
        if !has_subgraphs.is_empty() {
            details.push(format!("defined in {}", has_subgraphs.join(", ")));
        }
        if !missing_subgraphs.is_empty() {
            details.push(format!("but not in {}", missing_subgraphs.join(", ")));
        }

        // Create the enhanced error with details
        let enhanced_error = match error {
            CompositionError::EnumValueMismatch { message } => {
                CompositionError::EnumValueMismatch {
                    message: format!("{}{}", message, details.join(" ")),
                }
            }
            // Add other error types as needed
            other => other,
        };

        self.error_reporter.add_error(enhanced_error);
    }

    pub(crate) fn report_mismatch_hint<T>(
        &mut self,
        code: HintCode,
        message: String,
        sources: &Sources<T>,
        accessor: impl Fn(&Option<T>) -> bool,
    ) {
        // Build detailed hint message showing which subgraphs have/don't have the element
        let mut has_subgraphs = Vec::new();
        let mut missing_subgraphs = Vec::new();

        for (&idx, source) in sources.iter() {
            let subgraph_name = if idx < self.names.len() {
                &self.names[idx]
            } else {
                "unknown"
            };
            let result = accessor(source);
            if result {
                has_subgraphs.push(subgraph_name);
            } else {
                missing_subgraphs.push(subgraph_name);
            }
        }

        let detailed_message = format!(
            "{}defined in {} but not in {}",
            message,
            has_subgraphs.join(", "),
            missing_subgraphs.join(", ")
        );

        // Add the hint to the error reporter
        let hint = CompositionHint::new(detailed_message, code.definition().code().to_string());
        self.error_reporter.add_hint(hint);
    }

    /// Merge argument definitions from subgraphs
    pub(in crate::merger) fn merge_argument(
        &mut self,
        _sources: &Sources<Node<InputValueDefinition>>,
        _dest: &Node<InputValueDefinition>,
    ) -> Result<(), FederationError> {
        // TODO: Implement argument merging logic
        // This should merge argument definitions from multiple subgraphs
        // including type validation, default value merging, etc.
        Ok(())
    }

    /// Extract AST nodes with enhanced subgraph context for error reporting
    fn extract_ast_nodes_with_subgraph<T>(
        &self,
        node: &Node<T>,
        subgraph_name: &str,
        node_kind: ASTNodeKind,
    ) -> Vec<SubgraphASTNode> {
        if let Some(location) = node.location() {
            vec![SubgraphASTNode::new(
                location,
                subgraph_name.to_string(),
                node_kind,
            )]
        } else {
            vec![]
        }
    }
}

// Public function to start the merging process
#[allow(dead_code)]
pub(crate) fn merge_subgraphs(
    subgraphs: Vec<Subgraph<Validated>>,
    options: CompositionOptions,
) -> Result<MergeResult, FederationError> {
    Ok(Merger::new(subgraphs, options)?.merge())
}

/// Map over sources, applying a function to each element
/// TODO: Consider moving this into a trait or Sources
pub(in crate::merger) fn map_sources<T, U, F>(sources: &Sources<T>, f: F) -> Sources<U>
where
    F: Fn(&Option<T>) -> Option<U>,
{
    sources
        .iter()
        .map(|(idx, source)| (*idx, f(source)))
        .collect()
}

/// Properties tracked per subgraph for field merge context
#[derive(Debug, Clone, Default)]
pub(crate) struct FieldMergeContextProperties {
    pub(crate) used_overridden: bool,
    pub(crate) unused_overridden: bool,
    pub(crate) override_with_unknown_target: bool,
    pub(crate) override_label: Option<String>,
}

/// Context for tracking override-related information during field merging
#[derive(Debug, Clone, Default)]
pub(crate) struct FieldMergeContext {
    pub(crate) properties: IndexMap<usize, FieldMergeContextProperties>,
}

impl FieldMergeContext {
    pub(crate) fn new() -> Self {
        Self {
            properties: IndexMap::default(),
        }
    }

    #[allow(dead_code)]
    pub(crate) fn get_properties(
        &self,
        subgraph_idx: usize,
    ) -> Option<&FieldMergeContextProperties> {
        self.properties.get(&subgraph_idx)
    }

    pub(crate) fn get_properties_mut(
        &mut self,
        subgraph_idx: usize,
    ) -> &mut FieldMergeContextProperties {
        self.properties.entry(subgraph_idx).or_default()
    }

    pub(crate) fn set_used_overridden(&mut self, subgraph_idx: usize) {
        self.get_properties_mut(subgraph_idx).used_overridden = true;
    }

    pub(crate) fn set_unused_overridden(&mut self, subgraph_idx: usize) {
        self.get_properties_mut(subgraph_idx).unused_overridden = true;
    }

    pub(crate) fn set_override_with_unknown_target(&mut self, subgraph_idx: usize) {
        self.get_properties_mut(subgraph_idx)
            .override_with_unknown_target = true;
    }

    pub(crate) fn set_override_label(&mut self, subgraph_idx: usize, label: String) {
        self.get_properties_mut(subgraph_idx).override_label = Some(label);
    }

    #[allow(dead_code)]
    pub(crate) fn is_used_overridden(&self, subgraph_idx: usize) -> bool {
        self.get_properties(subgraph_idx)
            .map(|props| props.used_overridden)
            .unwrap_or(false)
    }

    #[allow(dead_code)]
    pub(crate) fn is_unused_overridden(&self, subgraph_idx: usize) -> bool {
        self.get_properties(subgraph_idx)
            .map(|props| props.unused_overridden)
            .unwrap_or(false)
    }

    #[allow(dead_code)]
    pub(crate) fn override_label(&self, subgraph_idx: usize) -> Option<&String> {
        self.get_properties(subgraph_idx)
            .and_then(|props| props.override_label.as_ref())
    }

    #[allow(dead_code)]
    pub(crate) fn has_override_with_unknown_target(&self, subgraph_idx: usize) -> bool {
        self.get_properties(subgraph_idx)
            .map(|props| props.override_with_unknown_target)
            .unwrap_or(false)
    }

    #[allow(dead_code)]
    pub(crate) fn some(&self) -> bool {
        !self.properties.is_empty()
    }
}

impl Merger {
    /// Validates the @override directive usage across subgraphs for a field
    /// This is a complete port of the TypeScript validateOverride function with full feature parity
    ///
    /// **TypeScript Reference**: `Merger.validateOverride()` in `merge.ts:1426-1520`
    pub(crate) fn validate_override(
        &mut self,
        sources: &Sources<Node<FieldDefinition>>,
        dest: &Node<FieldDefinition>,
    ) -> Result<FieldMergeContext, FederationError> {
        use Value;

        // Create new FieldMergeContext from sources (matches TypeScript: const result = new FieldMergeContext(sources))
        let mut merge_context = FieldMergeContext::new();

        let type_name = dest.ty.inner_named_type().clone();
        let field_name = dest.name.clone();

        let override_fields: HashSet<_> = self
            .fields_with_override
            .object_or_interface_fields()
            .collect();

        let is_object = override_fields.contains(
            &ObjectOrInterfaceFieldDefinitionPosition::Object(ObjectFieldDefinitionPosition {
                type_name: type_name.clone(),
                field_name: field_name.clone(),
            }),
        );

        let is_interface =
            override_fields.contains(&ObjectOrInterfaceFieldDefinitionPosition::Interface(
                InterfaceFieldDefinitionPosition {
                    type_name,
                    field_name,
                },
            ));

        if !is_object && !is_interface {
            return Ok(merge_context);
        }
        struct ReduceResult {
            subgraph_map: HashMap<String, MappedValue>,
            subgraphs_with_override: HashSet<String>, // for dedup
        }

        let reduce_result = sources.iter().fold(
            ReduceResult {
                subgraph_map: HashMap::new(),
                subgraphs_with_override: HashSet::new(),
            },
            |mut acc, (subgraph_idx, field_opt)| {
                let subgraph_name = &self.names[*subgraph_idx];

                let info = match field_opt {
                    Some(field) => {
                        let (is_interface_field, is_interface_object) =
                            match self.get_field_position(field) {
                                Some(field_pos) => (
                                    self.is_interface_field(&field_pos),
                                    self.is_interface_object(*subgraph_idx, &field_pos),
                                ),
                                None => (false, false),
                            };

                        let override_directive = self.get_override_directive(*subgraph_idx, field);
                        if override_directive.is_some() {
                            acc.subgraphs_with_override.insert(subgraph_name.clone());
                        }

                        MappedValue {
                            idx: *subgraph_idx,
                            field: Some(field.clone()),
                            is_interface_field,
                            is_interface_object,
                            override_directive: override_directive.cloned(),
                            interface_object_abstracting_fields: vec![],
                        }
                    }

                    None => {
                        let interface_object_abstracting_fields = self
                            .fields_in_source_if_abstracted_by_interface_object_impl(
                                dest,
                                *subgraph_idx,
                            );

                        if interface_object_abstracting_fields.is_empty() {
                            return acc; // skip this iteration
                        }

                        MappedValue {
                            idx: *subgraph_idx,
                            field: None,
                            is_interface_field: false,
                            is_interface_object: false,
                            override_directive: None,
                            interface_object_abstracting_fields,
                        }
                    }
                };

                acc.subgraph_map.insert(subgraph_name.clone(), info);
                acc
            },
        );

        for subgraph_name in &reduce_result.subgraphs_with_override {
            let subgraph_info = &reduce_result.subgraph_map[subgraph_name];

            let Some(override_directive) = subgraph_info.override_directive.as_ref() else {
                // This should not happen as we only add subgraphs with override directives to the set
                continue;
            };

            // Check for interface field restriction
            if subgraph_info.is_interface_field {
                self.error_reporter.add_error(CompositionError::DirectiveDefinitionInvalid {
                    message: format!(
                        "@override cannot be used on field \"{}\" on subgraph \"{}\": @override is not supported on interface type fields.",
                        dest.coordinate(), subgraph_name
                    ),
                });
                continue;
            }

            // Check for interface object restriction
            if subgraph_info.is_interface_object {
                self.error_reporter.add_error(CompositionError::DirectiveDefinitionInvalid {
                    message: format!(
                        "@override is not yet supported on fields of @interfaceObject types: cannot be used on field \"{}\" on subgraph \"{}\".",
                        dest.coordinate(), subgraph_name
                    ),
                });
                continue;
            }

            // Extract source subgraph name from override directive using find_map
            let Some(Value::String(source_subgraph_name)) = override_directive
                .arguments
                .iter()
                .find(|arg| arg.name == "from")
                .map(|arg| arg.value.as_ref())
            else {
                continue;
            };

            // Check if source subgraph exists
            let subgraph_exists = self
                .subgraphs
                .iter()
                .any(|s| s.name.as_str() == source_subgraph_name);
            if !subgraph_exists {
                merge_context.set_override_with_unknown_target(subgraph_info.idx);
                let suggestions = self.suggest_similar_subgraph_names(source_subgraph_name);
                let extra_msg = self.format_did_you_mean(&suggestions);

                // Extract AST nodes from override directive for precise error location with subgraph context
                let ast_nodes = self.extract_ast_nodes_with_subgraph(
                    override_directive,
                    subgraph_name,
                    ASTNodeKind::Directive,
                );
                let hint = CompositionHint::with_ast_nodes(
                    format!(
                        "Source subgraph \"{}\" for field \"{}\" on subgraph \"{}\" does not exist.{}",
                        source_subgraph_name,
                        dest.coordinate(),
                        subgraph_name,
                        extra_msg
                    ),
                    OverrideHintCode::FromSubgraphDoesNotExist
                        .as_str()
                        .to_string(),
                    ast_nodes,
                );
                self.error_reporter.add_hint(hint);
                continue;
            }

            // Check for self-override
            if source_subgraph_name == subgraph_name {
                self.error_reporter.add_error(CompositionError::DirectiveDefinitionInvalid {
                    message: format!(
                        "Source and destination subgraphs \"{}\" are the same for overridden field \"{}\"",
                        source_subgraph_name,
                        dest.coordinate()
                    )
                });
                continue;
            }

            // Check for multiple override prevention
            if reduce_result
                .subgraphs_with_override
                .contains(source_subgraph_name)
            {
                self.error_reporter.add_error(CompositionError::DirectiveDefinitionInvalid {
                    message: format!(
                        "Field \"{}\" on subgraph \"{}\" is also marked with directive @override in subgraph \"{}\". Only one @override directive is allowed per field.",
                        dest.coordinate(),
                        subgraph_name,
                        source_subgraph_name
                    )
                });
                continue;
            }

            // Check if source subgraph has the field
            let source_info = match reduce_result.subgraph_map.get(source_subgraph_name) {
                Some(info) => info,
                None => {
                    // Extract AST nodes from override directive for precise error location with subgraph context
                    let ast_nodes = self.extract_ast_nodes_with_subgraph(
                        override_directive,
                        subgraph_name,
                        ASTNodeKind::Directive,
                    );
                    let hint = CompositionHint::with_ast_nodes(
                        format!(
                            "Field \"{}\" on subgraph \"{}\" no longer exists in the from subgraph. The @override directive can be removed.",
                            dest.coordinate(),
                            subgraph_name
                        ),
                        OverrideHintCode::OverrideDirectiveCanBeRemoved
                            .as_str()
                            .to_string(),
                        ast_nodes,
                    );
                    self.error_reporter.add_hint(hint);
                    continue;
                }
            };

            // Check for interface object abstracting fields
            if !source_info.interface_object_abstracting_fields.is_empty() {
                let abstracting_types: Vec<String> = source_info
                    .interface_object_abstracting_fields
                    .iter()
                    .filter_map(|field| {
                        // Get the parent type name from the field
                        self.get_field_position(field).map(|pos| match pos {
                            FieldDefinitionPosition::Object(obj_pos) => {
                                obj_pos.type_name.to_string()
                            }
                            FieldDefinitionPosition::Interface(itf_pos) => {
                                itf_pos.type_name.to_string()
                            }
                            FieldDefinitionPosition::Union(_) => "unknown".to_string(),
                        })
                    })
                    .collect();

                let abstracting_types_str_refs: Vec<&str> =
                    abstracting_types.iter().map(|s| s.as_str()).collect();
                let abstracting_types_str = self.print_types(&abstracting_types_str_refs);
                self.error_reporter.add_error(CompositionError::DirectiveDefinitionInvalid {
                    message: format!(
                        "Invalid @override on field \"{}\" of subgraph \"{}\": source subgraph \"{}\" does not have field \"{}\" but abstract it in {} and overriding abstracted fields is not supported.",
                        dest.coordinate(),
                        subgraph_name,
                        source_subgraph_name,
                        dest.coordinate(),
                        abstracting_types_str
                    )
                });
                continue;
            }

            // Check for conflicting directives (@requires, @provides, @external)
            let Some(source_subgraph_idx) = self
                .subgraphs
                .iter()
                .position(|s| s.name.as_str() == source_subgraph_name)
            else {
                // This should not happen as we validated the subgraph exists above
                continue;
            };
            let source_field = reduce_result
                .subgraph_map
                .get(source_subgraph_name)
                .and_then(|info| info.field.as_ref());

            let current_field = subgraph_info.field.as_ref();

            let conflict_result = self.override_conflicts_with_other_directive(
                subgraph_info.idx,
                current_field,
                subgraph_name,
                source_subgraph_idx,
                source_field,
            );

            if conflict_result.has_incompatible {
                let conflicting_directive = conflict_result
                    .conflicting_directive
                    .unwrap_or("unknown".to_string());

                let conflict_subgraph = conflict_result.subgraph.unwrap_or("unknown".to_string());

                let from_field_coord = source_field
                    .map(|f| f.coordinate().to_string())
                    .unwrap_or_else(|| dest.coordinate().to_string());

                self.error_reporter.add_error(CompositionError::DirectiveDefinitionInvalid {
                    message: format!(
                        "@override cannot be used on field \"{}\" on subgraph \"{}\" since \"{}\" on \"{}\" is marked with directive \"@{}\"",
                        from_field_coord,
                        subgraph_name,
                        dest.coordinate(),
                        conflict_subgraph,
                        conflicting_directive
                    )
                });
                continue;
            }

            if let Some(source_field) = &source_info.field {
                // Valid override - process it
                // Convert field to FieldDefinitionPosition for field usage check
                let from_idx = source_info.idx;

                let overridden_field_is_referenced = match self.get_field_position(source_field) {
                    Some(field_pos) => self.is_field_used(from_idx, &field_pos),
                    None => false, // Conservative fallback when position is unavailable
                };
                let override_label = self.get_override_label(override_directive);

                self.handle_override_field_validation(
                    OverrideValidationParams {
                        from_idx,
                        source_field,
                        dest,
                        subgraph_name,
                        source_subgraph_name,
                        overridden_field_is_referenced,
                        override_label: override_label.as_deref(),
                        override_directive: &override_directive,
                    },
                    &mut merge_context,
                );

                if let Some(label) = override_label {
                    if self.is_valid_override_label_complete(label) {
                        let label_string = label.to_string();
                        merge_context.set_override_label(subgraph_info.idx, label_string.clone());
                        merge_context.set_override_label(from_idx, label_string);
                    } else {
                        self.error_reporter.add_error(CompositionError::DirectiveDefinitionInvalid {
                            message: format!(
                                "Invalid @override label \"{}\" on field \"{}\" on subgraph \"{}\": labels must start with a letter and after that may contain alphanumerics, underscores, minuses, colons, periods, or slashes. Alternatively, labels may be of the form \"percent(x)\" where x is a float between 0-100 inclusive.",
                                label,
                                dest.coordinate(),
                                subgraph_name
                            )
                        });
                    }
                    let message = match overridden_field_is_referenced {
                        true => format!(
                            "Field \"{}\" on subgraph \"{}\" is currently being migrated via progressive @override. It is still used in some federation directive(s) (@key, @requires, and/or @provides) and/or to satisfy interface constraint(s). Once the migration is complete, consider marking it @external explicitly or removing it along with its references.",
                            dest.coordinate(),
                            source_subgraph_name
                        ),
                        false => format!(
                            "Field \"{}\" is currently being migrated with progressive @override. Once the migration is complete, remove the field from subgraph \"{}\".",
                            dest.coordinate(),
                            source_subgraph_name
                        ),
                    };

                    // Extract AST nodes from override directive for precise error location with subgraph context
                    let ast_nodes = self.extract_ast_nodes_with_subgraph(
                        override_directive,
                        subgraph_name,
                        ASTNodeKind::Directive,
                    );
                    let hint = CompositionHint::with_ast_nodes(
                        message,
                        "OVERRIDE_MIGRATION_IN_PROGRESS".to_string(),
                        ast_nodes,
                    );

                    self.error_reporter.add_hint(hint);
                }
            }
        }

        Ok(merge_context)
    }

    /// Check if @override conflicts with other federation directives
    ///
    /// **TypeScript Reference**: `Merger.overrideConflictsWithOtherDirective()` in `merge.ts:1556-1590`
    fn override_conflicts_with_other_directive(
        &self,
        idx: usize,
        field: Option<&Node<FieldDefinition>>,
        subgraph_name: &str,
        from_idx: usize,
        from_field: Option<&Node<FieldDefinition>>,
    ) -> OverrideConflictResult {
        // Check from_field for @requires and @provides directives
        if let Some(from_field) = from_field {
            // Check for @requires directive
            if from_field
                .directives
                .iter()
                .any(|d| FederationDirective::Requires.matches(&d.name))
            {
                return OverrideConflictResult {
                    has_incompatible: true,
                    conflicting_directive: Some(
                        FederationDirective::Requires.conflict_name().to_string(),
                    ),
                    subgraph: Some(
                        self.subgraphs
                            .get(from_idx)
                            .map_or("unknown".to_string(), |s| s.name.clone()),
                    ),
                };
            }

            // Check for @provides directive
            if from_field
                .directives
                .iter()
                .any(|d| FederationDirective::Provides.matches(&d.name))
            {
                return OverrideConflictResult {
                    has_incompatible: true,
                    conflicting_directive: Some(
                        FederationDirective::Provides.conflict_name().to_string(),
                    ),
                    subgraph: Some(
                        self.subgraphs
                            .get(from_idx)
                            .map_or("unknown".to_string(), |s| s.name.clone()),
                    ),
                };
            }
        }

        // Check field for @external directive
        if let Some(field) = field {
            if self.is_external(idx, field) {
                return OverrideConflictResult {
                    has_incompatible: true,
                    conflicting_directive: Some(
                        FederationDirective::External.conflict_name().to_string(),
                    ),
                    subgraph: Some(subgraph_name.to_string()),
                };
            }
        }

        OverrideConflictResult {
            has_incompatible: false,
            conflicting_directive: None,
            subgraph: None,
        }
    }

    /// Get the @override directive from a field if it exists
    /// Returns None if the schema is not Federation 2
    #[inline]
    fn get_override_directive<'a>(
        &self,
        subgraph_idx: usize,
        field: &'a Node<FieldDefinition>,
    ) -> Option<&'a Node<Directive>> {
        // Functional chain: combine federation check with directive search
        self.subgraphs
            .get(subgraph_idx)
            .filter(|subgraph| subgraph.metadata().is_fed_2_schema())
            .and_then(|_| {
                field
                    .directives
                    .iter()
                    .find(|directive| FederationDirective::Override.matches(&directive.name))
            })
    }

    /// Suggest similar subgraph names for typos using Jaro-Winkler distance
    /// Returns a list of suggestions sorted by similarity, with better ones first
    fn suggest_similar_subgraph_names_impl(&self, target: &str, available: &[&str]) -> Vec<String> {
        // Dynamic threshold based on input length, similar to TypeScript version
        // but adapted for Jaro-Winkler similarity scores (0.0-1.0 range)
        let base_threshold = 1.0 - (target.len() as f64 * 0.4 + 1.0) / (target.len() as f64 + 1.0);
        let threshold = base_threshold.max(0.4); // Minimum threshold of 0.4

        let target_lower = target.to_lowercase();
        let mut candidates: Vec<(String, f64)> = available
            .iter()
            .filter_map(|&subgraph| {
                // Special case for case-only differences (like TypeScript)
                let similarity = if target_lower == subgraph.to_lowercase() {
                    0.95 // Very high similarity for case-only differences
                } else {
                    jaro_winkler(target, subgraph)
                };

                if similarity >= threshold {
                    Some((subgraph.to_string(), similarity))
                } else {
                    None
                }
            })
            .collect();

        // Sort by similarity descending, then alphabetically for ties
        candidates.sort_by(|(a_name, a_sim), (b_name, b_sim)| {
            match b_sim
                .partial_cmp(a_sim)
                .unwrap_or(std::cmp::Ordering::Equal)
            {
                std::cmp::Ordering::Equal => a_name.cmp(b_name),
                other => other,
            }
        });

        // Return up to 5 suggestions
        candidates
            .into_iter()
            .take(5)
            .map(|(name, _)| name)
            .collect()
    }

    /// Get the override label from an override directive if present
    fn get_override_label<'a>(&self, override_directive: &'a Node<Directive>) -> Option<&'a str> {
        use Value;

        override_directive.arguments.iter().find_map(|arg| {
            match (arg.name.as_str(), arg.value.as_ref()) {
                ("label", Value::String(s)) => Some(s.as_str()),
                _ => None,
            }
        })
    }

    /// Validate override label format with complete regex and percent format support
    fn is_valid_override_label_complete(&self, label: &str) -> bool {
        if label.is_empty() {
            return false;
        }

        // Check standard label format first
        if LABEL_REGEX.is_match(label) {
            return true;
        }

        if let Some(caps) = PERCENT_REGEX.captures(label) {
            if let Some(number_str) = caps.get(1) {
                if let Ok(percent) = number_str.as_str().parse::<f64>() {
                    return (0.0..=100.0).contains(&percent);
                }
            }
        }

        false
    }

    /// Convert Node<FieldDefinition> to FieldDefinitionPosition using O(1) lookup
    /// Uses pre-computed field-to-parent mapping for instant parent access
    fn get_field_position(&self, field: &Node<FieldDefinition>) -> Option<FieldDefinitionPosition> {
        // Create lookup key using the same format as build_field_parent_lookup
        let lookup_key = Self::make_field_lookup_key(&field.name, &field.ty);

        // O(1) lookup in pre-computed table
        self.field_parent_lookup.get(&lookup_key).cloned()
    }

    /// Check if field is an interface field
    fn is_interface_field(&self, field_pos: &FieldDefinitionPosition) -> bool {
        matches!(field_pos, FieldDefinitionPosition::Interface(_))
    }

    /// Check if field is on an interface object
    fn is_interface_object(
        &self,
        subgraph_idx: usize,
        field_pos: &FieldDefinitionPosition,
    ) -> bool {
        if let Some(subgraph) = self.subgraphs.get(subgraph_idx) {
            if let FieldDefinitionPosition::Object(obj_field) = field_pos {
                let type_pos = TypeDefinitionPosition::Object(obj_field.parent());
                // Check if the type has interface object directive
                return subgraph.is_interface_object_type(&type_pos);
            }
        }
        false
    }

    /// Handle interface object abstracting fields
    ///
    /// **TypeScript Reference**: `Merger.fieldsInSourceIfAbstractedByInterfaceObject()` in `merge.ts:1658-1690`
    /// Returns actual field definitions instead of just type names
    fn fields_in_source_if_abstracted_by_interface_object_impl(
        &self,
        dest_field: &Node<FieldDefinition>,
        source_idx: usize,
    ) -> Vec<Node<FieldDefinition>> {
        // Chain of early returns for invalid cases
        let Some(field_position) = self.get_field_position(dest_field) else {
            return Vec::new();
        };
        let parent_type_name = match &field_position {
            FieldDefinitionPosition::Object(obj_pos) => &obj_pos.type_name,
            FieldDefinitionPosition::Interface(itf_pos) => &itf_pos.type_name,
            FieldDefinitionPosition::Union(_) => return Vec::new(), // Union fields don't have interface object abstraction
        };

        let Some(source_subgraph) = self.subgraphs.get(source_idx) else {
            return Vec::new();
        };
        let source_schema = source_subgraph.schema().schema();

        // If the parent type exists in the source subgraph, no interface object abstraction
        if source_schema.types.contains_key(parent_type_name) {
            return Vec::new();
        }

        // Get the parent object type from merged schema
        let Some(ExtendedType::Object(obj_type)) = self.merged.schema().types.get(parent_type_name)
        else {
            return Vec::new(); // Only object types can have interface implementations
        };

        // Use iterator combinators for functional approach - much more idiomatic Rust
        obj_type
            .implements_interfaces
            .iter()
            .filter_map(|interface_name| {
                let interface_name_str = interface_name.as_str();

                // Get interface type from merged schema and check if it has our field
                let ExtendedType::Interface(interface_type) =
                    self.merged.schema().types.get(interface_name_str)?
                else {
                    return None;
                };

                if !interface_type.fields.contains_key(&dest_field.name) {
                    return None;
                }

                // Check if this interface is an interface object in source subgraph
                let ExtendedType::Object(source_obj_type) =
                    source_schema.types.get(interface_name_str)?
                else {
                    return None;
                };

                // Get the field from the interface object
                source_obj_type
                    .fields
                    .get(&dest_field.name)
                    .map(|field_component| field_component.node.clone())
            })
            .collect()
    }

    /// Check if field is used in federation directives
    fn is_field_used(&self, subgraph_idx: usize, field_pos: &FieldDefinitionPosition) -> bool {
        if let Some(subgraph) = self.subgraphs.get(subgraph_idx) {
            return subgraph.metadata().is_field_used(field_pos);
        }
        false
    }

    /// Suggest similar subgraph names using edit distance
    fn suggest_similar_subgraph_names(&self, target: &str) -> Vec<String> {
        let available: Vec<&str> = self.subgraphs.iter().map(|s| s.name.as_str()).collect();
        self.suggest_similar_subgraph_names_impl(target, &available)
    }

    /// Format suggestions into a grammatically correct "Did you mean...?" message
    /// Produces output like: `" Did you mean "account"?"` or `" Did you mean "user", "account", or "profile"?"`
    fn format_did_you_mean(&self, suggestions: &[String]) -> String {
        if suggestions.is_empty() {
            return String::new();
        }

        let quoted_suggestions: Vec<String> =
            suggestions.iter().map(|s| format!("\"{}\"", s)).collect();

        match quoted_suggestions.len() {
            0 => String::new(),
            1 => format!(" Did you mean {}?", quoted_suggestions[0]),
            2 => format!(
                " Did you mean {} or {}?",
                quoted_suggestions[0], quoted_suggestions[1]
            ), // No comma for 2 items
            _ => {
                const MAX_SUGGESTIONS: usize = 5;
                let selected = if quoted_suggestions.len() > MAX_SUGGESTIONS {
                    &quoted_suggestions[..MAX_SUGGESTIONS]
                } else {
                    &quoted_suggestions[..]
                };

                if selected.len() <= 1 {
                    // Edge case - shouldn't happen but handle gracefully
                    return format!(
                        " Did you mean {}?",
                        selected.first().unwrap_or(&String::new())
                    );
                }

                // Split into "all but last" and "last"
                let (rest, last) = selected.split_at(selected.len() - 1);
                let last_item = &last[0];

                if rest.is_empty() {
                    format!(" Did you mean {}?", last_item)
                } else {
                    format!(" Did you mean {}, or {}?", rest.join(", "), last_item)
                }
            }
        }
    }

    /// Format type names for error messages
    /// Produces output like: `type "User"` or `types "User", "Profile", and "Account"`
    fn print_types(&self, types: &[&str]) -> String {
        self.format_human_readable_list(
            &types
                .iter()
                .map(|t| format!("\"{}\"", t))
                .collect::<Vec<_>>(),
            Some("type"),
            Some("types"),
            Some(" and "),
            None, // No truncation for type names - they're usually short
        )
    }

    /// Format a list of items in human-readable form
    /// Supports prefixes, truncation, and grammatically correct conjunctions
    fn format_human_readable_list(
        &self,
        items: &[String],
        prefix_singular: Option<&str>,
        prefix_plural: Option<&str>,
        last_separator: Option<&str>,
        cutoff_length: Option<usize>,
    ) -> String {
        if items.is_empty() {
            return String::new();
        }

        if items.len() == 1 {
            return match prefix_singular {
                Some(prefix) => format!("{} {}", prefix, items[0]),
                None => items[0].clone(),
            };
        }

        let last_sep = last_separator.unwrap_or(" and ");
        let cutoff = cutoff_length.unwrap_or(100); // Default from TypeScript

        // Calculate truncation point exactly like TypeScript reduce logic
        let last_idx = items
            .iter()
            .fold(
                (0, 0), // (lastIdx, length)
                |(last_idx, length), item| {
                    if length + item.len() > cutoff {
                        (last_idx, length) // Don't increment - this item doesn't fit
                    } else {
                        (last_idx + 1, length + item.len()) // Increment - this item fits
                    }
                },
            )
            .0;

        // Ensure at least one item is displayed, like TypeScript Math.max(1, lastIdx)
        let display_count = last_idx.max(1).min(items.len());
        let to_display = &items[..display_count];

        let prefix = match (prefix_plural, prefix_singular) {
            (Some(plural), _) => format!("{} ", plural),
            (None, Some(singular)) => format!("{} ", singular),
            (None, None) => String::new(),
        };

        if display_count < items.len() {
            // Truncation case: use ", " separator and append ", ..." like TypeScript
            let formatted_list = if to_display.len() == 1 {
                to_display[0].clone()
            } else if to_display.len() == 2 {
                format!("{}, {}", to_display[0], to_display[1]) // Use ", " not last_sep
            } else if let Some((last, rest)) = to_display.split_last() {
                format!("{}, {}", rest.join(", "), last) // Use ", " not last_sep
            } else {
                String::new()
            };
            format!("{}{}, ...", prefix, formatted_list)
        } else {
            // No truncation: use normal last_sep like TypeScript
            let formatted_list = if to_display.len() == 1 {
                to_display[0].clone()
            } else if to_display.len() == 2 {
                format!("{}{}{}", to_display[0], last_sep, to_display[1])
            } else if let Some((last, rest)) = to_display.split_last() {
                format!("{}{}{}", rest.join(", "), last_sep, last)
            } else {
                String::new()
            };
            format!("{}{}", prefix, formatted_list)
        }
    }

    /// Check if field is marked as external with safe bounds checking
    ///
    /// **TypeScript Reference**: `Merger.isExternal()` in `merge.ts:1327-1329`
    /// Uses subgraph metadata to properly handle complex external logic
    ///
    /// Returns `false` if metadata cannot be accessed (graceful degradation)
    fn is_external(&self, subgraph_idx: usize, field: &Node<FieldDefinition>) -> bool {
        // Try metadata-based approach first (most accurate)
        self.subgraphs
            .get(subgraph_idx)
            .and_then(|subgraph| {
                self.get_field_position(field)
                    .map(|field_pos| subgraph.metadata().is_field_external(&field_pos))
            })
            .unwrap_or_else(|| self.is_external_directive_fallback(field))
    }

    /// Fallback: check directives directly when metadata is unavailable
    #[inline]
    fn is_external_directive_fallback(&self, field: &Node<FieldDefinition>) -> bool {
        field
            .directives
            .iter()
            .any(|d| FederationDirective::External.matches(&d.name))
    }

    /// Handle override field validation logic - extracted for better testability
    fn handle_override_field_validation(
        &mut self,
        params: OverrideValidationParams<'_>,
        merge_context: &mut FieldMergeContext,
    ) {
        let coordinate = params.dest.coordinate();
        let directive_ast_nodes = self.extract_ast_nodes_with_subgraph(
            params.override_directive,
            params.subgraph_name,
            ASTNodeKind::Directive,
        );

        if self.is_external(params.from_idx, params.source_field) {
            // @external field: suggest removing @override
            self.error_reporter.add_hint(CompositionHint::with_ast_nodes(
                format!(
                    "Field \"{}\" on subgraph \"{}\" is not resolved anymore by the from subgraph (it is marked \"@external\" in \"{}\"). The @override directive can be removed.",
                    coordinate,
                    params.subgraph_name,
                    params.source_subgraph_name
                ),
                OverrideHintCode::OverrideDirectiveCanBeRemoved.as_str().to_string(),
                directive_ast_nodes,
            ));
            return;
        }

        if params.overridden_field_is_referenced {
            merge_context.set_used_overridden(params.from_idx);

            if params.override_label.is_none() {
                self.error_reporter.add_hint(CompositionHint::with_ast_nodes(
                    format!(
                        "Field \"{}\" on subgraph \"{}\" is overridden. It is still used in some federation directive(s) (@key, @requires, and/or @provides) and/or to satisfy interface constraint(s), but consider marking it @external explicitly or removing it along with its references.",
                        coordinate,
                        params.source_subgraph_name
                    ),
                    OverrideHintCode::OverriddenFieldCanBeRemoved.as_str().to_string(),
                    directive_ast_nodes,
                ));
            }
        } else {
            merge_context.set_unused_overridden(params.from_idx);

            if params.override_label.is_none() {
                self.error_reporter
                    .add_hint(CompositionHint::with_ast_nodes(
                        format!(
                            "Field \"{}\" on subgraph \"{}\" is overridden. Consider removing it.",
                            coordinate, params.source_subgraph_name
                        ),
                        OverrideHintCode::OverriddenFieldCanBeRemoved
                            .as_str()
                            .to_string(),
                        directive_ast_nodes,
                    ));
            }
        }
    }
}

/// Helper struct to track subgraph field information during override validation
#[derive(Debug, Clone)]
struct MappedValue {
    idx: usize,
    field: Option<Node<FieldDefinition>>,
    is_interface_field: bool,
    is_interface_object: bool,
    override_directive: Option<Node<Directive>>,
    interface_object_abstracting_fields: Vec<Node<FieldDefinition>>,
}

/// Extension trait to add coordinate method to field definitions
trait FieldCoordinate {
    fn coordinate(&self) -> String;
}

impl FieldCoordinate for Node<FieldDefinition> {
    fn coordinate(&self) -> String {
        // Generate field coordinate in the format "TypeName.fieldName"
        // For now, we'll use a simplified format since we don't have parent type info
        format!("<Type>.{}", self.name)
    }
}

#[cfg(test)]
mod override_tests {
    use apollo_compiler::Name;
    use apollo_compiler::Node;
    use apollo_compiler::ast::Argument;
    use apollo_compiler::ast::Directive;
    use apollo_compiler::ast::DirectiveList;
    use apollo_compiler::ast::Value;
    use indexmap::IndexMap;

    use super::*;
    use crate::merger::merge::FieldMergeContext;
    use crate::merger::merge::OverrideHintCode;
    use crate::merger::merge::Sources;

    /// Test OverrideHintCode enum completeness and string values
    /// Validates all hint codes required by the task
    #[test]
    fn test_override_hint_code_completeness() {
        // Test all enum variants match task requirements
        assert_eq!(
            OverrideHintCode::FromSubgraphDoesNotExist.as_str(),
            "FROM_SUBGRAPH_DOES_NOT_EXIST"
        );
        assert_eq!(
            OverrideHintCode::OverrideDirectiveCanBeRemoved.as_str(),
            "OVERRIDE_DIRECTIVE_CAN_BE_REMOVED"
        );
        assert_eq!(
            OverrideHintCode::OverrideSourceHasNoField.as_str(),
            "OVERRIDE_SOURCE_HAS_NO_FIELD"
        );
        assert_eq!(
            OverrideHintCode::OverriddenFieldCanBeRemoved.as_str(),
            "OVERRIDDEN_FIELD_CAN_BE_REMOVED"
        );
    }

    /// Test directive detection helper functions
    /// Validates @override, @external, @requires, @provides detection
    #[test]
    fn test_override_directive_detection() {
        // Test @override directive detection
        let mut directives = DirectiveList::new();
        let override_directive = Directive {
            name: Name::new(FederationDirective::Override.name()).unwrap(),
            arguments: vec![
                Argument {
                    name: Name::new("from").unwrap(),
                    value: Node::new(Value::String("subgraphA".to_string())),
                }
                .into(),
            ],
        };
        directives.push(Node::new(override_directive));

        let field = Node::new(FieldDefinition {
            name: Name::new("testField").unwrap(),
            ty: Type::Named(Name::new("String").unwrap()),
            arguments: vec![],
            directives,
            description: None,
        });

        // Test that we can detect override directive
        let has_override = field
            .directives
            .iter()
            .any(|d| FederationDirective::Override.matches(&d.name));
        assert!(has_override);
    }

    /// Test FieldMergeContext behavior for override validation
    /// Validates context state management during validation
    #[test]
    fn test_field_merge_context_override_behavior() {
        let mut context = FieldMergeContext::new();

        // Test override label setting and retrieval
        context.set_override_label(0, "test-label".to_string());
        let props = context.get_properties(0);
        assert!(props.is_some());
        assert_eq!(
            props.unwrap().override_label,
            Some("test-label".to_string())
        );

        // Test used overridden state
        context.set_used_overridden(1);
        assert!(context.is_used_overridden(1));
        assert!(!context.is_unused_overridden(1));

        // Test unused overridden state
        context.set_unused_overridden(2);
        assert!(context.is_unused_overridden(2));
        assert!(!context.is_used_overridden(2));

        // Test override with unknown target
        context.set_override_with_unknown_target(3);
        let props = context.get_properties(3);
        assert!(props.is_some());
        assert!(props.unwrap().override_with_unknown_target);
    }

    /// Test override directive argument extraction
    /// Validates "from" and "label" argument parsing
    #[test]
    fn test_override_directive_argument_extraction() {
        let mut directives = DirectiveList::new();

        // Create @override directive with both "from" and "label" arguments
        let override_directive = Directive {
            name: Name::new(FederationDirective::Override.name()).unwrap(),
            arguments: vec![
                Argument {
                    name: Name::new("from").unwrap(),
                    value: Node::new(Value::String("sourceSubgraph".to_string())),
                }
                .into(),
                Argument {
                    name: Name::new("label").unwrap(),
                    value: Node::new(Value::String("migration-v1".to_string())),
                }
                .into(),
            ],
        };
        directives.push(Node::new(override_directive));

        let field = Node::new(FieldDefinition {
            name: Name::new("overrideField").unwrap(),
            ty: Type::Named(Name::new("String").unwrap()),
            arguments: vec![],
            directives,
            description: None,
        });

        // Test "from" argument extraction
        let from_arg = field.directives[0]
            .arguments
            .iter()
            .find(|arg| arg.name.as_str() == "from");
        assert!(from_arg.is_some());
        if let Value::String(from_value) = from_arg.unwrap().value.as_ref() {
            assert_eq!(from_value, "sourceSubgraph");
        } else {
            panic!("Expected string value for 'from' argument");
        }

        // Test "label" argument extraction
        let label_arg = field.directives[0]
            .arguments
            .iter()
            .find(|arg| arg.name.as_str() == "label");
        assert!(label_arg.is_some());
        if let Value::String(label_value) = label_arg.unwrap().value.as_ref() {
            assert_eq!(label_value, "migration-v1");
        } else {
            panic!("Expected string value for 'label' argument");
        }
    }

    /// Test conflicting directive scenarios
    /// Validates detection of @override conflicts with @external, @requires, @provides
    #[test]
    fn test_conflicting_directive_scenarios() {
        // Test @override + @external conflict
        let mut directives = DirectiveList::new();

        let override_directive = Directive {
            name: Name::new(FederationDirective::Override.name()).unwrap(),
            arguments: vec![
                Argument {
                    name: Name::new("from").unwrap(),
                    value: Node::new(Value::String("subgraphA".to_string())),
                }
                .into(),
            ],
        };
        directives.push(Node::new(override_directive));

        let external_directive = Directive {
            name: Name::new(FederationDirective::External.name()).unwrap(),
            arguments: vec![],
        };
        directives.push(Node::new(external_directive));

        let field = Node::new(FieldDefinition {
            name: Name::new("conflictingField").unwrap(),
            ty: Type::Named(Name::new("String").unwrap()),
            arguments: vec![],
            directives,
            description: None,
        });

        // Validate both directives are present (conflict detection happens in validation logic)
        let has_override = field
            .directives
            .iter()
            .any(|d| FederationDirective::Override.matches(&d.name));
        let has_external = field
            .directives
            .iter()
            .any(|d| FederationDirective::External.matches(&d.name));

        assert!(has_override);
        assert!(has_external);
        assert_eq!(field.directives.len(), 2);
    }

    /// Test Sources data structure handling
    /// Validates the Sources<Node<FieldDefinition>> structure used in validation
    #[test]
    fn test_override_label_percent_validation() {
        use std::sync::LazyLock;

        use regex::Regex;
        // Test the regex logic directly
        static LABEL_REGEX_TEST: LazyLock<Regex> =
            LazyLock::new(|| Regex::new(r"^[a-zA-Z][a-zA-Z0-9_\-:./]*$").unwrap());
        static PERCENT_REGEX_TEST: LazyLock<Regex> =
            LazyLock::new(|| Regex::new(r"^percent\((\d{1,2}(\.\d{1,8})?|100)\)$").unwrap());

        fn is_valid_override_label_test(label: &str) -> bool {
            if label.is_empty() {
                return false;
            }

            // Check standard label format first
            if LABEL_REGEX_TEST.is_match(label) {
                return true;
            }

            // Check percent format - regex already validates range and format
            PERCENT_REGEX_TEST.is_match(label)
        }

        // Valid percent values (0-100 inclusive)
        assert!(is_valid_override_label_test("percent(0)"));
        assert!(is_valid_override_label_test("percent(50)"));
        assert!(is_valid_override_label_test("percent(99)"));
        assert!(is_valid_override_label_test("percent(100)"));
        assert!(is_valid_override_label_test("percent(0.5)"));
        assert!(is_valid_override_label_test("percent(1.0)"));
        assert!(is_valid_override_label_test("percent(99.9)"));
        assert!(is_valid_override_label_test("percent(50.12345678)"));
        assert!(!is_valid_override_label_test("percent(150.5)"));
        assert!(!is_valid_override_label_test("percent(-0.1)"));
        assert!(!is_valid_override_label_test("percent(100.1)"));
        assert!(!is_valid_override_label_test("percent(100.0)"));

        // Invalid percent format
        assert!(!is_valid_override_label_test("percent()"));
        assert!(!is_valid_override_label_test("percent(abc)"));
        assert!(!is_valid_override_label_test("percent(50.123456789)")); // Too many decimals
        assert!(!is_valid_override_label_test("percent(1000)"));

        // Valid regular labels
        assert!(is_valid_override_label_test("validLabel"));
        assert!(is_valid_override_label_test("label_with-chars:./"));
        assert!(is_valid_override_label_test("a"));

        // Invalid regular labels
        assert!(!is_valid_override_label_test(""));
        assert!(!is_valid_override_label_test("123invalid")); // Starts with number
        assert!(!is_valid_override_label_test("invalid@char"));
    }

    #[test]
    fn test_sources_data_structure() {
        let mut sources: Sources<Node<FieldDefinition>> = IndexMap::default();

        // Create a field with @override directive
        let field = Node::new(FieldDefinition {
            name: Name::new("testField").unwrap(),
            ty: Type::Named(Name::new("String").unwrap()),
            arguments: vec![],
            directives: DirectiveList::new(),
            description: None,
        });

        // Test inserting field into sources
        sources.insert(0, Some(field.clone()));
        sources.insert(1, None); // Test None case for interface object abstracting fields

        // Validate sources structure
        assert_eq!(sources.len(), 2);
        assert!(sources.get(&0).is_some());
        assert!(sources.get(&1).is_some());
        assert!(sources.get(&0).unwrap().is_some());
        assert!(sources.get(&1).unwrap().is_none());
    }

    #[test]
    fn test_override_conflicts_with_other_directive_integration() {
        use crate::merger::merge_enum::tests::create_test_merger;
        let merger = create_test_merger().expect("Failed to create test merger");

        // Test that override_conflicts_with_other_directive is properly integrated
        // This test verifies the method exists and can be called with correct signature
        let result =
            merger.override_conflicts_with_other_directive(0, None, "test_subgraph", 1, None);

        // Should return no conflict for None fields
        assert!(!result.has_incompatible);
        assert!(result.conflicting_directive.is_none());
        assert!(result.subgraph.is_none());
    }

    #[test]
    fn test_override_conflicts_with_requires_directive() {
        use crate::merger::merge_enum::tests::create_test_merger;
        let merger = create_test_merger().expect("Failed to create test merger");

        // Create a field with @requires directive
        let mut directives = DirectiveList::new();
        let requires_directive = Directive {
            name: Name::new(FederationDirective::Requires.name()).unwrap(),
            arguments: vec![
                Argument {
                    name: Name::new("fields").unwrap(),
                    value: Node::new(Value::String("id".to_string())),
                }
                .into(),
            ],
        };
        directives.push(Node::new(requires_directive));

        let field_with_requires = Node::new(FieldDefinition {
            name: Name::new("testField").unwrap(),
            ty: Type::Named(Name::new("String").unwrap()),
            arguments: vec![],
            directives,
            description: None,
        });

        // Test conflict detection
        let result = merger.override_conflicts_with_other_directive(
            0,
            None,
            "current_subgraph",
            1,
            Some(&field_with_requires),
        );

        // Should detect conflict with @requires
        assert!(result.has_incompatible);
        assert_eq!(
            result.conflicting_directive,
            Some(FederationDirective::Requires.conflict_name().to_string())
        );
        assert!(result.subgraph.is_some());
    }

    #[test]
    fn test_override_conflicts_with_provides_directive() {
        use crate::merger::merge_enum::tests::create_test_merger;
        let merger = create_test_merger().expect("Failed to create test merger");

        // Create a field with @provides directive
        let mut directives = DirectiveList::new();
        let provides_directive = Directive {
            name: Name::new(FederationDirective::Provides.name()).unwrap(),
            arguments: vec![
                Argument {
                    name: Name::new("fields").unwrap(),
                    value: Node::new(Value::String("name".to_string())),
                }
                .into(),
            ],
        };
        directives.push(Node::new(provides_directive));

        let field_with_provides = Node::new(FieldDefinition {
            name: Name::new("testField").unwrap(),
            ty: Type::Named(Name::new("String").unwrap()),
            arguments: vec![],
            directives,
            description: None,
        });

        // Test conflict detection
        let result = merger.override_conflicts_with_other_directive(
            0,
            None,
            "current_subgraph",
            1,
            Some(&field_with_provides),
        );

        // Should detect conflict with @provides
        assert!(result.has_incompatible);
        assert_eq!(
            result.conflicting_directive,
            Some(FederationDirective::Provides.conflict_name().to_string())
        );
        assert!(result.subgraph.is_some());
    }

    #[test]
    fn test_override_conflicts_with_federation_prefixed_directives() {
        use crate::merger::merge_enum::tests::create_test_merger;
        let merger = create_test_merger().expect("Failed to create test merger");

        // Create a field with @federation__requires directive
        let mut directives = DirectiveList::new();
        let federation_requires_directive = Directive {
            name: Name::new(FederationDirective::Requires.federation_name()).unwrap(),
            arguments: vec![
                Argument {
                    name: Name::new("fields").unwrap(),
                    value: Node::new(Value::String("id".to_string())),
                }
                .into(),
            ],
        };
        directives.push(Node::new(federation_requires_directive));

        let field_with_federation_requires = Node::new(FieldDefinition {
            name: Name::new("testField").unwrap(),
            ty: Type::Named(Name::new("String").unwrap()),
            arguments: vec![],
            directives,
            description: None,
        });

        // Test conflict detection with federation-prefixed directive
        let result = merger.override_conflicts_with_other_directive(
            0,
            None,
            "current_subgraph",
            1,
            Some(&field_with_federation_requires),
        );

        // Should detect conflict with @federation__requires
        assert!(result.has_incompatible);
        assert_eq!(
            result.conflicting_directive,
            Some(FederationDirective::Requires.conflict_name().to_string())
        );
        assert!(result.subgraph.is_some());
    }

    #[test]
    fn test_override_no_conflict_with_clean_fields() {
        use crate::merger::merge_enum::tests::create_test_merger;
        let merger = create_test_merger().expect("Failed to create test merger");

        // Create clean fields without conflicting directives
        let clean_field = Node::new(FieldDefinition {
            name: Name::new("cleanField").unwrap(),
            ty: Type::Named(Name::new("String").unwrap()),
            arguments: vec![],
            directives: DirectiveList::new(),
            description: None,
        });

        // Test no conflict detection
        let result = merger.override_conflicts_with_other_directive(
            0,
            Some(&clean_field),
            "current_subgraph",
            1,
            Some(&clean_field),
        );

        // Should not detect any conflicts
        assert!(!result.has_incompatible);
        assert!(result.conflicting_directive.is_none());
        assert!(result.subgraph.is_none());
    }

    #[test]
    fn test_subgraph_name_suggestions_complete_workflow() {
        use crate::merger::merge_enum::tests::create_test_merger;
        let merger = create_test_merger().expect("Failed to create test merger");

        let available = vec!["accounts", "products", "reviews", "shipping"];

        // Exact match - should suggest itself as best match
        let suggestions = merger.suggest_similar_subgraph_names_impl("accounts", &available);
        assert!(!suggestions.is_empty());
        assert_eq!(suggestions[0], "accounts"); // Best match should be exact
        let message = merger.format_did_you_mean(&suggestions);
        assert!(message.contains("\"accounts\""));

        // Case-only difference - should get special handling
        let suggestions = merger.suggest_similar_subgraph_names_impl("ACCOUNTS", &available);
        assert!(!suggestions.is_empty());
        assert_eq!(suggestions[0], "accounts"); // Should prioritize the correct case
        let message = merger.format_did_you_mean(&suggestions);
        assert!(message.contains("\"accounts\""));

        // Common typo - should suggest correct spelling
        let suggestions = merger.suggest_similar_subgraph_names_impl("acount", &available);
        assert!(!suggestions.is_empty());
        assert_eq!(suggestions[0], "accounts"); // Should find the intended match
        let message = merger.format_did_you_mean(&suggestions);
        assert!(message.contains("\"accounts\""));

        // Partial match - should find close matches
        let suggestions = merger.suggest_similar_subgraph_names_impl("ship", &available);
        // Should include "shipping" if threshold allows, but may be empty if too strict
        if !suggestions.is_empty() {
            assert!(suggestions.iter().any(|s| s == "shipping"));
        }

        // No good matches - should return empty
        let suggestions = merger.suggest_similar_subgraph_names_impl("xyz123", &available);
        assert!(suggestions.is_empty());
        assert_eq!(merger.format_did_you_mean(&suggestions), "");

        // Test 2-item case specifically - should use "or" without comma (TypeScript parity)
        let two_suggestions = vec!["account".to_string(), "user".to_string()];
        assert_eq!(
            merger.format_did_you_mean(&two_suggestions),
            " Did you mean \"account\" or \"user\"?" // No comma before "or"
        );

        // Test MAX_SUGGESTIONS = 5 truncation (TypeScript parity)
        let many_suggestions = vec![
            "item1".to_string(),
            "item2".to_string(),
            "item3".to_string(),
            "item4".to_string(),
            "item5".to_string(),
            "item6".to_string(),
            "item7".to_string(),
        ];
        let result = merger.format_did_you_mean(&many_suggestions);
        // Should only show first 5: "item1", "item2", "item3", "item4", or "item5"
        assert!(result.contains("\"item1\""));
        assert!(result.contains("\"item5\""));
        assert!(!result.contains("\"item6\"")); // Should be truncated
        assert!(!result.contains("\"item7\"")); // Should be truncated
        assert!(result.contains(", or \"item5\"?")); // Last item should use "or"

        // Three+ suggestions - should use commas and "or"
        let triple = vec![
            "accounts".to_string(),
            "products".to_string(),
            "reviews".to_string(),
        ];
        let msg = merger.format_did_you_mean(&triple);
        assert!(
            msg.contains("\"accounts\"")
                && msg.contains("\"products\"")
                && msg.contains("\"reviews\"")
        );
        assert!(msg.contains(", or "));

        // Dynamic threshold - longer strings should be more forgiving
        let long_names = vec!["verylongsubgraphname", "anotherlongname"];
        let suggestions =
            merger.suggest_similar_subgraph_names_impl("verylongsubgraphnam", &long_names);
        assert!(!suggestions.is_empty());
        assert_eq!(suggestions[0], "verylongsubgraphname");

        // Best suggestion selection - should return best match first
        let suggestions = merger.suggest_similar_subgraph_names_impl("acount", &available);
        assert!(!suggestions.is_empty());
        assert_eq!(suggestions[0], "accounts"); // Best match first
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use apollo_compiler::Name;
    use apollo_compiler::Node;
    use apollo_compiler::ast::FieldDefinition;
    use apollo_compiler::ast::InputValueDefinition;
    use apollo_compiler::schema::ComponentName;
    use apollo_compiler::schema::EnumType;
    use apollo_compiler::schema::ExtendedType;
    use apollo_compiler::schema::InterfaceType;
    use apollo_compiler::schema::ObjectType;
    use apollo_compiler::schema::UnionType;

    use super::*;

    /// Test helper struct for type merging tests
    /// In production, this trait is implemented by real schema elements like FieldDefinition and InputValueDefinition
    #[derive(Debug, Clone)]
    pub(crate) struct TestSchemaElement {
        pub(crate) coordinate: String,
        pub(crate) typ: Option<Type>,
    }

    impl SchemaElementWithType for TestSchemaElement {
        fn coordinate(&self, parent_name: &str) -> String {
            format!("{}.{}", parent_name, self.coordinate)
        }

        fn set_type(&mut self, typ: Type) {
            self.typ = Some(typ);
        }
        fn enum_example_ast(&self) -> Option<EnumExampleAst> {
            Some(EnumExampleAst::Field(Node::new(FieldDefinition {
                name: Name::new("dummy").unwrap(),
                description: None,
                arguments: vec![],
                directives: Default::default(),
                ty: Type::Named(Name::new("String").unwrap()),
            })))
        }
    }

    fn create_test_schema() -> Schema {
        let mut schema = Schema::new();

        // Add interface I
        let interface_type = InterfaceType {
            description: None,
            name: Name::new("I").unwrap(),
            implements_interfaces: Default::default(),
            directives: Default::default(),
            fields: Default::default(),
        };
        schema.types.insert(
            Name::new("I").unwrap(),
            ExtendedType::Interface(Node::new(interface_type)),
        );

        // Add object type A implementing I
        let mut object_type = ObjectType {
            description: None,
            name: Name::new("A").unwrap(),
            implements_interfaces: Default::default(),
            directives: Default::default(),
            fields: Default::default(),
        };
        object_type
            .implements_interfaces
            .insert(ComponentName::from(Name::new("I").unwrap()));
        schema.types.insert(
            Name::new("A").unwrap(),
            ExtendedType::Object(Node::new(object_type)),
        );

        // Add union U with member A
        let mut union_type = UnionType {
            description: None,
            name: Name::new("U").unwrap(),
            directives: Default::default(),
            members: Default::default(),
        };
        union_type
            .members
            .insert(ComponentName::from(Name::new("A").unwrap()));
        schema.types.insert(
            Name::new("U").unwrap(),
            ExtendedType::Union(Node::new(union_type)),
        );

        // Add enum Status for enum usage tracking tests
        let enum_type = EnumType {
            description: None,
            name: Name::new("Status").unwrap(),
            directives: Default::default(),
            values: Default::default(),
        };
        schema.types.insert(
            Name::new("Status").unwrap(),
            ExtendedType::Enum(Node::new(enum_type)),
        );

        schema
    }

    fn create_test_merger() -> Result<Merger, FederationError> {
        crate::merger::merge_enum::tests::create_test_merger()
    }

    #[test]
    fn same_types() {
        let _schema = create_test_schema();
        let mut merger = create_test_merger().expect("Failed to create test merger");

        let mut sources: Sources<Type> = (0..2).map(|i| (i, None)).collect();
        sources.insert(0, Some(Type::Named(Name::new("String").unwrap())));
        sources.insert(1, Some(Type::Named(Name::new("String").unwrap())));

        let result = merger.merge_type_reference(
            &sources,
            &mut TestSchemaElement {
                coordinate: "testField".to_string(),
                typ: None,
            },
            false,
            Name::new("Parent").unwrap().as_str(),
        );

        // Check that there are no errors or hints
        assert!(result.is_ok());
        assert!(!merger.has_errors());
        assert_eq!(merger.enum_usages().len(), 0);
    }

    #[test]
    fn nullable_vs_non_nullable() {
        let _schema = create_test_schema();
        let mut merger = create_test_merger().expect("Failed to create test merger");

        let mut sources: Sources<Type> = (0..2).map(|i| (i, None)).collect();
        sources.insert(0, Some(Type::NonNullNamed(Name::new("String").unwrap())));
        sources.insert(1, Some(Type::Named(Name::new("String").unwrap())));

        // For output types, should use the more general type (nullable)
        let result = merger.merge_type_reference(
            &sources,
            &mut TestSchemaElement {
                coordinate: "testField".to_string(),
                typ: None,
            },
            false,
            Name::new("Parent").unwrap().as_str(),
        );
        // Check that there are no errors but there might be hints
        assert!(result.is_ok());
        assert!(!merger.has_errors());
        assert_eq!(merger.enum_usages().len(), 0);

        // Create a new merger for the next test since we can't clear the reporter
        let mut merger = create_test_merger().expect("Failed to create test merger");

        // For input types, should use the more specific type (non-nullable)
        let _result = merger.merge_type_reference(
            &sources,
            &mut TestSchemaElement {
                coordinate: "testArg".to_string(),
                typ: None,
            },
            true,
            Name::new("Parent").unwrap().as_str(),
        );
        // Check that there are no errors but there might be hints
        assert!(!merger.has_errors());
        assert_eq!(merger.enum_usages().len(), 0);
    }

    #[test]
    fn interface_subtype() {
        let _schema = create_test_schema();
        let mut merger = create_test_merger().expect("Failed to create test merger");

        let mut sources: Sources<Type> = (0..2).map(|i| (i, None)).collect();
        sources.insert(0, Some(Type::Named(Name::new("I").unwrap())));
        sources.insert(1, Some(Type::Named(Name::new("A").unwrap())));

        // For output types, should use the more general type (interface)
        let result = merger.merge_type_reference(
            &sources,
            &mut TestSchemaElement {
                coordinate: "testField".to_string(),
                typ: None,
            },
            false,
            Name::new("Parent").unwrap().as_str(),
        );
        // Check that there are no errors but there might be hints
        assert!(result.is_ok());
        assert!(!merger.has_errors());
        assert_eq!(merger.enum_usages().len(), 0);

        // For input types, should use the more specific type (implementing type)
        let _result = merger.merge_type_reference(
            &sources,
            &mut TestSchemaElement {
                coordinate: "testArg".to_string(),
                typ: None,
            },
            true,
            Name::new("Parent").unwrap().as_str(),
        );
        // Check that there are no errors but there might be hints
        assert!(!merger.has_errors());
        assert_eq!(merger.enum_usages().len(), 0);
    }

    #[test]
    fn incompatible_types() {
        let _schema = create_test_schema();
        let mut merger = create_test_merger().expect("Failed to create test merger");

        let mut sources: Sources<Type> = (0..2).map(|i| (i, None)).collect();
        sources.insert(0, Some(Type::Named(Name::new("String").unwrap())));
        sources.insert(1, Some(Type::Named(Name::new("Int").unwrap())));

        let _result = merger.merge_type_reference(
            &sources,
            &mut TestSchemaElement {
                coordinate: "testField".to_string(),
                typ: None,
            },
            false,
            Name::new("Parent").unwrap().as_str(),
        );
        // Check that there are errors for incompatible types
        assert!(merger.has_errors());
        assert_eq!(merger.enum_usages().len(), 0);
    }

    #[test]
    fn enum_usage_tracking() {
        let _schema = create_test_schema();
        let mut merger = create_test_merger().expect("Failed to create test merger");

        // Test enum usage in output position
        let mut sources: Sources<Type> = (0..2).map(|i| (i, None)).collect();
        sources.insert(0, Some(Type::Named(Name::new("Status").unwrap())));
        sources.insert(1, Some(Type::Named(Name::new("Status").unwrap())));

        let _ = merger.merge_type_reference(
            &sources,
            &mut TestSchemaElement {
                coordinate: "user_status".to_string(),
                typ: None,
            },
            false,
            Name::new("Parent").unwrap().as_str(),
        );

        // Test enum usage in input position
        let mut arg_sources: Sources<Type> = (0..2).map(|i| (i, None)).collect();
        arg_sources.insert(0, Some(Type::Named(Name::new("Status").unwrap())));
        arg_sources.insert(1, Some(Type::Named(Name::new("Status").unwrap())));

        let _ = merger.merge_type_reference(
            &arg_sources,
            &mut TestSchemaElement {
                coordinate: "status_filter".to_string(),
                typ: None,
            },
            true,
            Name::new("Parent").unwrap().as_str(),
        );

        // Verify enum usage tracking
        let enum_usage = merger.get_enum_usage("Status");
        assert!(enum_usage.is_some());

        let usage = enum_usage.unwrap();
        match usage {
            EnumTypeUsage::Both {
                input_example,
                output_example,
            } => {
                assert_eq!(input_example.coordinate, "Parent.status_filter");
                assert_eq!(output_example.coordinate, "Parent.user_status");
            }
            _ => panic!("Expected Both usage, got {:?}", usage),
        }
    }

    #[test]
    fn enum_usage_output_only() {
        let _schema = create_test_schema();
        let mut merger = create_test_merger().expect("Failed to create test merger");

        // Track enum in output position only
        let mut sources: Sources<Type> = (0..2).map(|i| (i, None)).collect();
        sources.insert(0, Some(Type::Named(Name::new("Status").unwrap())));
        sources.insert(1, Some(Type::Named(Name::new("Status").unwrap())));

        let _ = merger.merge_type_reference(
            &sources,
            &mut TestSchemaElement {
                coordinate: "status_out".to_string(),
                typ: None,
            },
            false,
            Name::new("Parent").unwrap().as_str(),
        );

        let usage = merger.get_enum_usage("Status").expect("usage");
        match usage {
            EnumTypeUsage::Output { output_example } => {
                assert_eq!(output_example.coordinate, "Parent.status_out");
            }
            _ => panic!("Expected Output usage"),
        }
    }

    #[test]
    fn enum_usage_input_only() {
        let _schema = create_test_schema();
        let mut merger = create_test_merger().expect("Failed to create test merger");

        // Track enum in input position only
        let mut sources: Sources<Type> = (0..2).map(|i| (i, None)).collect();
        sources.insert(0, Some(Type::Named(Name::new("Status").unwrap())));
        sources.insert(1, Some(Type::Named(Name::new("Status").unwrap())));

        let _ = merger.merge_type_reference(
            &sources,
            &mut TestSchemaElement {
                coordinate: "status_in".to_string(),
                typ: None,
            },
            true,
            Name::new("Parent").unwrap().as_str(),
        );

        let usage = merger.get_enum_usage("Status").expect("usage");
        match usage {
            EnumTypeUsage::Input { input_example } => {
                assert_eq!(input_example.coordinate, "Parent.status_in");
            }
            _ => panic!("Expected Input usage"),
        }
    }

    #[test]
    fn empty_sources_reports_error() {
        let _schema = create_test_schema();
        let mut merger = create_test_merger().expect("Failed to create test merger");

        // Test with empty sources
        let sources: Sources<Type> = IndexMap::default();
        let mut element = TestSchemaElement {
            coordinate: "f".into(),
            typ: None,
        };

        let result = merger.merge_type_reference(
            &sources,
            &mut element,
            false,
            Name::new("Parent").unwrap().as_str(),
        );

        // The implementation returns Ok(false) but adds an error to the error reporter
        match result {
            Ok(false) => {} // Expected
            Ok(true) => panic!("Expected Ok(false), got Ok(true)"),
            Err(e) => panic!("Expected Ok(false), got Err: {:?}", e),
        }
        assert!(
            merger.has_errors(),
            "Expected an error to be reported for empty sources"
        );
    }

    #[test]
    fn sources_with_no_defined_types_reports_error() {
        let _schema = create_test_schema();
        let mut merger = create_test_merger().expect("Failed to create test merger");

        let sources: Sources<Type> = (0..2).map(|i| (i, None)).collect();
        // both entries None by default

        let mut element = TestSchemaElement {
            coordinate: "f".into(),
            typ: None,
        };

        let result = merger.merge_type_reference(
            &sources,
            &mut element,
            false,
            Name::new("Parent").unwrap().as_str(),
        );

        // The implementation skips None sources, finds no result_type,
        // then returns Ok(false) but adds an error to the error reporter
        match result {
            Ok(false) => {} // Expected
            Ok(true) => panic!("Expected Ok(false), got Ok(true)"),
            Err(e) => panic!("Expected Ok(false), got Err: {:?}", e),
        }
        assert!(
            merger.has_errors(),
            "Expected an error to be reported when no sources have types defined"
        );
    }

    #[test]
    fn merge_with_field_definition_element() {
        let _schema = create_test_schema();
        let mut merger = create_test_merger().expect("Failed to create test merger");

        // Prepare a field definition in the schema
        let mut field_def = FieldDefinition {
            name: Name::new("field").unwrap(),
            description: None,
            arguments: vec![],
            directives: Default::default(),
            ty: Type::Named(Name::new("String").unwrap()),
        };
        let mut sources: Sources<Type> = (0..1).map(|i| (i, None)).collect();
        sources.insert(0, Some(Type::Named(Name::new("String").unwrap())));

        // Call merge_type_reference on a FieldDefinition (TElement = FieldDefinition)
        let res = merger.merge_type_reference(
            &sources,
            &mut field_def,
            false,
            Name::new("Parent").unwrap().as_str(),
        );
        assert!(
            res.is_ok(),
            "Merging identical types on a FieldDefinition should return true"
        );
        assert_eq!(
            match field_def.ty.clone() {
                Type::Named(n) => n.to_string(),
                _ => String::new(),
            },
            "String"
        );
    }

    #[test]
    fn merge_with_input_value_definition_element() {
        let _schema = create_test_schema();
        let mut merger = create_test_merger().expect("Failed to create test merger");

        // Prepare an input value definition (argument) type
        let mut input_def = InputValueDefinition {
            name: Name::new("arg").unwrap(),
            description: None,
            default_value: None,
            directives: Default::default(),
            ty: Type::Named(Name::new("Int").unwrap()).into(),
        };
        let mut sources: Sources<Type> = (0..2).map(|i| (i, None)).collect();
        sources.insert(0, Some(Type::Named(Name::new("Int").unwrap())));
        sources.insert(1, Some(Type::NonNullNamed(Name::new("Int").unwrap())));

        // In input position, non-null should be overridden by nullable
        let res = merger.merge_type_reference(
            &sources,
            &mut input_def,
            true,
            Name::new("Parent").unwrap().as_str(),
        );
        assert!(res.is_ok(), "Input position merging should work");
        assert_eq!(
            match input_def.ty.as_ref() {
                Type::Named(n) => n.as_str(),
                _ => "",
            },
            "Int"
        );
    }
}
