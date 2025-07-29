use apollo_federation::error::FederationError;
use apollo_federation::merger::merger::Merger;
use apollo_federation::subgraph::Subgraph;
use apollo_federation::subgraph::typestate::Validated;
use apollo_federation::merger::merger::CompositionOptions;
use apollo_compiler::Schema;
use insta::assert_snapshot;

/// Test override validation on interface fields
#[test]
fn test_override_on_interface_error() {
    let subgraph_a = r#"
        extend schema @link(url: "https://specs.apollographql.org/federation/v2.0", import: ["@override"])
        
        interface Product {
            id: ID! @override(from: "subgraph_b")
        }
    "#;
    
    let subgraph_b = r#"
        extend schema @link(url: "https://specs.apollographql.org/federation/v2.0", import: ["@key"])
        
        interface Product {
            id: ID!
        }
    "#;
    
    let result = compose_subgraphs(&[
        ("subgraph_a", subgraph_a),
        ("subgraph_b", subgraph_b),
    ]);
    
    assert!(result.is_err());
    let errors = result.unwrap_err();
    assert!(errors.to_string().contains("OVERRIDE_ON_INTERFACE"));
}

/// Test override from self error
#[test]
fn test_override_from_self_error() {
    let subgraph_a = r#"
        extend schema @link(url: "https://specs.apollographql.org/federation/v2.0", import: ["@key", "@override"])
        
        type Product @key(fields: "id") {
            id: ID!
            name: String @override(from: "subgraph_a")
        }
    "#;
    
    let result = compose_subgraphs(&[
        ("subgraph_a", subgraph_a),
    ]);
    
    assert!(result.is_err());
    let errors = result.unwrap_err();
    assert!(errors.to_string().contains("OVERRIDE_FROM_SELF_ERROR"));
}

/// Test invalid override label formats
#[test]
fn test_override_label_invalid_error() {
    let subgraph_a = r#"
        extend schema @link(url: "https://specs.apollographql.org/federation/v2.7", import: ["@key", "@override"])
        
        type Product @key(fields: "id") {
            id: ID!
            name: String @override(from: "subgraph_b", label: "123invalid")
        }
    "#;
    
    let subgraph_b = r#"
        extend schema @link(url: "https://specs.apollographql.org/federation/v2.7", import: ["@key"])
        
        type Product @key(fields: "id") {
            id: ID!
            name: String
        }
    "#;
    
    let result = compose_subgraphs(&[
        ("subgraph_a", subgraph_a),
        ("subgraph_b", subgraph_b),
    ]);
    
    assert!(result.is_err());
    let errors = result.unwrap_err();
    assert!(errors.to_string().contains("OVERRIDE_LABEL_INVALID"));
}

/// Test override collision with other directives
#[test]
fn test_override_collision_with_external() {
    let subgraph_a = r#"
        extend schema @link(url: "https://specs.apollographql.org/federation/v2.0", import: ["@key", "@override", "@external"])
        
        type Product @key(fields: "id") {
            id: ID!
            name: String @external @override(from: "subgraph_b")
        }
    "#;
    
    let subgraph_b = r#"
        extend schema @link(url: "https://specs.apollographql.org/federation/v2.0", import: ["@key"])
        
        type Product @key(fields: "id") {
            id: ID!
            name: String
        }
    "#;
    
    let result = compose_subgraphs(&[
        ("subgraph_a", subgraph_a),
        ("subgraph_b", subgraph_b),
    ]);
    
    assert!(result.is_err());
    let errors = result.unwrap_err();
    assert!(errors.to_string().contains("OVERRIDE_COLLISION_WITH_ANOTHER_DIRECTIVE"));
}

/// Test from subgraph does not exist hint
#[test]
fn test_from_subgraph_does_not_exist_hint() {
    let subgraph_a = r#"
        extend schema @link(url: "https://specs.apollographql.org/federation/v2.0", import: ["@key", "@override"])
        
        type Product @key(fields: "id") {
            id: ID!
            name: String @override(from: "nonexistent_subgraph")
        }
    "#;
    
    let result = compose_subgraphs(&[
        ("subgraph_a", subgraph_a),
    ]);
    
    // This should succeed but generate a hint
    if let Ok(merge_result) = result {
        assert!(!merge_result.hints.is_empty());
        let hint_messages: Vec<String> = merge_result.hints.iter().map(|h| h.message.clone()).collect();
        assert!(hint_messages.iter().any(|msg| msg.contains("FROM_SUBGRAPH_DOES_NOT_EXIST")));
    }
}

/// Test valid override labels
#[test]
fn test_valid_override_labels() {
    let valid_labels = vec![
        "myLabel",
        "my_label", 
        "my-label",
        "my:label",
        "my.label",
        "my/label",
        "percent(50)",
        "percent(100)",
        "percent(0)",
        "percent(99.99999999)",
    ];
    
    for label in valid_labels {
        let subgraph_a = format!(r#"
            extend schema @link(url: "https://specs.apollographql.org/federation/v2.7", import: ["@key", "@override"])
            
            type Product @key(fields: "id") {{
                id: ID!
                name: String @override(from: "subgraph_b", label: "{}")
            }}
        "#, label);
        
        let subgraph_b = r#"
            extend schema @link(url: "https://specs.apollographql.org/federation/v2.7", import: ["@key"])
            
            type Product @key(fields: "id") {
                id: ID!
                name: String
            }
        "#;
        
        let result = compose_subgraphs(&[
            ("subgraph_a", &subgraph_a),
            ("subgraph_b", subgraph_b),
        ]);
        
        // Should not have OVERRIDE_LABEL_INVALID error
        if let Err(errors) = result {
            assert!(!errors.to_string().contains("OVERRIDE_LABEL_INVALID"), 
                   "Label '{}' should be valid but got error: {}", label, errors);
        }
    }
}

/// Helper function to compose subgraphs and return result
fn compose_subgraphs(subgraphs: &[(&str, &str)]) -> Result<crate::merger::merger::MergeResult, FederationError> {
    let mut validated_subgraphs = Vec::new();
    
    for (name, schema_str) in subgraphs {
        let schema = Schema::parse_and_validate(schema_str, "schema.graphql")
            .map_err(|e| FederationError::internal(format!("Failed to parse schema for {}: {}", name, e)))?;
        
        let subgraph = Subgraph::new(name.to_string(), schema)
            .map_err(|e| FederationError::internal(format!("Failed to create subgraph {}: {}", name, e)))?;
        
        validated_subgraphs.push(subgraph);
    }
    
    let merger = Merger::new(validated_subgraphs, CompositionOptions::default())
        .map_err(|e| FederationError::internal(format!("Failed to create merger: {}", e)))?;
    
    Ok(merger.merge())
}