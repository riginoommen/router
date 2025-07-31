#!/usr/bin/env python3
"""
Generate a massive GraphQL supergraph schema by extending the existing schema
with thousands of interconnected types to reach approximately 10MB.
"""

import random
import string
from pathlib import Path

def generate_random_name(prefix="", length=8):
    """Generate a random name with optional prefix."""
    suffix = ''.join(random.choices(string.ascii_letters, k=length))
    return f"{prefix}{suffix}" if prefix else suffix

def generate_scalar_types(count=100, subgraph_names=["ACCOUNTS", "INVENTORY", "PRODUCTS", "REVIEWS"]):
    """Generate custom scalar types with federation directives."""
    scalars = []
    for i in range(count):
        name = f"CustomScalar{i:04d}"
        subgraph = random.choice(subgraph_names)
        scalars.append(f"scalar {name} @join__type(graph: {subgraph})")
    return scalars

def generate_enum_types(count=200, subgraph_names=["ACCOUNTS", "INVENTORY", "PRODUCTS", "REVIEWS"]):
    """Generate enum types with many values and federation directives."""
    enums = []
    for i in range(count):
        name = f"Enum{i:04d}"
        subgraph = random.choice(subgraph_names)
        
        values = []
        for j in range(random.randint(5, 20)):
            values.append(f"  VALUE_{j:03d}")
        
        enum_def = f"enum {name}\n  @join__type(graph: {subgraph}) {{\n" + "\n".join(values) + "\n}"
        enums.append(enum_def)
    return enums

def generate_input_types(count=300, subgraph_names=["ACCOUNTS", "INVENTORY", "PRODUCTS", "REVIEWS"]):
    """Generate input types with federation directives."""
    inputs = []
    scalar_types = ["String", "Int", "Float", "Boolean", "ID"]
    
    for i in range(count):
        name = f"Input{i:04d}"
        subgraph = random.choice(subgraph_names)
        fields = []
        field_count = random.randint(3, 15)
        
        for j in range(field_count):
            field_name = f"field{j:03d}"
            field_type = random.choice(scalar_types)
            if random.random() < 0.3:  # 30% chance of being required
                fields.append(f"  {field_name}: {field_type}!")
            else:
                fields.append(f"  {field_name}: {field_type}")
        
        input_def = f"input {name}\n  @join__type(graph: {subgraph}) {{\n" + "\n".join(fields) + "\n}"
        inputs.append(input_def)
    return inputs

def generate_interface_types(count=150, subgraph_names=["ACCOUNTS", "INVENTORY", "PRODUCTS", "REVIEWS"]):
    """Generate interface types with federation directives."""
    interfaces = []
    scalar_types = ["String", "Int", "Float", "Boolean", "ID"]
    
    for i in range(count):
        name = f"Interface{i:04d}"
        subgraph = random.choice(subgraph_names)
        fields = []
        field_count = random.randint(2, 8)
        
        for j in range(field_count):
            field_name = f"field{j:03d}"
            field_type = random.choice(scalar_types)
            fields.append(f"  {field_name}: {field_type}")
        
        interface_def = f"interface {name}\n  @join__type(graph: {subgraph}) {{\n" + "\n".join(fields) + "\n}"
        interfaces.append(interface_def)
    return interfaces

def generate_union_types(count=100, max_types_per_union=8, subgraph_names=["ACCOUNTS", "INVENTORY", "PRODUCTS", "REVIEWS"]):
    """Generate union types with federation directives."""
    unions = []
    
    # We'll reference types that will be generated
    for i in range(count):
        name = f"Union{i:04d}"
        subgraph = random.choice(subgraph_names)
        union_count = random.randint(2, max_types_per_union)
        union_types = []
        
        for j in range(union_count):
            # Reference other generated types
            type_name = f"Type{(i * max_types_per_union + j) % 1000:04d}"
            union_types.append(type_name)
        
        union_def = f"union {name}\n  @join__type(graph: {subgraph}) = " + " | ".join(union_types)
        unions.append(union_def)
    return unions

def generate_object_types(count=1000, subgraph_names=["ACCOUNTS", "INVENTORY", "PRODUCTS", "REVIEWS"]):
    """Generate object types with federation directives."""
    objects = []
    scalar_types = ["String", "Int", "Float", "Boolean", "ID"]
    
    for i in range(count):
        name = f"Type{i:04d}"
        subgraph = random.choice(subgraph_names)
        
        # Add federation directive
        key_field = f"id{i % 10}"  # Rotate key fields
        directives = f'@join__type(graph: {subgraph}, key: "{key_field}")'
        
        fields = []
        field_count = random.randint(5, 25)
        
        # Always include the key field
        fields.append(f"  {key_field}: ID!")
        
        for j in range(field_count - 1):
            field_name = f"field{j:03d}"
            
            # Use only scalar types to avoid reference issues
            field_type = random.choice(scalar_types)
            
            # Add array types sometimes
            if random.random() < 0.2:  # 20% chance
                field_type = f"[{field_type}]"
            
            # Add federation directives sometimes
            field_directive = ""
            if random.random() < 0.1:  # 10% chance
                field_directive = f" @join__field(graph: {subgraph})"
            
            fields.append(f"  {field_name}: {field_type}{field_directive}")
        
        object_def = f"type {name}\n  {directives} {{\n" + "\n".join(fields) + "\n}"
        objects.append(object_def)
    
    return objects

def generate_massive_extensions(base_schema_content):
    """Generate massive extensions to the base schema."""
    print("Generating massive schema extensions...")
    
    extensions = []
    
    # Generate different types
    print("- Generating scalar types...")
    extensions.extend(generate_scalar_types(500))
    
    print("- Generating enum types...")  
    extensions.extend(generate_enum_types(1000))
    
    print("- Generating input types...")
    extensions.extend(generate_input_types(1500))
    
    print("- Generating interface types...")
    extensions.extend(generate_interface_types(800))
    
    print("- Generating object types...")
    extensions.extend(generate_object_types(26000))  # Lots of object types
    
    print("- Generating union types...")
    extensions.extend(generate_union_types(500))
    
    # Add extensions to Query type
    query_extensions = []
    for i in range(2200):  # 2200 additional query fields
        field_name = f"massiveField{i:04d}"
        # Use basic scalar types for query fields to avoid reference issues
        return_type = random.choice(["String", "Int", "Boolean", "Float", "ID"])
        subgraph = random.choice(["ACCOUNTS", "INVENTORY", "PRODUCTS", "REVIEWS"])
        
        # Add arguments sometimes
        args = ""
        if random.random() < 0.3:  # 30% chance
            arg_count = random.randint(1, 3)
            arg_list = []
            for j in range(arg_count):
                arg_name = f"arg{j}"
                arg_type = random.choice(["String", "Int", "Boolean", "ID"])
                arg_list.append(f"{arg_name}: {arg_type}")
            args = f"({', '.join(arg_list)})"
        
        query_extensions.append(f"  {field_name}{args}: {return_type} @join__field(graph: {subgraph})")
    
    # Create extended Query type
    extended_query = """
type Query
  @join__type(graph: ACCOUNTS)
  @join__type(graph: INVENTORY)
  @join__type(graph: PRODUCTS)
  @join__type(graph: REVIEWS) {
  me: User @join__field(graph: ACCOUNTS)
  recommendedProducts: [Product] @join__field(graph: ACCOUNTS)
  topProducts(first: Int = 5): [Product] @join__field(graph: PRODUCTS)
""" + "\n".join(query_extensions) + "\n}"
    
    # Combine everything
    massive_schema = base_schema_content.replace(
        """type Query
  @join__type(graph: ACCOUNTS)
  @join__type(graph: INVENTORY)
  @join__type(graph: PRODUCTS)
  @join__type(graph: REVIEWS) {
  me: User @join__field(graph: ACCOUNTS)
  recommendedProducts: [Product] @join__field(graph: ACCOUNTS)
  topProducts(first: Int = 5): [Product] @join__field(graph: PRODUCTS)
}""", 
        extended_query
    )
    
    # Add all the generated types
    massive_schema += "\n\n# Generated massive extensions\n\n"
    massive_schema += "\n\n".join(extensions)
    
    return massive_schema

def main():
    """Main function to generate the massive schema."""
    print("Creating massive GraphQL supergraph schema...")
    
    # Read the original schema
    original_schema_path = Path("supergraph.graphql")
    if not original_schema_path.exists():
        print("Error: supergraph.graphql not found!")
        return
    
    with open(original_schema_path, 'r') as f:
        base_schema = f.read()
    
    print(f"Original schema size: {len(base_schema):,} bytes")
    
    # Generate massive extensions
    massive_schema = generate_massive_extensions(base_schema)
    
    # Write the massive schema
    massive_schema_path = Path("supergraph-massive.graphql")
    with open(massive_schema_path, 'w') as f:
        f.write(massive_schema)
    
    final_size = len(massive_schema)
    print(f"Massive schema size: {final_size:,} bytes ({final_size / 1024 / 1024:.2f} MB)")
    print(f"Generated schema saved to: {massive_schema_path}")
    
    if final_size < 10 * 1024 * 1024:  # If less than 10MB
        print("Schema is smaller than 10MB, you may want to increase the counts in the generation functions.")
    
    print("\nTo use the massive schema:")
    print("1. Update router.yaml to use supergraph-massive.graphql")
    print("2. Or modify run_load_test.sh to use --supergraph supergraph-massive.graphql")

if __name__ == "__main__":
    main()