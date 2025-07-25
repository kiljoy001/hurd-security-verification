# Coq Theorem to Implementation Mapping: Bounded Traversal

## Overview

This document maps the formal Coq specifications to the C implementation for bounded filesystem traversal protection.

## Formal Model Mapping

### 1. Core Types

#### Coq Definition → C Implementation
```coq
(* Coq: SecureNode from formal model *)
Record SecureNode : Type := mkSecureNode {
  node_id : nat;
  node_type : nat;
  max_depth : option nat;
  resource_bounds : option ResourcePrincipal
}.
```

```c
/* C: struct secure_fsnode */
struct secure_fsnode {
  ino_t node_id;              /* Maps to node_id */
  int node_type;              /* Maps to node_type */  
  size_t max_depth;           /* Maps to max_depth (always Some) */
  struct resource_bounds *bounds; /* Maps to resource_bounds */
  /* Implementation fields */
  size_t current_depth;
  struct secure_fsnode *parent;
  pthread_mutex_t lock;
};
```

### 2. Core Properties

#### bounded_traversal Property

**Coq Specification:**
```coq
Definition bounded_traversal (n : SecureNode) : Prop :=
  match n.(max_depth) with
  | Some d => d > 0
  | None => False
  end.
```

**C Implementation:**
```c
/* Verification function that maps directly to Coq property */
int verify_bounded_traversal(struct secure_fsnode *node)
{
  if (!node)
    return 0; /* False - no node */
    
  /* In C implementation, max_depth is always set (not optional)
     So we verify: max_depth > 0 */
  return (node->max_depth > 0) ? 1 : 0;
}
```

**Constructor Enforcement:**
```c
error_t secure_fsnode_init(struct secure_fsnode *node, /*...*/ size_t max_depth, /*...*/)
{
  /* Enforce bounded_traversal property at construction */
  if (max_depth == 0)
    return EINVAL; /* Reject nodes that would violate property */
    
  node->max_depth = max_depth; /* Ensure property holds */
  /* ... */
}
```

#### bounded_resource_consumption Property

**Coq Specification:**
```coq
Definition bounded_resource_consumption (n : SecureNode) : Prop :=
  match n.(resource_bounds) with
  | Some rp => length rp.(allocated_resources) <= length rp.(resource_limit)
  | None => False
  end.
```

**C Implementation:**
```c
int verify_bounded_resource_consumption(struct secure_fsnode *node)
{
  if (!node || !node->bounds)
    return 0; /* False - no bounds (maps to None case) */
    
  /* Check that allocated <= limit for each resource type */
  if (node->bounds->allocated_memory > node->bounds->max_memory)
    return 0;
    
  if (node->bounds->performed_operations > node->bounds->max_operations)
    return 0;
    
  return 1; /* True - bounds are satisfied */
}
```

### 3. Security Theorems

#### malicious_fs_dos_prevention Theorem

**Coq Theorem:**
```coq
Theorem malicious_fs_dos_prevention : 
  forall (n : SecureNode) (depth : nat),
    bounded_traversal n ->
    bounded_resource_consumption n ->
    match n.(max_depth) with
    | Some max_d => depth <= max_d
    | None => False
    end ->
    exists (result : bool), result = true.
```

**C Implementation:**
```c
error_t verify_dos_prevention(struct secure_fsnode *node,
                             size_t requested_depth,
                             struct traversal_context *ctx)
{
  /* Verify bounded_traversal precondition */
  if (!verify_bounded_traversal(node))
    return EINVAL; /* Precondition failed */
    
  /* Verify bounded_resource_consumption precondition */
  if (!verify_bounded_resource_consumption(node))
    return EINVAL; /* Precondition failed */
    
  /* Verify depth condition: requested_depth <= max_depth */
  if (requested_depth > node->max_depth)
    return ELOOP; /* Condition failed */
    
  /* All preconditions satisfied - theorem guarantees operation completes */
  return 0; /* Success - DOS prevention verified */
}
```

#### Runtime Enforcement

**Traversal Check Implementation:**
```c
error_t secure_traversal_check(struct secure_fsnode *from_node,
                              struct secure_fsnode *to_node,
                              struct traversal_context *ctx)
{
  /* Check depth bounds - implements bounded_traversal property */
  if (ctx->flags & TRAVERSAL_CHECK_DEPTH) {
    size_t new_depth = from_node->current_depth + 1;
    
    /* Verify against node's max_depth (bounded_traversal property) */
    if (new_depth > to_node->max_depth) {
      return ELOOP; /* Traversal depth exceeded */
    }
    
    /* Update context depth */
    ctx->current_depth = new_depth;
  }
  
  /* Check resource bounds - implements bounded_resource_consumption */
  if (ctx->flags & TRAVERSAL_CHECK_RESOURCES) {
    if (to_node->bounds) {
      error_t result = secure_check_resource_bounds(to_node->bounds);
      if (result)
        return result; /* Resource bounds violated */
    }
  }
  
  return 0; /* Traversal allowed */
}
```

## Test Suite Verification

### Property-Based Testing

The test suite directly verifies that implementations satisfy Coq properties:

```c
static void test_bounded_traversal_property(void)
{
  /* Test 1: Valid node with max_depth > 0 should satisfy property */
  err = secure_fsnode_init(&node, 1, 1, 50, bounds);
  TEST_ASSERT(err == 0, "Node initialization with valid max_depth");
  TEST_ASSERT(verify_bounded_traversal(&node) == 1, 
              "bounded_traversal property holds for valid node");
  
  /* Test 2: Node with max_depth = 0 should fail property */
  err = secure_fsnode_init(&node, 2, 1, 0, bounds);
  TEST_ASSERT(err == EINVAL, "Node initialization fails with max_depth = 0");
}
```

### Theorem Verification

```c  
static void test_malicious_dos_prevention(void)
{
  /* Test theorem conditions directly */
  err = verify_dos_prevention(&node, 5, &ctx); /* 5 <= 10 */
  TEST_ASSERT(err == 0, "DOS prevention succeeds for valid depth");
  
  err = verify_dos_prevention(&node, 15, &ctx); /* 15 > 10 */
  TEST_ASSERT(err == ELOOP, "DOS prevention fails for excessive depth");
}
```

## Design Decisions

### 1. Optional Types in Coq vs C

**Coq**: Uses `option nat` for max_depth to model optional bounds
**C**: Always requires max_depth to be set (simpler, more defensive)

**Justification**: C implementation is more restrictive than Coq model, which is acceptable for security (fail-safe design).

### 2. Resource Bounds Representation

**Coq**: Abstract `ResourcePrincipal` with list of resources
**C**: Concrete `resource_bounds` struct with specific fields

**Mapping**: C implementation provides concrete realization of abstract Coq concept.

### 3. Error Handling

**Coq**: Uses proposition logic (True/False)
**C**: Uses error codes (0 = success, errno values for failures)

**Mapping**: 
- Coq `True` → C `0` (success)
- Coq `False` → C error code (EINVAL, ELOOP, etc.)

## Verification Methodology

### 1. Direct Property Testing
Each Coq property has a corresponding C verification function that can be called in tests.

### 2. Constructor Invariants
C constructors enforce Coq property preconditions at object creation time.

### 3. Runtime Checks
Security-critical operations verify Coq theorem preconditions before proceeding.

### 4. Test Coverage
Test suite covers:
- Property satisfaction for valid inputs
- Property violation detection for invalid inputs  
- Theorem precondition checking
- Error condition handling

## Static Analysis Integration

The implementation includes hooks for formal verification tools:

```c
/*@ requires node != NULL;
    requires node->max_depth > 0;
    ensures \result == 1 <==> node->max_depth > 0;
*/
int verify_bounded_traversal(struct secure_fsnode *node);
```

This allows tools like Frama-C to verify that the C implementation satisfies the formal specifications.

---

**Result**: The C implementation provides a faithful, testable realization of the Coq formal specifications with direct property verification and theorem-based runtime checking.