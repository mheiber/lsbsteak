# Validation Plan: __ConsistentConstruct and abstract final classes

## Goal
Model `__ConsistentConstruct` in Alloy, showing that abstract final classes inheriting __ConsistentConstruct can lead to runtime errors when treated as concrete, then add a type system rule to prevent this.

## Key Insight
- `__ConsistentConstruct` is a CLASS-level attribute that enables `new static()` calls
- It propagates transitively through extends
- `new static()` = `static::__Construct()` in the model
- An abstract final class has no concrete constructor (it's AbstractClass)
- "Treating abstract final CC classes as concrete" = allowing ConcreteClassName types for them
- This lets code call methods (including __Construct) through ConcreteClassName
- The abstract constructor resolves at runtime -> RuntimeFatal
- The existing type system doesn't catch this because ConcreteClassName was previously restricted to ConcreteClass only

## Commits:

### Commit 1 (214f236): Initial approach (superseded)
- Added ConsistentConstruct + ClassFinal markers to model
- Added exception in TCCanOnlyUseStaticAsConcreteInConcreteClassMethods
- Problem: exception was too broad, affected all abstract classes not just abstract final

### Commit 2 (c6b9264): Correct approach for showing runtime error
- Removed the wrong exception
- Instead modified ConcreteClassName fact: abstract final CC classes can have ConcreteClassName types
- `check safe for 4` finds counterexample:
  - AbstractClass with ClassFinal and ConsistentConstruct inherits abstract constructor
  - Var with ConcreteClassName type points to this class
  - Calling __Construct through ConcreteClassName resolves to abstract method -> RuntimeFatal
  - No TypeCheckerError fires

### Commit 3 (03cdd15): Add rule preventing the error
- Added TCAbstractFinalCantInheritConsistentConstruct TypeCheckerError
- Rule: abstract + final + ConsistentConstruct -> type checker error
- Added Class to tc_error_at type union
- `check safe for 4` -> No counterexample found
- `check safe` -> No counterexample found
- `check static_always_resolves_to_a_concrete_class_in_concrete_class_methods` -> No counterexample found

## Validation criteria:
- [x] The alloy model compiles and runs
- [x] Before the fix: `check safe for 4` finds a counterexample showing RuntimeFatal with no TypeCheckerError
- [x] After the fix: `check safe for 4` finds NO counterexample
- [x] After the fix: `check safe` finds NO counterexample
- [x] After the fix: `check static_always_resolves_to_a_concrete_class_in_concrete_class_methods` finds NO counterexample
- [x] Multiple subagents have reviewed (3 review agents, all approved with no issues requiring fixes)

## Subagent Review Summary:
1. **Model review agent**: Approved. Noted is_class_final is unconstrained (by design). No bugs found.
2. **Counterexample verification agent**: Thoroughly traced the scenario. Confirmed all 7 existing TypeCheckerErrors correctly don't fire. Confirmed TCAbstractFinalCantInheritConsistentConstruct correctly fires after the fix. No issues.
3. **Edge case agent**: Checked 6 edge cases. Confirmed non-final abstract CC classes can't get ConcreteClassName types. Confirmed CC propagation is one-directional. Confirmed `some` constraint on tc_error_at works correctly with Class added. No bugs found.
