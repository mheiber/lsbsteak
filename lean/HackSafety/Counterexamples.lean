/-
  Counterexamples showing that removing each type checker rule allows runtime errors.

  For each rule, we construct a concrete "world" (program) where:
  - That rule is violated (the type checker would catch it but we omit the check)
  - A RuntimeFatal occurs (a call resolves to an abstract method)

  We use Hack-like notation to make the counterexamples readable.
-/
import HackSafety.Safety

-- ============================================================
-- Hack-like notation for building programs
-- ============================================================

namespace HackNotation

/-- Build a concrete class -/
def concreteClass (methods : List Method) : Class :=
  { kind := ClassKind.concrete, isClassFinal := false,
    hasConsistentConstruct := false, methods := methods }

/-- Build an abstract class -/
def abstractClass (methods : List Method) : Class :=
  { kind := ClassKind.abstract_, isClassFinal := false,
    hasConsistentConstruct := false, methods := methods }

/-- Build an abstract final class -/
def abstractFinalClass (methods : List Method) : Class :=
  { kind := ClassKind.abstract_, isClassFinal := true,
    hasConsistentConstruct := false, methods := methods }

/-- Build an abstract class with __ConsistentConstruct -/
def consistentConstructClass (methods : List Method) : Class :=
  { kind := ClassKind.abstract_, isClassFinal := false,
    hasConsistentConstruct := true, methods := methods }

/-- Build an abstract final class with __ConsistentConstruct -/
def abstractFinalCCClass (methods : List Method) : Class :=
  { kind := ClassKind.abstract_, isClassFinal := true,
    hasConsistentConstruct := true, methods := methods }

/-- A concrete method (public static function foo(): void { ... }) -/
def concreteMethod : Method :=
  { kind := MethodKind.concrete, hasConcreteClassAttr := false, isFinal := false }

/-- An abstract method (abstract static function foo(): void;) -/
def abstractMethod : Method :=
  { kind := MethodKind.abstract_, hasConcreteClassAttr := false, isFinal := false }

/-- A method with <<__ConcreteClass>> attribute -/
def concreteClassMethod : Method :=
  { kind := MethodKind.concrete, hasConcreteClassAttr := true, isFinal := false }

/-- An abstract constructor. Abstract classes have abstract constructors
    in the model (hack.als line 107-109) -/
def abstractConstructor : Method :=
  { kind := MethodKind.abstract_, hasConcreteClassAttr := true, isFinal := false }

/-- A concrete constructor -/
def concreteConstructor : Method :=
  { kind := MethodKind.concrete, hasConcreteClassAttr := true, isFinal := false }

/-- A call: $var::method() where $var: classname<C> and C is the given class -/
def callThroughClassName (cls : Class) (resolved : Method) (staticResolved : Method) : Call :=
  Call.varCall {
    receiverTypeKind := TypeKind.className,
    pointsToClass := cls,
    resolvesTo := resolved,
    staticResolvesTo := staticResolved
  }

/-- A call: $var::method() where $var: ConcreteClassName<C> -/
def callThroughConcreteClassName (cls : Class) (resolved : Method) (staticResolved : Method) : Call :=
  Call.varCall {
    receiverTypeKind := TypeKind.concreteClassName,
    pointsToClass := cls,
    resolvesTo := resolved,
    staticResolvesTo := staticResolved
  }

/-- A call: static::method() inside a method of a class -/
def staticCall' (resolvedClass : Class) (resolved : Method) (staticResolved : Method)
    (containingMethod : Method) (containingClass : Class) : Call :=
  Call.staticCall {
    resolvesToClass := resolvedClass,
    resolvesTo := resolved,
    staticResolvesTo := staticResolved,
    containingMethod := containingMethod,
    containingClass := containingClass
  }

end HackNotation

open HackNotation

-- ============================================================
-- Counterexample 1: Removing TCCantCallAbstractMethodThroughClassName
--
-- Hack code:
--   abstract class C {
--     abstract static function foo(): void;
--   }
--   $cls = C::class;                     // $cls: classname<C>
--   $cls::foo();                          // RUNTIME ERROR: calls abstract method
--
-- (hack.als line 258-266)
-- ============================================================

/-- An abstract class with an abstract method -/
private def ex1_C : Class := abstractClass [abstractMethod]

/-- The fatal call: $cls::foo() through classname<C> resolves to abstract foo -/
private def ex1_call : Call := callThroughClassName ex1_C abstractMethod abstractMethod

/-- This call is fatal: it resolves to an abstract method -/
theorem counterexample_no_abstract_through_classname :
    ex1_call.isFatal := by
  rfl

-- ============================================================
-- Counterexample 2: Removing TCAbstractFinalCantInheritConsistentConstruct
--
-- Hack code:
--   <<__ConsistentConstruct>>
--   abstract class C1 {
--     abstract static function abs(): void;
--     <<__ConcreteClass>>
--     public static function nc(): void {
--       new static();  // = static::__construct()
--     }
--   }
--
--   abstract final class C2 extends C1 {
--     // C2 inherits __ConsistentConstruct from C1
--     // C2 has NO concrete constructor (it's abstract)
--     public static function abs(): void { }
--   }
--
--   $cls: concrete_classname<C2> = C2::class;
--   // ^ allowed because we "treat abstract final CC as concrete"
--   $cls::__construct();  // RUNTIME ERROR: C2 has abstract constructor
--
-- (hack.als line 296-303)
-- ============================================================

/-- C2: abstract final class with __ConsistentConstruct, has abstract constructor -/
private def ex2_C2 : Class := abstractFinalCCClass [abstractConstructor]

/-- The fatal call: new C2() through concrete_classname<C2> -/
private def ex2_call : Call :=
  callThroughConcreteClassName ex2_C2 abstractConstructor abstractConstructor

/-- This call is fatal -/
theorem counterexample_no_abstract_final_cc_rule :
    ex2_call.isFatal := by
  rfl

/-- The TCAbstractFinalCantInheritConsistentConstruct rule catches this.
    C2 is abstract, final, and has __ConsistentConstruct. -/
theorem ex2_caught_by_rule :
    ex2_C2.kind = ClassKind.abstract_ ∧
    ex2_C2.isClassFinal ∧
    ex2_C2.hasConsistentConstruct := by
  exact ⟨rfl, rfl, rfl⟩

-- ============================================================
-- Counterexample 3: Removing TCCanOnlyUseStaticAsConcreteInConcreteClassMethods
--
-- Hack code:
--   abstract class Parent {
--     abstract static function abs(): void;
--     // NOT <<__ConcreteClass>>
--     public static function caller(): void {
--       static::abs();  // RUNTIME ERROR: Parent::abs() is abstract
--     }
--   }
--
--   $cls: classname<Parent> = Parent::class;
--   $cls::caller();
--   // Inside caller(), static:: resolves to Parent (abstract).
--   // static::abs() calls the abstract method.
--
-- If the rule existed, it would catch the static::abs() call inside caller()
-- because abs() is abstract but caller() is NOT <<__ConcreteClass>>.
--
-- (hack.als line 284-294)
-- ============================================================

private def ex3_abs : Method := abstractMethod
private def ex3_caller : Method := concreteMethod  -- NOT ConcreteClass-attributed

/-- Parent: abstract class with abs() and caller() -/
private def ex3_Parent : Class := abstractClass [ex3_abs, ex3_caller]

/-- The fatal call: static::abs() inside caller(), resolving to Parent -/
private def ex3_call : Call :=
  staticCall' ex3_Parent ex3_abs ex3_abs ex3_caller ex3_Parent

/-- This call is fatal -/
theorem counterexample_no_static_concrete_context_rule :
    ex3_call.isFatal := by
  rfl

/-- The TCCanOnlyUseStaticAsConcreteInConcreteClassMethods rule catches this:
    the called method (abs) is abstract, but the containing method (caller)
    is NOT effectively ConcreteClass. -/
theorem ex3_caught_by_rule :
    ex3_abs.kind = MethodKind.abstract_ ∧
    ¬ ex3_caller.effectivelyConcreteClass ex3_Parent := by
  constructor
  · rfl
  · intro h
    unfold Method.effectivelyConcreteClass at h
    simp [ex3_caller, concreteMethod, ex3_Parent, abstractClass] at h

-- ============================================================
-- Counterexample 4: Removing the concrete_no_abstract structural rule
--
-- Hack code:
--   // Hypothetical: a "concrete" class with an abstract method
--   class C {
--     abstract static function foo(): void;  // ILLEGAL in Hack
--   }
--   $cls: concrete_classname<C> = C::class;
--   $cls::foo();  // RUNTIME ERROR
--
-- (hack.als line 115-117)
-- ============================================================

/-- A "concrete" class with an abstract method (normally impossible) -/
private def ex4_C : Class := concreteClass [abstractMethod]

private def ex4_call : Call :=
  callThroughConcreteClassName ex4_C abstractMethod abstractMethod

theorem counterexample_concrete_with_abstract :
    ex4_call.isFatal := by
  rfl

-- ============================================================
-- Summary: each counterexample is fatal AND the corresponding
-- type checker rule would catch it
-- ============================================================

/-- All counterexamples are fatal calls -/
theorem all_counterexamples_are_fatal :
    ex1_call.isFatal ∧ ex2_call.isFatal ∧ ex3_call.isFatal ∧ ex4_call.isFatal := by
  exact ⟨rfl, rfl, rfl, rfl⟩
