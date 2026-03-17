/-
  Hack-like notation and counterexamples for the safety proof.

  Uses Lean notation to make counterexamples read like Hack source code,
  similar to the custom visualizer in the Alloy model (hack.als line 2:
  `//@custom_visualization: ./show ./example.php`)
-/
import HackSafety.Safety

-- ============================================================
-- Hack-like notation for declaring methods, classes, and calls
-- ============================================================

namespace Hack

-- ---- Method declarations ----
-- Method names are for readability only (not stored in the Method struct).

/-- `abstract static function "foo" : void` -/
abbrev «abstract static function» (_name : String := "") : Method :=
  { kind := MethodKind.abstract_, hasConcreteClassAttr := false, isFinal := false }

/-- `public static function "foo" : void { ... }` -/
abbrev «public static function» (_name : String := "") : Method :=
  { kind := MethodKind.concrete, hasConcreteClassAttr := false, isFinal := false }

/-- `<<__ConcreteClass>> public static function "foo" : void { ... }` -/
abbrev «<<__ConcreteClass>> public static function» (_name : String := "") : Method :=
  { kind := MethodKind.concrete, hasConcreteClassAttr := true, isFinal := false }

/-- `public function __construct() { }` (concrete constructor) -/
abbrev «public function __construct» : Method :=
  { kind := MethodKind.concrete, hasConcreteClassAttr := true, isFinal := false }

/-- Implicit abstract constructor (for abstract classes without explicit constructor) -/
abbrev «(no concrete __construct)» : Method :=
  { kind := MethodKind.abstract_, hasConcreteClassAttr := true, isFinal := false }

-- ---- Class declarations ----

/-- `abstract class Name { ... }` -/
abbrev «abstract class» (_name : String) (methods : List Method) : Class :=
  { kind := ClassKind.abstract_, isClassFinal := false,
    hasConsistentConstruct := false, methods }

/-- `<<__ConsistentConstruct>> abstract class Name { ... }` -/
abbrev «<<__ConsistentConstruct>> abstract class» (_name : String) (methods : List Method) : Class :=
  { kind := ClassKind.abstract_, isClassFinal := false,
    hasConsistentConstruct := true, methods }

/-- `abstract final class Name { ... }` -/
abbrev «abstract final class» (_name : String) (methods : List Method) : Class :=
  { kind := ClassKind.abstract_, isClassFinal := true,
    hasConsistentConstruct := false, methods }

/-- `<<__ConsistentConstruct>> abstract final class Name extends ... { ... }` -/
abbrev «<<__ConsistentConstruct>> abstract final class» (_name : String)
    (methods : List Method) : Class :=
  { kind := ClassKind.abstract_, isClassFinal := true,
    hasConsistentConstruct := true, methods }

/-- `class Name { ... }` (concrete class) -/
abbrev «class» (_name : String) (methods : List Method) : Class :=
  { kind := ClassKind.concrete, isClassFinal := false,
    hasConsistentConstruct := false, methods }

-- ---- Call expressions ----

/-- `$var::method()` where `$var : classname<C>` -/
abbrev «classname<_>::call» (cls : Class) (resolved staticResolved : Method) : Call :=
  Call.varCall {
    receiverTypeKind := TypeKind.className,
    pointsToClass := cls,
    resolvesTo := resolved,
    staticResolvesTo := staticResolved }

/-- `$var::method()` where `$var : concrete_classname<C>` -/
abbrev «concrete_classname<_>::call» (cls : Class) (resolved staticResolved : Method) : Call :=
  Call.varCall {
    receiverTypeKind := TypeKind.concreteClassName,
    pointsToClass := cls,
    resolvesTo := resolved,
    staticResolvesTo := staticResolved }

/-- `static::method()` inside containingMethod of containingClass -/
abbrev «static::call» (resolvesToClass : Class) (resolved staticResolved : Method)
    (containingMethod : Method) (containingClass : Class) : Call :=
  Call.staticCall {
    resolvesToClass,
    resolvesTo := resolved,
    staticResolvesTo := staticResolved,
    containingMethod,
    containingClass }

end Hack

-- ============================================================
-- Counterexample 1: Removing TCCantCallAbstractMethodThroughClassName
-- (hack.als line 258-266)
--
-- <?hh
-- abstract class C {
--   abstract static function foo(): void;
-- }
-- $cls = C::class;            // $cls: classname<C>
-- $cls::foo();                 // RUNTIME ERROR: calls abstract method
-- ============================================================

namespace Counterexample.AbstractThroughClassname
open Hack

private def C :=
  «abstract class» "C" [
    «abstract static function» "foo"
  ]

private def foo := «abstract static function» "foo"

private def the_call := «classname<_>::call» C foo foo

/-- Without TCCantCallAbstractMethodThroughClassName, calling an abstract
    method through classname<C> causes a runtime fatal. -/
theorem fatal : the_call.isFatal := rfl

end Counterexample.AbstractThroughClassname

-- ============================================================
-- Counterexample 2: Removing TCAbstractFinalCantInheritConsistentConstruct
-- (hack.als line 296-303)
--
-- <?hh
-- <<__ConsistentConstruct>>
-- abstract class C1 {
--   abstract static function abs(): void;
--   <<__ConcreteClass>>
--   public static function nc(): void { new static(); }
-- }
--
-- // C2 inherits __ConsistentConstruct from C1
-- abstract final class C2 extends C1 {
--   public static function abs(): void {}
--   // C2 has NO concrete constructor (it's abstract)
-- }
--
-- $cls = C2::class;           // $cls: concrete_classname<C2>
-- $cls::__construct();         // RUNTIME ERROR: abstract constructor
-- ============================================================

namespace Counterexample.AbstractFinalConsistentConstruct
open Hack

private def C1 :=
  «<<__ConsistentConstruct>> abstract class» "C1" [
    «abstract static function» "abs",
    «<<__ConcreteClass>> public static function» "nc",
    «(no concrete __construct)»
  ]

private def C2 :=
  «<<__ConsistentConstruct>> abstract final class» "C2" [
    «public static function» "abs",
    «(no concrete __construct)»
  ]

private def the_call :=
  «concrete_classname<_>::call» C2 «(no concrete __construct)» «(no concrete __construct)»

/-- Without TCAbstractFinalCantInheritConsistentConstruct, calling __construct
    on an abstract final CC class through concrete_classname causes a runtime fatal. -/
theorem fatal : the_call.isFatal := rfl

/-- The rule TCAbstractFinalCantInheritConsistentConstruct catches C2:
    it is abstract, final, and has __ConsistentConstruct. -/
theorem caught_by_rule :
    C2.kind = ClassKind.abstract_ ∧
    C2.isClassFinal ∧
    C2.hasConsistentConstruct := ⟨rfl, rfl, rfl⟩

end Counterexample.AbstractFinalConsistentConstruct

-- ============================================================
-- Counterexample 3: Removing TCCanOnlyUseStaticAsConcreteInConcreteClassMethods
-- (hack.als line 284-294)
--
-- <?hh
-- abstract class Parent {
--   abstract static function abs(): void;
--   // NOT <<__ConcreteClass>> — this is the bug
--   public static function caller(): void {
--     static::abs();          // RUNTIME ERROR when static = Parent
--   }
-- }
--
-- $cls = Parent::class;       // $cls: classname<Parent>
-- $cls::caller();
-- // Inside caller(), static:: resolves to Parent (abstract).
-- // static::abs() hits the abstract method → fatal.
-- ============================================================

namespace Counterexample.StaticInNonConcreteClassMethod
open Hack

private def abs := «abstract static function» "abs"
private def caller := «public static function» "caller"  -- NOT <<__ConcreteClass>>

private def Parent :=
  «abstract class» "Parent" [abs, caller]

private def the_call :=
  «static::call» Parent abs abs caller Parent

/-- Without TCCanOnlyUseStaticAsConcreteInConcreteClassMethods, calling
    static::abs() from a non-ConcreteClass method causes a runtime fatal. -/
theorem fatal : the_call.isFatal := rfl

/-- The rule would catch this: abs is abstract but caller is NOT
    effectively ConcreteClass. -/
theorem caller_not_concrete_class :
    ¬ caller.effectivelyConcreteClass Parent := by
  simp [caller, «public static function», Parent, «abstract class»,
        Method.effectivelyConcreteClass]

end Counterexample.StaticInNonConcreteClassMethod

-- ============================================================
-- Counterexample 4: Removing the concrete_no_abstract structural rule
-- (hack.als line 115-117)
--
-- <?hh
-- // Hypothetical — illegal in Hack:
-- class C {
--   abstract static function foo(): void;  // can't have abstract in concrete class
-- }
-- $cls = C::class;            // $cls: concrete_classname<C>
-- $cls::foo();                 // RUNTIME ERROR
-- ============================================================

namespace Counterexample.ConcreteClassWithAbstract
open Hack

private def C :=
  «class» "C" [
    «abstract static function» "foo"   -- illegal: abstract method in concrete class
  ]

private def the_call :=
  «concrete_classname<_>::call» C («abstract static function» "foo") («abstract static function» "foo")

/-- Without concrete_no_abstract, a concrete class with an abstract method
    causes a runtime fatal when called. -/
theorem fatal : the_call.isFatal := rfl

end Counterexample.ConcreteClassWithAbstract

-- ============================================================
-- Summary
-- ============================================================

theorem all_counterexamples_are_fatal :
    Counterexample.AbstractThroughClassname.the_call.isFatal ∧
    Counterexample.AbstractFinalConsistentConstruct.the_call.isFatal ∧
    Counterexample.StaticInNonConcreteClassMethod.the_call.isFatal ∧
    Counterexample.ConcreteClassWithAbstract.the_call.isFatal :=
  ⟨rfl, rfl, rfl, rfl⟩
