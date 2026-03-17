/-
  Hack-like notation for building Lean counterexamples.

  Goal: make counterexamples read like Hack source code,
  similar to the custom visualizer in the Alloy model (hack.als line 2:
  `//@custom_visualization: ./show ./example.php`)

  Example usage:
  ```
  abstract class "C1" with
    «__ConsistentConstruct»
  where
    abstract static function "abs" : void
    «__ConcreteClass» static function "nc" : void

  abstract final class "C2" extends "C1" where
    static function "abs" : void
  ```
-/
import HackSafety.Safety

-- ============================================================
-- Pretty-printed Hack declarations using custom syntax
-- ============================================================

/-- A named method for display -/
structure NamedMethod where
  name : String
  method : Method
  deriving DecidableEq

/-- A named class for display -/
structure NamedClass where
  name : String
  cls : Class
  deriving DecidableEq

/-- A named call for display -/
structure NamedCall where
  description : String
  call : Call

-- ============================================================
-- Method builders with Hack-like names
-- ============================================================

/-- `abstract static function "name" : void` -/
def «abstract static function» (name : String) : NamedMethod :=
  ⟨name, { kind := MethodKind.abstract_, hasConcreteClassAttr := false, isFinal := false }⟩

/-- `static function "name" : void` (concrete) -/
def «static function» (name : String) : NamedMethod :=
  ⟨name, { kind := MethodKind.concrete, hasConcreteClassAttr := false, isFinal := false }⟩

/-- `«__ConcreteClass» static function "name" : void` -/
def «concreteClass static function» (name : String) : NamedMethod :=
  ⟨name, { kind := MethodKind.concrete, hasConcreteClassAttr := true, isFinal := false }⟩

/-- Abstract constructor (for abstract classes) -/
def «abstract __construct» : NamedMethod :=
  ⟨"__construct", { kind := MethodKind.abstract_, hasConcreteClassAttr := true, isFinal := false }⟩

/-- Concrete constructor (for concrete classes) -/
def «__construct» : NamedMethod :=
  ⟨"__construct", { kind := MethodKind.concrete, hasConcreteClassAttr := true, isFinal := false }⟩

-- ============================================================
-- Class builders with Hack-like syntax
-- ============================================================

/-- `abstract class "Name" where ...methods...` -/
def «abstract class» (name : String) (methods : List NamedMethod) : NamedClass :=
  ⟨name, {
    kind := ClassKind.abstract_,
    isClassFinal := false,
    hasConsistentConstruct := false,
    methods := methods.map (·.method)
  }⟩

/-- `«__ConsistentConstruct» abstract class "Name" where ...` -/
def «cc abstract class» (name : String) (methods : List NamedMethod) : NamedClass :=
  ⟨name, {
    kind := ClassKind.abstract_,
    isClassFinal := false,
    hasConsistentConstruct := true,
    methods := methods.map (·.method)
  }⟩

/-- `abstract final class "Name" where ...` -/
def «abstract final class» (name : String) (methods : List NamedMethod) : NamedClass :=
  ⟨name, {
    kind := ClassKind.abstract_,
    isClassFinal := true,
    hasConsistentConstruct := false,
    methods := methods.map (·.method)
  }⟩

/-- `«__ConsistentConstruct» abstract final class "Name" where ...`
    (inherits CC from parent) -/
def «cc abstract final class» (name : String) (methods : List NamedMethod) : NamedClass :=
  ⟨name, {
    kind := ClassKind.abstract_,
    isClassFinal := true,
    hasConsistentConstruct := true,
    methods := methods.map (·.method)
  }⟩

/-- `class "Name" where ...` (concrete) -/
def «class» (name : String) (methods : List NamedMethod) : NamedClass :=
  ⟨name, {
    kind := ClassKind.concrete,
    isClassFinal := false,
    hasConsistentConstruct := false,
    methods := methods.map (·.method)
  }⟩

-- ============================================================
-- Call builders with Hack-like syntax
-- ============================================================

/-- `$var::method()` where `$var: classname<C>` -/
def «classname call» (desc : String) (cls : NamedClass) (resolved : NamedMethod)
    (staticResolved : NamedMethod) : NamedCall :=
  ⟨desc, Call.varCall {
    receiverTypeKind := TypeKind.className,
    pointsToClass := cls.cls,
    resolvesTo := resolved.method,
    staticResolvesTo := staticResolved.method
  }⟩

/-- `$var::method()` where `$var: concrete_classname<C>` -/
def «concrete_classname call» (desc : String) (cls : NamedClass) (resolved : NamedMethod)
    (staticResolved : NamedMethod) : NamedCall :=
  ⟨desc, Call.varCall {
    receiverTypeKind := TypeKind.concreteClassName,
    pointsToClass := cls.cls,
    resolvesTo := resolved.method,
    staticResolvesTo := staticResolved.method
  }⟩

/-- `static::method()` inside a method of a class -/
def «static:: call» (desc : String) (resolvedClass : NamedClass) (resolved : NamedMethod)
    (staticResolved : NamedMethod) (containingMethod : NamedMethod)
    (containingClass : NamedClass) : NamedCall :=
  ⟨desc, Call.staticCall {
    resolvesToClass := resolvedClass.cls,
    resolvesTo := resolved.method,
    staticResolvesTo := staticResolved.method,
    containingMethod := containingMethod.method,
    containingClass := containingClass.cls
  }⟩

-- ============================================================
-- Counterexample 1 (revisited with Hack notation):
-- Removing TCCantCallAbstractMethodThroughClassName
--
-- <?hh
-- abstract class C {
--   abstract static function foo(): void;
-- }
-- $cls = C::class;            // $cls: classname<C>
-- $cls::foo();                 // RUNTIME ERROR
-- ============================================================

namespace Example1

def C := «abstract class» "C" [
  «abstract static function» "foo"
]

def foo := «abstract static function» "foo"

def the_call := «classname call» "$cls::foo()" C foo foo

theorem fatal : the_call.call.isFatal := rfl

end Example1

-- ============================================================
-- Counterexample 2 (revisited with Hack notation):
-- Removing TCAbstractFinalCantInheritConsistentConstruct
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
-- }
--
-- $cls = C2::class;           // $cls: concrete_classname<C2>
-- $cls::__construct();        // RUNTIME ERROR: abstract constructor
-- ============================================================

namespace Example2

def C1 := «cc abstract class» "C1" [
  «abstract static function» "abs",
  «concreteClass static function» "nc",
  «abstract __construct»
]

def C2 := «cc abstract final class» "C2" [
  «static function» "abs",
  «abstract __construct»
]

def the_call := «concrete_classname call» "$cls::__construct()"
  C2 «abstract __construct» «abstract __construct»

theorem fatal : the_call.call.isFatal := rfl

theorem caught_by_rule :
    C2.cls.kind = ClassKind.abstract_ ∧
    C2.cls.isClassFinal ∧
    C2.cls.hasConsistentConstruct := ⟨rfl, rfl, rfl⟩

end Example2

-- ============================================================
-- Counterexample 3 (revisited with Hack notation):
-- Removing TCCanOnlyUseStaticAsConcreteInConcreteClassMethods
--
-- <?hh
-- abstract class Parent {
--   abstract static function abs(): void;
--   // NOT <<__ConcreteClass>> - this is the bug
--   public static function caller(): void {
--     static::abs();          // RUNTIME ERROR when static = Parent
--   }
-- }
--
-- $cls = Parent::class;       // $cls: classname<Parent>
-- $cls::caller();
-- ============================================================

namespace Example3

def abs := «abstract static function» "abs"
def caller := «static function» "caller"  -- NOT ConcreteClass

def Parent := «abstract class» "Parent" [abs, caller]

def the_call := «static:: call» "static::abs() inside caller()"
  Parent abs abs caller Parent

theorem fatal : the_call.call.isFatal := rfl

theorem caller_not_concrete_class :
    ¬ caller.method.effectivelyConcreteClass Parent.cls := by
  simp [caller, «static function», Parent, «abstract class»,
        Method.effectivelyConcreteClass]

end Example3
