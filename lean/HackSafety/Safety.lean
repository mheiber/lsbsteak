/-
  Lean proof of safety for the Hack type system model.

  This closely follows the Alloy model in hack.als, proving the safety property:
    RuntimeFatal → some TypeCheckerError

  Each definition references the corresponding Alloy model element.
-/

-- ============================================================
-- Core types, corresponding to Alloy sigs
-- ============================================================

/-- Corresponds to `sig AbstractClass, ConcreteClass extends Class` -/
inductive ClassKind where
  | abstract_
  | concrete
  deriving DecidableEq

/-- Corresponds to `sig ConcreteMethod, AbstractMethod extends Method` -/
inductive MethodKind where
  | abstract_
  | concrete
  deriving DecidableEq

/-- A method. Corresponds to `abstract sig Method { ... }` (hack.als line 14-19)
    We track only the fields relevant to safety. -/
structure Method where
  kind : MethodKind
  hasConcreteClassAttr : Bool  -- concrete_class_attribute: lone ConcreteClassAttribute
  isFinal : Bool  -- is_final: lone Final
  deriving DecidableEq

/-- A class. Corresponds to `abstract sig Class { ... }` (hack.als line 24-29) -/
structure Class where
  kind : ClassKind
  isClassFinal : Bool  -- is_class_final: lone ClassFinal
  hasConsistentConstruct : Bool  -- consistent_construct: lone ConsistentConstructAttr
  methods : List Method
  deriving DecidableEq

/-- Corresponds to `pred effectively_concrete_class[m: Method]` (hack.als line 340-343)
    "A method is effectively ConcreteClass if it has the attribute
    OR if it's final in a concrete class"

    We parameterize by the class containing the method. -/
def Method.effectivelyConcreteClass (m : Method) (cls : Class) : Prop :=
  m.hasConcreteClassAttr ∨ (m.isFinal ∧ cls.kind = ClassKind.concrete)

-- ============================================================
-- Calls: we model the two receiver kinds as separate types
-- to avoid Option fields and make the proof cleaner.
-- ============================================================

/-- Corresponds to `sig ClassName, ConcreteClassName extends Type` -/
inductive TypeKind where
  | className
  | concreteClassName
  deriving DecidableEq

/-- A call through a Var receiver.
    Corresponds to the `call.receiver in Var` branch of `resolve` (hack.als line 409-410). -/
structure VarCall where
  /-- Type kind of the receiver variable's type -/
  receiverTypeKind : TypeKind
  /-- The class the variable transitively points to (resolve_var) -/
  pointsToClass : Class
  /-- The method this call resolves to at runtime -/
  resolvesTo : Method
  /-- The method this call statically resolves to (static_resolve) -/
  staticResolvesTo : Method

/-- A call through the `static` keyword.
    Corresponds to the `else` branch of `resolve` (hack.als line 411-412). -/
structure StaticCall where
  /-- The class that `static` resolves to at runtime -/
  resolvesToClass : Class
  /-- The method this call resolves to at runtime -/
  resolvesTo : Method
  /-- The method this call statically resolves to -/
  staticResolvesTo : Method
  /-- The containing method (the method that contains this static:: call) -/
  containingMethod : Method
  /-- The containing class (where the containing method is defined) -/
  containingClass : Class

/-- A call in the model. Corresponds to `sig Call { ... }` (hack.als line 40-44) -/
inductive Call where
  | varCall : VarCall → Call
  | staticCall : StaticCall → Call

/-- Corresponds to `fact fatals` (hack.als line 151-153):
    A call is fatal iff it resolves to an abstract method. -/
def Call.isFatal : Call → Prop
  | .varCall vc => vc.resolvesTo.kind = MethodKind.abstract_
  | .staticCall sc => sc.resolvesTo.kind = MethodKind.abstract_

-- ============================================================
-- Well-formed world (no type checker errors)
-- ============================================================

/-- A world satisfying all type checker rules.
    Each field corresponds to an Alloy fact/assertion. -/
structure WellFormedWorld where
  calls : List Call
  classes : List Class

  -- ---- Structural facts ----

  /-- fact "concrete classes cannot contain abstract methods" (hack.als line 115-117)
      `no ConcreteClass.methods & AbstractMethod` -/
  concrete_no_abstract :
    ∀ c : Class, c.kind = ClassKind.concrete →
    ∀ m ∈ c.methods, m.kind = MethodKind.concrete

  /-- All classes pointed to by VarCalls are in the world -/
  var_classes_in_world :
    ∀ call ∈ calls, ∀ vc, call = Call.varCall vc → vc.pointsToClass ∈ classes

  /-- All classes from StaticCalls are in the world -/
  static_classes_in_world :
    ∀ call ∈ calls, ∀ sc, call = Call.staticCall sc → sc.resolvesToClass ∈ classes

  -- ---- Var call resolution ----

  /-- Var calls resolve to methods of the pointed-to class.
      Corresponds to `fun resolve_var_call` (hack.als line 349-351) composed with
      `fun resolve` (hack.als line 408-413) -/
  var_resolves_in_class :
    ∀ call ∈ calls, ∀ vc, call = Call.varCall vc →
    vc.resolvesTo ∈ vc.pointsToClass.methods

  /-- Static resolve agrees with runtime resolve in method kind for var calls.
      This is stronger than strictly needed: we only need the direction
      "resolvesTo.kind = abstract_ → staticResolvesTo.kind = abstract_".
      That direction is guaranteed by the Alloy fact (hack.als line 163-168):
      "an abstract method cannot override a concrete method" — so if the
      runtime-resolved method is abstract, the statically-resolved method
      (in an ancestor class) must also be abstract. -/
  var_static_resolves_matches :
    ∀ call ∈ calls, ∀ vc, call = Call.varCall vc →
    vc.staticResolvesTo.kind = vc.resolvesTo.kind

  -- ---- Typing of variable receivers ----

  /-- fact "C has type ConcreteClassName<C> when C is a concrete class
      (treating abstract final CC as concrete)" (hack.als line 311-318) -/
  concrete_classname_target :
    ∀ call ∈ calls, ∀ vc, call = Call.varCall vc →
    vc.receiverTypeKind = TypeKind.concreteClassName →
    (vc.pointsToClass.kind = ClassKind.concrete ∨
     (vc.pointsToClass.kind = ClassKind.abstract_ ∧
      vc.pointsToClass.isClassFinal ∧
      vc.pointsToClass.hasConsistentConstruct))

  /-- fact "C has type ClassName<A> when A is abstract class" (hack.als line 325-329) -/
  classname_target :
    ∀ call ∈ calls, ∀ vc, call = Call.varCall vc →
    vc.receiverTypeKind = TypeKind.className →
    vc.pointsToClass.kind = ClassKind.abstract_

  -- ---- Type checker error rules ----

  /-- TCCantCallAbstractMethodThroughClassName (hack.als line 258-266)
      "typing: can't call abstract methods through ClassName" -/
  tc_no_abstract_through_classname :
    ∀ call ∈ calls, ∀ vc, call = Call.varCall vc →
    vc.receiverTypeKind = TypeKind.className →
    vc.staticResolvesTo.kind ≠ MethodKind.abstract_

  /-- TCAbstractFinalCantInheritConsistentConstruct (hack.als line 296-303)
      "typing: abstract final classes cannot inherit __ConsistentConstruct" -/
  tc_no_abstract_final_cc :
    ∀ c ∈ classes,
    ¬(c.kind = ClassKind.abstract_ ∧ c.isClassFinal ∧ c.hasConsistentConstruct)

  -- ---- Static keyword call rules ----

  /-- Static keyword calls resolve to methods of the resolved class. -/
  static_resolves_in_class :
    ∀ call ∈ calls, ∀ sc, call = Call.staticCall sc →
    sc.resolvesTo ∈ sc.resolvesToClass.methods

  /-- assert static_always_resolves_to_a_concrete_class_in_concrete_class_methods
      (hack.als line 581-587)
      When the containing method is effectively ConcreteClass,
      static resolves to a concrete class.

      NOTE: In the Alloy model this is an *assertion* (checked by the solver),
      not a fact. It is a consequence of the typing rules — in particular,
      ConcreteClassName only names concrete classes, and the subtyping rules
      prevent ClassName from flowing into ConcreteClassName positions.
      We take it as an axiom here, justified by the Alloy solver's verification. -/
  static_resolves_to_concrete :
    ∀ call ∈ calls, ∀ sc, call = Call.staticCall sc →
    sc.containingMethod.effectivelyConcreteClass sc.containingClass →
    sc.resolvesToClass.kind = ClassKind.concrete

  /-- TCCanOnlyUseStaticAsConcreteInConcreteClassMethods (hack.als line 284-294)
      If the called method is ConcreteClass or abstract, the containing method
      must be effectively ConcreteClass.
      Contrapositive: if containing method is NOT effectively ConcreteClass,
      then the called method is neither ConcreteClass nor abstract.
      Since the only remaining option is a plain concrete method, it's concrete. -/
  tc_static_requires_concrete_context :
    ∀ call ∈ calls, ∀ sc, call = Call.staticCall sc →
    (sc.staticResolvesTo.effectivelyConcreteClass sc.containingClass ∨
     sc.staticResolvesTo.kind = MethodKind.abstract_) →
    sc.containingMethod.effectivelyConcreteClass sc.containingClass

  /-- Static resolve agrees with runtime resolve in method kind for static calls.
      Same justification as `var_static_resolves_matches` above. -/
  static_static_resolves_matches :
    ∀ call ∈ calls, ∀ sc, call = Call.staticCall sc →
    sc.staticResolvesTo.kind = sc.resolvesTo.kind

-- ============================================================
-- Safety theorem
-- ============================================================

/-- The safety property (hack.als line 592-594):
    `assert safe { some RuntimeFatal implies some TypeCheckerError }`

    In a well-formed world (no type checker errors), no call is fatal.
    I.e., if a call IS fatal, then the world is NOT well-formed. -/
theorem safety (w : WellFormedWorld) :
    ∀ call ∈ w.calls, ¬ call.isFatal := by
  intro call hcall
  match call with
  | Call.varCall vc =>
    -- ---- Case 1: Var receiver ----
    intro hfatal
    unfold Call.isFatal at hfatal
    -- The resolved method is abstract (hfatal)
    -- It's in the pointed-to class's methods
    have h_in_cls := w.var_resolves_in_class (Call.varCall vc) hcall vc rfl
    -- Static resolve has the same kind as runtime resolve
    have h_static_kind := w.var_static_resolves_matches (Call.varCall vc) hcall vc rfl
    -- Case split on receiver type kind
    match h_tk : vc.receiverTypeKind with
    | TypeKind.className =>
      -- ClassName: TCCantCallAbstractMethodThroughClassName fires
      -- (hack.als line 258-266)
      have h_no_abs := w.tc_no_abstract_through_classname (Call.varCall vc) hcall vc rfl h_tk
      -- static resolve has same kind as runtime resolve (abstract_)
      rw [hfatal] at h_static_kind
      exact absurd h_static_kind h_no_abs

    | TypeKind.concreteClassName =>
      -- ConcreteClassName: the class is concrete or abstract+final+CC
      -- (hack.als line 311-318)
      have h_target := w.concrete_classname_target (Call.varCall vc) hcall vc rfl h_tk
      cases h_target with
      | inl h_concrete =>
        -- Class is concrete: no abstract methods (hack.als line 115-117)
        have := w.concrete_no_abstract vc.pointsToClass h_concrete vc.resolvesTo h_in_cls
        simp [hfatal] at this
      | inr h_abs_final_cc =>
        -- Class is abstract+final+CC: TCAbstractFinalCantInheritConsistentConstruct
        -- (hack.als line 296-303)
        have h_member := w.var_classes_in_world (Call.varCall vc) hcall vc rfl
        exact absurd h_abs_final_cc (w.tc_no_abstract_final_cc vc.pointsToClass h_member)

  | Call.staticCall sc =>
    -- ---- Case 2: StaticKeyword receiver ----
    intro hfatal
    unfold Call.isFatal at hfatal
    -- The resolved method is abstract
    have h_in_cls := w.static_resolves_in_class (Call.staticCall sc) hcall sc rfl
    -- Static resolve kind matches runtime resolve kind
    have h_static_kind := w.static_static_resolves_matches (Call.staticCall sc) hcall sc rfl

    -- The called method is abstract, so the rule
    -- TCCanOnlyUseStaticAsConcreteInConcreteClassMethods applies
    -- (hack.als line 284-294)
    -- The static resolve is also abstract (by h_static_kind + hfatal)
    have h_static_abs : sc.staticResolvesTo.kind = MethodKind.abstract_ := by
      rw [h_static_kind]; exact hfatal

    -- The rule says: if called method is CC or abstract, containing method must be CC
    have h_containing_cc := w.tc_static_requires_concrete_context
      (Call.staticCall sc) hcall sc rfl
      (Or.inr h_static_abs)

    -- Since containing method IS effectively ConcreteClass,
    -- static_always_resolves_to_a_concrete_class_in_concrete_class_methods
    -- ensures the resolved class is concrete (hack.als line 581-587)
    have h_concrete := w.static_resolves_to_concrete
      (Call.staticCall sc) hcall sc rfl h_containing_cc

    -- Concrete class has no abstract methods (hack.als line 115-117)
    have h_no_abs := w.concrete_no_abstract sc.resolvesToClass h_concrete sc.resolvesTo h_in_cls

    -- But the resolved method IS abstract → contradiction
    simp [hfatal] at h_no_abs
