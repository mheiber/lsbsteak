# Why Abstract Final Classes Cannot Have `__ConsistentConstruct`

## The Rule

An `abstract final` class that has the `<<__ConsistentConstruct>>` attribute is a type error.

In the Lean proof this is the field `tc_no_abstract_final_cc` of `WellFormedWorld` (`lean/HackSafety/Safety.lean:173-175`):

```lean
tc_no_abstract_final_cc :
    ∀ c ∈ classes,
    ¬(c.kind = ClassKind.abstract_ ∧ c.isClassFinal ∧ c.hasConsistentConstruct)
```

In the Alloy model this is `TCAbstractFinalCantInheritConsistentConstruct` (`hack.als:296-303`).

## Background

In Hack, `<<__ConsistentConstruct>>` is a class attribute that guarantees all subclass constructors have compatible signatures. This enables patterns like `new static()` — constructing an instance of whatever the runtime class turns out to be.

The attribute propagates through inheritance: if a parent has it, all children have it too (`hack.als:93-96`).

In the type system model, classes are referenced through two kinds of type:

- `classname<C>` — names a class that might be abstract. You cannot call abstract methods or constructors through it.
- `concrete_classname<C>` — names a class that is definitely concrete (instantiable). You can call constructors through it.

A concrete class gets a `concrete_classname` type. An abstract class gets a `classname` type. The question is: can an `abstract final` class with `<<__ConsistentConstruct>>` get a `concrete_classname` type?

## Why It Would Seem Safe (But Isn't)

An `abstract final` class with `<<__ConsistentConstruct>>` looks like it could be treated as concrete:

- It's `final`, so no subclass can break constructor compatibility.
- It has `<<__ConsistentConstruct>>`, so its constructor signature is stable.

But it's still `abstract` — it has no concrete constructor. If the type system allows a `concrete_classname` for it, code can attempt to instantiate it, hitting a runtime fatal.

## The Counterexample

If the rule is removed, this Hack program compiles with no type errors but crashes at runtime:

```hack
<?hh

<<__ConsistentConstruct>>
abstract class C1 {
  abstract static function abs(): void;

  <<__ConcreteClass>>
  public static function nc(): void { new static(); }
}

// C2 inherits __ConsistentConstruct from C1
abstract final class C2 extends C1 {
  public static function abs(): void {}
  // C2 has NO concrete constructor — it's abstract
}

<<__EntryPoint>>
function main(): void {
  $cls = C2::class;           // $cls: concrete_classname<C2>
  new $cls();                  // RUNTIME FATAL: calls abstract constructor
}
```

Step by step:

1. `C1` is `<<__ConsistentConstruct>>`, so `C2` inherits it.
2. `C2` is `abstract final` with `<<__ConsistentConstruct>>`. Without the rule, the type system gives `C2::class` the type `concrete_classname<C2>`.
3. `new $cls()` resolves to `C2::__construct`. But `C2` is abstract — its constructor is abstract.
4. Calling an abstract method at runtime is a fatal error.

No other type checker rule catches this:

- `tc_no_abstract_through_classname` only fires for `classname`, not `concrete_classname`.
- `concrete_no_abstract` only applies to concrete classes. `C2` is abstract.
- `tc_static_requires_concrete_context` is about `static::` calls, not `$cls::` calls.

## The Lean Counterexample

The counterexample is formalized in `lean/HackSafety/HackNotation.lean:155-185` (`Counterexample.AbstractFinalConsistentConstruct`):

```lean
private def C2 :=
  «<<__ConsistentConstruct>> abstract final class» "C2" [
    «public static function» "abs",
    «(no concrete __construct)»
  ]

private def the_call :=
  «concrete_classname<_>::call» C2 «(no concrete __construct)» «(no concrete __construct)»

theorem fatal : the_call.isFatal := rfl
```

`the_call.isFatal` reduces to `true` by computation (`rfl`): the call resolves to a method with `kind = MethodKind.abstract_`.

The theorem `caught_by_rule` (`HackNotation.lean:180-183`) confirms the rule detects `C2`:

```lean
theorem caught_by_rule :
    C2.kind = ClassKind.abstract_ ∧
    C2.isClassFinal ∧
    C2.hasConsistentConstruct := ⟨rfl, rfl, rfl⟩
```

## How the Rule Participates in the Safety Proof

The safety theorem (`lean/HackSafety/Safety.lean:226-295`) proves: in a `WellFormedWorld` (no type checker errors), no call is fatal.

For var calls through `concrete_classname`, the proof case-splits on what class the variable points to (`Safety.lean:252-262`):

1. **Concrete class** — concrete classes have no abstract methods (`concrete_no_abstract`), so the resolved method can't be abstract. Contradiction.

2. **Abstract + final + `__ConsistentConstruct`** — this is where `tc_no_abstract_final_cc` is used (`Safety.lean:258-262`). The `concrete_classname_target` axiom says the pointed-to class is either concrete or abstract+final+CC. If it's the latter, `tc_no_abstract_final_cc` says this class cannot exist in a well-formed world. Contradiction.

```lean
| inr h_abs_final_cc =>
    have h_member := w.var_classes_in_world (Call.varCall vc) hcall vc rfl
    exact absurd h_abs_final_cc (w.tc_no_abstract_final_cc vc.pointsToClass h_member)
```

Without this rule, the `inr` branch has no contradiction — the proof cannot go through, and the counterexample above shows this is a genuine gap, not a proof limitation.

## Expressing "Turn Off a Rule" in the Lean Proof

Each type checker rule is a separate field of the `WellFormedWorld` structure (`Safety.lean:104-215`). To show that removing a specific rule is unsound:

1. Construct a call and prove it is fatal (as above: `theorem fatal : the_call.isFatal := rfl`).
2. Show the specific rule catches it (`theorem caught_by_rule`).

This is the pattern used for all counterexamples in `HackNotation.lean`. The structure of `WellFormedWorld` — with each rule as an independent field — makes it architecturally clear which rule is "turned off": the counterexample satisfies all other rules but violates exactly one.
