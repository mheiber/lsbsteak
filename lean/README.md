# HackSafety

Lean 4 proof of safety for the Hack type system model in `../hack.als`.

## Files

- **Safety.lean**: Proof that `RuntimeFatal → TypeCheckerError` (no well-typed program crashes)
- **Counterexamples.lean**: Concrete programs showing each type checker rule is necessary
- **HackNotation.lean**: Hack-like DSL for writing readable counterexamples

## Build

```
lake build
```
