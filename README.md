# Verified independent integer exchange price certificate

The exact requested theorem is in `TuringTask/Basic.lean`. Its three original definitions and theorem signature are unchanged. `Verify.lean` also checks the requested type directly by assigning the proved theorem to that exact type.

The independently authored proof maximizes an integer dual value, chooses a closest pair of minimizers at a maximizing integer price, and rules out distinct minimizers using a shortest zero-cost exchange route. All exchange, no-shortcut, cut, route, and augmentation arguments are proved in this project.

## Pinned environment

- Lean: `leanprover/lean4:v4.33.0-rc1`
- Mathlib: `9944fe2973b8dc0b86949101ed98232c07cd54a0`

## Reproduce

```bash
lean --version
lake update
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = "9944fe2973b8dc0b86949101ed98232c07cd54a0"
lake exe cache get
lake build
lake env lean TuringTask/Basic.lean
lake env lean Verify.lean
```

Dependency setup requires network access unless the pinned packages and cache are already supplied. The proof checks then use the local pinned environment.

`verification.log` contains actual final CI output. `Golden_Explanation.md` follows every definition and helper in source order.

The permitted foundational dependencies are `propext`, `Classical.choice`, and `Quot.sound`. There are no proof escape declarations. Empty and singleton finite index types are included without added assumptions.
