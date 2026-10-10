import Mathlib

open scoped BigOperators

namespace TuringTask

def moveUnit
    {E : Type*} [DecidableEq E]
    (x : E → ℤ) (i j : E) : E → ℤ :=
  fun k =>
    x k - (if k = i then 1 else 0) +
      (if k = j then 1 else 0)

def integerPairing
    {E : Type*} [Fintype E]
    (p x : E → ℤ) : ℤ :=
  ∑ i, p i * x i

def IntegerExchangeAxioms
    {E : Type*} [Fintype E] [DecidableEq E]
    (D : Finset (E → ℤ))
    (c : (E → ℤ) → ℤ)
    (r : ℤ) : Prop :=
  (∀ x ∈ D, (∑ i, x i) = r) ∧
  (∀ x ∈ D, ∀ y ∈ D, ∀ i : E,
    y i < x i →
      ∃ j : E,
        x j < y j ∧
        moveUnit x i j ∈ D ∧
        moveUnit y j i ∈ D ∧
        c (moveUnit x i j) + c (moveUnit y j i) ≤
          c x + c y)

theorem integer_exchange_price_certificate
    {E : Type*} [Fintype E] [DecidableEq E]
    (D₁ D₂ : Finset (E → ℤ))
    (c₁ c₂ : (E → ℤ) → ℤ)
    (r : ℤ)
    (h₁ : IntegerExchangeAxioms D₁ c₁ r)
    (h₂ : IntegerExchangeAxioms D₂ c₂ r)
    (hcommon : ∃ x : E → ℤ, x ∈ D₁ ∧ x ∈ D₂) :
    ∃ x p : E → ℤ,
      x ∈ D₁ ∧
      x ∈ D₂ ∧
      (∀ y ∈ D₁,
        c₁ x - integerPairing p x ≤
          c₁ y - integerPairing p y) ∧
      (∀ y ∈ D₂,
        c₂ x + integerPairing p x ≤
          c₂ y + integerPairing p y) := by
  sorry

end TuringTask
