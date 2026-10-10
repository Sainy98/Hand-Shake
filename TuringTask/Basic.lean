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

section BasicIdentities

variable {E : Type*} [Fintype E] [DecidableEq E]

@[simp] lemma moveUnit_apply (x : E → ℤ) (i j k : E) :
    moveUnit x i j k =
      x k - (if k = i then 1 else 0) +
        (if k = j then 1 else 0) := rfl

lemma moveUnit_self (x : E → ℤ) (i : E) :
    moveUnit x i i = x := by
  funext k
  simp [moveUnit]

lemma sum_moveUnit (x : E → ℤ) (i j : E) :
    (∑ k, moveUnit x i j k) = ∑ k, x k := by
  classical
  simp [moveUnit, Finset.sum_sub_distrib, Finset.sum_add_distrib]

lemma integerPairing_moveUnit (p x : E → ℤ) (i j : E) :
    integerPairing p (moveUnit x i j) =
      integerPairing p x - p i + p j := by
  classical
  simp [integerPairing, moveUnit, mul_sub, mul_add,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

lemma moveUnit_commute (x : E → ℤ) (i j k l : E) :
    moveUnit (moveUnit x i j) k l =
      moveUnit (moveUnit x k l) i j := by
  funext a
  simp [moveUnit]
  ring


def positiveGap (x y : E → ℤ) : ℤ :=
  ∑ k, max (x k - y k) 0

lemma sum_two_change (f g : E → ℤ) (i j : E) (hij : i ≠ j)
    (hrest : ∀ k, k ≠ i → k ≠ j → f k = g k) :
    (∑ k, f k) =
      (∑ k, g k) + (f i - g i) + (f j - g j) := by
  classical
  calc
    (∑ k, f k) =
        ∑ k, (g k +
          (if k = i then f i - g i else 0) +
          (if k = j then f j - g j else 0)) := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hki : k = i
      · subst k
        simp [hij]
      · by_cases hkj : k = j
        · subst k
          simp [hki, hij]
        · simp [hki, hkj, hrest k hki hkj]
    _ = (∑ k, g k) + (f i - g i) + (f j - g j) := by
      simp [Finset.sum_add_distrib]
      ring

lemma positiveGap_nonneg (x y : E → ℤ) :
    0 ≤ positiveGap x y := by
  unfold positiveGap
  exact Finset.sum_nonneg fun _ _ => le_max_right _ _

lemma positiveGap_moveToward (x y : E → ℤ) (i j : E)
    (hi : y i < x i) (hj : x j < y j) :
    positiveGap x (moveUnit y j i) = positiveGap x y - 1 := by
  have hij : i ≠ j := by
    intro h
    subst j
    omega
  let f : E → ℤ := fun k => max (x k - moveUnit y j i k) 0
  let g : E → ℤ := fun k => max (x k - y k) 0
  have hrest : ∀ k, k ≠ i → k ≠ j → f k = g k := by
    intro k hki hkj
    simp [f, g, moveUnit, hki, hkj]
  have hsum := sum_two_change f g i j hij hrest
  have hfi : f i = x i - y i - 1 := by
    have hnonneg : 0 ≤ x i - y i - 1 := by omega
    simp [f, moveUnit, hij, max_eq_left hnonneg]
  have hgi : g i = x i - y i := by
    have hnonneg : 0 ≤ x i - y i := by omega
    simp [g, max_eq_left hnonneg]
  have hfj : f j = 0 := by
    have hnonpos : x j - (y j - 1) ≤ 0 := by omega
    simp [f, moveUnit, hij, max_eq_right hnonpos]
  have hgj : g j = 0 := by
    have hnonpos : x j - y j ≤ 0 := by omega
    simp [g, max_eq_right hnonpos]
  change (∑ k, f k) = (∑ k, g k) - 1
  rw [hsum, hfi, hgi, hfj, hgj]
  ring

end BasicIdentities

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
