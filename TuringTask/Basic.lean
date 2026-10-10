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
    have hmove : moveUnit y j i i = y i + 1 := by
      simp [moveUnit, hij]
    dsimp [f]
    rw [hmove, max_eq_left]
    · ring
    · omega
  have hgi : g i = x i - y i := by
    dsimp [g]
    rw [max_eq_left]
    · rfl
    · omega
  have hfj : f j = 0 := by
    have hmove : moveUnit y j i j = y j - 1 := by
      simp [moveUnit, hij, hij.symm]
    dsimp [f]
    rw [hmove, max_eq_right]
    omega
  have hgj : g j = 0 := by
    dsimp [g]
    rw [max_eq_right]
    omega
  change (∑ k, f k) = (∑ k, g k) - 1
  rw [hsum, hfi, hgi, hfj, hgj]
  ring


lemma exists_lt_coord_of_same_sum_ne
    (x y : E → ℤ)
    (hsum : (∑ i, x i) = ∑ i, y i)
    (hne : x ≠ y) :
    ∃ i, y i < x i := by
  by_contra h
  push_neg at h
  have hdiff : (∑ i, (x i - y i)) = 0 := by
    rw [Finset.sum_sub_distrib, hsum]
    ring
  have hnonneg : ∀ i ∈ (Finset.univ : Finset E), 0 ≤ y i - x i := by
    intro i hi
    exact sub_nonneg.mpr (h i)
  have hdiff' : (∑ i, (y i - x i)) = 0 := by
    rw [Finset.sum_sub_distrib, ← hsum]
    ring
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hdiff'
  apply hne
  funext i
  have hi : y i - x i = 0 := hzero i (Finset.mem_univ i)
  omega

lemma local_optimal_implies_global
    (D : Finset (E → ℤ)) (c : (E → ℤ) → ℤ) (r : ℤ)
    (h : IntegerExchangeAxioms D c r)
    (x : E → ℤ) (hx : x ∈ D)
    (hlocal : ∀ i j : E, moveUnit x i j ∈ D → c x ≤ c (moveUnit x i j)) :
    ∀ y ∈ D, c x ≤ c y := by
  intro y hy
  by_contra hxy
  have hylt : c y < c x := lt_of_not_ge hxy
  let B : Set (E → ℤ) := {z | z ∈ D ∧ c z < c x}
  have hBfinite : B.Finite := by
    refine D.finite_toSet.subset ?_
    intro z hz
    exact hz.1
  have hBnonempty : B.Nonempty := ⟨y, hy, hylt⟩
  obtain ⟨z, hzB, hzmin⟩ :=
    Set.exists_min_image B (positiveGap x) hBfinite hBnonempty
  have hzD : z ∈ D := hzB.1
  have hzlt : c z < c x := hzB.2
  have hne : x ≠ z := by
    intro hxz
    subst z
    exact (lt_irrefl _ hzlt)
  have hsumxz : (∑ i, x i) = ∑ i, z i := by
    rw [h.1 x hx, h.1 z hzD]
  obtain ⟨i, hi⟩ := exists_lt_coord_of_same_sum_ne x z hsumxz hne
  obtain ⟨j, hj, hxmove, hzmove, hcost⟩ :=
    h.2 x hx z hzD i hi
  have hxlocal : c x ≤ c (moveUnit x i j) :=
    hlocal i j hxmove
  have hzmove_le : c (moveUnit z j i) ≤ c z := by
    omega
  have hzmoveB : moveUnit z j i ∈ B := by
    exact ⟨hzmove, lt_of_le_of_lt hzmove_le hzlt⟩
  have hgap :=
    positiveGap_moveToward x z i j hi hj
  have hmin := hzmin (moveUnit z j i) hzmoveB
  omega


def minusTilt (c : (E → ℤ) → ℤ) (p : E → ℤ) (x : E → ℤ) : ℤ :=
  c x - integerPairing p x

def plusTilt (c : (E → ℤ) → ℤ) (p : E → ℤ) (x : E → ℤ) : ℤ :=
  c x + integerPairing p x

lemma IntegerExchangeAxioms.minusTilt
    (D : Finset (E → ℤ)) (c : (E → ℤ) → ℤ) (r : ℤ)
    (h : IntegerExchangeAxioms D c r) (p : E → ℤ) :
    IntegerExchangeAxioms D (minusTilt c p) r := by
  refine ⟨h.1, ?_⟩
  intro x hx y hy i hi
  obtain ⟨j, hj, hxmove, hymove, hcost⟩ := h.2 x hx y hy i hi
  refine ⟨j, hj, hxmove, hymove, ?_⟩
  rw [minusTilt, minusTilt, minusTilt, minusTilt,
    integerPairing_moveUnit, integerPairing_moveUnit]
  omega

lemma IntegerExchangeAxioms.plusTilt
    (D : Finset (E → ℤ)) (c : (E → ℤ) → ℤ) (r : ℤ)
    (h : IntegerExchangeAxioms D c r) (p : E → ℤ) :
    IntegerExchangeAxioms D (plusTilt c p) r := by
  refine ⟨h.1, ?_⟩
  intro x hx y hy i hi
  obtain ⟨j, hj, hxmove, hymove, hcost⟩ := h.2 x hx y hy i hi
  refine ⟨j, hj, hxmove, hymove, ?_⟩
  rw [plusTilt, plusTilt, plusTilt, plusTilt,
    integerPairing_moveUnit, integerPairing_moveUnit]
  omega

def IsGlobalMin
    (D : Finset (E → ℤ)) (c : (E → ℤ) → ℤ) (x : E → ℤ) : Prop :=
  x ∈ D ∧ ∀ y ∈ D, c x ≤ c y

lemma exists_globalMin
    (D : Finset (E → ℤ)) (c : (E → ℤ) → ℤ)
    (hne : D.Nonempty) :
    ∃ x, IsGlobalMin D c x := by
  classical
  obtain ⟨x, hx, hxmin⟩ := D.exists_min_image c hne
  exact ⟨x, hx, hxmin⟩

lemma IsGlobalMin.local
    (D : Finset (E → ℤ)) (c : (E → ℤ) → ℤ)
    {x : E → ℤ} (hx : IsGlobalMin D c x) :
    ∀ i j : E, moveUnit x i j ∈ D → c x ≤ c (moveUnit x i j) := by
  intro i j hmove
  exact hx.2 _ hmove

lemma exchange_of_globalMins
    (D : Finset (E → ℤ)) (c : (E → ℤ) → ℤ) (r : ℤ)
    (h : IntegerExchangeAxioms D c r)
    {x y : E → ℤ}
    (hx : IsGlobalMin D c x) (hy : IsGlobalMin D c y)
    (i : E) (hi : y i < x i) :
    ∃ j : E,
      x j < y j ∧
      IsGlobalMin D c (moveUnit x i j) ∧
      IsGlobalMin D c (moveUnit y j i) := by
  obtain ⟨j, hj, hxmove, hymove, hcost⟩ :=
    h.2 x hx.1 y hy.1 i hi
  have hxy : c x = c y :=
    le_antisymm (hx.2 y hy.1) (hy.2 x hx.1)
  have hxlo : c x ≤ c (moveUnit x i j) := hx.2 _ hxmove
  have hylo : c y ≤ c (moveUnit y j i) := hy.2 _ hymove
  have hxeq : c (moveUnit x i j) = c x := by
    omega
  have hyeq : c (moveUnit y j i) = c y := by
    omega
  refine ⟨j, hj, ⟨hxmove, ?_⟩, ⟨hymove, ?_⟩⟩
  · intro z hz
    rw [hxeq]
    exact hx.2 z hz
  · intro z hz
    rw [hyeq]
    exact hy.2 z hz


def ExchangeClosed (B : Set (E → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ i : E,
    y i < x i →
      ∃ j : E,
        x j < y j ∧
        moveUnit x i j ∈ B ∧
        moveUnit y j i ∈ B

def minimizerSet
    (D : Finset (E → ℤ)) (c : (E → ℤ) → ℤ) : Set (E → ℤ) :=
  {x | IsGlobalMin D c x}

lemma minimizerSet_exchangeClosed
    (D : Finset (E → ℤ)) (c : (E → ℤ) → ℤ) (r : ℤ)
    (h : IntegerExchangeAxioms D c r) :
    ExchangeClosed (minimizerSet D c) := by
  intro x hx y hy i hi
  exact exchange_of_globalMins D c r h hx hy i hi

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
