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

@[simp] lemma moveUnit_same
    {E : Type*} [DecidableEq E] (x : E → ℤ) (i : E) :
    moveUnit x i i = x := by
  funext k
  simp [moveUnit]

lemma moveUnit_apply_src
    {E : Type*} [DecidableEq E] {x : E → ℤ} {i j : E}
    (hij : i ≠ j) :
    moveUnit x i j i = x i - 1 := by
  simp [moveUnit, hij]

lemma moveUnit_apply_dst
    {E : Type*} [DecidableEq E] {x : E → ℤ} {i j : E}
    (hij : i ≠ j) :
    moveUnit x i j j = x j + 1 := by
  simp [moveUnit, hij, Ne.symm hij]

lemma moveUnit_apply_of_ne
    {E : Type*} [DecidableEq E] {x : E → ℤ} {i j k : E}
    (hki : k ≠ i) (hkj : k ≠ j) :
    moveUnit x i j k = x k := by
  simp [moveUnit, hki, hkj]

lemma sum_moveUnit
    {E : Type*} [Fintype E] [DecidableEq E]
    (x : E → ℤ) (i j : E) :
    (∑ k, moveUnit x i j k) = ∑ k, x k := by
  classical
  simp [moveUnit, Finset.sum_sub_distrib, Finset.sum_add_distrib]

lemma integerPairing_moveUnit
    {E : Type*} [Fintype E] [DecidableEq E]
    (p x : E → ℤ) (i j : E) :
    integerPairing p (moveUnit x i j) =
      integerPairing p x - p i + p j := by
  classical
  simp [integerPairing, moveUnit, mul_sub, mul_add,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]

lemma IntegerExchangeAxioms.sub_pairing
    {E : Type*} [Fintype E] [DecidableEq E]
    {D : Finset (E → ℤ)} {c : (E → ℤ) → ℤ} {r : ℤ}
    (h : IntegerExchangeAxioms D c r) (p : E → ℤ) :
    IntegerExchangeAxioms D
      (fun x => c x - integerPairing p x) r := by
  refine ⟨h.1, ?_⟩
  intro x hx y hy i hi
  obtain ⟨j, hj, hxj, hyj, hcost⟩ := h.2 x hx y hy i hi
  refine ⟨j, hj, hxj, hyj, ?_⟩
  change
    (c (moveUnit x i j) - integerPairing p (moveUnit x i j)) +
        (c (moveUnit y j i) - integerPairing p (moveUnit y j i)) ≤
      (c x - integerPairing p x) + (c y - integerPairing p y)
  rw [integerPairing_moveUnit, integerPairing_moveUnit]
  omega

lemma IntegerExchangeAxioms.add_pairing
    {E : Type*} [Fintype E] [DecidableEq E]
    {D : Finset (E → ℤ)} {c : (E → ℤ) → ℤ} {r : ℤ}
    (h : IntegerExchangeAxioms D c r) (p : E → ℤ) :
    IntegerExchangeAxioms D
      (fun x => c x + integerPairing p x) r := by
  refine ⟨h.1, ?_⟩
  intro x hx y hy i hi
  obtain ⟨j, hj, hxj, hyj, hcost⟩ := h.2 x hx y hy i hi
  refine ⟨j, hj, hxj, hyj, ?_⟩
  change
    (c (moveUnit x i j) + integerPairing p (moveUnit x i j)) +
        (c (moveUnit y j i) + integerPairing p (moveUnit y j i)) ≤
      (c x + integerPairing p x) + (c y + integerPairing p y)
  rw [integerPairing_moveUnit, integerPairing_moveUnit]
  omega

def IsMinOn
    {α : Type*} (D : Finset α) (f : α → ℤ) (x : α) : Prop :=
  x ∈ D ∧ ∀ y ∈ D, f x ≤ f y

lemma exists_minOn
    {α : Type*} [DecidableEq α]
    (D : Finset α) (f : α → ℤ) (hne : D.Nonempty) :
    ∃ x, IsMinOn D f x := by
  classical
  obtain ⟨x, hx, hmin⟩ :=
    Set.exists_min_image (D : Set α) f D.finite_toSet
      ⟨hne.choose, hne.choose_spec⟩
  exact ⟨x, hx, hmin⟩


def posDist
    {E : Type*} [Fintype E] (x y : E → ℤ) : ℕ :=
  ∑ i, Int.toNat (x i - y i)

lemma exists_source_of_sum_eq_of_ne
    {E : Type*} [Fintype E]
    {x y : E → ℤ}
    (hsum : (∑ i, x i) = ∑ i, y i)
    (hne : x ≠ y) :
    ∃ i, y i < x i := by
  classical
  by_contra h
  push_neg at h
  have hle : ∀ i, x i ≤ y i := h
  have hstrict : ∃ i, x i < y i := by
    by_contra h'
    push_neg at h'
    apply hne
    funext i
    exact le_antisymm (hle i) (h' i)
  obtain ⟨i, hi⟩ := hstrict
  have hlt : (∑ k, x k) < ∑ k, y k := by
    refine Finset.sum_lt_sum (fun k _ => hle k) ?_
    exact ⟨i, Finset.mem_univ i, hi⟩
  rw [hsum] at hlt
  exact (lt_irrefl _ hlt)

lemma posDist_move_toward
    {E : Type*} [Fintype E] [DecidableEq E]
    {x y : E → ℤ} {i j : E}
    (hi : y i < x i) (hj : x j < y j) :
    posDist x (moveUnit y j i) + 1 = posDist x y := by
  classical
  have hij : i ≠ j := by
    intro h
    subst j
    omega
  unfold posDist
  have hrest :
      (Finset.univ.erase i).sum
        (fun k => Int.toNat (x k - moveUnit y j i k)) =
      (Finset.univ.erase i).sum
        (fun k => Int.toNat (x k - y k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    by_cases hkj : k = j
    · subst k
      rw [moveUnit_apply_src (x := y) (i := j) (j := i) (Ne.symm hij)]
      omega
    · rw [moveUnit_apply_of_ne (x := y) (i := j) (j := i) hkj hki]
  rw [← Finset.sum_erase_add Finset.univ
      (fun k => Int.toNat (x k - moveUnit y j i k)) (Finset.mem_univ i),
    ← Finset.sum_erase_add Finset.univ
      (fun k => Int.toNat (x k - y k)) (Finset.mem_univ i),
    hrest,
    moveUnit_apply_dst (x := y) (i := j) (j := i) (Ne.symm hij)]
  omega

lemma local_optimal_implies_global
    {E : Type*} [Fintype E] [DecidableEq E]
    {D : Finset (E → ℤ)} {c : (E → ℤ) → ℤ} {r : ℤ}
    (h : IntegerExchangeAxioms D c r)
    {x : E → ℤ} (hx : x ∈ D)
    (hloc : ∀ i j : E, moveUnit x i j ∈ D →
      c x ≤ c (moveUnit x i j))
    (y : E → ℤ) (hy : y ∈ D) :
    c x ≤ c y := by
  by_cases hxy : x = y
  · simpa [hxy]
  have hsum : (∑ i, x i) = ∑ i, y i := by
    rw [h.1 x hx, h.1 y hy]
  obtain ⟨i, hi⟩ := exists_source_of_sum_eq_of_ne hsum hxy
  obtain ⟨j, hj, hxj, hyj, hcost⟩ := h.2 x hx y hy i hi
  have hxle := hloc i j hxj
  have hynew : c (moveUnit y j i) ≤ c y := by
    omega
  have hdist :
      posDist x (moveUnit y j i) < posDist x y := by
    have hd := posDist_move_toward (x := x) (y := y) hi hj
    omega
  have hrec :=
    local_optimal_implies_global h hx hloc (moveUnit y j i) hyj
  exact hrec.trans hynew
termination_by posDist x y
decreasing_by exact hdist

lemma isMinOn_iff_local
    {E : Type*} [Fintype E] [DecidableEq E]
    {D : Finset (E → ℤ)} {c : (E → ℤ) → ℤ} {r : ℤ}
    (h : IntegerExchangeAxioms D c r)
    {x : E → ℤ} (hx : x ∈ D) :
    IsMinOn D c x ↔
      ∀ i j : E, moveUnit x i j ∈ D →
        c x ≤ c (moveUnit x i j) := by
  constructor
  · intro hmin i j hij
    exact hmin.2 _ hij
  · intro hloc
    exact ⟨hx, fun y hy => local_optimal_implies_global h hx hloc y hy⟩

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
