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


lemma moveUnit_self {E : Type*} [DecidableEq E] (x : E → ℤ) (i : E) :
    moveUnit x i i = x := by
  funext k
  simp [moveUnit]

lemma sum_moveUnit {E : Type*} [Fintype E] [DecidableEq E]
    (x : E → ℤ) (i j : E) : (∑ k, moveUnit x i j k) = ∑ k, x k := by
  simp [moveUnit, Finset.sum_add_distrib, Finset.sum_sub_distrib]

lemma integerPairing_moveUnit {E : Type*} [Fintype E] [DecidableEq E]
    (p x : E → ℤ) (i j : E) :
    integerPairing p (moveUnit x i j) = integerPairing p x - p i + p j := by
  simp [integerPairing, moveUnit, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, mul_ite]

lemma pairing_add_price {E : Type*} [Fintype E] (p q x : E → ℤ) :
    integerPairing (p + q) x = integerPairing p x + integerPairing q x := by
  simp [integerPairing, add_mul, Finset.sum_add_distrib]

lemma tilt_exchange {E : Type*} [Fintype E] [DecidableEq E]
    {D : Finset (E → ℤ)} {c : (E → ℤ) → ℤ} {r : ℤ}
    (h : IntegerExchangeAxioms D c r) (p : E → ℤ) :
    IntegerExchangeAxioms D (fun x => c x + integerPairing p x) r := by
  refine ⟨h.1, ?_⟩
  intro x hx y hy i hi
  obtain ⟨j, hj, hx', hy', hc⟩ := h.2 x hx y hy i hi
  refine ⟨j, hj, hx', hy', ?_⟩
  rw [integerPairing_moveUnit, integerPairing_moveUnit]
  omega

def gap {E : Type*} [Fintype E] (x y : E → ℤ) : ℕ :=
  ∑ i, (x i - y i).toNat

lemma exists_excess {E : Type*} [Fintype E] {x y : E → ℤ}
    (hs : (∑ i, x i) = ∑ i, y i) (hne : x ≠ y) : ∃ i, y i < x i := by
  by_contra hn
  push_neg at hn
  have hx : ∀ i, x i ≤ y i := fun i => hn i
  have heq : ∀ i, x i = y i := by
    intro i
    by_contra hi
    have hlt : x i < y i := lt_of_le_of_ne (hx i) hi
    have := Finset.sum_lt_sum (fun k (_ : k ∈ Finset.univ) => hx k)
      ⟨i, Finset.mem_univ i, hlt⟩
    omega
  exact hne (funext heq)

lemma gap_exchange_right {E : Type*} [Fintype E] [DecidableEq E]
    (x y : E → ℤ) (i j : E) (hi : y i < x i) (hj : x j < y j) :
    gap x (moveUnit y j i) + 1 = gap x y := by
  have hij : i ≠ j := by intro h; subst j; omega
  have hpoint : ∀ k, (x k - moveUnit y j i k).toNat + (if k = i then 1 else 0) =
      (x k - y k).toNat := by
    intro k
    by_cases hki : k = i
    · subst k
      simp [moveUnit, hij, Ne.symm hij]
      omega
    · by_cases hkj : k = j
      · subst k
        simp [moveUnit, hki]
        omega
      · simp [moveUnit, hki, hkj]
  have hsum := congrArg (fun f : E → ℕ => ∑ k, f k) (funext hpoint)
  simpa [gap, Finset.sum_add_distrib] using hsum

lemma local_global {E : Type*} [Fintype E] [DecidableEq E]
    {D : Finset (E → ℤ)} {c : (E → ℤ) → ℤ} {r : ℤ}
    (h : IntegerExchangeAxioms D c r) {x : E → ℤ} (hx : x ∈ D)
    (hl : ∀ i j, moveUnit x i j ∈ D → c x ≤ c (moveUnit x i j)) :
    ∀ y ∈ D, c x ≤ c y := by
  classical
  intro y hy
  suffices hmain : ∀ n : ℕ, ∀ y ∈ D, gap x y = n → c x ≤ c y by
    exact hmain _ y hy rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy hn
    by_cases hxy : x = y
    · subst y; rfl
    obtain ⟨i, hi⟩ := exists_excess ((h.1 x hx).trans (h.1 y hy).symm) hxy
    obtain ⟨j, hj, hx', hy', hc⟩ := h.2 x hx y hy i hi
    have hd := gap_exchange_right x y i j hi hj
    have hc' := ih (gap x (moveUnit y j i)) (by omega) (moveUnit y j i) hy' rfl
    have hxle := hl i j hx'
    omega

lemma minimizers_exchange {E : Type*} [Fintype E] [DecidableEq E]
    {D : Finset (E → ℤ)} {c : (E → ℤ) → ℤ} {r : ℤ}
    (h : IntegerExchangeAxioms D c r)
    {x y : E → ℤ} (hx : x ∈ D) (hy : y ∈ D)
    (hxm : ∀ z ∈ D, c x ≤ c z) (hym : ∀ z ∈ D, c y ≤ c z)
    {i : E} (hi : y i < x i) :
    ∃ j, x j < y j ∧ moveUnit x i j ∈ D ∧ moveUnit y j i ∈ D ∧
      c (moveUnit x i j) = c x ∧ c (moveUnit y j i) = c y := by
  obtain ⟨j, hj, hx', hy', hc⟩ := h.2 x hx y hy i hi
  have hcx := hxm _ hx'
  have hcy := hym _ hy'
  refine ⟨j, hj, hx', hy', ?_, ?_⟩ <;> omega

def ExchangeSet {E : Type*} [DecidableEq E] (B : Set (E → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ i, y i < x i →
    ∃ j, x j < y j ∧ moveUnit x i j ∈ B ∧ moveUnit y j i ∈ B

lemma minimizer_set_exchange {E : Type*} [Fintype E] [DecidableEq E]
    {D : Finset (E → ℤ)} {c : (E → ℤ) → ℤ} {r : ℤ}
    (h : IntegerExchangeAxioms D c r) :
    ExchangeSet {x | x ∈ D ∧ ∀ y ∈ D, c x ≤ c y} := by
  intro x hx y hy i hi
  obtain ⟨j, hj, hx', hy', hcx, hcy⟩ :=
    minimizers_exchange h hx.1 hy.1 hx.2 hy.2 hi
  refine ⟨j, hj, ⟨hx', ?_⟩, ⟨hy', ?_⟩⟩
  · intro z hz; rw [hcx]; exact hx.2 z hz
  · intro z hz; rw [hcy]; exact hy.2 z hz

def multiMove {E : Type*} [DecidableEq E]
    (x : E → ℤ) (u v : ℕ → E) (n : ℕ) : E → ℤ :=
  fun k => x k + ∑ t ∈ Finset.range n,
    ((if k = v t then 1 else 0) - (if k = u t then 1 else 0))

lemma multiMove_away {E : Type*} [DecidableEq E]
    (x : E → ℤ) (u v : ℕ → E) (n : ℕ) (k : E)
    (hu : ∀ t < n, k ≠ u t) (hv : ∀ t < n, k ≠ v t) :
    multiMove x u v n k = x k := by
  have : (∑ t ∈ Finset.range n,
      ((if k = v t then 1 else 0 : ℤ) - (if k = u t then 1 else 0))) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    simp [hu t (Finset.mem_range.mp ht), hv t (Finset.mem_range.mp ht)]
  simp [multiMove, this]

lemma multiMove_nondecrease {E : Type*} [DecidableEq E]
    (x : E → ℤ) (u v : ℕ → E) (n : ℕ) (k : E)
    (hu : ∀ t < n, k ≠ u t) : x k ≤ multiMove x u v n k := by
  have : 0 ≤ ∑ t ∈ Finset.range n,
      ((if k = v t then 1 else 0 : ℤ) - (if k = u t then 1 else 0)) := by
    apply Finset.sum_nonneg
    intro t ht
    simp only [if_neg (hu t (Finset.mem_range.mp ht)), sub_zero]
    split_ifs <;> omega
  unfold multiMove
  omega

lemma multiMove_succ {E : Type*} [DecidableEq E]
    (x : E → ℤ) (u v : ℕ → E) (n : ℕ) :
    multiMove x u v (n+1) = moveUnit (multiMove x u v n) (u n) (v n) := by
  funext k
  simp only [multiMove, moveUnit, Finset.sum_range_succ]
  omega

lemma moveUnit_cancel_middle {E : Type*} [DecidableEq E]
    (x : E → ℤ) (u v j : E) :
    moveUnit (moveUnit x u v) j u = moveUnit x j v := by
  funext k
  simp only [moveUnit]
  omega

lemma no_shortcut_multiMove {E : Type*} [DecidableEq E]
    {B : Set (E → ℤ)} (hB : ExchangeSet B)
    (x : E → ℤ) (hx : x ∈ B) (u v : ℕ → E) (n : ℕ)
    (huu : ∀ a < n, ∀ b < n, u a = u b → a = b)
    (hvv : ∀ a < n, ∀ b < n, v a = v b → a = b)
    (huv : ∀ a < n, ∀ b < n, u a ≠ v b)
    (hedge : ∀ a < n, moveUnit x (u a) (v a) ∈ B)
    (hforbid : ∀ a < n, ∀ b < n, a < b → moveUnit x (u a) (v b) ∉ B) :
    multiMove x u v n ∈ B := by
  induction n with
  | zero => simpa [multiMove] using hx
  | succ n ih =>
    have hy : multiMove x u v n ∈ B := ih
      (fun a ha b hb => huu a (by omega) b (by omega))
      (fun a ha b hb => hvv a (by omega) b (by omega))
      (fun a ha b hb => huv a (by omega) b (by omega))
      (fun a ha => hedge a (by omega))
      (fun a ha b hb => hforbid a (by omega) b (by omega))
    have hun : ∀ t < n, u n ≠ u t := by
      intro t ht he
      have := huu n (by omega) t (by omega) he
      omega
    have hvn : ∀ t < n, u n ≠ v t := fun t ht => huv n (by omega) t (by omega)
    have haway := multiMove_away x u v n (u n) hun hvn
    have hne : u n ≠ v n := huv n (by omega) n (by omega)
    have hless : moveUnit x (u n) (v n) (u n) < multiMove x u v n (u n) := by
      simp [moveUnit, hne, haway]
    obtain ⟨j, hj, hyj, hzj⟩ := hB _ hy _ (hedge n (by omega)) (u n) hless
    have hjv : j = v n := by
      by_contra hneq
      have hsource : ∃ t < n, j = u t := by
        by_contra hno
        push_neg at hno
        have hge := multiMove_nondecrease x u v n j hno
        have hval : moveUnit x (u n) (v n) j ≤ x j := by
          simp only [moveUnit, if_neg hneq, add_zero]
          split_ifs <;> omega
        omega
      obtain ⟨t, ht, rfl⟩ := hsource
      have hbad : moveUnit x (u t) (v n) ∈ B := by
        simpa only [moveUnit_cancel_middle] using hzj
      exact hforbid t (by omega) n (by omega) ht hbad
    rw [multiMove_succ]
    simpa only [hjv] using hyj

end TuringTask
