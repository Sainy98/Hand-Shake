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
    dsimp [f]
    simp [moveUnit, hij]
    rw [max_eq_left] <;> omega
  have hgi : g i = x i - y i := by
    dsimp [g]
    rw [max_eq_left] <;> omega
  have hfj : f j = 0 := by
    dsimp [f]
    have hnonpos : x j - (y j - 1) ≤ 0 := by omega
    simpa [moveUnit, hij.symm, max_eq_right hnonpos]
  have hgj : g j = 0 := by
    dsimp [g]
    rw [max_eq_right] <;> omega
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
  rw [TuringTask.minusTilt, TuringTask.minusTilt, TuringTask.minusTilt, TuringTask.minusTilt,
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
  rw [TuringTask.plusTilt, TuringTask.plusTilt, TuringTask.plusTilt, TuringTask.plusTilt,
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


def multiMove {n : ℕ} (x : E → ℤ)
    (u v : Fin n → E) : E → ℤ :=
  fun k =>
    x k -
      (∑ a, if k = u a then (1 : ℤ) else 0) +
      (∑ a, if k = v a then (1 : ℤ) else 0)

def endpointMap {n : ℕ} (u v : Fin n → E) :
    Fin n ⊕ Fin n → E :=
  Sum.elim u v

def EndpointsInjective {n : ℕ} (u v : Fin n → E) : Prop :=
  Function.Injective (endpointMap u v)

lemma multiMove_zero (x : E → ℤ)
    (u v : Fin 0 → E) :
    multiMove x u v = x := by
  funext k
  simp [multiMove]

lemma multiMove_snoc {n : ℕ} (x : E → ℤ)
    (u v : Fin (n + 1) → E) :
    multiMove x u v =
      moveUnit
        (multiMove x (fun a : Fin n => u a.castSucc)
          (fun a : Fin n => v a.castSucc))
        (u (Fin.last n)) (v (Fin.last n)) := by
  funext k
  simp only [multiMove, moveUnit]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  ring

lemma endpointsInjective_prefix {n : ℕ}
    {u v : Fin (n + 1) → E}
    (h : EndpointsInjective u v) :
    EndpointsInjective
      (fun a : Fin n => u a.castSucc)
      (fun a : Fin n => v a.castSucc) := by
  intro a b hab
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          have hbig :
              (Sum.inl a.castSucc : Fin (n + 1) ⊕ Fin (n + 1)) =
                Sum.inl b.castSucc := h hab
          have hab' : a.castSucc = b.castSucc := Sum.inl.inj hbig
          exact congrArg Sum.inl ((Fin.castSucc_injective _) hab')
      | inr b =>
          have hbig :
              (Sum.inl a.castSucc : Fin (n + 1) ⊕ Fin (n + 1)) =
                Sum.inr b.castSucc := h hab
          cases hbig
  | inr a =>
      cases b with
      | inl b =>
          have hbig :
              (Sum.inr a.castSucc : Fin (n + 1) ⊕ Fin (n + 1)) =
                Sum.inl b.castSucc := h hab
          cases hbig
      | inr b =>
          have hbig :
              (Sum.inr a.castSucc : Fin (n + 1) ⊕ Fin (n + 1)) =
                Sum.inr b.castSucc := h hab
          have hab' : a.castSucc = b.castSucc := Sum.inr.inj hbig
          exact congrArg Sum.inr ((Fin.castSucc_injective _) hab')

lemma endpointsInjective_u_ne_v {n : ℕ}
    {u v : Fin n → E} (h : EndpointsInjective u v)
    (a b : Fin n) :
    u a ≠ v b := by
  intro huv
  have hsum :
      (Sum.inl a : Fin n ⊕ Fin n) = Sum.inr b :=
    h huv
  cases hsum

lemma endpointsInjective_u {n : ℕ}
    {u v : Fin n → E} (h : EndpointsInjective u v) :
    Function.Injective u := by
  intro a b hab
  have hsum :
      (Sum.inl a : Fin n ⊕ Fin n) = Sum.inl b :=
    h hab
  exact Sum.inl.inj hsum

lemma endpointsInjective_v {n : ℕ}
    {u v : Fin n → E} (h : EndpointsInjective u v) :
    Function.Injective v := by
  intro a b hab
  have hsum :
      (Sum.inr a : Fin n ⊕ Fin n) = Sum.inr b :=
    h hab
  exact Sum.inr.inj hsum

lemma noShortcut_multiMove_mem
    (B : Set (E → ℤ)) (hB : ExchangeClosed B)
    (x : E → ℤ) (hx : x ∈ B) :
    ∀ (n : ℕ) (u v : Fin n → E),
      EndpointsInjective u v →
      (∀ a : Fin n, moveUnit x (u a) (v a) ∈ B) →
      (∀ a b : Fin n, a < b →
        moveUnit x (u a) (v b) ∉ B) →
      multiMove x u v ∈ B := by
  intro n
  induction n with
  | zero =>
      intro u v hinj hsingle hshortcut
      rw [multiMove_zero x u v]
      exact hx
  | succ n ih =>
      intro u v hinj hsingle hshortcut
      let u0 : Fin n → E := fun a => u a.castSucc
      let v0 : Fin n → E := fun a => v a.castSucc
      let ul : E := u (Fin.last n)
      let vl : E := v (Fin.last n)
      have hinj0 : EndpointsInjective u0 v0 := by
        exact endpointsInjective_prefix hinj
      have hsingle0 : ∀ a : Fin n, moveUnit x (u0 a) (v0 a) ∈ B := by
        intro a
        exact hsingle a.castSucc
      have hshortcut0 :
          ∀ a b : Fin n, a < b →
            moveUnit x (u0 a) (v0 b) ∉ B := by
        intro a b hab
        exact hshortcut a.castSucc b.castSucc (by simpa using hab)
      have hyB : multiMove x u0 v0 ∈ B :=
        ih u0 v0 hinj0 hsingle0 hshortcut0
      have hzB : moveUnit x ul vl ∈ B :=
        hsingle (Fin.last n)
      have hul_ne_vl : ul ≠ vl := by
        exact endpointsInjective_u_ne_v hinj (Fin.last n) (Fin.last n)
      have hul_fresh_u : ∀ a : Fin n, ul ≠ u0 a := by
        intro a hua
        have huinj := endpointsInjective_u hinj
        have heq : (Fin.last n : Fin (n + 1)) = a.castSucc :=
          huinj hua
        have hval := congrArg Fin.val heq
        simp at hval
        omega
      have hul_fresh_v : ∀ a : Fin n, ul ≠ v0 a := by
        intro a huv
        exact endpointsInjective_u_ne_v hinj (Fin.last n) a.castSucc huv
      have hyl : multiMove x u0 v0 ul = x ul := by
        simp [multiMove, hul_fresh_u, hul_fresh_v]
      have hzl : moveUnit x ul vl ul = x ul - 1 := by
        simp [moveUnit, hul_ne_vl]
      have hlt : moveUnit x ul vl ul < multiMove x u0 v0 ul := by
        rw [hyl, hzl]
        omega
      obtain ⟨j, hj, hymove, hzmove⟩ :=
        hB (multiMove x u0 v0) hyB
          (moveUnit x ul vl) hzB ul hlt
      have hj_eq : j = vl := by
        by_contra hjv
        have hjul : j ≠ ul := by
          intro hju
          subst j
          rw [hyl, hzl] at hj
          omega
        have hzj : moveUnit x ul vl j = x j := by
          simp [moveUnit, hjul, hjv]
        have hyltx : multiMove x u0 v0 j < x j := by
          rw [← hzj]
          exact hj
        have hsrc : ∃ a : Fin n, j = u0 a := by
          by_contra hnone
          push Not at hnone
          have ht_nonneg :
              0 ≤ (∑ a : Fin n,
                if j = v0 a then (1 : ℤ) else 0) := by
            exact Finset.sum_nonneg fun a ha => by
              split_ifs <;> omega
          have hyformula :
              multiMove x u0 v0 j =
                x j +
                  (∑ a : Fin n,
                    if j = v0 a then (1 : ℤ) else 0) := by
            simp [multiMove, hnone]
          rw [hyformula] at hyltx
          omega
        obtain ⟨a, rfl⟩ := hsrc
        have hcross_not :
            moveUnit x (u0 a) vl ∉ B := by
          exact hshortcut a.castSucc (Fin.last n)
            (Fin.castSucc_lt_last a)
        have hpaired_eq :
            moveUnit (moveUnit x ul vl) (u0 a) ul =
              moveUnit x (u0 a) vl := by
          funext k
          simp [moveUnit]
          ring
        apply hcross_not
        rw [← hpaired_eq]
        exact hzmove
      subst j
      have hfull :
          multiMove x u v =
            moveUnit (multiMove x u0 v0) ul vl := by
        simpa [u0, v0, ul, vl] using multiMove_snoc x u v
      rw [hfull]
      exact hymove

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
