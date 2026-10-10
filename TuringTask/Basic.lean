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


lemma integerPairing_moveUnit {E : Type*} [Fintype E] [DecidableEq E]
    (p x : E → ℤ) (i j : E) :
    integerPairing p (moveUnit x i j) = integerPairing p x - p i + p j := by
  simp [integerPairing, moveUnit, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, mul_ite]

lemma tilt_exchange {E : Type*} [Fintype E] [DecidableEq E]
    {D : Finset (E → ℤ)} {c : (E → ℤ) → ℤ} {r : ℤ}
    (h : IntegerExchangeAxioms D c r) (p : E → ℤ) :
    IntegerExchangeAxioms D (fun x => c x + integerPairing p x) r := by
  refine ⟨h.1, ?_⟩
  intro x hx y hy i hi
  obtain ⟨j, hj, hx', hy', hc⟩ := h.2 x hx y hy i hi
  refine ⟨j, hj, hx', hy', ?_⟩
  dsimp only
  rw [integerPairing_moveUnit, integerPairing_moveUnit]
  omega

def gap {E : Type*} [Fintype E] (x y : E → ℤ) : ℕ :=
  ∑ i, (x i - y i).toNat

lemma exists_excess {E : Type*} [Fintype E] {x y : E → ℤ}
    (hs : (∑ i, x i) = ∑ i, y i) (hne : x ≠ y) : ∃ i, y i < x i := by
  by_contra hn
  push Not at hn
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
      simp [moveUnit, hij]
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

lemma moveUnit_cancel_middle {E : Type*} [DecidableEq E]
    (x : E → ℤ) (u v j : E) :
    moveUnit (moveUnit x u v) j u = moveUnit x j v := by
  funext k
  simp only [moveUnit]
  omega


lemma exchange_transitive {E : Type*} [DecidableEq E]
    {B : Set (E → ℤ)} (hB : ExchangeSet B) {x : E → ℤ}
    {i j k : E} (hij : i ≠ j) (hjk : j ≠ k) (_hik : i ≠ k)
    (ha : moveUnit x i j ∈ B) (hb : moveUnit x j k ∈ B) :
    moveUnit x i k ∈ B := by
  have hi : moveUnit x j k j < moveUnit x i j j := by
    simp [moveUnit, Ne.symm hij, hjk]
    omega
  obtain ⟨t, ht, hat, hbt⟩ := hB _ ha _ hb j hi
  have htik : t = i ∨ t = k := by
    by_contra hh
    have hti : t ≠ i := fun he => hh (Or.inl he)
    have htk : t ≠ k := fun he => hh (Or.inr he)
    simp only [moveUnit, if_neg hti, if_neg htk] at ht
    split_ifs at ht <;> omega
  rcases htik with hti | htk
  · subst t
    simpa only [moveUnit_cancel_middle] using hbt
  · subst t
    have heq : moveUnit (moveUnit x i j) j k = moveUnit x i k := by
      funext z; simp only [moveUnit]; omega
    simpa only [heq] using hat

lemma pairing_neg_price {E : Type*} [Fintype E] (p x : E → ℤ) :
    integerPairing (-p) x = -integerPairing p x := by
  simp [integerPairing, Finset.sum_neg_distrib]

lemma tilt_exchange_minus {E : Type*} [Fintype E] [DecidableEq E]
    {D : Finset (E → ℤ)} {c : (E → ℤ) → ℤ} {r : ℤ}
    (h : IntegerExchangeAxioms D c r) (p : E → ℤ) :
    IntegerExchangeAxioms D (fun x => c x - integerPairing p x) r := by
  simpa only [pairing_neg_price, sub_eq_add_neg] using tilt_exchange h (-p)

def IsMin {E : Type*} (D : Finset (E → ℤ)) (c : (E → ℤ) → ℤ) (x : E → ℤ) : Prop :=
  x ∈ D ∧ ∀ y ∈ D, c x ≤ c y

lemma finite_min {E : Type*} (D : Finset (E → ℤ)) (c : (E → ℤ) → ℤ)
    (hD : D.Nonempty) : ∃ x, IsMin D c x := by
  obtain ⟨x, hx, hc⟩ := D.exists_min_image c hD
  exact ⟨x, hx, hc⟩

def DualPair {E : Type*} [Fintype E]
    (D₁ D₂ : Finset (E → ℤ)) (c₁ c₂ : (E → ℤ) → ℤ)
    (p x y : E → ℤ) : Prop :=
  IsMin D₁ (fun z => c₁ z - integerPairing p z) x ∧
  IsMin D₂ (fun z => c₂ z + integerPairing p z) y

def dualValue {E : Type*} [Fintype E]
    (c₁ c₂ : (E → ℤ) → ℤ) (p x y : E → ℤ) : ℤ :=
  c₁ x - integerPairing p x + (c₂ y + integerPairing p y)

lemma dual_maximum {E : Type*} [Fintype E]
    (D₁ D₂ : Finset (E → ℤ)) (c₁ c₂ : (E → ℤ) → ℤ)
    (hcommon : ∃ z, z ∈ D₁ ∧ z ∈ D₂) :
    ∃ p x y, DualPair D₁ D₂ c₁ c₂ p x y ∧
      ∀ q u v, DualPair D₁ D₂ c₁ c₂ q u v →
        dualValue c₁ c₂ q u v ≤ dualValue c₁ c₂ p x y := by
  classical
  obtain ⟨z, hz₁, hz₂⟩ := hcommon
  let P : ℤ → Prop := fun a => ∃ p x y, DualPair D₁ D₂ c₁ c₂ p x y ∧
    dualValue c₁ c₂ p x y = a
  have hbound : ∀ a, P a → a ≤ c₁ z + c₂ z := by
    rintro a ⟨p,x,y,hmin,rfl⟩
    have hleft := hmin.1.2 z hz₁
    have hright := hmin.2.2 z hz₂
    dsimp only at hleft hright
    unfold dualValue
    omega
  have hnon : ∃ a, P a := by
    obtain ⟨x,hx⟩ := finite_min D₁ (fun x => c₁ x - integerPairing 0 x) ⟨z,hz₁⟩
    obtain ⟨y,hy⟩ := finite_min D₂ (fun x => c₂ x + integerPairing 0 x) ⟨z,hz₂⟩
    exact ⟨_,0,x,y,⟨hx,hy⟩,rfl⟩
  obtain ⟨a, ha, hmax⟩ := Int.exists_greatest_of_bdd ⟨c₁ z + c₂ z, hbound⟩ hnon
  obtain ⟨p,x,y,hmin,hval⟩ := ha
  refine ⟨p,x,y,hmin,?_⟩
  intro q u v hm
  have hb := hmax _ ⟨q,u,v,hm,rfl⟩
  simpa only [← hval] using hb

def multiMoveOn {E I : Type*} [DecidableEq E]
    (x : E → ℤ) (u v : I → E) (A : Finset I) : E → ℤ :=
  fun k => x k + ∑ t ∈ A,
    ((if k = v t then 1 else 0) - (if k = u t then 1 else 0))

lemma multiMoveOn_away {E I : Type*} [DecidableEq E]
    (x : E → ℤ) (u v : I → E) (A : Finset I) (k : E)
    (hu : ∀ t ∈ A, k ≠ u t) (hv : ∀ t ∈ A, k ≠ v t) :
    multiMoveOn x u v A k = x k := by
  have : (∑ t ∈ A,
      ((if k = v t then 1 else 0 : ℤ) - (if k = u t then 1 else 0))) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    simp [hu t ht, hv t ht]
  simp [multiMoveOn, this]

lemma multiMoveOn_nondecrease {E I : Type*} [DecidableEq E]
    (x : E → ℤ) (u v : I → E) (A : Finset I) (k : E)
    (hu : ∀ t ∈ A, k ≠ u t) : x k ≤ multiMoveOn x u v A k := by
  have : 0 ≤ ∑ t ∈ A,
      ((if k = v t then 1 else 0 : ℤ) - (if k = u t then 1 else 0)) := by
    apply Finset.sum_nonneg
    intro t ht
    simp only [if_neg (hu t ht), sub_zero]
    split_ifs <;> omega
  unfold multiMoveOn
  omega

lemma multiMoveOn_insert {E I : Type*} [DecidableEq E] [DecidableEq I]
    (x : E → ℤ) (u v : I → E) (A : Finset I) (a : I) (ha : a ∉ A) :
    multiMoveOn x u v (insert a A) = moveUnit (multiMoveOn x u v A) (u a) (v a) := by
  funext k
  simp only [multiMoveOn, moveUnit, Finset.sum_insert ha]
  omega

lemma no_shortcut_on {E I : Type*} [DecidableEq E] [LinearOrder I]
    {B : Set (E → ℤ)} (hB : ExchangeSet B)
    (x : E → ℤ) (hx : x ∈ B) (u v : I → E) (A : Finset I)
    (huu : ∀ a ∈ A, ∀ b ∈ A, u a = u b → a = b)
    (hvv : ∀ a ∈ A, ∀ b ∈ A, v a = v b → a = b)
    (huv : ∀ a ∈ A, ∀ b ∈ A, u a ≠ v b)
    (hedge : ∀ a ∈ A, moveUnit x (u a) (v a) ∈ B)
    (hforbid : ∀ a ∈ A, ∀ b ∈ A, a < b → moveUnit x (u a) (v b) ∉ B) :
    multiMoveOn x u v A ∈ B := by
  induction A using Finset.induction_on_max with
  | empty =>
    have heq : multiMoveOn x u v (∅ : Finset I) = x := by funext k; simp [multiMoveOn]
    simpa only [heq] using hx
  | insert a A hmax ih =>
    have hsub : ∀ t ∈ A, t ∈ insert a A := fun t ht => Finset.mem_insert_of_mem ht
    have ha : a ∈ insert a A := Finset.mem_insert_self a A
    have hnot : a ∉ A := by intro hh; have := hmax a hh; exact lt_irrefl a this
    have hy : multiMoveOn x u v A ∈ B := ih
      (fun b hb c hc => huu b (hsub b hb) c (hsub c hc))
      (fun b hb c hc => hvv b (hsub b hb) c (hsub c hc))
      (fun b hb c hc => huv b (hsub b hb) c (hsub c hc))
      (fun b hb => hedge b (hsub b hb))
      (fun b hb c hc => hforbid b (hsub b hb) c (hsub c hc))
    have hun : ∀ t ∈ A, u a ≠ u t := by
      intro t ht he
      have hh := huu a ha t (hsub t ht) he
      subst t
      exact hnot ht
    have hvn : ∀ t ∈ A, u a ≠ v t := fun t ht => huv a ha t (hsub t ht)
    have haway := multiMoveOn_away x u v A (u a) hun hvn
    have hne : u a ≠ v a := huv a ha a ha
    have hless : moveUnit x (u a) (v a) (u a) < multiMoveOn x u v A (u a) := by
      simp [moveUnit, hne, haway]
    obtain ⟨j, hj, hyj, hzj⟩ := hB _ hy _ (hedge a ha) (u a) hless
    have hjv : j = v a := by
      by_contra hneq
      have hsource : ∃ t ∈ A, j = u t := by
        by_contra hno
        push Not at hno
        have hge := multiMoveOn_nondecrease x u v A j hno
        have hval : moveUnit x (u a) (v a) j ≤ x j := by
          simp only [moveUnit, if_neg hneq, add_zero]
          split_ifs <;> omega
        omega
      obtain ⟨t, ht, rfl⟩ := hsource
      have hbad : moveUnit x (u t) (v a) ∈ B := by
        simpa only [moveUnit_cancel_middle] using hzj
      exact hforbid t (hsub t ht) a ha (hmax t ht) hbad
    rw [multiMoveOn_insert x u v A a hnot]
    simpa only [hjv] using hyj

-- A route is indexed by its number of edges; vertices are stored in a total sequence.
def Route {E : Type*} (R : E → E → Prop) (S T : E → Prop)
    (n : ℕ) (v : ℕ → E) : Prop :=
  S (v 0) ∧ T (v n) ∧ ∀ k < n, R (v k) (v (k+1))

lemma route_extend {E : Type*} {R : E → E → Prop} {S : E → Prop}
    {n : ℕ} {v : ℕ → E} {t : E}
    (hs : S (v 0)) (he : ∀ k < n, R (v k) (v (k+1))) (ht : R (v n) t) :
    ∃ w : ℕ → E, S (w 0) ∧ w (n+1) = t ∧ ∀ k < n+1, R (w k) (w (k+1)) := by
  let w : ℕ → E := fun k => if k ≤ n then v k else t
  refine ⟨w, ?_, ?_, ?_⟩
  · simpa [w] using hs
  · simp [w]
  · intro k hk
    by_cases hkn : k < n
    · simpa [w, show k ≤ n by omega, show k+1 ≤ n by omega] using he k hkn
    · have hkEq : k = n := by omega
      subst k
      simpa [w] using ht

lemma minimal_route {E : Type*} {R : E → E → Prop} {S T : E → Prop}
    (hex : ∃ n v, Route R S T n v) :
    ∃ n v, Route R S T n v ∧ ∀ m w, Route R S T m w → n ≤ m := by
  classical
  let P : ℕ → Prop := fun n => ∃ v, Route R S T n v
  have hn : ∃ n, P n := hex
  obtain ⟨v,hv⟩ := Nat.find_spec hn
  exact ⟨Nat.find hn, v, hv, fun m w hw => Nat.find_min' hn ⟨w,hw⟩⟩

lemma minimal_route_no_shortcut {E : Type*} {R : E → E → Prop} {S T : E → Prop}
    {n : ℕ} {v : ℕ → E} (hv : Route R S T n v)
    (hmin : ∀ m w, Route R S T m w → n ≤ m)
    {a b : ℕ} (hab : a+1 < b) (hbn : b ≤ n) : ¬ R (v a) (v b) := by
  intro hr
  let d := b-a-1
  let m := n-d
  let w : ℕ → E := fun k => if k ≤ a then v k else v (k+d)
  have hpos : 0 < d := by dsimp [d]; omega
  have hd : a+1+d = b := by dsimp [d]; omega
  have hm : m+d = n := by dsimp [m,d]; omega
  have ham : a < m := by dsimp [m,d]; omega
  have hw : Route R S T m w := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [w] using hv.1
    · have : w m = v n := by simp [w, show ¬m ≤ a by omega, hm]
      simpa only [this] using hv.2.1
    · intro k hk
      by_cases hka : k < a
      · simpa [w, show k ≤ a by omega, show k+1 ≤ a by omega] using hv.2.2 k (by omega)
      · by_cases hke : k = a
        · subst k
          simpa [w, hd] using hr
        · have hle : ¬ k ≤ a := by omega
          have hle' : ¬ k+1 ≤ a := by omega
          have hh := hv.2.2 (k+d) (by omega)
          simpa [w, hle, hle', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
  have := hmin m w hw
  dsimp [m] at this
  omega

lemma minimal_route_injective {E : Type*} {R : E → E → Prop} {S T : E → Prop}
    {n : ℕ} {v : ℕ → E} (hv : Route R S T n v)
    (hmin : ∀ m w, Route R S T m w → n ≤ m)
    (_hirr : ∀ i, ¬R i i) :
    ∀ a ≤ n, ∀ b ≤ n, v a = v b → a = b := by
  suffices h : ∀ a b, a < b → b ≤ n → v a ≠ v b by
    intro a ha b hb he
    rcases lt_trichotomy a b with hh | hh | hh
    · exact False.elim (h a b hh hb he)
    · exact hh
    · exact False.elim (h b a hh ha he.symm)
  intro a b hab hbn he
  by_cases hbe : b = n
  · subst b
    have hw : Route R S T a v := ⟨hv.1, by simpa [he] using hv.2.1,
      fun k hk => hv.2.2 k (by omega)⟩
    have := hmin a v hw
    omega
  · have hblt : b < n := by omega
    have hr : R (v a) (v (b+1)) := by rw [he]; exact hv.2.2 b hblt
    exact minimal_route_no_shortcut hv hmin (by omega) (by omega) hr

noncomputable def indicatorPrice {E : Type*} (W : Set E) : E → ℤ := by
  classical
  exact fun i => if i ∈ W then 1 else 0

lemma cut_min_plus {E : Type*} [Fintype E] [DecidableEq E]
    {D : Finset (E → ℤ)} {c : (E → ℤ) → ℤ} {r : ℤ}
    (h : IntegerExchangeAxioms D c r) {x : E → ℤ} (hx : IsMin D c x)
    (W : Set E)
    (hclosed : ∀ i j, moveUnit x i j ∈ D → c (moveUnit x i j) = c x →
      i ∈ W → j ∈ W) :
    IsMin D (fun z => c z + integerPairing (indicatorPrice W) z) x := by
  classical
  refine ⟨hx.1, local_global (tilt_exchange h (indicatorPrice W)) hx.1 ?_⟩
  intro i j hij
  rw [integerPairing_moveUnit]
  have hcost := hx.2 _ hij
  by_cases heq : c (moveUnit x i j) = c x
  · by_cases hi : i ∈ W
    · have hj := hclosed i j hij heq hi
      simp only [indicatorPrice, if_pos hi, if_pos hj]
      omega
    · simp only [indicatorPrice, if_neg hi]
      split_ifs <;> omega
  · simp only [indicatorPrice]
    split_ifs <;> omega

lemma cut_min_minus {E : Type*} [Fintype E] [DecidableEq E]
    {D : Finset (E → ℤ)} {c : (E → ℤ) → ℤ} {r : ℤ}
    (h : IntegerExchangeAxioms D c r) {x : E → ℤ} (hx : IsMin D c x)
    (W : Set E)
    (hclosed : ∀ i j, moveUnit x i j ∈ D → c (moveUnit x i j) = c x →
      j ∈ W → i ∈ W) :
    IsMin D (fun z => c z - integerPairing (indicatorPrice W) z) x := by
  classical
  refine ⟨hx.1, local_global (tilt_exchange_minus h (indicatorPrice W)) hx.1 ?_⟩
  intro i j hij
  rw [integerPairing_moveUnit]
  have hcost := hx.2 _ hij
  by_cases heq : c (moveUnit x i j) = c x
  · by_cases hj : j ∈ W
    · have hi := hclosed i j hij heq hj
      simp only [indicatorPrice, if_pos hi, if_pos hj]
      omega
    · simp only [indicatorPrice, if_neg hj]
      split_ifs <;> omega
  · simp only [indicatorPrice]
    split_ifs <;> omega

lemma pairing_sub_price {E : Type*} [Fintype E] (p q x : E → ℤ) :
    integerPairing (p-q) x = integerPairing p x - integerPairing q x := by
  simp [integerPairing, sub_mul, Finset.sum_sub_distrib]

def ZeroArc {E : Type*} [DecidableEq E]
    (D₁ D₂ : Finset (E → ℤ)) (a b : (E → ℤ) → ℤ)
    (x y : E → ℤ) (i j : E) : Prop :=
  i ≠ j ∧ ((moveUnit x i j ∈ D₁ ∧ a (moveUnit x i j) = a x) ∨
    (moveUnit y j i ∈ D₂ ∧ b (moveUnit y j i) = b y))

lemma zero_route_exists {E : Type*} [Fintype E] [DecidableEq E]
    {D₁ D₂ : Finset (E → ℤ)} {c₁ c₂ : (E → ℤ) → ℤ} {r : ℤ}
    (h₁ : IntegerExchangeAxioms D₁ c₁ r) (h₂ : IntegerExchangeAxioms D₂ c₂ r)
    {p x y : E → ℤ} (hm : DualPair D₁ D₂ c₁ c₂ p x y)
    (hmax : ∀ q u v, DualPair D₁ D₂ c₁ c₂ q u v →
      dualValue c₁ c₂ q u v ≤ dualValue c₁ c₂ p x y)
    (hne : x ≠ y) :
    ∃ n v, Route (ZeroArc D₁ D₂ (fun z => c₁ z - integerPairing p z)
      (fun z => c₂ z + integerPairing p z) x y)
      (fun i => y i < x i) (fun i => x i < y i) n v := by
  classical
  let a := fun z => c₁ z - integerPairing p z
  let b := fun z => c₂ z + integerPairing p z
  let R := ZeroArc D₁ D₂ a b x y
  let S := fun i => y i < x i
  let T := fun i => x i < y i
  change ∃ n v, Route R S T n v
  by_contra hno
  let W : Set E := {i | ∃ (n : ℕ) (v : ℕ → E), S (v 0) ∧ v n = i ∧ ∀ k < n, R (v k) (v (k+1))}
  have hsW : ∀ i, S i → i ∈ W := by
    intro i hi
    exact ⟨0,fun _ => i,hi,rfl,fun k hk => by omega⟩
  have hWt : ∀ i ∈ W, ¬T i := by
    rintro i ⟨n,v,hs,he,hr⟩ hi
    exact hno ⟨n,v,hs,by simpa [he] using hi,hr⟩
  have hWclosed : ∀ i j, R i j → i ∈ W → j ∈ W := by
    rintro i j hij ⟨n,v,hs,he,hr⟩
    obtain ⟨w,hw₀,hw₁,hw₂⟩ := route_extend hs hr (by simpa [he] using hij)
    exact ⟨n+1,w,hw₀,hw₁,hw₂⟩
  have ha : IsMin D₁ (fun z => a z + integerPairing (indicatorPrice W) z) x :=
    cut_min_plus (tilt_exchange_minus h₁ p) hm.1 W (by
      intro i j hij heq hi
      by_cases hije : i = j
      · simpa [hije] using hi
      · exact hWclosed i j ⟨hije,Or.inl ⟨hij,heq⟩⟩ hi)
  have hb : IsMin D₂ (fun z => b z - integerPairing (indicatorPrice W) z) y :=
    cut_min_minus (tilt_exchange h₂ p) hm.2 W (by
      intro i j hij heq hj
      by_cases hije : j = i
      · simpa [hije] using hj
      · exact hWclosed j i ⟨hije,Or.inr ⟨hij,heq⟩⟩ hj)
  let q := p - indicatorPrice W
  have hnew : DualPair D₁ D₂ c₁ c₂ q x y := by
    refine ⟨⟨ha.1,?_⟩,⟨hb.1,?_⟩⟩
    · intro z hz
      have hh := ha.2 z hz
      dsimp only [a] at hh
      dsimp only [q]
      rw [pairing_sub_price,pairing_sub_price]
      omega
    · intro z hz
      have hh := hb.2 z hz
      dsimp only [b] at hh
      dsimp only [q]
      rw [pairing_sub_price,pairing_sub_price]
      omega
  obtain ⟨s,hs⟩ := exists_excess ((h₁.1 x hm.1.1).trans (h₂.1 y hm.2.1).symm) hne
  have hpos : integerPairing (indicatorPrice W) y < integerPairing (indicatorPrice W) x := by
    unfold integerPairing
    apply Finset.sum_lt_sum
    · intro i hi
      by_cases hwi : i ∈ W
      · have hh := hWt i hwi
        dsimp only [T] at hh
        simp only [indicatorPrice,if_pos hwi,one_mul]
        omega
      · simp [indicatorPrice,hwi]
    · refine ⟨s,Finset.mem_univ s,?_⟩
      have hsw : s ∈ W := hsW s hs
      simpa [indicatorPrice,hsw] using hs
  have hval := hmax q x y hnew
  dsimp only [dualValue,q] at hval
  rw [pairing_sub_price,pairing_sub_price] at hval
  omega

lemma gap_from_difference {E : Type*} [Fintype E] [DecidableEq E]
    (x y x' y' : E → ℤ) (s t : E) (hs : y s < x s) (ht : x t < y t)
    (hd : ∀ k, x' k - y' k = x k - y k - (if k = s then 1 else 0) +
      (if k = t then 1 else 0)) : gap x' y' + 1 = gap x y := by
  have hg : gap x' y' = gap x (moveUnit y t s) := by
    unfold gap
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    simp only [moveUnit]
    have := hd k
    omega
  rw [hg]
  exact gap_exchange_right x y s t hs ht

lemma sum_range_telescope (f : ℕ → ℤ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (f (i+1)-f i)) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; omega

lemma zero_route_augment {E : Type*} [Fintype E] [DecidableEq E]
    {D₁ D₂ : Finset (E → ℤ)} {a b : (E → ℤ) → ℤ} {r : ℤ}
    (h₁ : IntegerExchangeAxioms D₁ a r) (h₂ : IntegerExchangeAxioms D₂ b r)
    {x y : E → ℤ} (hx : IsMin D₁ a x) (hy : IsMin D₂ b y)
    {n : ℕ} {v : ℕ → E}
    (hv : Route (ZeroArc D₁ D₂ a b x y) (fun i => y i < x i) (fun i => x i < y i) n v)
    (hmin : ∀ m w, Route (ZeroArc D₁ D₂ a b x y) (fun i => y i < x i)
      (fun i => x i < y i) m w → n ≤ m) :
    ∃ x' y', IsMin D₁ a x' ∧ IsMin D₂ b y' ∧ gap x' y' < gap x y := by
  classical
  let B₁ : Set (E → ℤ) := {z | IsMin D₁ a z}
  let B₂ : Set (E → ℤ) := {z | IsMin D₂ b z}
  have hB₁ : ExchangeSet B₁ := minimizer_set_exchange h₁
  have hB₂ : ExchangeSet B₂ := minimizer_set_exchange h₂
  have hinj := minimal_route_injective hv hmin (fun i hi => hi.1 rfl)
  have hneq : ∀ i ≤ n, ∀ j ≤ n, i ≠ j → v i ≠ v j := by
    intro i hi j hj hij he
    exact hij (hinj i hi j hj he)
  have hshort := @minimal_route_no_shortcut E _ _ _ n v hv hmin
  let F : ℕ → Prop := fun k => moveUnit x (v k) (v (k+1)) ∈ B₁
  have hF : ∀ k < n, F k ↔ moveUnit x (v k) (v (k+1)) ∈ D₁ ∧
      a (moveUnit x (v k) (v (k+1))) = a x := by
    intro k hk
    constructor
    · intro hh
      refine ⟨hh.1, le_antisymm (hh.2 x hx.1) (hx.2 _ hh.1)⟩
    · rintro ⟨hh,he⟩
      refine ⟨hh,?_⟩
      intro z hz
      rw [he]
      exact hx.2 z hz
  have hG : ∀ k < n, ¬F k → moveUnit y (v (k+1)) (v k) ∈ B₂ := by
    intro k hk hf
    have hr := hv.2.2 k hk
    rcases hr.2 with hh | hh
    · exact False.elim (hf ((hF k hk).2 hh))
    · refine ⟨hh.1,?_⟩
      intro z hz
      rw [hh.2]
      exact hy.2 z hz
  have haltF : ∀ k, k+1 < n → F k → ¬F (k+1) := by
    intro k hk hf hf'
    have hmem : moveUnit x (v k) (v (k+2)) ∈ B₁ :=
      exchange_transitive hB₁ (hneq k (by omega) (k+1) (by omega) (by omega))
        (hneq (k+1) (by omega) (k+2) (by omega) (by omega))
        (hneq k (by omega) (k+2) (by omega) (by omega)) hf (by simpa [Nat.add_assoc] using hf')
    have heq : a (moveUnit x (v k) (v (k+2))) = a x :=
      le_antisymm (hmem.2 x hx.1) (hx.2 _ hmem.1)
    exact hshort (by omega) (by omega)
      ⟨hneq k (by omega) (k+2) (by omega) (by omega),Or.inl ⟨hmem.1,heq⟩⟩
  have haltG : ∀ k, k+1 < n → ¬F k → F (k+1) := by
    intro k hk hf
    by_contra hf'
    have hg := hG k (by omega) hf
    have hg' := hG (k+1) hk hf'
    have hmem : moveUnit y (v (k+2)) (v k) ∈ B₂ :=
      exchange_transitive hB₂
        (hneq (k+2) (by omega) (k+1) (by omega) (by omega))
        (hneq (k+1) (by omega) k (by omega) (by omega))
        (hneq (k+2) (by omega) k (by omega) (by omega))
        (by simpa [Nat.add_assoc] using hg') hg
    have heq : b (moveUnit y (v (k+2)) (v k)) = b y :=
      le_antisymm (hmem.2 y hy.1) (hy.2 _ hmem.1)
    exact hshort (by omega) (by omega)
      ⟨hneq k (by omega) (k+2) (by omega) (by omega),Or.inr ⟨hmem.1,heq⟩⟩
  let A₁ := (Finset.range n).filter F
  let A₂ := (Finset.range n).filter (fun k => ¬F k)
  have hA₁ : ∀ k ∈ A₁, k < n ∧ F k := by
    intro k hk
    exact ⟨Finset.mem_range.mp (Finset.mem_filter.mp hk).1,(Finset.mem_filter.mp hk).2⟩
  have hA₂ : ∀ k ∈ A₂, k < n ∧ ¬F k := by
    intro k hk
    exact ⟨Finset.mem_range.mp (Finset.mem_filter.mp hk).1,(Finset.mem_filter.mp hk).2⟩
  let x' := multiMoveOn x v (fun k => v (k+1)) A₁
  let y' := multiMoveOn y (fun k => v (k+1)) v A₂
  have hx' : x' ∈ B₁ := by
    apply no_shortcut_on hB₁ x hx v (fun k => v (k+1)) A₁
    · intro i hi j hj he
      exact hinj i (by have := (hA₁ i hi).1; omega) j (by have := (hA₁ j hj).1; omega) he
    · intro i hi j hj he
      have hh := hinj (i+1) (by have := (hA₁ i hi).1; omega)
        (j+1) (by have := (hA₁ j hj).1; omega) he
      omega
    · intro i hi j hj he
      have hh := hinj i (by have := (hA₁ i hi).1; omega)
        (j+1) (by have := (hA₁ j hj).1; omega) he
      subst i
      exact haltF j (hA₁ (j+1) hi).1 (hA₁ j hj).2 (hA₁ (j+1) hi).2
    · intro i hi; exact (hA₁ i hi).2
    · intro i hi j hj hij hmem
      have hh := (hA₁ j hj).1
      have hh' := (hA₁ i hi).1
      have heq : a (moveUnit x (v i) (v (j+1))) = a x :=
        le_antisymm (hmem.2 x hx.1) (hx.2 _ hmem.1)
      exact hshort (by omega) (by omega)
        ⟨hneq i (by omega) (j+1) (by omega) (by omega),Or.inl ⟨hmem.1,heq⟩⟩
  have hy' : y' ∈ B₂ := by
    apply no_shortcut_on (I := ℕᵒᵈ) hB₂ y hy
      (fun k => v (OrderDual.ofDual k+1)) (fun k => v (OrderDual.ofDual k)) A₂
    · change ∀ (i : ℕ), i ∈ A₂ → ∀ (j : ℕ), j ∈ A₂ → v (i+1) = v (j+1) → i = j
      intro i hi j hj he
      have hh := hinj (i+1) (by have := (hA₂ i hi).1; omega)
        (j+1) (by have := (hA₂ j hj).1; omega) he
      exact Nat.add_right_cancel hh
    · change ∀ (i : ℕ), i ∈ A₂ → ∀ (j : ℕ), j ∈ A₂ → v i = v j → i = j
      intro i hi j hj he
      exact hinj i (by have := (hA₂ i hi).1; omega) j (by have := (hA₂ j hj).1; omega) he
    · change ∀ (i : ℕ), i ∈ A₂ → ∀ (j : ℕ), j ∈ A₂ → v (i+1) ≠ v j
      intro i hi j hj he
      have hh := hinj (i+1) (by have := (hA₂ i hi).1; omega)
        j (by have := (hA₂ j hj).1; omega) he
      subst j
      exact (hA₂ (i+1) hj).2 (haltG i (hA₂ (i+1) hj).1 (hA₂ i hi).2)
    · change ∀ (i : ℕ), i ∈ A₂ → moveUnit y (v (i+1)) (v i) ∈ B₂
      intro i hi; exact hG i (hA₂ i hi).1 (hA₂ i hi).2
    · change ∀ (i : ℕ), i ∈ A₂ → ∀ (j : ℕ), j ∈ A₂ → j < i →
        moveUnit y (v (i+1)) (v j) ∉ B₂
      intro i hi j hj hij hmem
      have hh := (hA₂ j hj).1
      have hh' := (hA₂ i hi).1
      have heq : b (moveUnit y (v (i+1)) (v j)) = b y :=
        le_antisymm (hmem.2 y hy.1) (hy.2 _ hmem.1)
      exact hshort (by omega) (by omega)
        ⟨hneq j (by omega) (i+1) (by omega) (by omega),Or.inr ⟨hmem.1,heq⟩⟩
  have hd : ∀ k, x' k - y' k = x k - y k - (if k = v 0 then 1 else 0) +
      (if k = v n then 1 else 0) := by
    intro k
    let f : ℕ → ℤ := fun i => if k = v i then 1 else 0
    have hp := Finset.sum_filter_add_sum_filter_not (Finset.range n) F
      (fun i => f (i+1) - f i)
    have ht := sum_range_telescope f n
    have hneg : (∑ i ∈ A₂, (f i - f (i+1))) = -∑ i ∈ A₂, (f (i+1)-f i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      omega
    dsimp only [x',y',multiMoveOn]
    change x k + (∑ i ∈ A₁, (f (i+1)-f i)) -
      (y k + (∑ i ∈ A₂, (f i-f (i+1)))) = x k - y k - f 0 + f n
    rw [hneg]
    change (∑ i ∈ A₁, (f (i+1)-f i)) + (∑ i ∈ A₂, (f (i+1)-f i)) =
      (∑ i ∈ Finset.range n, (f (i+1)-f i)) at hp
    omega
  have hgap := gap_from_difference x y x' y' (v 0) (v n) hv.1 hv.2.1 hd
  exact ⟨x',y',hx',hy',by omega⟩

lemma dualValue_eq {E : Type*} [Fintype E]
    {D₁ D₂ : Finset (E → ℤ)} {c₁ c₂ : (E → ℤ) → ℤ} {p x y u v : E → ℤ}
    (hxy : DualPair D₁ D₂ c₁ c₂ p x y) (huv : DualPair D₁ D₂ c₁ c₂ p u v) :
    dualValue c₁ c₂ p x y = dualValue c₁ c₂ p u v := by
  have h₁ := hxy.1.2 u huv.1.1
  have h₂ := huv.1.2 x hxy.1.1
  have h₃ := hxy.2.2 v huv.2.1
  have h₄ := huv.2.2 y hxy.2.1
  dsimp only at h₁ h₂ h₃ h₄
  unfold dualValue
  omega

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
  classical
  obtain ⟨p,x₀,y₀,hm₀,hmax₀⟩ := dual_maximum D₁ D₂ c₁ c₂ hcommon
  let A := (D₁.product D₂).filter (fun z => DualPair D₁ D₂ c₁ c₂ p z.1 z.2)
  have hA : A.Nonempty := by
    refine ⟨(x₀,y₀),?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm₀.1.1,hm₀.2.1⟩,hm₀⟩
  obtain ⟨z,hz,hmin⟩ := A.exists_min_image (fun z => gap z.1 z.2) hA
  let x := z.1
  let y := z.2
  have hm : DualPair D₁ D₂ c₁ c₂ p x y := (Finset.mem_filter.mp hz).2
  have hmax : ∀ q u v, DualPair D₁ D₂ c₁ c₂ q u v →
      dualValue c₁ c₂ q u v ≤ dualValue c₁ c₂ p x y := by
    intro q u v hh
    rw [← dualValue_eq hm₀ hm]
    exact hmax₀ q u v hh
  have heq : x = y := by
    by_contra hne
    obtain ⟨n,v,hv,hroute⟩ := minimal_route (zero_route_exists h₁ h₂ hm hmax hne)
    obtain ⟨x',y',hx',hy',hgap⟩ := zero_route_augment
      (tilt_exchange_minus h₁ p) (tilt_exchange h₂ p) hm.1 hm.2 hv hroute
    have hmem : (x',y') ∈ A := Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hx'.1,hy'.1⟩,⟨hx',hy'⟩⟩
    have hsmall := hmin (x',y') hmem
    change gap x y ≤ gap x' y' at hsmall
    omega
  refine ⟨x,p,hm.1.1,?_,hm.1.2,?_⟩
  · simpa only [heq] using hm.2.1
  · simpa only [heq] using hm.2.2

end TuringTask

