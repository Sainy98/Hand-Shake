import Mathlib

open scoped BigOperators

namespace TuringTask

def incidentEdges
    {V A : Type*} [DecidableEq V] [Fintype A]
    (src dst : A → V) (v : V) : Finset A :=
  Finset.univ.filter (fun e => src e = v ∨ dst e = v)

def internalEdges
    {V A : Type*} [DecidableEq V] [Fintype A]
    (src dst : A → V) (U : Finset V) : Finset A :=
  Finset.univ.filter (fun e => src e ∈ U ∧ dst e ∈ U)

def boundaryEdges
    {V A : Type*} [DecidableEq V] [Fintype A]
    (src dst : A → V) (U : Finset V) : Finset A :=
  Finset.univ.filter (fun e =>
    (src e ∈ U ∧ dst e ∉ U) ∨
    (src e ∉ U ∧ dst e ∈ U))

def blossomBudget
    {V A : Type*}
    (b : V → ℕ) (c : A → ℕ)
    (U : Finset V) (F : Finset A) : ℕ :=
  (∑ v ∈ U, b v) + (∑ e ∈ F, c e)

def IsIntegralBMatching
    {V A : Type*} [DecidableEq V] [Fintype A]
    (src dst : A → V)
    (b : V → ℕ) (c : A → ℕ)
    (q : A → ℕ) : Prop :=
  (∀ e : A, q e ≤ c e) ∧
  (∀ v : V, (∑ e ∈ incidentEdges src dst v, q e) ≤ b v)

noncomputable def integralBMatchings
    {V A : Type*} [DecidableEq V] [Fintype A]
    (src dst : A → V)
    (b : V → ℕ) (c : A → ℕ) : Finset (A → ℕ) := by
  classical
  exact
    (Fintype.piFinset
      (fun e : A => Finset.range (c e + 1))).filter
      (fun q => IsIntegralBMatching src dst b c q)

noncomputable def SatisfiesBlossomConstraints
    {V A : Type*} [DecidableEq V] [Fintype A]
    (src dst : A → V)
    (b : V → ℕ) (c : A → ℕ)
    (x : A → ℝ) : Prop := by
  classical
  exact
    (∀ e : A, 0 ≤ x e ∧ x e ≤ (c e : ℝ)) ∧
    (∀ v : V,
      (∑ e ∈ incidentEdges src dst v, x e) ≤ (b v : ℝ)) ∧
    (∀ U : Finset V, ∀ F : Finset A,
      F ⊆ boundaryEdges src dst U →
      Odd (blossomBudget b c U F) →
      (∑ e ∈ internalEdges src dst U, x e) +
        (∑ e ∈ F, x e) ≤
          ((blossomBudget b c U F / 2 : ℕ) : ℝ))

noncomputable def HasIntegralBMatchingDecomposition
    {V A : Type*} [DecidableEq V] [Fintype A]
    (src dst : A → V)
    (b : V → ℕ) (c : A → ℕ)
    (x : A → ℝ) : Prop := by
  classical
  exact
    ∃ p : (A → ℕ) → ℝ,
      (∀ q ∈ integralBMatchings src dst b c, 0 ≤ p q) ∧
      (∑ q ∈ integralBMatchings src dst b c, p q) = 1 ∧
      (∀ e : A,
        x e =
          ∑ q ∈ integralBMatchings src dst b c,
            p q * (q e : ℝ))


section Incidence

variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A]

lemma endpoint_indicator_total (src dst : A → V)
    (hloop : ∀ e, src e ≠ dst e) (U : Finset V) (e : A) (m : ℕ) :
    (∑ v ∈ U, if src e = v ∨ dst e = v then m else 0) =
      (if src e ∈ U then m else 0) + (if dst e ∈ U then m else 0) := by
  classical
  have split (v : V) :
      (if src e = v ∨ dst e = v then m else 0) =
        (if src e = v then m else 0) + (if dst e = v then m else 0) := by
    by_cases hs : src e = v <;> by_cases hd : dst e = v <;> simp_all
    exact False.elim (hloop e (hs.trans hd.symm))
  simp_rw [split]
  rw [Finset.sum_add_distrib]
  simp

lemma incidence_total_identity (src dst : A → V)
    (hloop : ∀ e, src e ≠ dst e) (q : A → ℕ) (U : Finset V) :
    (∑ v ∈ U, ∑ e ∈ incidentEdges src dst v, q e) =
      2 * (∑ e ∈ internalEdges src dst U, q e) +
        (∑ e ∈ boundaryEdges src dst U, q e) := by
  classical
  simp only [incidentEdges, internalEdges, boundaryEdges, Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rw [endpoint_indicator_total src dst hloop U e (q e)]
  by_cases hs : src e ∈ U <;> by_cases hd : dst e ∈ U <;>
    simp [hs, hd, two_mul]

lemma integral_blossom_bound (src dst : A → V)
    (hloop : ∀ e, src e ≠ dst e) (b : V → ℕ) (c : A → ℕ)
    (q : A → ℕ) (hq : IsIntegralBMatching src dst b c q)
    (U : Finset V) (F : Finset A) (hF : F ⊆ boundaryEdges src dst U) :
    (∑ e ∈ internalEdges src dst U, q e) + (∑ e ∈ F, q e) ≤
      blossomBudget b c U F / 2 := by
  classical
  have deg := Finset.sum_le_sum (fun v (_ : v ∈ U) => hq.2 v)
  rw [incidence_total_identity src dst hloop q U] at deg
  have part : (∑ e ∈ F, q e) ≤ ∑ e ∈ boundaryEdges src dst U, q e :=
    Finset.sum_le_sum_of_subset hF
  have cap := Finset.sum_le_sum (fun e (_ : e ∈ F) => hq.1 e)
  unfold blossomBudget
  omega

lemma listed_matching_feasible (src dst : A → V) (b : V → ℕ) (c : A → ℕ)
    (q : A → ℕ) (hq : q ∈ integralBMatchings src dst b c) :
    IsIntegralBMatching src dst b c q := by
  classical
  exact (Finset.mem_filter.mp hq).2

lemma finite_average_bound {I : Type*} (S : Finset I) (p f : I → ℝ) (t : ℝ)
    (hp : ∀ i ∈ S, 0 ≤ p i) (hm : ∑ i ∈ S, p i = 1)
    (hf : ∀ i ∈ S, f i ≤ t) : (∑ i ∈ S, p i * f i) ≤ t := by
  calc
    (∑ i ∈ S, p i * f i) ≤ ∑ i ∈ S, p i * t :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hf i hi) (hp i hi))
    _ = (∑ i ∈ S, p i) * t := (Finset.sum_mul S p t).symm
    _ = t := by rw [hm, one_mul]

lemma decomposition_is_blossom_feasible (src dst : A → V)
    (hloop : ∀ e, src e ≠ dst e) (b : V → ℕ) (c : A → ℕ)
    (x : A → ℝ) (hx : HasIntegralBMatchingDecomposition src dst b c x) :
    SatisfiesBlossomConstraints src dst b c x := by
  classical
  obtain ⟨p, hpos, hmass, hcoord⟩ := hx
  let S := integralBMatchings src dst b c
  have hmatch (q : A → ℕ) (hq : q ∈ S) : IsIntegralBMatching src dst b c q :=
    listed_matching_feasible src dst b c q hq
  have collection (G : Finset A) :
      (∑ e ∈ G, x e) = ∑ q ∈ S, p q * (∑ e ∈ G, (q e : ℝ)) := by
    simp_rw [hcoord, Finset.mul_sum]
    exact Finset.sum_comm
  refine ⟨?_, ?_, ?_⟩
  · intro e
    constructor
    · rw [hcoord]
      exact Finset.sum_nonneg (fun q hq => mul_nonneg (hpos q hq) (Nat.cast_nonneg _))
    · rw [hcoord]
      apply finite_average_bound S p (fun q => (q e : ℝ)) (c e : ℝ) hpos hmass
      intro q hq
      exact_mod_cast (hmatch q hq).1 e
  · intro v
    rw [collection]
    apply finite_average_bound S p (fun q => ∑ e ∈ incidentEdges src dst v, (q e : ℝ))
      (b v : ℝ) hpos hmass
    intro q hq
    exact_mod_cast (hmatch q hq).2 v
  · intro U F hF hodd
    rw [collection, collection, ← Finset.sum_add_distrib]
    simp_rw [← mul_add]
    apply finite_average_bound S p
      (fun q => (∑ e ∈ internalEdges src dst U, (q e : ℝ)) + ∑ e ∈ F, (q e : ℝ))
      ((blossomBudget b c U F / 2 : ℕ) : ℝ) hpos hmass
    intro q hq
    exact_mod_cast integral_blossom_bound src dst hloop b c q (hmatch q hq) U F hF

end Incidence

end TuringTask
