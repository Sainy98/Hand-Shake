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

end Incidence

end TuringTask
