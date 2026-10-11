import TuringTask.Basic

example {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A]
    (src dst : A → V) (k : ℕ) (R : Fin k → Finset V) :
    (∃ B : Fin k → Finset A,
      (∀ i : Fin k, TuringTask.IsSpanningBranching src dst (R i) (B i)) ∧
      (∀ i j : Fin k, i ≠ j → Disjoint (B i) (B j))) ↔
    (∀ X : Finset V, X.Nonempty →
      (TuringTask.rootsMissingSet R X).card ≤ (TuringTask.enteringArcs src dst X).card) :=
  TuringTask.prescribed_root_branching_packing src dst k R

#print TuringTask.prescribed_root_branching_packing
#print axioms TuringTask.prescribed_root_branching_packing
