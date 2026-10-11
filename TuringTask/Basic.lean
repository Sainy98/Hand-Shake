import TuringTask.Support.Main

namespace TuringTask

def selectedArcStep {V A : Type*}
    (src dst : A → V) (B : Finset A) (u v : V) : Prop :=
  ∃ e ∈ B, src e = u ∧ dst e = v

def IsSpanningBranching {V A : Type*} [DecidableEq V]
    (src dst : A → V) (R : Finset V) (B : Finset A) : Prop :=
  (∀ v : V,
    (B.filter (fun e => dst e = v)).card =
      if v ∈ R then 0 else 1) ∧
  (∀ v : V, ∃ r ∈ R,
    Relation.ReflTransGen (selectedArcStep src dst B) r v)

def enteringArcs {V A : Type*} [DecidableEq V] [Fintype A]
    (src dst : A → V) (X : Finset V) : Finset A :=
  Finset.univ.filter (fun e => src e ∉ X ∧ dst e ∈ X)

def rootsMissingSet {V : Type*} [DecidableEq V] {k : ℕ}
    (R : Fin k → Finset V) (X : Finset V) : Finset (Fin k) :=
  Finset.univ.filter (fun i => Disjoint (R i) X)

theorem prescribed_root_branching_packing
    {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A]
    (src dst : A → V)
    (k : ℕ) (R : Fin k → Finset V) :
    (∃ B : Fin k → Finset A,
      (∀ i : Fin k, IsSpanningBranching src dst (R i) (B i)) ∧
      (∀ i j : Fin k, i ≠ j → Disjoint (B i) (B j))) ↔
    (∀ X : Finset V, X.Nonempty →
      (rootsMissingSet R X).card ≤ (enteringArcs src dst X).card) := by
  simpa [IsSpanningBranching, selectedArcStep, enteringArcs, rootsMissingSet,
    Support.Branching, Support.step, Support.allEntering, Support.missingRoots] using
    (Support.packing_iff_cut (V := V) (A := A) src dst k R)

end TuringTask
