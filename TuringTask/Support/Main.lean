import TuringTask.Support.Safe
import TuringTask.Support.Necessity

namespace TuringTask
namespace Support

theorem packing_iff_cut
    {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A]
    (src dst : A → V)
    (k : ℕ) (R : Fin k → Finset V) :
    (∃ B : Fin k → Finset A,
      (∀ i : Fin k, Branching src dst (R i) (B i)) ∧
      (∀ i j : Fin k, i ≠ j → Disjoint (B i) (B j))) ↔
    (∀ X : Finset V, X.Nonempty →
      (missingRoots R X).card ≤ (allEntering src dst X).card) := by
  classical
  constructor
  · rintro ⟨B, hbranch, hdis⟩ X hX
    exact packing_implies_cut src dst R B hbranch hdis X hX
  · intro hcut
    have hcut' : CutOK src dst R (Finset.univ : Finset A) := by
      intro X hX
      simpa [cutArcs, allEntering] using hcut X hX
    obtain ⟨B, hsub, hbranch, hdis⟩ :=
      packing_from_cut (V := V) (A := A) src dst R (Finset.univ : Finset A) hcut'
    exact ⟨B, hbranch, hdis⟩

end Support
end TuringTask
