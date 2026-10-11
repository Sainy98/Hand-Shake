import TuringTask.Support.Core

namespace TuringTask
namespace Support

section Auxiliary

variable {V A : Type*} [Fintype V] [DecidableEq V]

lemma path_crosses_cut (src dst : A → V) (B : Finset A)
    (X : Finset V) {u v : V}
    (hp : Relation.ReflTransGen (step src dst B) u v)
    (hu : u ∉ X) (hv : v ∈ X) :
    ∃ e ∈ B, src e ∉ X ∧ dst e ∈ X := by
  induction hp with
  | refl => exact (hu hv).elim
  | tail hp hstep ih =>
      rcases hstep with ⟨e, heB, hsrc, hdst⟩
      by_cases hm : _ ∈ X
      · exact ih hu hm
      · refine ⟨e, heB, ?_, ?_⟩
        · simpa [hsrc] using hm
        · simpa [hdst] using hv

lemma branching_hits_cut (src dst : A → V)
    (R : Finset V) (B : Finset A) (X : Finset V)
    (hB : Branching src dst R B)
    (hX : X.Nonempty) (hmiss : Disjoint R X) :
    ∃ e ∈ B, src e ∉ X ∧ dst e ∈ X := by
  obtain ⟨v, hv⟩ := hX
  obtain ⟨r, hr, hp⟩ := hB.2 v
  have hrout : r ∉ X := by
    exact Finset.disjoint_left.mp hmiss hr
  exact path_crosses_cut src dst B X hp hrout hv

lemma packing_implies_cut (src dst : A → V) {k : ℕ}
    (R : Fin k → Finset V) (B : Fin k → Finset A)
    (hbranch : ∀ i, Branching src dst (R i) (B i))
    (hdis : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (X : Finset V) (hX : X.Nonempty) :
    (missingRoots R X).card ≤ (allEntering src dst X).card := by
  classical
  let chooseArc : (i : Fin k) → i ∈ missingRoots R X → A :=
    fun i hi => Classical.choose
      (branching_hits_cut src dst (R i) (B i) X (hbranch i) hX
        (by simpa [mem_rootsMissing] using hi))
  have chooseArc_spec : ∀ (i : Fin k) (hi : i ∈ missingRoots R X),
      chooseArc i hi ∈ B i ∧ chooseArc i hi ∈ allEntering src dst X := by
    intro i hi
    have hs := Classical.choose_spec
      (branching_hits_cut src dst (R i) (B i) X (hbranch i) hX
        (by simpa [mem_rootsMissing] using hi))
    refine ⟨hs.1, ?_⟩
    simp [allEntering, hs.2.1, hs.2.2]
  let f : ↥(missingRoots R X) → ↥(allEntering src dst X) :=
    fun i => ⟨chooseArc i i.property, (chooseArc_spec i i.property).2⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hval : chooseArc i i.property = chooseArc j j.property :=
      congrArg Subtype.val hij
    have hiB := (chooseArc_spec i i.property).1
    have hjB := (chooseArc_spec j j.property).1
    have hd := hdis i j (by simpa using hne)
    exact (Finset.disjoint_left.mp hd) hiB (hval ▸ hjB)
  simpa using Fintype.card_le_of_injective f hf

end Auxiliary
end Support
end TuringTask
