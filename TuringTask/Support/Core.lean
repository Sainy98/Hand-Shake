import Mathlib

namespace TuringTask
namespace Support

def step {V A : Type*}
    (src dst : A → V) (B : Finset A) (u v : V) : Prop :=
  ∃ e ∈ B, src e = u ∧ dst e = v

def Branching {V A : Type*} [DecidableEq V]
    (src dst : A → V) (R : Finset V) (B : Finset A) : Prop :=
  (∀ v : V,
    (B.filter (fun e => dst e = v)).card =
      if v ∈ R then 0 else 1) ∧
  (∀ v : V, ∃ r ∈ R,
    Relation.ReflTransGen (step src dst B) r v)

def allEntering {V A : Type*} [DecidableEq V] [Fintype A]
    (src dst : A → V) (X : Finset V) : Finset A :=
  Finset.univ.filter (fun e => src e ∉ X ∧ dst e ∈ X)

def missingRoots {V : Type*} [DecidableEq V] {k : ℕ}
    (R : Fin k → Finset V) (X : Finset V) : Finset (Fin k) :=
  Finset.univ.filter (fun i => Disjoint (R i) X)

section Auxiliary

variable {V A : Type*} [Fintype V] [DecidableEq V]

def cutArcs (src dst : A → V) (avail : Finset A) (X : Finset V) : Finset A :=
  avail.filter (fun e => src e ∉ X ∧ dst e ∈ X)

def CutOK (src dst : A → V) {k : ℕ}
    (R : Fin k → Finset V) (avail : Finset A) : Prop :=
  ∀ X : Finset V, X.Nonempty →
    (missingRoots R X).card ≤ (cutArcs src dst avail X).card

lemma mem_cutArcs {src dst : A → V} {avail : Finset A}
    {X : Finset V} {e : A} :
    e ∈ cutArcs src dst avail X ↔ e ∈ avail ∧ src e ∉ X ∧ dst e ∈ X := by
  simp [cutArcs]

lemma mem_rootsMissing {k : ℕ} {R : Fin k → Finset V}
    {X : Finset V} {i : Fin k} :
    i ∈ missingRoots R X ↔ Disjoint (R i) X := by
  simp [missingRoots]

lemma cutArcs_mono_avail {src dst : A → V} {a b : Finset A}
    (hab : a ⊆ b) (X : Finset V) :
    cutArcs src dst a X ⊆ cutArcs src dst b X := by
  intro e he
  rw [mem_cutArcs] at he ⊢
  exact ⟨hab he.1, he.2⟩

lemma cut_count_submodular (src dst : A → V) (avail : Finset A)
    (X Y : Finset V) :
    (cutArcs src dst avail (X ∩ Y)).card +
        (cutArcs src dst avail (X ∪ Y)).card ≤
      (cutArcs src dst avail X).card +
        (cutArcs src dst avail Y).card := by
  classical
  simp only [cutArcs, Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e he
  by_cases hsX : src e ∈ X <;>
    by_cases hsY : src e ∈ Y <;>
    by_cases hdX : dst e ∈ X <;>
    by_cases hdY : dst e ∈ Y <;>
    simp [hsX, hsY, hdX, hdY] <;> omega

lemma missing_count_supermodular {k : ℕ} (R : Fin k → Finset V)
    (X Y : Finset V) :
    (missingRoots R X).card + (missingRoots R Y).card ≤
      (missingRoots R (X ∩ Y)).card +
        (missingRoots R (X ∪ Y)).card := by
  classical
  simp only [missingRoots, Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hX : Disjoint (R i) X
  · by_cases hY : Disjoint (R i) Y
    · have hI : Disjoint (R i) (X ∩ Y) := hX.mono_right Finset.inter_subset_left
      have hU : Disjoint (R i) (X ∪ Y) := by simpa using And.intro hX hY
      simp [hX, hY, hI, hU]
    · have hI : Disjoint (R i) (X ∩ Y) := hX.mono_right Finset.inter_subset_left
      have hU : ¬ Disjoint (R i) (X ∪ Y) := by
        intro h
        exact hY (h.mono_right Finset.subset_union_right)
      simp [hX, hY, hI, hU]
  · by_cases hY : Disjoint (R i) Y
    · have hI : Disjoint (R i) (X ∩ Y) := hY.mono_right Finset.inter_subset_right
      have hU : ¬ Disjoint (R i) (X ∪ Y) := by
        intro h
        exact hX (h.mono_right Finset.subset_union_left)
      simp [hX, hY, hI, hU]
    · have hU : ¬ Disjoint (R i) (X ∪ Y) := by
        intro h
        exact hX (h.mono_right Finset.subset_union_left)
      by_cases hI : Disjoint (R i) (X ∩ Y)
      · simp [hX, hY, hI, hU]
      · simp [hX, hY, hI, hU]

lemma missing_count_strict_cross {k : ℕ} (R : Fin k → Finset V)
    (X Y : Finset V) (i : Fin k)
    (hX : ¬ Disjoint (R i) X) (hY : ¬ Disjoint (R i) Y)
    (hI : Disjoint (R i) (X ∩ Y)) :
    (missingRoots R X).card + (missingRoots R Y).card <
      (missingRoots R (X ∩ Y)).card +
        (missingRoots R (X ∪ Y)).card := by
  classical
  simp only [missingRoots, Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_lt_sum
  · intro j hj
    by_cases hXj : Disjoint (R j) X
    · by_cases hYj : Disjoint (R j) Y
      · have hIj : Disjoint (R j) (X ∩ Y) := hXj.mono_right Finset.inter_subset_left
        have hUj : Disjoint (R j) (X ∪ Y) := by simpa using And.intro hXj hYj
        simp [hXj, hYj, hIj, hUj]
      · have hIj : Disjoint (R j) (X ∩ Y) := hXj.mono_right Finset.inter_subset_left
        have hUj : ¬ Disjoint (R j) (X ∪ Y) := by
          intro h
          exact hYj (h.mono_right Finset.subset_union_right)
        simp [hXj, hYj, hIj, hUj]
    · by_cases hYj : Disjoint (R j) Y
      · have hIj : Disjoint (R j) (X ∩ Y) := hYj.mono_right Finset.inter_subset_right
        have hUj : ¬ Disjoint (R j) (X ∪ Y) := by
          intro h
          exact hXj (h.mono_right Finset.subset_union_left)
        simp [hXj, hYj, hIj, hUj]
      · have hUj : ¬ Disjoint (R j) (X ∪ Y) := by
          intro h
          exact hXj (h.mono_right Finset.subset_union_left)
        by_cases hIj : Disjoint (R j) (X ∩ Y)
        · simp [hXj, hYj, hIj, hUj]
        · simp [hXj, hYj, hIj, hUj]
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    have hU : ¬ Disjoint (R i) (X ∪ Y) := by
      intro h
      exact hX (h.mono_right Finset.subset_union_left)
    simp [hX, hY, hI, hU]

lemma uncross_inter_tight (src dst : A → V) {k : ℕ}
    (R : Fin k → Finset V) (avail : Finset A) (hcut : CutOK src dst R avail)
    (X Y : Finset V) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXt : (cutArcs src dst avail X).card = (missingRoots R X).card)
    (hYt : (cutArcs src dst avail Y).card = (missingRoots R Y).card)
    (hIne : (X ∩ Y).Nonempty) (i : Fin k)
    (hiX : ¬ Disjoint (R i) X) (hiY : ¬ Disjoint (R i) Y) :
    (cutArcs src dst avail (X ∩ Y)).card =
        (missingRoots R (X ∩ Y)).card ∧
      ¬ Disjoint (R i) (X ∩ Y) := by
  classical
  have hUne : (X ∪ Y).Nonempty := hXne.mono Finset.subset_union_left
  have hcutI := hcut (X ∩ Y) hIne
  have hcutU := hcut (X ∪ Y) hUne
  have hsub := cut_count_submodular src dst avail X Y
  have hsuper := missing_count_supermodular R X Y
  have hsum_eq :
      (cutArcs src dst avail (X ∩ Y)).card +
          (cutArcs src dst avail (X ∪ Y)).card =
        (missingRoots R (X ∩ Y)).card +
          (missingRoots R (X ∪ Y)).card := by
    omega
  have hiI : ¬ Disjoint (R i) (X ∩ Y) := by
    intro hd
    have hs := missing_count_strict_cross R X Y i hiX hiY hd
    omega
  constructor
  · omega
  · exact hiI

lemma roots_nonempty_of_cut (src dst : A → V) {k : ℕ}
    (R : Fin k → Finset V) (avail : Finset A)
    (hcut : CutOK src dst R avail) (hV : (Finset.univ : Finset V).Nonempty) :
    ∀ i : Fin k, (R i).Nonempty := by
  classical
  have hc := hcut (Finset.univ : Finset V) hV
  have hcut0 : (cutArcs src dst avail (Finset.univ : Finset V)).card = 0 := by
    simp [cutArcs]
  have hm0 : (missingRoots R (Finset.univ : Finset V)).card = 0 := by
    omega
  intro i
  by_contra hRi
  have hRi0 : R i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hRi
  have himem : i ∈ missingRoots R (Finset.univ : Finset V) := by
    rw [mem_rootsMissing]
    simp [hRi0]
  have : missingRoots R (Finset.univ : Finset V) = ∅ := Finset.card_eq_zero.mp hm0
  rw [this] at himem
  exact Finset.notMem_empty i himem

lemma missing_mono_of_shrink_set {k : ℕ} (R : Fin k → Finset V)
    {X Y : Finset V} (hXY : X ⊆ Y) :
    missingRoots R Y ⊆ missingRoots R X := by
  intro i hi
  rw [mem_rootsMissing] at hi ⊢
  exact hi.mono_right hXY

end Auxiliary
end Support
end TuringTask
