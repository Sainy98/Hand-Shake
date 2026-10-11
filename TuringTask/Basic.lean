import Mathlib

open scoped BigOperators
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

def cut {V A : Type*} [DecidableEq V]
    (src dst : A → V) (E : Finset A) (X : Finset V) : Finset A :=
  E.filter (fun e => src e ∉ X ∧ dst e ∈ X)

def CutCondition {V A : Type*} [DecidableEq V] {k : ℕ}
    (src dst : A → V) (E : Finset A) (R : Fin k → Finset V) : Prop :=
  ∀ X : Finset V, X.Nonempty → (rootsMissingSet R X).card ≤ (cut src dst E X).card

def Dangerous {V A : Type*} [DecidableEq V] {k : ℕ}
    (src dst : A → V) (E : Finset A) (R : Fin k → Finset V)
    (i : Fin k) (X : Finset V) : Prop :=
  X.Nonempty ∧ (cut src dst E X).card = (rootsMissingSet R X).card ∧
    ¬ Disjoint (R i) X

variable {V A : Type*} [DecidableEq V] {k : ℕ}

lemma missing_sum (R : Fin k → Finset V) (X : Finset V) :
    (rootsMissingSet R X).card = ∑ i : Fin k, if Disjoint (R i) X then 1 else 0 := by
  classical
  simp only [rootsMissingSet, Finset.card_eq_sum_ones, Finset.sum_filter]

lemma cut_sum (src dst : A → V) (E : Finset A) (X : Finset V) :
    (cut src dst E X).card = ∑ e ∈ E, if src e ∉ X ∧ dst e ∈ X then 1 else 0 := by
  classical
  simp only [cut, Finset.card_eq_sum_ones, Finset.sum_filter]

lemma cut_submodular (src dst : A → V) (E : Finset A) (X Y : Finset V) :
    (cut src dst E (X ∪ Y)).card + (cut src dst E (X ∩ Y)).card ≤
      (cut src dst E X).card + (cut src dst E Y).card := by
  classical
  simp only [cut_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e he
  by_cases h₁ : src e ∈ X <;> by_cases h₂ : src e ∈ Y <;>
    by_cases h₃ : dst e ∈ X <;> by_cases h₄ : dst e ∈ Y <;>
    simp [h₁, h₂, h₃, h₄]

lemma missing_term (Q X Y : Finset V) :
    (if Disjoint Q X then 1 else 0) + (if Disjoint Q Y then 1 else 0) ≤
      (if Disjoint Q (X ∪ Y) then 1 else 0) +
        (if Disjoint Q (X ∩ Y) then 1 else 0 : ℕ) := by
  classical
  have hx : Disjoint Q X → Disjoint Q (X ∩ Y) :=
    fun h => h.mono_right Finset.inter_subset_left
  have hy : Disjoint Q Y → Disjoint Q (X ∩ Y) :=
    fun h => h.mono_right Finset.inter_subset_right
  by_cases hX : Disjoint Q X <;> by_cases hY : Disjoint Q Y <;>
    by_cases hI : Disjoint Q (X ∩ Y) <;>
    simp_all [Finset.disjoint_union_right]

lemma missing_supermodular (R : Fin k → Finset V) (X Y : Finset V) :
    (rootsMissingSet R X).card + (rootsMissingSet R Y).card ≤
      (rootsMissingSet R (X ∪ Y)).card + (rootsMissingSet R (X ∩ Y)).card := by
  classical
  simp only [missing_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => missing_term (R i) X Y

lemma missing_strict (R : Fin k → Finset V) (i : Fin k) (X Y : Finset V)
    (hX : ¬ Disjoint (R i) X) (hY : ¬ Disjoint (R i) Y)
    (hI : Disjoint (R i) (X ∩ Y)) :
    (rootsMissingSet R X).card + (rootsMissingSet R Y).card <
      (rootsMissingSet R (X ∪ Y)).card + (rootsMissingSet R (X ∩ Y)).card := by
  classical
  simp only [missing_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_lt_sum (fun j _ => missing_term (R j) X Y)
  refine ⟨i, Finset.mem_univ _, ?_⟩
  simp [hX, hY, hI, Finset.disjoint_union_right]

lemma dangerous_inter (src dst : A → V) (E : Finset A) (R : Fin k → Finset V)
    (hc : CutCondition src dst E R) (i : Fin k) (X Y : Finset V)
    (hX : Dangerous src dst E R i X) (hY : Dangerous src dst E R i Y)
    (hI : (X ∩ Y).Nonempty) : Dangerous src dst E R i (X ∩ Y) := by
  have hU := hc (X ∪ Y) (hX.1.mono Finset.subset_union_left)
  have hb := hc (X ∩ Y) hI
  have hsub := cut_submodular src dst E X Y
  have hsup := missing_supermodular R X Y
  have heq : (cut src dst E (X ∩ Y)).card = (rootsMissingSet R (X ∩ Y)).card := by
    rw [hX.2.1, hY.2.1] at hsub
    omega
  refine ⟨hI, heq, ?_⟩
  intro hd
  have hstrict := missing_strict R i X Y hX.2.2 hY.2.2 hd
  rw [hX.2.1, hY.2.1] at hsub
  omega

lemma missing_antitone (R : Fin k → Finset V) {X Y : Finset V} (h : X ⊆ Y) :
    rootsMissingSet R Y ⊆ rootsMissingSet R X := by
  intro i hi
  simp only [rootsMissingSet, Finset.mem_filter, Finset.mem_univ, true_and] at *
  exact hi.mono_right h

lemma dangerous_has_arc (src dst : A → V) (E : Finset A) (R : Fin k → Finset V)
    (hc : CutCondition src dst E R) (i : Fin k) (X : Finset V)
    (hX : Dangerous src dst E R i X) (hout : ¬ X ⊆ R i) :
    ∃ e ∈ E, src e ∈ R i ∧ src e ∈ X ∧ dst e ∈ X ∧ dst e ∉ R i := by
  classical
  by_contra! hn
  have hne : (X \ R i).Nonempty := by
    simpa [Finset.sdiff_nonempty] using hout
  have hcut : cut src dst E (X \ R i) ⊆ cut src dst E X := by
    intro e he
    simp only [cut, Finset.mem_filter, Finset.mem_sdiff] at *
    refine ⟨he.1, ?_, he.2.2.1⟩
    intro hs
    have hr : src e ∈ R i := by
      by_contra hr
      exact he.2.1 ⟨hs, hr⟩
    exact hn e he.1 hr hs he.2.2.1 he.2.2.2
  have hmiss : rootsMissingSet R X ⊂ rootsMissingSet R (X \ R i) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨missing_antitone R Finset.sdiff_subset, ?_⟩
    intro heq
    have hi : i ∈ rootsMissingSet R (X \ R i) := by
      simp [rootsMissingSet, Finset.disjoint_sdiff_right]
    have hi' : i ∈ rootsMissingSet R X := heq.symm ▸ hi
    exact hX.2.2 (by simpa [rootsMissingSet] using hi')
  have hlt := Finset.card_lt_card hmiss
  have hle := Finset.card_le_card hcut
  have hcond := hc (X \ R i) hne
  rw [hX.2.1] at hle
  omega

lemma safe_arc_in_danger (src dst : A → V) (E : Finset A) (R : Fin k → Finset V)
    (hc : CutCondition src dst E R) (i : Fin k) (X : Finset V)
    (hX : Dangerous src dst E R i X) (hout : ¬ X ⊆ R i) :
    ∃ e ∈ E, src e ∈ R i ∧ dst e ∉ R i ∧
      ∀ Y : Finset V, Dangerous src dst E R i Y →
        ¬ (src e ∉ Y ∧ dst e ∈ Y) := by
  classical
  revert hX hout
  induction X using Finset.strongInductionOn with
  | h X ih =>
    intro hX hout
    obtain ⟨e, he, hsR, hsX, hdX, hdR⟩ := dangerous_has_arc src dst E R hc i X hX hout
    by_cases hsafe : ∀ Y : Finset V, Dangerous src dst E R i Y →
        ¬ (src e ∉ Y ∧ dst e ∈ Y)
    · exact ⟨e, he, hsR, hdR, hsafe⟩
    · push_neg at hsafe
      obtain ⟨Y, hY, hsY, hdY⟩ := hsafe
      have hI := dangerous_inter src dst E R hc i X Y hX hY
        ⟨dst e, Finset.mem_inter.mpr ⟨hdX, hdY⟩⟩
      have hlt : X ∩ Y ⊂ X := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.inter_subset_left, ?_⟩
        intro heq
        have : src e ∈ X ∩ Y := heq.symm ▸ hsX
        exact hsY (Finset.mem_inter.mp this).2
      exact ih (X ∩ Y) hlt hI (fun h => hdR (h (Finset.mem_inter.mpr ⟨hdX, hdY⟩)))

lemma safe_arc [Fintype V] (src dst : A → V) (E : Finset A)
    (R : Fin k → Finset V) (hc : CutCondition src dst E R)
    (i : Fin k) (v : V) (hv : v ∉ R i) :
    ∃ e ∈ E, src e ∈ R i ∧ dst e ∉ R i ∧
      ∀ Y : Finset V, Dangerous src dst E R i Y →
        ¬ (src e ∉ Y ∧ dst e ∈ Y) := by
  classical
  have hcut : cut src dst E Finset.univ = ∅ := by
    simp [cut]
  have hcond := hc Finset.univ ⟨v, Finset.mem_univ _⟩
  have hzero : rootsMissingSet R Finset.univ = ∅ :=
    Finset.card_eq_zero.mp (by simpa [hcut] using hcond)
  have hdis : ¬ Disjoint (R i) Finset.univ := by
    intro hd
    have : i ∈ rootsMissingSet R Finset.univ := by simp [rootsMissingSet, hd]
    simpa [hzero] using this
  apply safe_arc_in_danger src dst E R hc i Finset.univ
  · exact ⟨⟨v, Finset.mem_univ _⟩, by simp [hcut, hzero], hdis⟩
  · exact fun h => hv (h (Finset.mem_univ v))

def growRoots (R : Fin k → Finset V) (i : Fin k) (v : V) : Fin k → Finset V :=
  Function.update R i (insert v (R i))

lemma grow_missing (R : Fin k → Finset V) (i : Fin k) (v : V) (X : Finset V) :
    rootsMissingSet (growRoots R i v) X =
      if v ∈ X then (rootsMissingSet R X).erase i else rootsMissingSet R X := by
  classical
  ext j
  by_cases hv : v ∈ X <;> by_cases hji : j = i
  all_goals simp [rootsMissingSet, growRoots, hv, hji, Finset.disjoint_insert_left]

lemma cut_erase (src dst : A → V) (E : Finset A) (e : A) (X : Finset V) :
    cut src dst (E.erase e) X = (cut src dst E X).erase e := by
  classical
  ext a
  simp [cut, and_assoc, and_left_comm, and_comm]

lemma grow_preserves_cut (src dst : A → V) (E : Finset A) (R : Fin k → Finset V)
    (hc : CutCondition src dst E R) (i : Fin k) (e : A)
    (hsafe : ∀ Y : Finset V, Dangerous src dst E R i Y →
      ¬ (src e ∉ Y ∧ dst e ∈ Y)) :
    CutCondition src dst (E.erase e) (growRoots R i (dst e)) := by
  classical
  intro X hX
  have h := hc X hX
  rw [cut_erase, grow_missing]
  by_cases he : e ∈ cut src dst E X
  · have he' := Finset.mem_filter.mp he
    change e ∈ E ∧ src e ∉ X ∧ dst e ∈ X at he'
    rw [if_pos he'.2.2]
    by_cases hi : i ∈ rootsMissingSet R X
    · rw [Finset.card_erase_of_mem hi, Finset.card_erase_of_mem he]
      omega
    · rw [Finset.erase_eq_of_notMem hi, Finset.card_erase_of_mem he]
      have hne : (cut src dst E X).card ≠ (rootsMissingSet R X).card := by
        intro heq
        have hd : ¬ Disjoint (R i) X := by simpa [rootsMissingSet] using hi
        exact hsafe X ⟨hX, heq, hd⟩ he'.2
      omega
  · rw [Finset.erase_eq_of_notMem he]
    split_ifs
    · exact le_trans (Finset.card_le_card (Finset.erase_subset _ _)) h
    · exact h

lemma step_mono (src dst : A → V) {B C : Finset A} (h : B ⊆ C) :
    selectedArcStep src dst B ≤ selectedArcStep src dst C := by
  rintro u v ⟨e, he, hs, hd⟩
  exact ⟨e, h he, hs, hd⟩

lemma branching_add_arc (src dst : A → V) (R : Finset V) (B : Finset A) (e : A)
    (hB : IsSpanningBranching src dst (insert (dst e) R) B)
    (hs : src e ∈ R) (hd : dst e ∉ R) (he : e ∉ B) :
    IsSpanningBranching src dst R (insert e B) := by
  classical
  constructor
  · intro v
    by_cases hv : v = dst e
    · subst v
      have hzero : (B.filter (fun a => dst a = dst e)).card = 0 := by
        simpa using hB.1 (dst e)
      simp [Finset.filter_insert, he, hzero, hd]
    · have hne : dst e ≠ v := Ne.symm hv
      simpa [Finset.filter_insert, hne, hv] using hB.1 v
  · intro v
    obtain ⟨r, hr, hp⟩ := hB.2 v
    have hp' := hp.mono (step_mono src dst (Finset.subset_insert e B))
    obtain hr | hr := Finset.mem_insert.mp hr
    · subst r
      refine ⟨src e, hs, (Relation.ReflTransGen.single ?_).trans hp'⟩
      exact ⟨e, Finset.mem_insert_self _ _, rfl, rfl⟩
    · exact ⟨r, hr, hp'⟩

lemma packing_from_cut [Fintype V] (src dst : A → V) (E : Finset A)
    (R : Fin k → Finset V) (hc : CutCondition src dst E R) :
    ∃ B : Fin k → Finset A,
      (∀ i, B i ⊆ E) ∧
      (∀ i, IsSpanningBranching src dst (R i) (B i)) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) := by
  classical
  revert R
  induction E using Finset.strongInductionOn with
  | h E ih =>
    intro R hc
    by_cases hfull : ∀ i : Fin k, ∀ v : V, v ∈ R i
    · refine ⟨fun _ => ∅, fun _ => Finset.empty_subset _, ?_, ?_⟩
      · intro i
        refine ⟨fun v => by simp [hfull i v], fun v => ⟨v, hfull i v, .refl⟩⟩
      · simp
    · push_neg at hfull
      obtain ⟨i, v, hv⟩ := hfull
      obtain ⟨e, he, hs, hd, hsafe⟩ := safe_arc src dst E R hc i v hv
      have hc' := grow_preserves_cut src dst E R hc i e hsafe
      obtain ⟨B, hsub, hbranch, hdis⟩ := ih (E.erase e) (Finset.erase_ssubset he)
        (growRoots R i (dst e)) hc'
      have hnot (j : Fin k) : e ∉ B j := by
        intro h
        exact (Finset.mem_erase.mp (hsub j h)).1 rfl
      refine ⟨Function.update B i (insert e (B i)), ?_, ?_, ?_⟩
      · intro j
        by_cases hj : j = i
        · subst j
          simp only [Function.update_same]
          exact Finset.insert_subset he (fun a ha => Finset.mem_of_mem_erase (hsub i ha))
        · simp only [Function.update_noteq hj]
          exact fun a ha => Finset.mem_of_mem_erase (hsub j ha)
      · intro j
        by_cases hj : j = i
        · subst j
          simp only [Function.update_same]
          apply branching_add_arc src dst (R i) (B i) e
          · simpa [growRoots] using hbranch i
          · exact hs
          · exact hd
          · exact hnot i
        · simpa [Function.update_noteq hj, growRoots, hj] using hbranch j
      · intro j l hjl
        by_cases hj : j = i <;> by_cases hl : l = i
        · exact False.elim (hjl (hj.trans hl.symm))
        · subst j
          simp only [Function.update_same, Function.update_noteq hl]
          exact Finset.disjoint_insert_left.mpr ⟨hnot l, hdis i l hjl⟩
        · subst l
          simp only [Function.update_same, Function.update_noteq hj]
          exact Finset.disjoint_insert_right.mpr ⟨hnot j, hdis j i hjl⟩
        · simpa only [Function.update_noteq hj, Function.update_noteq hl] using hdis j l hjl

lemma path_crosses (src dst : A → V) (B : Finset A) (X : Finset V)
    {r v : V} (hp : Relation.ReflTransGen (selectedArcStep src dst B) r v)
    (hr : r ∉ X) (hv : v ∈ X) :
    ∃ e ∈ B, src e ∉ X ∧ dst e ∈ X := by
  revert hv
  induction hp with
  | refl => exact fun hv => False.elim (hr hv)
  | @tail u v hp hstep ih =>
    intro hv
    by_cases hu : u ∈ X
    · exact ih hu
    · obtain ⟨e, he, hs, hd⟩ := hstep
      exact ⟨e, he, hs ▸ hu, hd ▸ hv⟩

lemma packing_implies_cut [Fintype A] (src dst : A → V)
    (R : Fin k → Finset V) (B : Fin k → Finset A)
    (hb : ∀ i, IsSpanningBranching src dst (R i) (B i))
    (hd : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (X : Finset V) (hX : X.Nonempty) :
    (rootsMissingSet R X).card ≤ (enteringArcs src dst X).card := by
  classical
  obtain ⟨v, hv⟩ := hX
  have hex (i : ↥(rootsMissingSet R X)) :
      ∃ e ∈ B i, src e ∉ X ∧ dst e ∈ X := by
    have hi : Disjoint (R i) X := by simpa [rootsMissingSet] using i.property
    obtain ⟨r, hr, hp⟩ := (hb i).2 v
    exact path_crosses src dst (B i) X hp (fun h => Finset.disjoint_left.mp hi hr h) hv
  choose f hfB hfX using hex
  let g : ↥(rootsMissingSet R X) → ↥(enteringArcs src dst X) :=
    fun i => ⟨f i, by simp [enteringArcs, hfX i]⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hf : f i = f j := congrArg Subtype.val hij
    exact Finset.disjoint_left.mp (hd i j hne) (hfB i) (hf ▸ hfB j)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective g hg

theorem prescribed_root_branching_packing
    {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A]
    (src dst : A → V)
    (k : ℕ) (R : Fin k → Finset V) :
    (∃ B : Fin k → Finset A,
      (∀ i : Fin k, IsSpanningBranching src dst (R i) (B i)) ∧
      (∀ i j : Fin k, i ≠ j → Disjoint (B i) (B j))) ↔
    (∀ X : Finset V, X.Nonempty →
      (rootsMissingSet R X).card ≤ (enteringArcs src dst X).card) := by
  classical
  constructor
  · rintro ⟨B, hb, hd⟩ X hX
    exact packing_implies_cut src dst R B hb hd X hX
  · intro hc
    have hc' : CutCondition src dst Finset.univ R := hc
    obtain ⟨B, _, hb, hd⟩ := packing_from_cut src dst Finset.univ R hc'
    exact ⟨B, hb, hd⟩

end TuringTask
