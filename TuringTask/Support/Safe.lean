import TuringTask.Support.Core

namespace TuringTask
namespace Support

section Auxiliary

variable {V A : Type*} [Fintype V] [DecidableEq V]

lemma exists_safe_root_arc (src dst : A → V) {k : ℕ}
    (R : Fin k → Finset V) (avail : Finset A)
    (hcut : CutOK src dst R avail) (i : Fin k)
    (hi : R i ≠ (Finset.univ : Finset V)) :
    ∃ e ∈ avail,
      src e ∈ R i ∧ dst e ∉ R i ∧
      CutOK src dst
        (Function.update R i (insert (dst e) (R i))) (avail.erase e) := by
  classical
  have hvout : ∃ v : V, v ∉ R i := by
    by_contra h
    push_neg at h
    apply hi
    ext v
    simp [h v]
  obtain ⟨v0, hv0⟩ := hvout
  have hV : (Finset.univ : Finset V).Nonempty := ⟨v0, Finset.mem_univ _⟩
  have hRne := roots_nonempty_of_cut src dst R avail hcut hV

  let fam : Finset (Finset V) :=
    (Finset.univ : Finset (Finset V)).filter (fun Y =>
      (cutArcs src dst avail Y).card = (missingRoots R Y).card ∧
      (Y ∩ R i).Nonempty ∧ ¬ Y ⊆ R i)

  have huniv_tight :
      (cutArcs src dst avail (Finset.univ : Finset V)).card =
        (missingRoots R (Finset.univ : Finset V)).card := by
    have hc := hcut (Finset.univ : Finset V) hV
    have hleft : (cutArcs src dst avail (Finset.univ : Finset V)).card = 0 := by
      simp [cutArcs]
    have hright : (missingRoots R (Finset.univ : Finset V)).card = 0 := by
      have : missingRoots R (Finset.univ : Finset V) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        rw [mem_rootsMissing] at hj
        exact (hj.notMem_of_mem_right (Finset.mem_univ (Classical.choose (hRne j))))
          (Classical.choose_spec (hRne j))
      simp [this]
    omega

  have hfam : fam.Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    simp only [fam, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨huniv_tight, ?_, ?_⟩
    · simpa using hRne i
    · intro hsub
      exact hv0 (hsub (Finset.mem_univ v0))

  obtain ⟨Y, hYfam, hYmin⟩ := fam.exists_min_image Finset.card hfam
  have hYdata :
      (cutArcs src dst avail Y).card = (missingRoots R Y).card ∧
      (Y ∩ R i).Nonempty ∧ ¬ Y ⊆ R i := by
    simpa [fam] using hYfam
  rcases hYdata with ⟨hYtight, hYroot, hYnot⟩
  have hYne : Y.Nonempty := hYroot.mono Finset.inter_subset_left

  have houtside : (Y \ R i).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hz
    apply hYnot
    intro y hy
    by_contra hyr
    have : y ∈ Y \ R i := by simp [hy, hyr]
    simpa [hz] using this

  have hmissStrict :
      (missingRoots R Y).card < (missingRoots R (Y \ R i)).card := by
    have hsub : missingRoots R Y ⊆ missingRoots R (Y \ R i) :=
      missing_mono_of_shrink_set R Finset.sdiff_subset
    have hiSmall : i ∈ missingRoots R (Y \ R i) := by
      rw [mem_rootsMissing, Finset.disjoint_left]
      intro x hxR hxDiff
      exact hxDiff.2 hxR
    have hiBig : i ∉ missingRoots R Y := by
      rw [mem_rootsMissing]
      exact fun hd => hYroot.not_disjoint hd.symm
    exact Finset.card_lt_card (Finset.ssubset_iff_of_subset hsub |>.2 ⟨i, hiSmall, hiBig⟩)

  have hcutOutside := hcut (Y \ R i) houtside
  have hcutYtoOutside :
      ¬ cutArcs src dst avail (Y \ R i) ⊆ cutArcs src dst avail Y := by
    intro hsub
    have hc := Finset.card_le_card hsub
    omega
  obtain ⟨e, heOut, heNotY⟩ := Finset.not_subset.mp hcutYtoOutside
  have heOut' := (mem_cutArcs.mp heOut)
  have heAvail : e ∈ avail := heOut'.1
  have heDstDiff : dst e ∈ Y \ R i := heOut'.2.2
  have heDstY : dst e ∈ Y := heDstDiff.1
  have heDstR : dst e ∉ R i := heDstDiff.2
  have heSrcNotDiff : src e ∉ Y \ R i := heOut'.2.1
  have heNotY' : ¬ (src e ∉ Y ∧ dst e ∈ Y) := by
    intro h
    exact heNotY (mem_cutArcs.mpr ⟨heAvail, h⟩)
  have heSrcY : src e ∈ Y := by
    by_contra h
    exact heNotY' ⟨h, heDstY⟩
  have heSrcR : src e ∈ R i := by
    by_contra h
    exact heSrcNotDiff (by simp [heSrcY, h])

  refine ⟨e, heAvail, heSrcR, heDstR, ?_⟩
  intro X hXne
  let R' := Function.update R i (insert (dst e) (R i))
  have hmissSub : missingRoots R' X ⊆ missingRoots R X := by
    intro j hj
    rw [mem_rootsMissing] at hj ⊢
    by_cases hji : j = i
    · subst j
      simpa [R', Function.update_same] using
        hj.mono_left (by intro x hx; exact Finset.mem_insert_of_mem hx)
    · simpa [R', Function.update_noteq hji] using hj

  by_cases heX : e ∈ cutArcs src dst avail X
  · have heXdata := mem_cutArcs.mp heX
    have hsrcX : src e ∉ X := heXdata.2.1
    have hdstX : dst e ∈ X := heXdata.2.2
    have hcutEraseEq :
        cutArcs src dst (avail.erase e) X = (cutArcs src dst avail X).erase e := by
      ext a
      simp [cutArcs, and_assoc, and_left_comm, and_comm]
    have hcardCutErase :
        (cutArcs src dst (avail.erase e) X).card + 1 =
          (cutArcs src dst avail X).card := by
      rw [hcutEraseEq, Finset.card_erase_of_mem heX]

    by_cases hRiX : Disjoint (R i) X
    · have hiOld : i ∈ missingRoots R X := by simpa [mem_rootsMissing]
      have hmissEq : missingRoots R' X = (missingRoots R X).erase i := by
        ext j
        by_cases hji : j = i
        · subst j
          simp [R', missingRoots, hRiX, hdstX]
        · simp [R', missingRoots, hji]
      have hcardMiss :
          (missingRoots R' X).card + 1 = (missingRoots R X).card := by
        rw [hmissEq, Finset.card_erase_of_mem hiOld]
      have hc := hcut X hXne
      omega
    · have hmissEq : missingRoots R' X = missingRoots R X := by
        ext j
        by_cases hji : j = i
        · subst j
          simp [R', missingRoots, hRiX]
        · simp [R', missingRoots, hji]
      have hc := hcut X hXne
      have hstrict : (missingRoots R X).card < (cutArcs src dst avail X).card := by
        by_contra hnot
        have htight : (cutArcs src dst avail X).card = (missingRoots R X).card := by
          omega
        have hrootX : (X ∩ R i).Nonempty := by
          simpa [Finset.not_disjoint_iff_nonempty_inter] using hRiX
        have hnotSub : ¬ X ⊆ R i := by
          intro hsub
          exact heDstR (hsub hdstX)
        have hXfam : X ∈ fam := by
          simp [fam, htight, hrootX, hnotSub]
        have hIXne : (Y ∩ X).Nonempty := by
          refine ⟨dst e, ?_⟩
          simp [heDstY, hdstX]
        have hrootY : ¬ Disjoint (R i) Y := by
          exact fun hd => hYroot.not_disjoint hd.symm
        have hrootX' : ¬ Disjoint (R i) X := hRiX
        obtain ⟨hItight, hrootI⟩ :=
          uncross_inter_tight src dst R avail hcut Y X hYne hXne
            hYtight htight hIXne i hrootY hrootX'
        have hIfam : Y ∩ X ∈ fam := by
          simp only [fam, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨hItight, ?_, ?_⟩
          · simpa [Finset.inter_assoc, Finset.inter_left_comm, Finset.inter_comm,
              Finset.not_disjoint_iff_nonempty_inter] using hrootI
          · intro hsub
            exact heDstR (hsub (by simp [heDstY, hdstX]))
        have hproper : Y ∩ X ⊂ Y := by
          rw [Finset.ssubset_iff_of_subset Finset.inter_subset_left]
          refine ⟨src e, heSrcY, ?_⟩
          simp [hsrcX]
        have hlt := Finset.card_lt_card hproper
        have hmin := hYmin (Y ∩ X) hIfam
        omega
      rw [hmissEq]
      omega
  · have hcutSame : cutArcs src dst (avail.erase e) X = cutArcs src dst avail X := by
      ext a
      by_cases hae : a = e
      · subst a
        simp [cutArcs, heX]
      · simp [cutArcs, hae]
    have hc := hcut X hXne
    have hm := Finset.card_le_card hmissSub
    rw [hcutSame]
    exact hm.trans hc

def rootDeficit {k : ℕ} (R : Fin k → Finset V) : ℕ :=
  ∑ i, ((Finset.univ : Finset V) \ R i).card

lemma rootDeficit_grow {k : ℕ} (R : Fin k → Finset V)
    (i : Fin k) (v : V) (hv : v ∉ R i) :
    rootDeficit (Function.update R i (insert v (R i))) < rootDeficit R := by
  classical
  simp only [rootDeficit]
  apply Finset.sum_lt_sum
  · intro j hj
    by_cases hji : j = i
    · subst j
      simp only [Function.update_same]
      exact Finset.card_le_card (by
        intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx ⊢
        exact fun h => hx (Finset.mem_insert_of_mem h))
    · simp [Function.update_noteq hji]
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    simp only [Function.update_same]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨v, ?_, ?_⟩
      · simp [hv]
      · simp
    · intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx ⊢
      exact fun h => hx (Finset.mem_insert_of_mem h)

lemma add_arc_to_extra_root (src dst : A → V)
    (R : Finset V) (B : Finset A) (e : A)
    (heB : e ∉ B) (hsrc : src e ∈ R) (hdst : dst e ∉ R)
    (hB : Branching src dst (insert (dst e) R) B) :
    Branching src dst R (insert e B) := by
  classical
  constructor
  · intro v
    by_cases hv : v = dst e
    · subst v
      have hzero := hB.1 (dst e)
      simp [heB, hdst] at hzero ⊢
      exact hzero
    · have hold := hB.1 v
      have hins : (v ∈ insert (dst e) R) ↔ v ∈ R := by simp [hv]
      simpa [hv, heB, hins] using hold
  · intro v
    obtain ⟨r, hr, hp⟩ := hB.2 v
    have hmono :
        Relation.ReflTransGen (step src dst B) r v →
          Relation.ReflTransGen (step src dst (insert e B)) r v :=
      Relation.ReflTransGen.mono (by
        intro a b hab
        rcases hab with ⟨f, hf, hfa, hfb⟩
        exact ⟨f, Finset.mem_insert_of_mem hf, hfa, hfb⟩)
    rcases Finset.mem_insert.mp hr with hr | hr
    · subst r
      refine ⟨src e, hsrc, ?_⟩
      apply Relation.ReflTransGen.head
      · exact ⟨e, Finset.mem_insert_self _ _, rfl, rfl⟩
      · exact hmono hp
    · exact ⟨r, hr, hmono hp⟩

lemma branching_univ_empty (src dst : A → V) :
    Branching src dst (Finset.univ : Finset V) (∅ : Finset A) := by
  classical
  constructor
  · intro v
    simp
  · intro v
    exact ⟨v, Finset.mem_univ v, Relation.ReflTransGen.refl⟩

lemma packing_from_cut (src dst : A → V) {k : ℕ}
    (R : Fin k → Finset V) (avail : Finset A)
    (hcut : CutOK src dst R avail) :
    ∃ B : Fin k → Finset A,
      (∀ i, B i ⊆ avail) ∧
      (∀ i, Branching src dst (R i) (B i)) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) := by
  classical
  let Goal : ℕ → Prop := fun n =>
    ∀ (R : Fin k → Finset V) (avail : Finset A),
      rootDeficit R = n → CutOK src dst R avail →
      ∃ B : Fin k → Finset A,
        (∀ i, B i ⊆ avail) ∧
        (∀ i, Branching src dst (R i) (B i)) ∧
        (∀ i j, i ≠ j → Disjoint (B i) (B j))
  have build : ∀ n, Goal n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro R0 avail0 hdef hcut0
      by_cases hn : n = 0
      · have hsum0 : rootDeficit R0 = 0 := hdef.trans hn
        have hall : ∀ i : Fin k, R0 i = (Finset.univ : Finset V) := by
          intro i
          have hterms : ∀ j ∈ (Finset.univ : Finset (Fin k)),
              ((Finset.univ : Finset V) \ R0 j).card = 0 := by
            apply (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp
            simpa [rootDeficit] using hsum0
          have hz := hterms i (Finset.mem_univ i)
          have hempty : (Finset.univ : Finset V) \ R0 i = ∅ := Finset.card_eq_zero.mp hz
          ext v
          constructor
          · intro hv
            simp
          · intro hv
            by_contra hvr
            have : v ∈ (Finset.univ : Finset V) \ R0 i := by simp [hvr]
            rw [hempty] at this
            exact Finset.notMem_empty v this
        refine ⟨fun _ => ∅, ?_, ?_, ?_⟩
        · intro i x hx
          exact Finset.notMem_empty x hx
        · intro i
          simpa [hall i] using branching_univ_empty (V := V) (A := A) src dst
        · intro i j hij
          simp
      · have hex : ∃ i : Fin k, R0 i ≠ (Finset.univ : Finset V) := by
          by_contra hnone
          push_neg at hnone
          have hz : rootDeficit R0 = 0 := by
            simp [rootDeficit, hnone]
          omega
        obtain ⟨i, hi⟩ := hex
        obtain ⟨e, heAvail, heSrc, heDst, hcut1⟩ :=
          exists_safe_root_arc src dst R0 avail0 hcut0 i hi
        let R1 := Function.update R0 i (insert (dst e) (R0 i))
        have hdec : rootDeficit R1 < n := by
          rw [← hdef]
          exact rootDeficit_grow R0 i (dst e) heDst
        obtain ⟨B, hBavail, hBbranch, hBdis⟩ :=
          ih (rootDeficit R1) hdec R1 (avail0.erase e) rfl hcut1
        let B1 : Fin k → Finset A := Function.update B i (insert e (B i))
        refine ⟨B1, ?_, ?_, ?_⟩
        · intro j
          by_cases hji : j = i
          · subst j
            intro a ha
            simp only [B1, Function.update_same] at ha
            rcases Finset.mem_insert.mp ha with rfl | ha
            · exact heAvail
            · exact Finset.mem_of_mem_erase (hBavail i ha)
          · simpa [B1, Function.update_noteq hji] using
              (fun a ha => Finset.mem_of_mem_erase (hBavail j ha))
        · intro j
          by_cases hji : j = i
          · subst j
            have heNotB : e ∉ B i := by
              intro he
              exact (Finset.notMem_erase e avail0) (hBavail i he)
            have hroot : R1 i = insert (dst e) (R0 i) := by simp [R1]
            have hb := hBbranch i
            rw [hroot] at hb
            simpa [B1] using
              add_arc_to_extra_root src dst (R0 i) (B i) e heNotB heSrc heDst hb
          · have hroot : R1 j = R0 j := by simp [R1, Function.update_noteq hji]
            have hb := hBbranch j
            rw [hroot] at hb
            simpa [B1, Function.update_noteq hji] using hb
        · intro p q hpq
          by_cases hpi : p = i
          · subst p
            have hqi : q ≠ i := by exact fun h => hpq h
            rw [show B1 i = insert e (B i) by simp [B1],
              show B1 q = B q by simp [B1, Function.update_noteq hqi]]
            rw [Finset.disjoint_left]
            intro a ha haq
            rcases Finset.mem_insert.mp ha with rfl | ha
            · exact (Finset.notMem_erase e avail0) (hBavail q haq)
            · exact (Finset.disjoint_left.mp (hBdis i q hpq)) ha haq
          · by_cases hqi : q = i
            · subst q
              have hip : i ≠ p := Ne.symm hpi
              rw [show B1 p = B p by simp [B1, Function.update_noteq hpi],
                show B1 i = insert e (B i) by simp [B1]]
              rw [Finset.disjoint_left]
              intro a hap ha
              rcases Finset.mem_insert.mp ha with rfl | hai
              · exact (Finset.notMem_erase e avail0) (hBavail p hap)
              · exact (Finset.disjoint_left.mp (hBdis p i hpq)) hap hai
            · simpa [B1, Function.update_noteq hpi, Function.update_noteq hqi] using
                hBdis p q hpq
  exact build (rootDeficit R) R avail rfl hcut

end Auxiliary
end Support
end TuringTask
