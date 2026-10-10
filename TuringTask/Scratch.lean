import Mathlib

open Set

namespace TuringTask.Scratch

variable {α : Type*} {r : SetRel α α}

lemma exists_shortest_relSeries
    (S T : Set α)
    (hex : ∃ p : RelSeries r, p.head ∈ S ∧ p.last ∈ T) :
    ∃ p : RelSeries r,
      p.head ∈ S ∧ p.last ∈ T ∧
      ∀ q : RelSeries r,
        q.head ∈ S → q.last ∈ T → p.length ≤ q.length := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ p : RelSeries r, p.length = n ∧ p.head ∈ S ∧ p.last ∈ T
  have hP : ∃ n, P n := by
    obtain ⟨p, hpS, hpT⟩ := hex
    exact ⟨p.length, p, rfl, hpS, hpT⟩
  obtain ⟨p, hplen, hpS, hpT⟩ := Nat.find_spec hP
  refine ⟨p, hpS, hpT, ?_⟩
  intro q hqS hqT
  rw [hplen]
  exact Nat.find_min' hP ⟨q, rfl, hqS, hqT⟩

lemma shortest_relSeries_injective
    (S T : Set α) (p : RelSeries r)
    (hpS : p.head ∈ S) (hpT : p.last ∈ T)
    (hmin : ∀ q : RelSeries r,
      q.head ∈ S → q.last ∈ T → p.length ≤ q.length) :
    Function.Injective p := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · have hjoin : (p.take i).last = (p.drop j).head := by
      simpa using hij
    let q : RelSeries r := (p.take i).smash (p.drop j) hjoin
    have hqS : q.head ∈ S := by
      simpa [q] using hpS
    have hqT : q.last ∈ T := by
      simpa [q] using hpT
    have hle := hmin q hqS hqT
    simp [q] at hle
    omega
  · have hjoin : (p.take j).last = (p.drop i).head := by
      simpa using hij.symm
    let q : RelSeries r := (p.take j).smash (p.drop i) hjoin
    have hqS : q.head ∈ S := by
      simpa [q] using hpS
    have hqT : q.last ∈ T := by
      simpa [q] using hpT
    have hle := hmin q hqS hqT
    simp [q] at hle
    omega

lemma shortest_relSeries_no_forward_chord
    (S T : Set α) (p : RelSeries r)
    (hpS : p.head ∈ S) (hpT : p.last ∈ T)
    (hmin : ∀ q : RelSeries r,
      q.head ∈ S → q.last ∈ T → p.length ≤ q.length)
    (i j : Fin (p.length + 1))
    (hskip : i.1 + 1 < j.1) :
    ¬ r (p i) (p j) := by
  intro hchord
  have hconnect :
      (p.take i).last ~[r] (p.drop j).head := by
    simpa using hchord
  let q : RelSeries r :=
    (p.take i).append (p.drop j) hconnect
  have hqS : q.head ∈ S := by
    simpa [q] using hpS
  have hqT : q.last ∈ T := by
    simpa [q] using hpT
  have hle := hmin q hqS hqT
  simp [q] at hle
  omega

end TuringTask.Scratch
