import Mathlib

namespace TuringTask.Golden

section Paths

variable {α : Type*}

def IsRoute (R : α → α → Prop) (F : α → Prop) (t : α) (p : List α) : Prop :=
  p.IsChain R ∧ (∃ s, p.head? = some s ∧ F s) ∧ p.getLast? = some t

lemma IsRoute.nonempty {R : α → α → Prop} {F : α → Prop} {t : α} {p : List α}
    (h : IsRoute R F t p) : p ≠ [] := by
  intro hp
  subst p
  simp [IsRoute] at h

lemma exists_shortest_route {R : α → α → Prop} {F : α → Prop} {t : α}
    (h : ∃ p : List α, IsRoute R F t p) :
    ∃ p : List α, IsRoute R F t p ∧ ∀ q : List α, IsRoute R F t q → p.length ≤ q.length := by
  let n := Nat.find (show ∃ n : ℕ, ∃ p : List α, IsRoute R F t p ∧ p.length = n by
    obtain ⟨p, hp⟩ := h
    exact ⟨p.length, p, hp, rfl⟩)
  obtain ⟨p, hp, hlen⟩ := Nat.find_spec
    (show ∃ n : ℕ, ∃ p : List α, IsRoute R F t p ∧ p.length = n by
      obtain ⟨p, hp⟩ := h
      exact ⟨p.length, p, hp, rfl⟩)
  refine ⟨p, hp, ?_⟩
  intro q hq
  by_contra hlt
  have hqn : q.length < n := by omega
  exact (Nat.find_min'
    (show ∃ n : ℕ, ∃ p : List α, IsRoute R F t p ∧ p.length = n by
      obtain ⟨p, hp⟩ := h
      exact ⟨p.length, p, hp, rfl⟩)
    ⟨q, hq, rfl⟩) hqn

lemma shortest_route_no_forward_chord
    {R : α → α → Prop} {F : α → Prop} {t : α}
    {p : List α}
    (hp : IsRoute R F t p)
    (hmin : ∀ q : List α, IsRoute R F t q → p.length ≤ q.length)
    {i j : ℕ}
    (hi : i < p.length)
    (hj : j < p.length)
    (hskip : i + 1 < j)
    (hR : R p[i] p[j]) :
    False := by
  let q := p.take (i + 1) ++ p.drop j
  have hq_len : q.length < p.length := by
    simp [q, List.length_take, hi.le, List.length_drop]
    omega
  have hq_start : q.head? = p.head? := by
    simp [q, hi]
  have hq_last : q.getLast? = p.getLast? := by
    have hj' : p.drop j ≠ [] := by
      simpa [List.drop_eq_nil_iff_le] using (show ¬ p.length ≤ j by omega)
    rw [q, List.getLast?_append_of_ne_nil hj']
    simp
  have hq_chain : q.IsChain R := by
    rw [q, List.isChain_append]
    refine ⟨hp.1.take _, hp.1.drop _, ?_⟩
    intro a ha b hb
    have ha_eq : a = p[i] := by
      have hlen_take : (p.take (i + 1)).length = i + 1 := by simp [hi.le]
      have hlast := List.getLast?_eq_some_getElem (l := p.take (i + 1)) (by simp [hi])
      sorry
    have hb_eq : b = p[j] := by
      sorry
    simpa [ha_eq, hb_eq] using hR
  have hq : IsRoute R F t q := by
    refine ⟨hq_chain, ?_, ?_⟩
    · obtain ⟨s, hs, hFs⟩ := hp.2.1
      exact ⟨s, hq_start.trans hs, hFs⟩
    · exact hq_last.trans hp.2.2
  exact (not_lt_of_ge (hmin q hq)) hq_len

end Paths

end TuringTask.Golden
