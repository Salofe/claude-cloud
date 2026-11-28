import OMAStatements.S_oeis_a384318
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a384318

/-- A finite set of positive integers with sum `s` that contains `s` is `{s}`. -/
theorem a384318_eq_singleton {T : Finset ℕ} {s : ℕ} (hpos : ∀ x ∈ T, 0 < x)
    (hsum : T.sum id = s) (hs : s ∈ T) : T = {s} := by
  have h := Finset.add_sum_erase T id hs
  rw [hsum] at h
  have h0 : (T.erase s).sum id = 0 := by simp only [id] at h ⊢; omega
  rw [Finset.sum_eq_zero_iff] at h0
  have he : T.erase s = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    have hx0 := h0 x hx
    have hxp := hpos x (Finset.mem_of_mem_erase hx)
    simp only [id] at hx0
    omega
  rcases Finset.erase_eq_empty_iff T s |>.mp he with h1 | h1
  · rw [h1] at hs; simp at hs
  · exact h1

/-- The family of singletons, modified at one part. -/
def a384318_fam (s : ℕ) (T : Finset ℕ) : ℕ → Finset ℕ := fun t => if t = s then T else {t}

theorem a384318_forward {y : Finset ℕ} (hy : ∀ t ∈ y, 0 < t) (h : NotMaximallyRefined y) :
    MoreThanOneWay y := by
  obtain ⟨s, hs, T, hT, hTs⟩ := h
  refine ⟨a384318_fam s T, fun t => {t}, ⟨?_, ?_⟩, ⟨?_, ?_⟩, s, hs, ?_⟩
  · intro t ht
    by_cases h : t = s
    · subst h
      simp only [a384318_fam, if_true]
      exact ⟨fun x hx => (hT x hx).1, hTs⟩
    · simp only [a384318_fam, h, if_false, Finset.mem_singleton, forall_eq,
        Finset.sum_singleton, id]
      exact ⟨hy t ht, trivial⟩
  · intro t ht u hu htu
    by_cases h1 : t = s
    · subst h1
      have h2 : u ≠ t := fun e => htu e.symm
      simp only [a384318_fam, if_true, h2, if_false, Finset.disjoint_singleton_right]
      intro hm
      exact (hT u hm).2 hu
    · by_cases h2 : u = s
      · subst h2
        simp only [a384318_fam, if_true, h1, if_false, Finset.disjoint_singleton_left]
        intro hm
        exact (hT t hm).2 ht
      · simp only [a384318_fam, h1, h2, if_false, Finset.disjoint_singleton]
        exact htu
  · intro t ht
    simp only [Finset.mem_singleton, forall_eq, Finset.sum_singleton, id]
    exact ⟨hy t ht, trivial⟩
  · intro t ht u hu htu
    simp only [Finset.disjoint_singleton]
    exact htu
  · simp only [a384318_fam, if_true]
    intro he
    have : s ∈ T := by rw [he]; exact Finset.mem_singleton_self s
    exact (hT s this).2 hs

/-- A family that is not the family of singletons gives a part that is a sum of distinct
non-parts: take the least part where the family is not a singleton. -/
theorem a384318_of_family {y : Finset ℕ} {f : ℕ → Finset ℕ} (hf : IsFamily y f)
    (hne : ∃ s ∈ y, f s ≠ {s}) : NotMaximallyRefined y := by
  obtain ⟨hf1, hf2⟩ := hf
  have hnonempty : (y.filter (fun s => f s ≠ {s})).Nonempty := by
    obtain ⟨s, hs, h⟩ := hne
    exact ⟨s, Finset.mem_filter.mpr ⟨hs, h⟩⟩
  obtain ⟨s, hsm, hmin⟩ := Finset.exists_min_image _ id hnonempty
  rw [Finset.mem_filter] at hsm
  obtain ⟨hs, hfs⟩ := hsm
  refine ⟨s, hs, f s, fun t ht => ⟨(hf1 s hs).1 t ht, ?_⟩, (hf1 s hs).2⟩
  intro hty
  by_cases hts : t = s
  · subst hts
    exact hfs (a384318_eq_singleton (hf1 t hs).1 (hf1 t hs).2 ht)
  · have hle : t ≤ s := by
      have := Finset.single_le_sum (f := id) (fun x _ => Nat.zero_le x) ht
      rw [(hf1 s hs).2] at this
      exact this
    have hlt : t < s := lt_of_le_of_ne hle hts
    have hft : f t = {t} := by
      by_contra hc
      have := hmin t (Finset.mem_filter.mpr ⟨hty, hc⟩)
      simp only [id] at this
      omega
    have hd := hf2 s hs t hty (fun e => hts e.symm)
    rw [hft, Finset.disjoint_singleton_right] at hd
    exact hd ht

theorem a384318_backward {y : Finset ℕ} (h : MoreThanOneWay y) : NotMaximallyRefined y := by
  obtain ⟨f, g, hf, hg, s, hs, hfg⟩ := h
  by_cases h1 : f s = {s}
  · have h2 : g s ≠ {s} := fun e => hfg (h1.trans e.symm)
    exact a384318_of_family hg ⟨s, hs, h2⟩
  · exact a384318_of_family hf ⟨s, hs, h1⟩

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a384318.main := by
  intro n
  unfold OMA.S_oeis_a384318.a
  classical
  congr 1
  apply Finset.filter_congr
  intro y hy
  have hpos : ∀ t ∈ y, 0 < t := by
    intro t ht
    simp only [OMA.S_oeis_a384318.strictPartitions, Finset.mem_filter,
      Finset.mem_powerset] at hy
    have := hy.1 ht
    rw [Finset.mem_Icc] at this
    omega
  exact ⟨a384318_forward hpos, a384318_backward⟩
