import OMAStatements.S_oeis_a159999
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a159999

theorem traj_add (n i m : ℕ) : trajectory n (i + m) = trajectory (trajectory n i) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show collatzStep (trajectory n (i + m)) = collatzStep (trajectory (trajectory n i) m)
    rw [ih]

theorem traj_shift {n i j : ℕ} (h : trajectory n i = trajectory n j) (m : ℕ) :
    trajectory n (i + m) = trajectory n (j + m) := by
  rw [traj_add, traj_add, h]

end OMA.Helpers

open OMA.S_oeis_a159999 OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a159999.main := by
  intro hC n hn
  classical
  have hex : ∃ k : ℕ, trajectory n k = 1 := hC n hn
  have hs : stopping n = Nat.find hex := by
    unfold stopping
    rw [dif_pos hex]
  have hdist : ∀ i j : ℕ, i < j → j ≤ stopping n → trajectory n i ≠ trajectory n j := by
    intro i j hij hj heq
    have h1 := traj_shift heq (stopping n - j)
    have e1 : j + (stopping n - j) = stopping n := by omega
    rw [e1] at h1
    have hs1 : trajectory n (stopping n) = 1 := by
      rw [hs]; exact Nat.find_spec hex
    have hlt : i + (stopping n - j) < Nat.find hex := by rw [← hs]; omega
    exact Nat.find_min hex hlt (h1.trans hs1)
  refine ⟨hdist, ?_⟩
  have hsplit : hits n (· ≤ n) = insert 0 (hits n (· < n)) := by
    ext i
    simp only [hits, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨hi, hle⟩
      rcases Nat.lt_or_ge (trajectory n i) n with h | h
      · exact Or.inr ⟨hi, h⟩
      · left
        have heq : trajectory n i = n := le_antisymm hle h
        by_contra h0
        exact hdist 0 i (Nat.pos_of_ne_zero h0) (by omega) (by rw [heq]; rfl)
    · rintro (h | ⟨hi, hlt⟩)
      · subst h; exact ⟨by omega, le_refl _⟩
      · exact ⟨hi, hlt.le⟩
  have h0 : (0 : ℕ) ∉ hits n (· < n) := by
    simp [hits, trajectory]
  rw [hsplit, Finset.card_insert_of_notMem h0]
  omega
