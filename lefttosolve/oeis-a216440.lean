import OMAStatements.S_oeis_a216440
import Mathlib

namespace OMA.Helpers.A216440

open OMA.S_oeis_a216440

theorem src_spec (k j : ℕ) (hj : j < 2 * k) :
    src k j < 2 * k ∧ (2 * k + 1 : ℤ) ∣ 2 * ((src k j : ℤ) + 1) - (j + 1) := by
  by_cases h : j % 2 = 0
  · have e : src k j = k + j / 2 := by simp [src, h]
    rw [e]
    refine ⟨by omega, ⟨1, ?_⟩⟩
    push_cast
    omega
  · have e : src k j = j / 2 := by simp [src, h]
    rw [e]
    refine ⟨by omega, ⟨0, ?_⟩⟩
    push_cast
    omega

theorem deck_spec (k m : ℕ) : ∀ j, j < 2 * k →
    deck k m j < 2 * k ∧ (2 * k + 1 : ℤ) ∣ 2 ^ m * ((deck k m j : ℤ) + 1) - (j + 1) := by
  induction m with
  | zero =>
    intro j hj
    refine ⟨by simpa [deck] using hj, ⟨0, ?_⟩⟩
    simp [deck]
  | succ m ih =>
    intro j hj
    obtain ⟨hs, hsd⟩ := src_spec k j hj
    obtain ⟨hd, hdd⟩ := ih (src k j) hs
    have e : deck k (m + 1) j = deck k m (src k j) := rfl
    rw [e]
    refine ⟨hd, ?_⟩
    have : (2 : ℤ) ^ (m + 1) * ((deck k m (src k j) : ℤ) + 1) - (j + 1) =
        2 * (2 ^ m * ((deck k m (src k j) : ℤ) + 1) - (src k j + 1)) +
          (2 * ((src k j : ℤ) + 1) - (j + 1)) := by ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right hdd 2) hsd

theorem reverses_iff (k m : ℕ) : Reverses k m ↔ (2 * k + 1) ∣ 2 ^ m + 1 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · have h0 := h 0 (by omega)
      obtain ⟨_, hdd⟩ := deck_spec k m 0 (by omega)
      rw [h0] at hdd
      have hc : ((2 * k - 1 - 0 : ℕ) : ℤ) = 2 * k - 1 := by omega
      rw [hc] at hdd
      have : (2 : ℤ) ^ m + 1 = 2 ^ m * (2 * k + 1) - (2 ^ m * (2 * k - 1 + 1) - (0 + 1)) := by
        push_cast
        ring
      have hz : (2 * k + 1 : ℤ) ∣ 2 ^ m + 1 := by
        rw [this]
        exact dvd_sub (dvd_mul_left _ _) (by exact_mod_cast hdd)
      exact_mod_cast hz
  · intro h j hj
    obtain ⟨hd, hdd⟩ := deck_spec k m j hj
    have hz : (2 * k + 1 : ℤ) ∣ 2 ^ m + 1 := by exact_mod_cast h
    have h2 : (2 * k + 1 : ℤ) ∣ (deck k m j : ℤ) + j + 2 := by
      have : (deck k m j : ℤ) + j + 2 =
          (2 ^ m + 1) * ((deck k m j : ℤ) + 1) - (2 ^ m * ((deck k m j : ℤ) + 1) - (j + 1)) := by
        ring
      rw [this]
      exact dvd_sub (dvd_mul_of_dvd_left hz _) hdd
    obtain ⟨c, hc⟩ := h2
    have hc1 : c = 1 := by
      have hlo : (0 : ℤ) < c := by
        by_contra hneg
        have hneg' : c ≤ 0 := not_lt.mp hneg
        nlinarith
      have hhi : c < 2 := by
        by_contra hge
        have hge' : 2 ≤ c := not_lt.mp hge
        have : (2 * k + 1 : ℤ) * 2 ≤ (2 * k + 1) * c := by nlinarith
        omega
      omega
    subst hc1
    omega

end OMA.Helpers.A216440

open OMA.Helpers.A216440 OMA.S_oeis_a216440 in
theorem OMA.solution : type_of% @OMA.S_oeis_a216440.main := by
  intro n hn
  classical
  have key : ∀ m, Reverses (n - 1) m ↔ (2 * n - 1) ∣ 2 ^ m + 1 := by
    intro m
    have : 2 * (n - 1) + 1 = 2 * n - 1 := by omega
    rw [reverses_iff, this]
  have hex : (∃ m, 1 ≤ m ∧ Reverses (n - 1) m) ↔ (∃ m, 1 ≤ m ∧ (2 * n - 1) ∣ 2 ^ m + 1) := by
    simp only [key]
  unfold shuffles a
  by_cases h : ∃ m, 1 ≤ m ∧ (2 * n - 1) ∣ 2 ^ m + 1
  · have h1 := hex.2 h
    rw [dif_pos h1, dif_pos h]
    apply le_antisymm
    · apply Nat.find_min'
      obtain ⟨a1, a2⟩ := Nat.find_spec h
      exact ⟨a1, (key _).2 a2⟩
    · apply Nat.find_min'
      obtain ⟨a1, a2⟩ := Nat.find_spec h1
      exact ⟨a1, (key _).1 a2⟩
  · rw [dif_neg (fun h1 => h (hex.1 h1)), dif_neg h]
