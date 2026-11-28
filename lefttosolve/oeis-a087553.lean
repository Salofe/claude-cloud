import OMAStatements.S_oeis_a087553
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a087553

theorem listP (m : ℕ) (l : List ℕ) (hl : l = List.replicate m 0 ++ [1, 2, 1]) :
    ∀ i : ℕ, (h : i + 1 < l.length) →
      digitNeighbors (l[i]'(Nat.lt_of_succ_lt h)) (l[i + 1]'h) := by
  subst hl
  intro i h
  simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil] at h
  simp only [List.getElem_append, List.length_replicate, List.getElem_replicate]
  unfold digitNeighbors
  rcases lt_trichotomy (i + 1) m with h1 | h1 | h1
  · rw [dif_pos (by omega), dif_pos h1]; omega
  · rw [dif_pos (by omega), dif_neg (by omega)]
    have : i + 1 - m = 0 := by omega
    simp [this]
  · rw [dif_neg (by omega), dif_neg (by omega)]
    have h2 : i - m = 0 ∨ i - m = 1 := by omega
    rcases h2 with h2 | h2
    · have h3 : i + 1 - m = 1 := by omega
      simp [h2, h3]
    · have h3 : i + 1 - m = 2 := by omega
      simp [h2, h3]

theorem neigh (m : ℕ) : HasNeighborDigits (10 ^ m * 121) := by
  have h121 : Nat.digits 10 121 = [1, 2, 1] := by norm_num
  exact listP m (Nat.digits 10 (10 ^ m * 121))
    (by rw [Nat.digits_base_pow_mul (by norm_num) (by norm_num), h121])

theorem nontriv (m : ℕ) : ¬ IsTrivialTerm (10 ^ m * 121) := by
  rintro ⟨k, hk | hk⟩
  · have h11 : (11 : ℕ) ∣ 10 ^ (2 * k) := hk ▸ Dvd.dvd.mul_left (by norm_num) _
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h11)
    omega
  · have h11 : (11 : ℕ) ∣ 9 * 10 ^ (2 * k) := hk ▸ Dvd.dvd.mul_left (by norm_num) _
    rcases (Nat.Prime.dvd_mul (by norm_num)).1 h11 with h | h
    · omega
    · have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h)
      omega

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a087553.main := by
  have hinj : Function.Injective (fun k : ℕ => 10 ^ (2 * k) * 121) := by
    intro a b hab
    simp only at hab
    have h2 : 10 ^ (2 * a) = 10 ^ (2 * b) := by omega
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 10) h2
    omega
  refine Set.infinite_of_injective_forall_mem hinj ?_
  intro k
  refine ⟨⟨10 ^ k * 11, ?_⟩, OMA.Helpers.neigh _, OMA.Helpers.nontriv _⟩
  ring
