import OMAStatements.S_oeis_a131853
import Mathlib

namespace OMA.Helpers

/-- Reducing modulo `5` sends `i` to `2`, and `n` is congruent to the image of `z n`. -/
theorem a131853_key (n : ℕ) : ∃ c : ℤ,
    (n : ℤ) = (OMA.S_oeis_a131853.z n).re + 2 * (OMA.S_oeis_a131853.z n).im + 5 * c := by
  refine Nat.strong_induction_on n ?_
  intro m ih
  by_cases hm : m = 0
  · subst hm
    exact ⟨0, by rw [OMA.S_oeis_a131853.z, dif_pos rfl]; simp⟩
  · obtain ⟨c, hc⟩ := ih (m / 2) (by omega)
    refine ⟨(OMA.S_oeis_a131853.z (m / 2)).im + 2 * c, ?_⟩
    rw [OMA.S_oeis_a131853.z, dif_neg hm]
    simp only
    have h2 : (m : ℤ) = 2 * ((m / 2 : ℕ) : ℤ) + ((m % 2 : ℕ) : ℤ) := by
      exact_mod_cast (Nat.div_add_mod m 2).symm
    rw [h2, hc]
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a131853.main := by
  intro n hz
  obtain ⟨c, hc⟩ := OMA.Helpers.a131853_key n
  rw [hz] at hc
  have h0 : (n : ℤ) = 5 * c := by simpa using hc
  omega
