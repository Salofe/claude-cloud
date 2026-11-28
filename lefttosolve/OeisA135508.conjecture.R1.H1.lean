import OMAReductions.R_OeisA135508_conjecture_R1

/-!
Step H1 of reduction OeisA135508.conjecture.R1: `3 ∣ x n` for every `n ≥ 4`.

`x 4 = 60` is divisible by 3, and from index 2 on the recurrence reads
`x (m + 2) = 2 * x (m + 1) + lcm (x (m + 1)) (m + 2)`; both summands are multiples of
`x (m + 1)`, so divisibility by 3 propagates upward (induction from 4).
-/

namespace OMA.Helpers

/-- The recurrence of `OeisA135508.x` from index 2 on, written with an explicit successor. -/
theorem x_succ_succ (m : ℕ) :
    OeisA135508.x (m + 2) = 2 * OeisA135508.x (m + 1) + Nat.lcm (OeisA135508.x (m + 1)) (m + 2) :=
  rfl

/-- Base case: `x 4 = 60`. -/
theorem three_dvd_x_four : 3 ∣ OeisA135508.x 4 := by decide

end OMA.Helpers

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact OMA.Helpers.three_dvd_x_four
  | succ k hk ih =>
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [OMA.Helpers.x_succ_succ m]
    exact dvd_add (Dvd.dvd.mul_left ih 2) (dvd_trans ih (Nat.dvd_lcm_left _ _))
