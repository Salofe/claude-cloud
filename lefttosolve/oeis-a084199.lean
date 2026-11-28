import OMAStatements.S_oeis_a084199
import Mathlib

/-!
Disproof of the range conjecture of OEIS A084199 as formalized: the value 5 is never taken,
since 6 dividing p + 1 forces 3 to divide p + 1, so 2 is a smaller admissible prime.
-/

namespace OMA.Helpers

open OMA.S_oeis_a084199

/-- The value 5 is never taken: if 6 divides p + 1 then so does 3, so 2 is a smaller witness. -/
theorem a084199_ne_five (n : ℕ) : a n ≠ 5 := by
  intro hn
  unfold a at hn
  simp only at hn
  split_ifs at hn with hS
  · have hmem := Nat.sInf_mem hS
    rw [hn] at hmem
    obtain ⟨-, h5, h6⟩ := hmem
    have h2 : 2 ∈ {q : ℕ | Nat.Prime q ∧ q < Nat.nth Nat.Prime n ∧ (q + 1) ∣ (Nat.nth Nat.Prime n + 1)} :=
      ⟨Nat.prime_two, by omega, dvd_trans ⟨2, by norm_num⟩ h6⟩
    have hle := Nat.sInf_le h2
    omega
  · omega

end OMA.Helpers

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a084199.main) := by
  intro h
  obtain ⟨n, hn⟩ := h 5 (by norm_num)
  exact OMA.Helpers.a084199_ne_five n hn
