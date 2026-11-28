import OMAStatements.S_oeis_a110408
import Mathlib

/-!
The equivalence fails for n = 121: rev 121 = 121, so every number rev(n)...rev(n)n is 121121...121
= 121 * (1 + 1000 + ... + 1000^m), which is composite; hence a(121) = 0, but 121 = 11^2 is not prime
and 121 is not a multiple of 3.
-/

namespace OMA.Helpers

theorem d121 : Nat.digits 10 121 = [1, 2, 1] := by norm_num

theorem rev121 : OMA.S_oeis_a110408.rev 121 = 121 := by
  simp [OMA.S_oeis_a110408.rev, Nat.ofDigits_cons]

theorem rep_dvd (m : ℕ) :
    ∃ c, Nat.ofDigits 10 (List.replicate m [1, 2, 1]).flatten = 121 * c ∧ (1 ≤ m → 1 ≤ c) := by
  induction m with
  | zero => exact ⟨0, by simp, by omega⟩
  | succ k ih =>
    obtain ⟨c, hc, -⟩ := ih
    refine ⟨1 + 1000 * c, ?_, fun _ => by omega⟩
    rw [List.replicate_succ, List.flatten_cons, Nat.ofDigits_append, hc]
    simp [Nat.ofDigits_cons]
    ring

end OMA.Helpers

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a110408.main) := by
  intro h
  have key := h 121 (by norm_num)
  have hz : OMA.S_oeis_a110408.ZeroTerm 121 := by
    intro m hm hp
    obtain ⟨c, hc, hc1⟩ := OMA.Helpers.rep_dvd m
    have hF : OMA.S_oeis_a110408.F 121 m = 121 * (1 + 1000 * c) := by
      unfold OMA.S_oeis_a110408.F
      rw [OMA.Helpers.rev121, OMA.Helpers.d121, Nat.ofDigits_append, hc]
      simp [Nat.ofDigits_cons]
      ring
    rw [hF] at hp
    have h1 := hc1 hm
    have := (Nat.prime_mul_iff.mp hp)
    rcases this with ⟨h121, _⟩ | ⟨_, h2⟩
    · norm_num at h121
    · omega
  have := key.mp hz
  rcases this with ⟨hp, _⟩ | h3
  · norm_num at hp
  · norm_num at h3
