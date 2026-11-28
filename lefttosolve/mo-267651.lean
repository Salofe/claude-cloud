import OMAStatements.S_mo_267651
import Mathlib

namespace OMA.Helpers

theorem progression_infinite (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ({r : ℕ | Nat.Prime r ∧ ∃ k : ℕ, r = p + k * q}).Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).mpr hne
  obtain ⟨r, hrN, hr, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq (N + p) hq.ne_zero hcop
  have hpr : p ≤ r := by omega
  have hdvd : q ∣ r - p := (Nat.modEq_iff_dvd' hpr).mp hmod.symm
  refine ⟨r, ⟨hr, (r - p) / q, ?_⟩, by omega⟩
  rw [Nat.div_mul_cancel hdvd]
  omega

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_mo_267651.main := by
  apply Set.Finite.subset (Set.finite_empty)
  rintro ⟨p, q⟩ ⟨hp, hq, hne, hfin⟩
  exact absurd hfin (OMA.Helpers.progression_infinite p q hp hq hne)
