import OMAReductions.R_Erdos436_erdos_436_variants_ge_four_R2

/-!
# Step H2 of the reduction Erdos436.erdos_436.variants.ge_four.R2

For every bound M there are infinitely many primes p such that 2 is a quadratic non-residue
modulo p while every odd prime r at most M is a quadratic residue modulo p.

Let m be the product of the odd primes at most M (an odd number). By Dirichlet's theorem
there are infinitely many primes p with p congruent to 1 + 4 m modulo 8 m. Such a prime is
congruent to 5 modulo 8, so 2 is not a square modulo p, and p is congruent to 1 modulo every
odd prime r at most M; since p is 1 modulo 4, quadratic reciprocity shows that r is a square
modulo p.
-/

namespace OMA.Helpers

open Erdos436

/-- The product of the odd primes at most `M`. -/
def erdos436OddPrimeProd (M : ℕ) : ℕ :=
  ∏ r ∈ (Finset.range (M + 1)).filter (fun r => r.Prime ∧ 2 < r), r

theorem erdos436OddPrimeProd_odd (M : ℕ) : Odd (erdos436OddPrimeProd M) := by
  unfold erdos436OddPrimeProd
  refine Finset.prod_induction _ (fun x => Odd x) (fun a b ha hb => ha.mul hb) odd_one ?_
  intro r hr
  rw [Finset.mem_filter] at hr
  exact hr.2.1.odd_of_ne_two (by omega)

theorem erdos436_dvd_oddPrimeProd {M r : ℕ} (hr : r.Prime) (hr2 : 2 < r) (hrM : r ≤ M) :
    r ∣ erdos436OddPrimeProd M := by
  unfold erdos436OddPrimeProd
  apply Finset.dvd_prod_of_mem
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hr, hr2⟩

theorem erdos436_good_prime (M p : ℕ) (hp : p.Prime)
    (hmod : p ≡ 1 + 4 * erdos436OddPrimeProd M [MOD 8 * erdos436OddPrimeProd M]) :
    p.Prime ∧ ¬ IsPowerResidue 2 p 2 ∧
      ∀ r : ℕ, r.Prime → 2 < r → r ≤ M → IsPowerResidue 2 p r := by
  set m := erdos436OddPrimeProd M with hm
  have hmodd : Odd m := erdos436OddPrimeProd_odd M
  have h8 : p % 8 = 5 := by
    have h := Nat.ModEq.of_mul_right m hmod
    obtain ⟨k, hk⟩ := hmodd
    unfold Nat.ModEq at h
    omega
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at h8
    norm_num at h8
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨hp, ?_, ?_⟩
  · rintro ⟨-, x, hx⟩
    have hsq : IsSquare (2 : ZMod p) := ⟨x, by rw [← sq, hx]; push_cast; rfl⟩
    rcases (ZMod.exists_sq_eq_two_iff hp2).mp hsq with h | h <;> omega
  · intro r hr hr2 hrM
    have : Fact r.Prime := ⟨hr⟩
    have hrm : r ∣ m := erdos436_dvd_oddPrimeProd hr hr2 hrM
    have hpr : (p : ZMod r) = 1 := by
      have h1 : p ≡ 1 + 4 * m [MOD r] :=
        Nat.ModEq.of_dvd (dvd_mul_of_dvd_right hrm 8) hmod
      rw [(ZMod.natCast_eq_natCast_iff p (1 + 4 * m) r).mpr h1]
      push_cast
      rw [(ZMod.natCast_eq_zero_iff m r).mpr hrm]
      ring
    have hp4 : p % 4 = 1 := by omega
    have hsq : IsSquare (r : ZMod p) :=
      (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one hp4 (by omega)).mpr
        (by rw [hpr]; exact IsSquare.one)
    refine ⟨?_, ?_⟩
    · intro h0
      rw [ZMod.natCast_eq_zero_iff] at h0
      have hpe : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp h0
      rw [hpe, ZMod.natCast_self] at hpr
      exact zero_ne_one hpr
    · obtain ⟨x, hx⟩ := hsq
      exact ⟨x, by rw [sq, hx]⟩

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_ge_four_R2.H2 := by
  intro M
  set m := erdos436OddPrimeProd M with hm
  have hmodd : Odd m := erdos436OddPrimeProd_odd M
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hmodd
    exact Nat.not_odd_zero hmodd
  have hcop : Nat.Coprime (1 + 4 * m) (8 * m) := by
    apply Nat.Coprime.mul_right
    · have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
      rw [h8]
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_two_right]
      exact ⟨2 * m, by ring⟩
    · exact (Nat.coprime_add_mul_right_left 1 m 4).mpr (Nat.coprime_one_left m)
  apply Set.infinite_of_forall_exists_gt
  intro n
  obtain ⟨p, hpn, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq n (by positivity : 8 * m ≠ 0) hcop
  exact ⟨p, erdos436_good_prime M p hp hpmod, hpn⟩
