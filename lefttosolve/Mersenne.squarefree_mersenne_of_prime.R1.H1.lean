import OMAReductions.R_Mersenne_squarefree_mersenne_of_prime_R1

/-!
# Step H1 of the reduction Mersenne.squarefree_mersenne_of_prime.R1

Claim: for primes `q, p`, if `p ^ 2 ∣ M_q = 2 ^ q - 1` then `p` is a Wieferich prime,
i.e. `p ^ 2 ∣ 2 ^ (p - 1) - 1`.

Proof (all in `ℕ`, via the gcd identity for numbers of the form `2 ^ n - 1`):
* `2 ^ q - 1` is odd, so `p ≠ 2` and `2` is coprime to `p`.
* Euler / Fermat: `p ∣ 2 ^ (p - 1) - 1`.
* Hence `p ∣ gcd (2 ^ q - 1) (2 ^ (p - 1) - 1) = 2 ^ gcd q (p - 1) - 1`.
* `gcd q (p - 1)` divides the prime `q`; it is not `1` (else `p ∣ 1`), so it is `q`.
* Then `2 ^ q - 1 = gcd (2 ^ q - 1) (2 ^ (p - 1) - 1)` divides `2 ^ (p - 1) - 1`,
  and `p ^ 2 ∣ 2 ^ q - 1 ∣ 2 ^ (p - 1) - 1`.
Only the upstream definitions `mersenne` and `IsWieferichPrimeBase` are used.
-/

namespace OMA.Helpers

/-- `2 ^ n - 1` is odd when `n ≠ 0`. -/
theorem two_not_dvd_two_pow_sub_one {n : ℕ} (hn : n ≠ 0) : ¬ 2 ∣ 2 ^ n - 1 := by
  intro h
  have h1 : 2 ∣ 2 ^ n := dvd_pow_self 2 hn
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

/-- Fermat's little theorem for base `2` at an odd prime, as a divisibility in `ℕ`. -/
theorem dvd_two_pow_pred_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ 2 ^ (p - 1) - 1 := by
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  have hfermat : 2 ^ (p - 1) ≡ 1 [MOD p] := by
    have h := Nat.ModEq.pow_totient hcop
    rwa [Nat.totient_prime hp] at h
  exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hfermat.symm

/-- If an odd prime `p` divides `2 ^ q - 1` with `q` prime, then `gcd q (p - 1) = q`. -/
theorem gcd_eq_of_dvd_two_pow_sub_one {q p : ℕ} (hq : q.Prime) (hp : p.Prime)
    (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ q - 1) : Nat.gcd q (p - 1) = q := by
  have hW : p ∣ 2 ^ (p - 1) - 1 := dvd_two_pow_pred_sub_one hp hp2
  have hg : p ∣ 2 ^ Nat.gcd q (p - 1) - 1 := by
    have h := Nat.dvd_gcd hdvd hW
    rwa [Nat.pow_sub_one_gcd_pow_sub_one] at h
  rcases hq.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_left q (p - 1)) with h1 | hqq
  · have h21 : (2 : ℕ) ^ 1 - 1 = 1 := by norm_num
    rw [h1, h21, Nat.dvd_one] at hg
    exact absurd hg hp.one_lt.ne'
  · exact hqq

/-- A square prime factor of `2 ^ q - 1` (with `q` prime) is a Wieferich prime. -/
theorem wieferich_of_sq_dvd_mersenne (q p : ℕ) (hq : q.Prime) (hp : p.Prime)
    (h : p ^ 2 ∣ mersenne q) : IsWieferichPrime p := by
  have hM : mersenne q = 2 ^ q - 1 := rfl
  rw [hM] at h
  have hdvd : p ∣ 2 ^ q - 1 := (dvd_pow_self p two_ne_zero).trans h
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact two_not_dvd_two_pow_sub_one hq.ne_zero hdvd
  have hg : Nat.gcd q (p - 1) = q := gcd_eq_of_dvd_two_pow_sub_one hq hp hp2 hdvd
  have hMW : 2 ^ q - 1 ∣ 2 ^ (p - 1) - 1 := by
    have h' := Nat.gcd_dvd_right (2 ^ q - 1) (2 ^ (p - 1) - 1)
    rwa [Nat.pow_sub_one_gcd_pow_sub_one, hg] at h'
  exact ⟨hp, h.trans hMW⟩

end OMA.Helpers

theorem OMA.solution : OMA.R_Mersenne_squarefree_mersenne_of_prime_R1.H1 :=
  fun q p hq hp h => OMA.Helpers.wieferich_of_sq_dvd_mersenne q p hq hp h
