import OMAReductions.R_Erdos913_erdos_913_variants_infinite_many_8p_sq_add_one_primes_R1

/-!
# Step H1 of the reduction Erdos913.erdos_913.variants.infinite_many_8p_sq_add_one_primes.R1

Let `M` be the product of the odd numbers `1, 3, ..., 2B-1`, so `M = 2k+1` is odd and every odd
prime up to `B` divides `M`. By Dirichlet's theorem there are arbitrarily large primes `p` with
`p = k+1` modulo `M`. Then `2p - 1` is divisible by `M`, and `8p^2 - 1 = (2p-1)(4p+2) + 1`, so no
odd prime up to `B` divides `8p^2 - 1`; the prime `2` does not divide it since it is odd.
-/

namespace OMA.Helpers

/-- The product of the first `B` odd numbers is odd. -/
theorem oddProd_odd (B : ℕ) : Odd (∏ i ∈ Finset.range B, (2 * i + 1)) :=
  Finset.prod_induction (fun i => 2 * i + 1) Odd (fun _ _ ha hb => ha.mul hb) odd_one
    (fun i _ => odd_two_mul_add_one i)

/-- Every odd prime up to `B` divides the product of the first `B` odd numbers. -/
theorem prime_dvd_oddProd (B q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqB : q ≤ B) :
    q ∣ ∏ i ∈ Finset.range B, (2 * i + 1) := by
  have hodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
  have hq1 := hq.one_lt
  have hmem : q / 2 ∈ Finset.range B := Finset.mem_range.mpr (by omega)
  have heq : 2 * (q / 2) + 1 = q := by omega
  have h := Finset.dvd_prod_of_mem (fun i => 2 * i + 1) hmem
  rw [heq] at h
  exact h

theorem coprime_succ_two_mul_add_one (k : ℕ) : Nat.Coprime (k + 1) (2 * k + 1) := by
  have h1 : Nat.gcd (k + 1) (2 * k + 1) ∣ 2 * (k + 1) :=
    Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) 2
  have h2 : Nat.gcd (k + 1) (2 * k + 1) ∣ 2 * k + 1 := Nat.gcd_dvd_right _ _
  have h3 : Nat.gcd (k + 1) (2 * k + 1) ∣ 1 := by
    have e : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    rw [e] at h1
    exact (Nat.dvd_add_right h2).mp h1
  exact Nat.dvd_one.mp h3

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution :
    OMA.R_Erdos913_erdos_913_variants_infinite_many_8p_sq_add_one_primes_R1.H1 := by
  intro B N
  obtain ⟨k, hk⟩ := oddProd_odd B
  set M := ∏ i ∈ Finset.range B, (2 * i + 1) with hMdef
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := M) (a := k + 1) (by omega)
      (by rw [hk]; exact coprime_succ_two_mul_add_one k)
  refine ⟨p, hpN.le, hp, ?_⟩
  intro q hqB hq hdvd
  have hp2 := hp.two_le
  have hsq : 4 ≤ p ^ 2 := by nlinarith
  by_cases hq2 : q = 2
  · subst hq2
    generalize p ^ 2 = x at hsq hdvd
    omega
  · have hqM : q ∣ M := prime_dvd_oddProd B q hq hq2 hqB
    have hMi : (M : ℤ) ∣ ((k + 1 : ℕ) : ℤ) - (p : ℤ) := (Nat.modEq_iff_dvd.mp hmod)
    have hqi : (q : ℤ) ∣ ((k + 1 : ℕ) : ℤ) - (p : ℤ) := (Int.natCast_dvd_natCast.mpr hqM).trans hMi
    have hqM' : (q : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.mpr hqM
    have hqd : (q : ℤ) ∣ ((8 * p ^ 2 - 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hdvd
    have h8 : 1 ≤ 8 * p ^ 2 := by omega
    have key : (1 : ℤ) = ((8 * p ^ 2 - 1 : ℕ) : ℤ) -
        ((M : ℤ) - 2 * (((k + 1 : ℕ) : ℤ) - (p : ℤ))) * (4 * (p : ℤ) + 2) := by
      rw [hk]
      push_cast [Nat.cast_sub h8]
      ring
    have h1 : (q : ℤ) ∣ 1 := by
      rw [key]
      exact hqd.sub ((hqM'.sub (hqi.mul_left 2)).mul_right _)
    have h1' : q ∣ 1 := Int.natCast_dvd_natCast.mp (by simpa using h1)
    exact hq.one_lt.ne' (Nat.dvd_one.mp h1')
