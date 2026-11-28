import OMAReductions.R_Erdos420_erdos_420_parts_i_R1

-- Step H2 of reduction Erdos420.erdos_420.parts.i.R1.
-- Write a! = p^e * m and b! = p^f * m' with p coprime to m, m'. Since a < s p < p^2, Legendre
-- gives e = a / p <= s - 1, while (p s)! divides b! gives f >= s. As m divides m', the divisor
-- counts satisfy d(a!) = (e+1) d(m) and d(b!) >= (f+1) d(m), and (s+1)(e+1) <= s (f+1).

open scoped ArithmeticFunction.sigma

namespace OMA.Helpers

theorem sigma_split (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    σ 0 n = (n.factorization p + 1) * σ 0 (ordCompl[p] n) := by
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
    ((Nat.coprime_ordCompl hp hn).pow_left _), ArithmeticFunction.sigma_zero_apply_prime_pow hp]

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos420_erdos_420_parts_i_R1.H2 := by
  intro a b p s hp hs hsp hab hb
  have ha0 : a.factorial ≠ 0 := Nat.factorial_ne_zero a
  have hb0 : b.factorial ≠ 0 := Nat.factorial_ne_zero b
  have he : a.factorial.factorization p + 1 ≤ s := by
    have hlog : Nat.log p a < 2 := by
      rcases Nat.eq_zero_or_pos a with h0 | hpos
      · simp [h0]
      apply Nat.log_lt_of_lt_pow hpos.ne'
      calc a < s * p := hab
        _ ≤ p * p := Nat.mul_le_mul_right _ hsp.le
        _ = p ^ 2 := by ring
    rw [Nat.factorization_factorial hp hlog]
    have hdiv : a / p < s := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hab)
    simp only [Nat.Ico_succ_singleton, Finset.sum_singleton, pow_one]
    omega
  have he' : s ≤ b.factorial.factorization p := by
    have h1 : (p * s).factorial.factorization p = s.factorial.factorization p + s :=
      Nat.factorization_factorial_mul hp
    have h2 : (p * s).factorial ∣ b.factorial :=
      Nat.factorial_dvd_factorial (by rw [mul_comm]; exact hb)
    have h3 := (Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero _) hb0).2 h2 p
    omega
  have hm : σ 0 (ordCompl[p] a.factorial) ≤ σ 0 (ordCompl[p] b.factorial) := by
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    apply Finset.card_le_card
    apply Nat.divisors_subset_of_dvd
    · exact (Nat.ordCompl_pos p hb0).ne'
    · exact Nat.ordCompl_dvd_ordCompl_of_dvd (Nat.factorial_dvd_factorial (by omega)) p
  rw [OMA.Helpers.sigma_split p _ hp ha0, OMA.Helpers.sigma_split p _ hp hb0]
  calc (s + 1) * ((a.factorial.factorization p + 1) * σ 0 (ordCompl[p] a.factorial))
      ≤ (s + 1) * (s * σ 0 (ordCompl[p] a.factorial)) := by gcongr
    _ = s * ((s + 1) * σ 0 (ordCompl[p] a.factorial)) := by ring
    _ ≤ s * ((b.factorial.factorization p + 1) * σ 0 (ordCompl[p] b.factorial)) := by
      gcongr
