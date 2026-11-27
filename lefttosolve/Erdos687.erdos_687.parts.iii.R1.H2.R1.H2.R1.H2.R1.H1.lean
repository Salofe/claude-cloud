import OMAReductions.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1

/-!
# Step `Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1.H2.R1.H1`

An unconditional `L²` bound for the minor-arc Ramanujan-Fejer sum over a full primorial
period. Expanding the square and using exact orthogonality of the reduced fractions `r / d`
(`d ∣ Q`) over `ℤ / Q ℤ`, the mean square is at most `Q` times the sum of the squared
coefficients. Parseval for the Fejer sum and the cancellation of complete periods bound the
fourth moment of each denominator by `2 d L ^ 3`, so the total is at most
`2 Q L ∑_{d ∣ Q} d / φ(d) ^ 2 = 2 Q L ∏_{p ≤ x} (1 + p / (p - 1) ^ 2)`. The last product is
`O(log x)` by an elementary Mertens bound, proved here from the Chebyshev bound
`∏_{p ≤ n} p ≤ 4 ^ n` and discrete Abel summation.
-/

open Finset Real

namespace OMA.Helpers

/-- Sum over the primes up to `N + 1` in terms of the primes up to `N`. -/
lemma sum_primes_succ (f : ℕ → ℝ) (N : ℕ) :
    ∑ p ∈ (range (N + 1 + 1)).filter Nat.Prime, f p =
      ∑ p ∈ (range (N + 1)).filter Nat.Prime, f p + (if (N + 1).Prime then f (N + 1) else 0) := by
  rw [Finset.range_add_one (n := N + 1), Finset.filter_insert]
  split_ifs with h
  · rw [Finset.sum_insert (by simp), add_comm]
  · rw [add_zero]

/-- Legendre-type bound `∑_{p ≤ N} ⌊N / p⌋ log p ≤ ∑_{m ≤ N} log m`: the primes `p ≤ N`
dividing a given `m` multiply to a divisor of `m`. -/
lemma sum_log_le_of_dvd (N : ℕ) :
    ∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p * ((N / p : ℕ) : ℝ) ≤
      ∑ m ∈ Ioc 0 N, Real.log m := by
  have key : ∀ m ∈ Ioc 0 N, ∑ p ∈ (range (N + 1)).filter Nat.Prime,
      (if p ∣ m then Real.log p else 0) ≤ Real.log m := by
    intro m hm
    have hm0 : 0 < m := (mem_Ioc.mp hm).1
    rw [← Finset.sum_filter]
    set S := ((range (N + 1)).filter Nat.Prime).filter (fun p => p ∣ m) with hS
    have hSprime : ∀ p ∈ S, p.Prime := fun p hp => (mem_filter.mp (mem_filter.mp hp).1).2
    have hprod : ∏ p ∈ S, p ∣ m := Finset.prod_primes_dvd m
      (fun p hp => (hSprime p hp).prime) (fun p hp => (mem_filter.mp hp).2)
    have hle : (∏ p ∈ S, p) ≤ m := Nat.le_of_dvd hm0 hprod
    have hprod_pos : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p hp => (hSprime p hp).pos)
    calc ∑ p ∈ S, Real.log p = Real.log (∏ p ∈ S, (p : ℝ)) := by
          rw [Real.log_prod]
          intro p hp
          exact_mod_cast (hSprime p hp).ne_zero
      _ = Real.log ((∏ p ∈ S, p : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ Real.log m := by
          apply Real.log_le_log (by exact_mod_cast hprod_pos)
          exact_mod_cast hle
  calc ∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p * ((N / p : ℕ) : ℝ)
        = ∑ p ∈ (range (N + 1)).filter Nat.Prime,
            ∑ m ∈ Ioc 0 N, (if p ∣ m then Real.log p else 0) := by
        refine sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul]
        ring
    _ = ∑ m ∈ Ioc 0 N, ∑ p ∈ (range (N + 1)).filter Nat.Prime,
            (if p ∣ m then Real.log p else 0) := Finset.sum_comm
    _ ≤ ∑ m ∈ Ioc 0 N, Real.log m := sum_le_sum key

/-- Chebyshev bound `θ(N) ≤ N log 4`. -/
lemma sum_log_primes_le (N : ℕ) :
    ∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p ≤ N * Real.log 4 := by
  have h4 := primorial_le_four_pow N
  have hpos : 0 < primorial N := primorial_pos N
  calc ∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p
        = Real.log (∏ p ∈ (range (N + 1)).filter Nat.Prime, (p : ℝ)) := by
        rw [Real.log_prod]
        intro p hp
        exact_mod_cast (mem_filter.mp hp).2.ne_zero
    _ = Real.log (primorial N : ℝ) := by
        unfold primorial
        push_cast
        rfl
    _ ≤ Real.log ((4 : ℝ) ^ N) := by
        apply Real.log_le_log (by exact_mod_cast hpos)
        exact_mod_cast h4
    _ = N * Real.log 4 := Real.log_pow 4 N

/-- Mertens' first theorem (upper bound): `∑_{p ≤ N} log p / p ≤ log N + log 4`. -/
lemma sum_log_div_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p / p ≤ Real.log N + Real.log 4 := by
  have h1 := sum_log_le_of_dvd N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h2 : ∑ m ∈ Ioc 0 N, Real.log m ≤ N * Real.log N := by
    calc ∑ m ∈ Ioc 0 N, Real.log m ≤ ∑ m ∈ Ioc 0 N, Real.log N := by
          refine sum_le_sum fun m hm => ?_
          have hm' := mem_Ioc.mp hm
          apply Real.log_le_log (by exact_mod_cast hm'.1)
          exact_mod_cast hm'.2
      _ = N * Real.log N := by
          rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.sub_zero]
  have h3 := sum_log_primes_le N
  have h4 : ∀ p ∈ (range (N + 1)).filter Nat.Prime,
      (N : ℝ) * (Real.log p / p) - Real.log p ≤ Real.log p * ((N / p : ℕ) : ℝ) := by
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hdiv : (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
      have hdm := Nat.div_add_mod N p
      have hlt := Nat.mod_lt N hpp.pos
      have hdm' : (p : ℝ) * ((N / p : ℕ) : ℝ) + ((N % p : ℕ) : ℝ) = N := by exact_mod_cast hdm
      have hlt' : ((N % p : ℕ) : ℝ) < p := by exact_mod_cast hlt
      rw [div_sub_one hp0.ne', div_le_iff₀ hp0]
      nlinarith
    calc (N : ℝ) * (Real.log p / p) - Real.log p = Real.log p * ((N : ℝ) / p - 1) := by
          field_simp
      _ ≤ Real.log p * ((N / p : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hdiv hlog
  have h5 : (N : ℝ) * ∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p / p -
      ∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p ≤ N * Real.log N := by
    rw [mul_sum, ← sum_sub_distrib]
    exact (sum_le_sum h4).trans (h1.trans h2)
  have h6 : (N : ℝ) * ∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p / p ≤
      N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left h6 hNpos

/-- `1 - log n / log (n + 1) ≤ log log (n + 1) - log log n` for `n ≥ 2`. -/
lemma loglog_step (n : ℕ) (hn : 2 ≤ n) :
    1 - Real.log n / Real.log ((n + 1 : ℕ) : ℝ) ≤
      Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log n) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hz : 0 < Real.log n := Real.log_pos hn1
  have hzy : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) (by push_cast; linarith)
  have hy : 0 < Real.log ((n + 1 : ℕ) : ℝ) := lt_of_lt_of_le hz hzy
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hy hz)
  rw [Real.log_div hy.ne' hz.ne', inv_div] at h
  linarith

/-- Partial sums `∑_{p ≤ N} log p / p`. -/
noncomputable def Asum (N : ℕ) : ℝ := ∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p / p

/-- Partial sums `∑_{p ≤ N} 1 / p`. -/
noncomputable def Bsum (N : ℕ) : ℝ := ∑ p ∈ (range (N + 1)).filter Nat.Prime, (1 : ℝ) / p

lemma AB_step (N : ℕ) (hN : 1 ≤ N) :
    Bsum (N + 1) - Asum (N + 1) / Real.log ((N + 1 : ℕ) : ℝ) =
      Bsum N - Asum N / Real.log ((N + 1 : ℕ) : ℝ) := by
  have hlog : Real.log ((N + 1 : ℕ) : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    exact_mod_cast (show 1 < N + 1 by omega)
  have hN0 : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold Asum Bsum
  rw [sum_primes_succ, sum_primes_succ]
  split_ifs with h
  · field_simp
    ring
  · simp

lemma abel_invariant (N : ℕ) (hN : 2 ≤ N) :
    Bsum N - Asum N / Real.log N ≤
      Real.log (Real.log N) - Real.log (Real.log 2) + Real.log 4 / Real.log 2 -
        Real.log 4 / Real.log N := by
  induction N, hN using Nat.le_induction with
  | base =>
    have hP : (range (2 + 1)).filter Nat.Prime = {2} := by decide
    have hlog2 : Real.log 2 ≠ 0 := by positivity
    unfold Asum Bsum
    rw [hP, sum_singleton, sum_singleton]
    push_cast
    field_simp
    ring_nf
    rfl
  | succ n hn ih =>
    have hstep := AB_step n (by omega)
    have hA := sum_log_div_le n (by omega)
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hz : 0 < Real.log n := Real.log_pos hn1
    have hzy : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) (by push_cast; linarith)
    have hy : 0 < Real.log ((n + 1 : ℕ) : ℝ) := lt_of_lt_of_le hz hzy
    have hll := loglog_step n hn
    have hnonneg : 0 ≤ 1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le hz hzy
    have hmul : Asum n * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) ≤
        (Real.log n + Real.log 4) * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hA hnonneg
    have hexpand : (Real.log n + Real.log 4) * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) =
        (1 - Real.log n / Real.log ((n + 1 : ℕ) : ℝ)) + Real.log 4 / Real.log n -
          Real.log 4 / Real.log ((n + 1 : ℕ) : ℝ) := by
      field_simp
      ring
    have hsplit : Bsum n - Asum n / Real.log ((n + 1 : ℕ) : ℝ) =
        (Bsum n - Asum n / Real.log n) +
          Asum n * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) := by
      field_simp
      ring
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [show ((n + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) from rfl]
    rw [hstep, hsplit]
    linarith

/-- Mertens' second theorem (upper bound): `∑_{p ≤ N} 1 / p ≤ log log N + K₀`. -/
lemma sum_inv_primes_le (N : ℕ) (hN : 2 ≤ N) :
    Bsum N ≤ Real.log (Real.log N) +
      (1 - Real.log (Real.log 2) + Real.log 4 / Real.log 2) := by
  have hinv := abel_invariant N hN
  have hA := sum_log_div_le N (by omega)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hz : 0 < Real.log N := Real.log_pos hN1
  have hdiv : Asum N / Real.log N ≤ 1 + Real.log 4 / Real.log N := by
    rw [div_le_iff₀ hz]
    have : (1 + Real.log 4 / Real.log N) * Real.log N = Real.log N + Real.log 4 := by
      field_simp
    unfold Asum
    rw [this]
    exact hA
  linarith

/-- The correction terms `p / (p - 1) ^ 2 - 1 / p` have bounded sum. -/
lemma sum_correction_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ p ∈ (range (N + 1)).filter Nat.Prime, ((p : ℝ) / ((p : ℝ) - 1) ^ 2 - 1 / (p : ℝ)) ≤
      (3 : ℝ) - 3 / (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base =>
    have hP : (range (1 + 1)).filter Nat.Prime = ∅ := by decide
    rw [hP, sum_empty]
    norm_num
  | succ n hn ih =>
    rw [sum_primes_succ]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hmono : 3 - 3 / (n : ℝ) ≤ 3 - 3 / ((n + 1 : ℕ) : ℝ) := by
      have : 3 / ((n + 1 : ℕ) : ℝ) ≤ 3 / (n : ℝ) := by
        apply div_le_div_of_nonneg_left (by norm_num) hn0
        push_cast
        linarith
      linarith
    split_ifs with h
    · have hterm : ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) - 1) ^ 2 - 1 / ((n + 1 : ℕ) : ℝ) ≤
          3 / (n : ℝ) - 3 / ((n + 1 : ℕ) : ℝ) := by
        push_cast
        have e : ((n : ℝ) + 1 - 1) = n := by ring
        rw [e]
        rw [div_sub_div _ _ (by positivity) (by positivity),
          div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith [mul_pos hn0 hn0, mul_pos (mul_pos hn0 hn0) hn0]
      linarith
    · linarith

/-- Mertens-type product bound: `∏_{p ≤ N} (1 + p / (p - 1) ^ 2) ≤ K log N` for `N ≥ 2`. -/
lemma mertens_prod_bound : ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 2 ≤ N →
    ∏ p ∈ (range (N + 1)).filter Nat.Prime, (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) ≤
      K * Real.log N := by
  refine ⟨Real.exp ((1 - Real.log (Real.log 2) + Real.log 4 / Real.log 2) + 3),
    Real.exp_pos _, fun N hN => ?_⟩
  have hB := sum_inv_primes_le N hN
  have hT := sum_correction_le N (by omega)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hz : 0 < Real.log N := Real.log_pos hN1
  have hprod_le : ∏ p ∈ (range (N + 1)).filter Nat.Prime, (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) ≤
      ∏ p ∈ (range (N + 1)).filter Nat.Prime, Real.exp ((p : ℝ) / ((p : ℝ) - 1) ^ 2) := by
    apply Finset.prod_le_prod
    · intro p hp
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
      have : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by positivity
      linarith
    · intro p _
      linarith [Real.add_one_le_exp ((p : ℝ) / ((p : ℝ) - 1) ^ 2)]
  rw [← Real.exp_sum] at hprod_le
  have hsum : ∑ p ∈ (range (N + 1)).filter Nat.Prime, (p : ℝ) / ((p : ℝ) - 1) ^ 2 =
      Bsum N + ∑ p ∈ (range (N + 1)).filter Nat.Prime,
        ((p : ℝ) / ((p : ℝ) - 1) ^ 2 - 1 / (p : ℝ)) := by
    unfold Bsum
    rw [← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    ring
  have h3N : 0 ≤ 3 / (N : ℝ) := by positivity
  have hle : ∑ p ∈ (range (N + 1)).filter Nat.Prime, (p : ℝ) / ((p : ℝ) - 1) ^ 2 ≤
      Real.log (Real.log N) + ((1 - Real.log (Real.log 2) + Real.log 4 / Real.log 2) + 3) := by
    rw [hsum]
    linarith
  calc ∏ p ∈ (range (N + 1)).filter Nat.Prime, (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2)
      ≤ Real.exp (∑ p ∈ (range (N + 1)).filter Nat.Prime, (p : ℝ) / ((p : ℝ) - 1) ^ 2) :=
        hprod_le
    _ ≤ Real.exp (Real.log (Real.log N) +
          ((1 - Real.log (Real.log 2) + Real.log 4 / Real.log 2) + 3)) := Real.exp_le_exp.mpr hle
    _ = Real.exp ((1 - Real.log (Real.log 2) + Real.log 4 / Real.log 2) + 3) * Real.log N := by
        rw [Real.exp_add, Real.exp_log hz]
        ring


/-- `ex d r n = exp(2 π i r n / d)`. -/
noncomputable def ex (d r n : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * (r : ℝ) * (n : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)

/-- The Fejér-type exponential sum `F_d(r) = ∑_{u < L} e(r u / d)`. -/
noncomputable def FF (d r L : ℕ) : ℂ := ∑ u ∈ range L, ex d r u

lemma norm_ex (d r n : ℕ) : ‖ex d r n‖ = 1 := Complex.norm_exp_ofReal_mul_I _

/-- `exp(2 π i m / Q) ≠ 1` when `Q ∤ m`. -/
lemma exp_ne_one_of_not_dvd (Q : ℕ) (hQ : 0 < Q) (m : ℤ) (h : ¬ (Q : ℤ) ∣ m) :
    Complex.exp (((2 * Real.pi * (m : ℝ) / (Q : ℝ) : ℝ) : ℂ) * Complex.I) ≠ 1 := by
  intro h1
  rw [Complex.exp_eq_one_iff] at h1
  obtain ⟨n, hn⟩ := h1
  apply h
  refine ⟨n, ?_⟩
  have hQne : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have h2 : ((2 * Real.pi * (m : ℝ) / (Q : ℝ) : ℝ) : ℂ) = (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
    apply mul_right_cancel₀ Complex.I_ne_zero
    rw [hn]
    push_cast
    ring
  have h3 : 2 * Real.pi * (m : ℝ) / (Q : ℝ) = (n : ℝ) * (2 * Real.pi) := by exact_mod_cast h2
  rw [div_eq_iff hQne] at h3
  have h4 : (2 * Real.pi) * ((m : ℝ) - (Q : ℝ) * n) = 0 := by linear_combination h3
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  have key : (m : ℝ) = (Q : ℝ) * n := by
    have := (mul_eq_zero.mp h4).resolve_left h2pi
    linarith
  exact_mod_cast key

/-- `exp(2 π i m / Q) ^ Q = 1`. -/
lemma exp_pow_eq_one (Q : ℕ) (hQ : 0 < Q) (m : ℤ) :
    (Complex.exp (((2 * Real.pi * (m : ℝ) / (Q : ℝ) : ℝ) : ℂ) * Complex.I)) ^ Q = 1 := by
  rw [← Complex.exp_nat_mul]
  have hQne : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have : (Q : ℂ) * (((2 * Real.pi * (m : ℝ) / (Q : ℝ) : ℝ) : ℂ) * Complex.I) =
      (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp
  rw [this]
  exact Complex.exp_int_mul_two_pi_mul_I m

/-- Geometric sum of `Q`-th roots of unity. -/
lemma sum_range_exp_int (Q : ℕ) (hQ : 0 < Q) (m : ℤ) :
    ∑ M ∈ range Q, Complex.exp (((2 * Real.pi * (m : ℝ) * (M : ℝ) / (Q : ℝ) : ℝ) : ℂ) * Complex.I) =
      if (Q : ℤ) ∣ m then (Q : ℂ) else 0 := by
  set ζ : ℂ := Complex.exp (((2 * Real.pi * (m : ℝ) / (Q : ℝ) : ℝ) : ℂ) * Complex.I) with hζ
  have hterm : ∀ M : ℕ,
      Complex.exp (((2 * Real.pi * (m : ℝ) * (M : ℝ) / (Q : ℝ) : ℝ) : ℂ) * Complex.I) = ζ ^ M := by
    intro M
    rw [hζ, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun M _ => hterm M)]
  have hQne : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  by_cases h : (Q : ℤ) ∣ m
  · rw [if_pos h]
    obtain ⟨k, hk⟩ := h
    have hζ1 : ζ = 1 := by
      rw [hζ]
      have : (((2 * Real.pi * (m : ℝ) / (Q : ℝ) : ℝ) : ℂ) * Complex.I) =
          (k : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hk]
        push_cast
        field_simp
      rw [this]
      exact Complex.exp_int_mul_two_pi_mul_I k
    simp [hζ1]
  · rw [if_neg h]
    have hζne : ζ ≠ 1 := exp_ne_one_of_not_dvd Q hQ m h
    have hζQ : ζ ^ Q = 1 := exp_pow_eq_one Q hQ m
    rw [geom_sum_eq hζne, hζQ, sub_self, zero_div]

/-- Exact orthogonality of distinct reduced fractions `r / d` with `d ∣ Q` over a full period. -/
lemma orth (Q L : ℕ) (hQ : 0 < Q) {d₁ d₂ r₁ r₂ : ℕ} (h₁ : d₁ ∣ Q) (h₂ : d₂ ∣ Q)
    (hr₁ : r₁ < d₁) (hr₂ : r₂ < d₂) (hc₁ : Nat.Coprime r₁ d₁) (hc₂ : Nat.Coprime r₂ d₂) :
    ∑ M ∈ range Q, ex d₁ r₁ (M + L) * (starRingEnd ℂ) (ex d₂ r₂ (M + L)) =
      if d₁ = d₂ ∧ r₁ = r₂ then (Q : ℂ) else 0 := by
  by_cases heq : d₁ = d₂ ∧ r₁ = r₂
  · rw [if_pos heq]
    obtain ⟨rfl, rfl⟩ := heq
    have hone : ∀ M : ℕ, ex d₁ r₁ (M + L) * (starRingEnd ℂ) (ex d₁ r₁ (M + L)) = 1 := by
      intro M
      rw [Complex.mul_conj', norm_ex]
      simp
    rw [Finset.sum_congr rfl (fun M _ => hone M)]
    simp
  · rw [if_neg heq]
    obtain ⟨q₁, hq₁⟩ := h₁
    obtain ⟨q₂, hq₂⟩ := h₂
    have hd₁ : 0 < d₁ := by omega
    have hd₂ : 0 < d₂ := by omega
    have hq₁pos : 0 < q₁ := by
      rcases Nat.eq_zero_or_pos q₁ with h | h
      · rw [h, mul_zero] at hq₁
        omega
      · exact h
    have hq₂pos : 0 < q₂ := by
      rcases Nat.eq_zero_or_pos q₂ with h | h
      · rw [h, mul_zero] at hq₂
        omega
      · exact h
    set m : ℤ := ((r₁ * q₁ : ℕ) : ℤ) - ((r₂ * q₂ : ℕ) : ℤ) with hm
    have hterm : ∀ M : ℕ, ex d₁ r₁ (M + L) * (starRingEnd ℂ) (ex d₂ r₂ (M + L)) =
        Complex.exp (((2 * Real.pi * (m : ℝ) * (L : ℝ) / (Q : ℝ) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((2 * Real.pi * (m : ℝ) * (M : ℝ) / (Q : ℝ) : ℝ) : ℂ) * Complex.I) := by
      intro M
      unfold ex
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add,
        ← Complex.exp_add]
      congr 1
      have hQ₁ : (Q : ℝ) = (d₁ : ℝ) * (q₁ : ℝ) := by exact_mod_cast hq₁
      have hQ₂ : (Q : ℝ) = (d₂ : ℝ) * (q₂ : ℝ) := by exact_mod_cast hq₂
      have hd₁ne : (d₁ : ℝ) ≠ 0 := by exact_mod_cast hd₁.ne'
      have hd₂ne : (d₂ : ℝ) ≠ 0 := by exact_mod_cast hd₂.ne'
      have hq₁ne : (q₁ : ℝ) ≠ 0 := by exact_mod_cast hq₁pos.ne'
      have hq₂ne : (q₂ : ℝ) ≠ 0 := by exact_mod_cast hq₂pos.ne'
      have e1 : (r₁ : ℝ) / d₁ = ((r₁ : ℝ) * q₁) / Q := by
        rw [hQ₁]
        field_simp
      have e2 : (r₂ : ℝ) / d₂ = ((r₂ : ℝ) * q₂) / Q := by
        rw [hQ₂]
        field_simp
      have hmR : (m : ℝ) = (r₁ : ℝ) * q₁ - (r₂ : ℝ) * q₂ := by
        rw [hm]
        push_cast
        ring
      have hreal : 2 * Real.pi * (r₁ : ℝ) * ((M + L : ℕ) : ℝ) / (d₁ : ℝ) -
          2 * Real.pi * (r₂ : ℝ) * ((M + L : ℕ) : ℝ) / (d₂ : ℝ) =
          2 * Real.pi * (m : ℝ) * (L : ℝ) / (Q : ℝ) + 2 * Real.pi * (m : ℝ) * (M : ℝ) / (Q : ℝ) := by
        calc _ = 2 * Real.pi * ((M + L : ℕ) : ℝ) * ((r₁ : ℝ) / d₁ - (r₂ : ℝ) / d₂) := by ring
          _ = 2 * Real.pi * ((M + L : ℕ) : ℝ) * (((r₁ : ℝ) * q₁) / Q - ((r₂ : ℝ) * q₂) / Q) := by
              rw [e1, e2]
          _ = _ := by
              rw [hmR]
              push_cast
              ring
      have hc := congrArg (fun t : ℝ => (t : ℂ) * Complex.I) hreal
      push_cast at hc ⊢
      linear_combination hc
    rw [Finset.sum_congr rfl (fun M _ => hterm M), ← Finset.mul_sum, sum_range_exp_int Q hQ m]
    have hndvd : ¬ (Q : ℤ) ∣ m := by
      intro hdvd
      have hlt1 : r₁ * q₁ < Q := by
        rw [hq₁]
        exact Nat.mul_lt_mul_of_pos_right hr₁ hq₁pos
      have hlt2 : r₂ * q₂ < Q := by
        rw [hq₂]
        exact Nat.mul_lt_mul_of_pos_right hr₂ hq₂pos
      generalize ha : r₁ * q₁ = a at hlt1 hm
      generalize hb : r₂ * q₂ = b at hlt2 hm
      have habs : |m| < (Q : ℤ) := by
        rw [abs_lt, hm]
        constructor <;> omega
      have hm0 : m = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
      have heqn : r₁ * q₁ = r₂ * q₂ := by
        rw [ha, hb]
        omega
      have hcross : r₁ * d₂ * Q = r₂ * d₁ * Q := by
        calc r₁ * d₂ * Q = r₁ * d₂ * (d₁ * q₁) := by rw [← hq₁]
          _ = d₁ * d₂ * (r₁ * q₁) := by ring
          _ = d₁ * d₂ * (r₂ * q₂) := by rw [heqn]
          _ = r₂ * d₁ * (d₂ * q₂) := by ring
          _ = r₂ * d₁ * Q := by rw [← hq₂]
      have hcross' : r₁ * d₂ = r₂ * d₁ := Nat.eq_of_mul_eq_mul_right hQ hcross
      have hd12 : d₁ ∣ d₂ := by
        have : d₁ ∣ r₁ * d₂ := ⟨r₂, by rw [hcross', mul_comm]⟩
        exact Nat.Coprime.dvd_of_dvd_mul_left hc₁.symm this
      have hd21 : d₂ ∣ d₁ := by
        have : d₂ ∣ r₂ * d₁ := ⟨r₁, by rw [← hcross', mul_comm]⟩
        exact Nat.Coprime.dvd_of_dvd_mul_left hc₂.symm this
      have hd : d₁ = d₂ := Nat.dvd_antisymm hd12 hd21
      subst hd
      have hr : r₁ = r₂ := Nat.eq_of_mul_eq_mul_right hd₁ hcross'
      exact heq ⟨rfl, hr⟩
    rw [if_neg hndvd, mul_zero]

/-- Abstract `L²` expansion over a finite orthogonal system. -/
lemma l2_expand {ι : Type*} [DecidableEq ι] (I : Finset ι) (c : ι → ℝ) (E : ι → ℕ → ℂ) (Q : ℕ)
    (horth : ∀ k ∈ I, ∀ l ∈ I, ∑ M ∈ range Q, E k M * (starRingEnd ℂ) (E l M) =
      if k = l then (Q : ℂ) else 0) :
    ∑ M ∈ range Q, ‖∑ k ∈ I, (c k : ℂ) * E k M‖ ^ 2 = (Q : ℝ) * ∑ k ∈ I, (c k) ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  have h1 : ∀ M ∈ range Q, ((‖∑ k ∈ I, (c k : ℂ) * E k M‖ : ℝ) : ℂ) ^ 2 =
      ∑ k ∈ I, ∑ l ∈ I, ((c k : ℂ) * (c l : ℂ)) * (E k M * (starRingEnd ℂ) (E l M)) := by
    intro M _
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∀ k ∈ I, ∑ M ∈ range Q, ∑ l ∈ I,
      ((c k : ℂ) * (c l : ℂ)) * (E k M * (starRingEnd ℂ) (E l M)) = (Q : ℂ) * (c k : ℂ) ^ 2 := by
    intro k hk
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun l hl => by rw [horth k hk l hl])]
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq I k, if_pos hk]
    ring
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]

/-- Parseval identity for the Fejér-type sum. -/
lemma parseval (d L : ℕ) (hd : 0 < d) :
    ∑ r ∈ range d, ‖FF d r L‖ ^ 2 =
      (d : ℝ) * ∑ u ∈ range L, ∑ v ∈ range L,
        (if (d : ℤ) ∣ ((u : ℤ) - (v : ℤ)) then (1 : ℝ) else 0) := by
  apply Complex.ofReal_injective
  push_cast
  have h1 : ∀ r ∈ range d, ((‖FF d r L‖ : ℝ) : ℂ) ^ 2 = ∑ u ∈ range L, ∑ v ∈ range L,
      Complex.exp (((2 * Real.pi * (((u : ℤ) - (v : ℤ) : ℤ) : ℝ) * (r : ℝ) / (d : ℝ) : ℝ) : ℂ) *
        Complex.I) := by
    intro r _
    rw [← Complex.mul_conj', FF, map_sum, Finset.sum_mul_sum]
    refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
    unfold ex
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  refine sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine sum_congr rfl fun v _ => ?_
  rw [sum_range_exp_int d hd]
  split_ifs <;> simp

/-- Counting the `v < L` in a fixed residue class modulo `d`. -/
lemma count_le (d L u : ℕ) :
    ∑ v ∈ range L, (if (d : ℤ) ∣ ((u : ℤ) - (v : ℤ)) then (1 : ℝ) else 0) ≤
      ((L / d : ℕ) : ℝ) + 1 := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : ((range L).filter (fun v : ℕ => (d : ℤ) ∣ ((u : ℤ) - (v : ℤ)))).card ≤ L / d + 1 := by
    have h := Finset.card_le_card_of_injOn (fun v => v / d)
      (s := (range L).filter (fun v : ℕ => (d : ℤ) ∣ ((u : ℤ) - (v : ℤ)))) (t := range (L / d + 1))
      ?_ ?_
    · simpa using h
    · intro v hv
      simp only [Finset.mem_coe, mem_filter, mem_range] at hv ⊢
      exact Nat.lt_succ_of_le (Nat.div_le_div_right hv.1.le)
    · intro v₁ hv₁ v₂ hv₂ heq
      simp only [Finset.mem_coe, mem_filter, mem_range] at hv₁ hv₂
      simp only at heq
      have h12 : (d : ℤ) ∣ (v₂ : ℤ) - (v₁ : ℤ) := by
        have := dvd_sub hv₁.2 hv₂.2
        rwa [show ((u : ℤ) - v₁) - ((u : ℤ) - v₂) = (v₂ : ℤ) - v₁ by ring] at this
      have hmod : v₁ % d = v₂ % d := Nat.modEq_iff_dvd.mpr h12
      calc v₁ = d * (v₁ / d) + v₁ % d := (Nat.div_add_mod v₁ d).symm
        _ = d * (v₂ / d) + v₂ % d := by rw [heq, hmod]
        _ = v₂ := Nat.div_add_mod v₂ d
  have : (((range L).filter (fun v : ℕ => (d : ℤ) ∣ ((u : ℤ) - (v : ℤ)))).card : ℝ) ≤
      ((L / d + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
  simpa using this

/-- Parseval upper bound: `∑_{r < d} |F_d(r)|² ≤ L (L + d)`. -/
lemma parseval_le (d L : ℕ) (hd : 0 < d) :
    ∑ r ∈ range d, ‖FF d r L‖ ^ 2 ≤ (L : ℝ) * (L + d) := by
  rw [parseval d L hd]
  have hcount : ∀ u ∈ range L, ∑ v ∈ range L,
      (if (d : ℤ) ∣ ((u : ℤ) - (v : ℤ)) then (1 : ℝ) else 0) ≤ ((L / d : ℕ) : ℝ) + 1 :=
    fun u _ => count_le d L u
  have hdiv : (d : ℝ) * ((L / d : ℕ) : ℝ) ≤ L := by exact_mod_cast Nat.mul_div_le L d
  calc (d : ℝ) * ∑ u ∈ range L, ∑ v ∈ range L,
        (if (d : ℤ) ∣ ((u : ℤ) - (v : ℤ)) then (1 : ℝ) else 0)
      ≤ (d : ℝ) * ∑ u ∈ range L, (((L / d : ℕ) : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (sum_le_sum hcount) (by positivity)
    _ = (L : ℝ) * ((d : ℝ) * ((L / d : ℕ) : ℝ) + d) := by
        rw [sum_const, card_range, nsmul_eq_mul]
        ring
    _ ≤ (L : ℝ) * (L + d) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

lemma norm_FF_le_L (d r L : ℕ) : ‖FF d r L‖ ≤ L := by
  unfold FF
  calc ‖∑ u ∈ range L, ex d r u‖ ≤ ∑ u ∈ range L, ‖ex d r u‖ := norm_sum_le _ _
    _ = L := by simp [norm_ex]

lemma FF_eq_geom (d r L : ℕ) : FF d r L = ∑ u ∈ range L, (ex d r 1) ^ u := by
  unfold FF
  refine sum_congr rfl fun u _ => ?_
  unfold ex
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma ex_one_eq (d r : ℕ) :
    ex d r 1 = Complex.exp (((2 * Real.pi * ((r : ℤ) : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I) := by
  unfold ex
  congr 1
  push_cast
  ring

/-- For `d ∤ r`, the Fejér-type sum is bounded by `d` (full periods cancel). -/
lemma norm_FF_le_d (d r L : ℕ) (hd : 0 < d) (hr : ¬ d ∣ r) : ‖FF d r L‖ ≤ d := by
  have hζ : ex d r 1 ≠ 1 := by
    rw [ex_one_eq]
    exact exp_ne_one_of_not_dvd d hd r (fun h => hr (Int.natCast_dvd_natCast.mp h))
  have hζd : (ex d r 1) ^ d = 1 := by
    rw [ex_one_eq]
    exact exp_pow_eq_one d hd r
  have hFF : FF d r L = FF d r (L % d) := by
    rw [FF_eq_geom, FF_eq_geom, geom_sum_eq hζ, geom_sum_eq hζ]
    congr 2
    conv_lhs => rw [← Nat.div_add_mod L d]
    rw [pow_add, pow_mul, hζd, one_pow, one_mul]
  rw [hFF]
  calc ‖FF d r (L % d)‖ ≤ ((L % d : ℕ) : ℝ) := norm_FF_le_L d r (L % d)
    _ ≤ d := by exact_mod_cast (Nat.mod_lt L hd).le

/-- Fourth-moment bound for one denominator `d ≥ 2`. -/
lemma sum_FF4_le (d L : ℕ) (hd : 2 ≤ d) :
    ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d), ‖FF d r L‖ ^ 4 ≤
      2 * (d : ℝ) * (L : ℝ) ^ 3 := by
  have hpars : ∑ r ∈ range d, ‖FF d r L‖ ^ 2 ≤ (L : ℝ) * (L + d) := parseval_le d L (by omega)
  have hnd : ∀ r ∈ (range d).filter (fun r => Nat.Coprime r d), ¬ d ∣ r := by
    intro r hr hdvd
    obtain ⟨hr1, hr2⟩ := mem_filter.mp hr
    have hrd := mem_range.mp hr1
    have hr0 : r = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hrd
    rw [hr0, Nat.coprime_zero_left] at hr2
    omega
  have key : ∀ B : ℝ, 0 ≤ B →
      (∀ r ∈ (range d).filter (fun r => Nat.Coprime r d), ‖FF d r L‖ ≤ B) →
      ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d), ‖FF d r L‖ ^ 4 ≤
        B ^ 2 * ((L : ℝ) * (L + d)) := by
    intro B hB hbound
    calc ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d), ‖FF d r L‖ ^ 4
        ≤ ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d), B ^ 2 * ‖FF d r L‖ ^ 2 := by
          refine sum_le_sum fun r hr => ?_
          have h := hbound r hr
          have h0 := norm_nonneg (FF d r L)
          have hsq : ‖FF d r L‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ h0 h 2
          have hsq0 : 0 ≤ ‖FF d r L‖ ^ 2 := by positivity
          calc ‖FF d r L‖ ^ 4 = ‖FF d r L‖ ^ 2 * ‖FF d r L‖ ^ 2 := by ring
            _ ≤ B ^ 2 * ‖FF d r L‖ ^ 2 := mul_le_mul_of_nonneg_right hsq hsq0
      _ ≤ ∑ r ∈ range d, B ^ 2 * ‖FF d r L‖ ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
      _ = B ^ 2 * ∑ r ∈ range d, ‖FF d r L‖ ^ 2 := by rw [mul_sum]
      _ ≤ B ^ 2 * ((L : ℝ) * (L + d)) := mul_le_mul_of_nonneg_left hpars (by positivity)
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hL0 : (0 : ℝ) ≤ L := by positivity
  by_cases hdL : d ≤ L
  · have h := key d hd0 (fun r hr => norm_FF_le_d d r L (by omega) (hnd r hr))
    have hdL' : (d : ℝ) ≤ L := by exact_mod_cast hdL
    have hfin : (d : ℝ) ^ 2 * ((L : ℝ) * (L + d)) ≤ 2 * (d : ℝ) * (L : ℝ) ^ 3 := by
      have h1 : 0 ≤ (d : ℝ) * L * ((L - d) * (2 * L + d)) :=
        mul_nonneg (mul_nonneg hd0 hL0) (mul_nonneg (by linarith) (by linarith))
      nlinarith [h1]
    linarith
  · have h := key L hL0 (fun r _ => norm_FF_le_L d r L)
    have hdL' : (L : ℝ) ≤ d := by exact_mod_cast (not_le.mp hdL).le
    have hfin : (L : ℝ) ^ 2 * ((L : ℝ) * (L + d)) ≤ 2 * (d : ℝ) * (L : ℝ) ^ 3 := by
      have h1 : 0 ≤ (L : ℝ) ^ 3 * (d - L) := mul_nonneg (by positivity) (by linarith)
      nlinarith [h1]
    linarith

/-- Coefficient bound for one denominator `d ≥ 2`. -/
lemma per_d_bound (d L : ℕ) (hd : 2 ≤ d) (hL : 1 ≤ L) :
    ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
      (((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) * (‖FF d r L‖ ^ 2 / (L : ℝ))) ^ 2 ≤
      2 * (L : ℝ) * ((d : ℝ) / (Nat.totient d : ℝ) ^ 2) := by
  have h4 := sum_FF4_le d L hd
  have hmu : ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 ≤ 1 := by
    have h := ArithmeticFunction.abs_moebius_le_one (n := d)
    have h' : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast h
    have h0 : 0 ≤ |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := abs_nonneg _
    rw [← sq_abs]
    nlinarith
  have hφ : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hsum_nn : 0 ≤ ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d), ‖FF d r L‖ ^ 4 :=
    sum_nonneg (fun _ _ => by positivity)
  calc ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
        (((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) * (‖FF d r L‖ ^ 2 / (L : ℝ))) ^ 2
      = (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 / ((Nat.totient d : ℝ) ^ 2 * (L : ℝ) ^ 2)) *
          ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d), ‖FF d r L‖ ^ 4 := by
        rw [mul_sum]
        refine sum_congr rfl fun r _ => ?_
        field_simp
    _ ≤ (1 / ((Nat.totient d : ℝ) ^ 2 * (L : ℝ) ^ 2)) * (2 * (d : ℝ) * (L : ℝ) ^ 3) := by
        apply mul_le_mul _ h4 hsum_nn (by positivity)
        exact div_le_div_of_nonneg_right hmu (by positivity)
    _ = 2 * (L : ℝ) * ((d : ℝ) / (Nat.totient d : ℝ) ^ 2) := by
        field_simp

/-- The minor-arc sum is the real part of an exponential sum over a sigma-finset. -/
lemma S_eq_re (Dset : Finset ℕ) (L M : ℕ) (w : ℕ → ℕ → ℝ) (a : ℕ → ℝ) :
    ∑ d ∈ Dset, a d * ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
        Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) * w d r =
      (∑ k ∈ Dset.sigma (fun d => (range d).filter (fun r => Nat.Coprime r d)),
        ((a k.1 * w k.1 k.2 : ℝ) : ℂ) * ex k.1 k.2 (M + L)).re := by
  rw [Finset.sum_sigma, Complex.re_sum]
  refine sum_congr rfl fun d _ => ?_
  rw [Complex.re_sum, Finset.mul_sum]
  refine sum_congr rfl fun r _ => ?_
  rw [Complex.re_ofReal_mul, ex, Complex.exp_ofReal_mul_I_re]
  ring

/-- Main `L²` bound for the minor-arc sum over a full period. -/
theorem fourier_bound (Q L : ℕ) (hQ : 0 < Q) (hL : 1 ≤ L) (Dset : Finset ℕ)
    (hD : ∀ d ∈ Dset, d ∣ Q ∧ 2 ≤ d) :
    ∑ M ∈ range Q, (∑ d ∈ Dset, ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
        ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
          Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
            (‖∑ u ∈ range L,
              Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
              (L : ℝ))) ^ 2 ≤
      (Q : ℝ) * (2 * (L : ℝ) * ∑ d ∈ Dset, (d : ℝ) / (Nat.totient d : ℝ) ^ 2) := by
  set I := Dset.sigma (fun d => (range d).filter (fun r => Nat.Coprime r d)) with hI
  set c : (Σ _ : ℕ, ℕ) → ℝ := fun k =>
    ((ArithmeticFunction.moebius k.1 : ℝ) / (Nat.totient k.1 : ℝ)) * (‖FF k.1 k.2 L‖ ^ 2 / (L : ℝ))
    with hc
  set E : (Σ _ : ℕ, ℕ) → ℕ → ℂ := fun k M => ex k.1 k.2 (M + L) with hE
  have hS : ∀ M : ℕ, (∑ d ∈ Dset, ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
        ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
          Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
            (‖∑ u ∈ range L,
              Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
              (L : ℝ))) = (∑ k ∈ I, (c k : ℂ) * E k M).re := by
    intro M
    exact S_eq_re Dset L M (fun d r => ‖FF d r L‖ ^ 2 / (L : ℝ))
      (fun d => (ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ))
  have hle : ∀ M : ℕ, ((∑ k ∈ I, (c k : ℂ) * E k M).re) ^ 2 ≤ ‖∑ k ∈ I, (c k : ℂ) * E k M‖ ^ 2 := by
    intro M
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
  have horth : ∀ k ∈ I, ∀ l ∈ I, ∑ M ∈ range Q, E k M * (starRingEnd ℂ) (E l M) =
      if k = l then (Q : ℂ) else 0 := by
    intro k hk l hl
    obtain ⟨d₁, r₁⟩ := k
    obtain ⟨d₂, r₂⟩ := l
    rw [hI, Finset.mem_sigma, mem_filter, mem_range] at hk hl
    have h := orth Q L hQ (hD d₁ hk.1).1 (hD d₂ hl.1).1 hk.2.1 hl.2.1 hk.2.2 hl.2.2
    simp only [hE]
    rw [h]
    congr 1
    simp
  calc ∑ M ∈ range Q, (∑ d ∈ Dset, ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
        ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
          Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
            (‖∑ u ∈ range L,
              Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
              (L : ℝ))) ^ 2
      = ∑ M ∈ range Q, ((∑ k ∈ I, (c k : ℂ) * E k M).re) ^ 2 := by
        refine sum_congr rfl fun M _ => ?_
        rw [hS M]
    _ ≤ ∑ M ∈ range Q, ‖∑ k ∈ I, (c k : ℂ) * E k M‖ ^ 2 := sum_le_sum fun M _ => hle M
    _ = (Q : ℝ) * ∑ k ∈ I, (c k) ^ 2 := l2_expand I c E Q horth
    _ ≤ (Q : ℝ) * (2 * (L : ℝ) * ∑ d ∈ Dset, (d : ℝ) / (Nat.totient d : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hI, Finset.sum_sigma, mul_sum]
        refine sum_le_sum fun d hd => ?_
        exact per_d_bound d L (hD d hd).2 hL


/-- The arithmetic function `d ↦ d / φ(d) ^ 2`. -/
noncomputable def gfun : ArithmeticFunction ℝ :=
  ⟨fun n => (n : ℝ) / (Nat.totient n : ℝ) ^ 2, by simp⟩

lemma gfun_apply (n : ℕ) : gfun n = (n : ℝ) / (Nat.totient n : ℝ) ^ 2 := rfl

lemma gfun_mult : gfun.IsMultiplicative := by
  refine ⟨by simp [gfun_apply], fun {m n} hmn => ?_⟩
  rw [gfun_apply, gfun_apply, gfun_apply, Nat.totient_mul hmn]
  push_cast
  ring

/-- `∑_{d ∣ Q} d / φ(d) ^ 2 = ∏_{p ≤ x} (1 + p / (p - 1) ^ 2)` for the primorial `Q`. -/
lemma divisor_sum_eq (x : ℕ) :
    ∑ d ∈ (∏ p ∈ (range (x + 1)).filter Nat.Prime, p).divisors,
        (d : ℝ) / (Nat.totient d : ℝ) ^ 2 =
      ∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) := by
  have hsq : Squarefree (∏ p ∈ (range (x + 1)).filter Nat.Prime, p) := squarefree_primorial x
  have hpf : (∏ p ∈ (range (x + 1)).filter Nat.Prime, p).primeFactors =
      (range (x + 1)).filter Nat.Prime :=
    Nat.primeFactors_prod (fun p hp => (mem_filter.mp hp).2)
  have h := gfun_mult.prodPrimeFactors_one_add_of_squarefree hsq
  rw [hpf] at h
  simp only [gfun_apply] at h
  rw [← h]
  refine prod_congr rfl fun p hp => ?_
  have hp' := (mem_filter.mp hp).2
  rw [Nat.totient_prime hp', Nat.cast_sub hp'.one_le, Nat.cast_one]

end OMA.Helpers

open Finset in
theorem OMA.solution : OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1.H1 := by
  obtain ⟨K, hK, hKbound⟩ := OMA.Helpers.mertens_prod_bound
  refine ⟨2 * K, by positivity, fun x hx L hL => ?_⟩
  intro D Q
  have hQpos : 0 < Q := Finset.prod_pos (fun p hp => (mem_filter.mp hp).2.pos)
  have hD1 : 1 ≤ D := by
    show 1 ≤ L / (Nat.log 2 L + 1)
    rw [Nat.le_div_iff_mul_le (Nat.succ_pos _), one_mul]
    exact Nat.log_lt_self 2 (by omega)
  have hDset : ∀ d ∈ Q.divisors.filter (fun d => D < d), d ∣ Q ∧ 2 ≤ d := by
    intro d hd
    obtain ⟨hd1, hd2⟩ := mem_filter.mp hd
    exact ⟨(Nat.mem_divisors.mp hd1).1, by omega⟩
  have hF := OMA.Helpers.fourier_bound Q L hQpos hL (Q.divisors.filter (fun d => D < d)) hDset
  have hsub : ∑ d ∈ Q.divisors.filter (fun d => D < d), (d : ℝ) / (Nat.totient d : ℝ) ^ 2 ≤
      ∑ d ∈ Q.divisors, (d : ℝ) / (Nat.totient d : ℝ) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
  have hprod := OMA.Helpers.divisor_sum_eq x
  have hmert := hKbound x hx
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hL0 : (0 : ℝ) ≤ L := by positivity
  have hdiv : ∑ d ∈ Q.divisors.filter (fun d => D < d), (d : ℝ) / (Nat.totient d : ℝ) ^ 2 ≤
      K * Real.log x := by
    calc ∑ d ∈ Q.divisors.filter (fun d => D < d), (d : ℝ) / (Nat.totient d : ℝ) ^ 2
        ≤ ∑ d ∈ Q.divisors, (d : ℝ) / (Nat.totient d : ℝ) ^ 2 := hsub
      _ = ∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2) := hprod
      _ ≤ K * Real.log x := hmert
  calc _ ≤ (Q : ℝ) * (2 * (L : ℝ) *
          ∑ d ∈ Q.divisors.filter (fun d => D < d), (d : ℝ) / (Nat.totient d : ℝ) ^ 2) := hF
    _ ≤ (Q : ℝ) * (2 * (L : ℝ) * (K * Real.log x)) := by
        apply mul_le_mul_of_nonneg_left _ hQ0
        exact mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = 2 * K * (Q : ℝ) * (L : ℝ) * Real.log x := by ring
