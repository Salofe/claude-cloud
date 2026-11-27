import OMAReductions.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1
import Mathlib

-- Step H1 of reduction Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1: Mertens lower bound
-- prod_{p <= x} (1 - 1/p) >= c / log x.
-- (1) Mertens 1: sum_{p <= N} log p / p <= log N + log 4, from Legendre (floor(N/p) <= v_p(N!)),
--     N! <= N^N and theta(N) <= N log 4.
-- (2) Discrete Abel summation: T(N) = R(N) - S(N)/log N satisfies
--     T(N+1) = T(N) + S(N) (1/log N - 1/log(N+1)), and log N (1/log N - 1/log(N+1)) is at most
--     loglog(N+1) - loglog N; so sum_{p <= N} 1/p <= loglog N + C.
-- (3) log(1 - 1/p) >= -1/(p-1) = -1/p - (1/(p-1) - 1/p), and the last sum telescopes to at most 1.

open Finset

namespace OMA.Helpers

theorem legendre_first (N p : ℕ) (hp : p.Prime) : N / p ≤ (N.factorial).factorization p := by
  rw [Nat.factorization_factorial hp (b := Nat.log p N + 2) (by omega)]
  have h1 : (1 : ℕ) ∈ Ico 1 (Nat.log p N + 2) := by simp
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) h1
  simpa using this

theorem log_factorial_ge (N : ℕ) :
    ∑ p ∈ (range (N + 1)).filter Nat.Prime, ((N / p : ℕ) : ℝ) * Real.log p ≤
      Real.log (N.factorial : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization]
  have hsub : (N.factorial).factorization.support ⊆ (range (N + 1)).filter Nat.Prime := by
    intro p hp
    rw [Nat.support_factorization] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    rw [hpp.dvd_factorial] at hdvd
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpp⟩
  rw [Finsupp.sum_of_support_subset _ hsub _ (by simp)]
  apply Finset.sum_le_sum
  intro p hp
  have hpp : p.Prime := (Finset.mem_filter.1 hp).2
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
  apply mul_le_mul_of_nonneg_right _ hlog
  exact_mod_cast legendre_first N p hpp

theorem mertens1 (N : ℕ) (hN : 1 ≤ N) :
    ∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p / p ≤ Real.log N + Real.log 4 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have htheta : ∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p ≤ Real.log 4 * N := by
    have := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) hNpos.le
    rwa [Chebyshev.theta_eq_sum_primesLE_log] at this
  have hfact : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
    exact_mod_cast Nat.factorial_le_pow N
  have hterm : ∀ p ∈ (range (N + 1)).filter Nat.Prime,
      (N : ℝ) * (Real.log p / p) ≤ ((N / p : ℕ) : ℝ) * Real.log p + Real.log p := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.1 hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hlt : (N : ℝ) < p * ((N / p : ℕ) + 1) := by exact_mod_cast Nat.lt_mul_div_succ N hpp.pos
    have : (N : ℝ) / p ≤ ((N / p : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hp0]; linarith
    calc (N : ℝ) * (Real.log p / p) = ((N : ℝ) / p) * Real.log p := by ring
      _ ≤ (((N / p : ℕ) : ℝ) + 1) * Real.log p := mul_le_mul_of_nonneg_right this hlog
      _ = _ := by ring
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have h2 := log_factorial_ge N
  have : (N : ℝ) * ∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p / p ≤
      N * (Real.log N + Real.log 4) := by
    linarith
  exact le_of_mul_le_mul_left this hNpos

theorem sum_primes_succ (f : ℕ → ℝ) (N : ℕ) :
    ∑ p ∈ (range (N + 2)).filter Nat.Prime, f p =
      ∑ p ∈ (range (N + 1)).filter Nat.Prime, f p + (if (N + 1).Prime then f (N + 1) else 0) := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_range_succ]

theorem abel_step (N : ℕ) (hN : 2 ≤ N) :
    (∑ p ∈ (range (N + 2)).filter Nat.Prime, ((p : ℝ))⁻¹) -
      (∑ p ∈ (range (N + 2)).filter Nat.Prime, Real.log p / p) / Real.log ((N + 1 : ℕ) : ℝ) =
    (∑ p ∈ (range (N + 1)).filter Nat.Prime, ((p : ℝ))⁻¹) -
      (∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p / p) / Real.log (N : ℝ) +
    (∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p / p) *
      (1 / Real.log (N : ℝ) - 1 / Real.log ((N + 1 : ℕ) : ℝ)) := by
  rw [sum_primes_succ, sum_primes_succ]
  have h1 : Real.log ((N + 1 : ℕ) : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N + 1))).ne'
  have h2 : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  have h3 : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  split_ifs
  · field_simp
    ring
  · field_simp
    ring

theorem mertens2 : ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
    ∑ p ∈ (range (N + 1)).filter Nat.Prime, ((p : ℝ))⁻¹ ≤ Real.log (Real.log N) + C := by
  set K := Real.log 4 with hK
  have hK0 : 0 ≤ K := Real.log_nonneg (by norm_num)
  let S : ℕ → ℝ := fun N => ∑ p ∈ (range (N + 1)).filter Nat.Prime, Real.log p / p
  let R : ℕ → ℝ := fun N => ∑ p ∈ (range (N + 1)).filter Nat.Prime, ((p : ℝ))⁻¹
  let T : ℕ → ℝ := fun N => R N - S N / Real.log N
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hind : ∀ N, 2 ≤ N → T N ≤ T 2 + (Real.log (Real.log N) - Real.log (Real.log 2)) +
      K * (1 / Real.log 2 - 1 / Real.log N) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ N hN ih =>
      have hstep : T (N + 1) = T N + S N * (1 / Real.log N - 1 / Real.log ((N + 1 : ℕ) : ℝ)) :=
        abel_step N hN
      have hlN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
      have hlN1 : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < N + 1))
      have hmono : Real.log (N : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by push_cast; linarith)
      have hd : 0 ≤ 1 / Real.log N - 1 / Real.log ((N + 1 : ℕ) : ℝ) := by
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le hlN hmono
      have hS : S N ≤ Real.log N + K := mertens1 N (by omega)
      have hconc : 1 - Real.log N / Real.log ((N + 1 : ℕ) : ℝ) ≤
          Real.log (Real.log ((N + 1 : ℕ) : ℝ)) - Real.log (Real.log N) := by
        have := Real.log_le_sub_one_of_pos (div_pos hlN hlN1)
        rw [Real.log_div hlN.ne' hlN1.ne'] at this
        linarith
      have hexp : Real.log N * (1 / Real.log N - 1 / Real.log ((N + 1 : ℕ) : ℝ)) =
          1 - Real.log N / Real.log ((N + 1 : ℕ) : ℝ) := by
        field_simp
      have hprod : S N * (1 / Real.log N - 1 / Real.log ((N + 1 : ℕ) : ℝ)) ≤
          (Real.log N + K) * (1 / Real.log N - 1 / Real.log ((N + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hS hd
      rw [hstep]
      push_cast at *
      nlinarith
  refine ⟨T 2 - Real.log (Real.log 2) + K / Real.log 2 + K / Real.log 2 + 1, ?_⟩
  intro N hN
  have hT := hind N hN
  have hlN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hmono : Real.log (2 : ℝ) ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hS : S N ≤ Real.log N + K := mertens1 N (by omega)
  have hR : R N = T N + S N / Real.log N := by simp only [T]; ring
  have hSdiv : S N / Real.log N ≤ 1 + K / Real.log 2 := by
    rw [div_le_iff₀ hlN]
    have : K / Real.log 2 * Real.log N ≥ K := by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hmono hK0
    nlinarith
  have hKN : 0 ≤ K * (1 / Real.log N) := by positivity
  change R N ≤ _
  rw [hR]
  have : K * (1 / Real.log 2 - 1 / Real.log N) = K / Real.log 2 - K * (1 / Real.log N) := by
    ring
  linarith

theorem tele (N : ℕ) (hN : 1 ≤ N) :
    ∑ p ∈ (range (N + 1)).filter Nat.Prime, (1 / ((p : ℝ) - 1) - 1 / p) ≤ 1 - 1 / N := by
  induction N, hN using Nat.le_induction with
  | base => simp [Finset.sum_filter, Finset.sum_range_succ, Nat.not_prime_zero, Nat.not_prime_one]
  | succ N hN ih =>
    rw [sum_primes_succ]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hgap : 0 ≤ 1 / (N : ℝ) - 1 / ((N + 1 : ℕ) : ℝ) := by
      rw [sub_nonneg]; apply one_div_le_one_div_of_le hN0; push_cast; linarith
    split_ifs
    · have : 1 / (((N + 1 : ℕ) : ℝ) - 1) - 1 / ((N + 1 : ℕ) : ℝ) =
          1 / (N : ℝ) - 1 / ((N + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [this]
      linarith
    · linarith

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1.H1 := by
  unfold OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1.H1
  obtain ⟨C, hC⟩ := OMA.Helpers.mertens2
  refine ⟨Real.exp (-(C + 1)), Real.exp_pos _, ?_⟩
  intro x hx
  have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hpos : ∀ p ∈ (Finset.range (x + 1)).filter Nat.Prime, 0 < 1 - (p : ℝ)⁻¹ := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.1 hp).2
    have : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have : (p : ℝ)⁻¹ ≤ 1 / 2 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) this
    linarith
  have hprod : ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) =
      Real.exp (∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, Real.log (1 - (p : ℝ)⁻¹)) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Real.exp_log (hpos p hp)]
  have hterm : ∀ p ∈ (Finset.range (x + 1)).filter Nat.Prime,
      -((p : ℝ)⁻¹ + (1 / ((p : ℝ) - 1) - 1 / p)) ≤ Real.log (1 - (p : ℝ)⁻¹) := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.1 hp).2
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hq := hpos p hp
    have hle := Real.log_le_sub_one_of_pos (inv_pos.2 hq)
    rw [Real.log_inv] at hle
    have hcalc : (1 - (p : ℝ)⁻¹)⁻¹ - 1 = (p : ℝ)⁻¹ + (1 / ((p : ℝ) - 1) - 1 / p) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib] at hsum
  have hR := hC x hx
  have hU := OMA.Helpers.tele x (by omega)
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hx1 : 0 ≤ 1 / (x : ℝ) := by positivity
  have hU' : 1 - 1 / (x : ℝ) ≤ 1 := by linarith
  have hlow : -(Real.log (Real.log x) + (C + 1)) ≤
      ∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, Real.log (1 - (p : ℝ)⁻¹) := by
    linarith
  rw [hprod]
  have hexp := Real.exp_le_exp.2 hlow
  have heq : Real.exp (-(Real.log (Real.log x) + (C + 1))) = Real.exp (-(C + 1)) / Real.log x := by
    rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hlogx]
    field_simp
  rw [heq] at hexp
  exact hexp
