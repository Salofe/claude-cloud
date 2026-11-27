import OMAReductions.R_Erdos535_erdos_535_R1

/-!
# Step H3 of the reduction Erdos535.erdos_535.R1

Explicit cutoffs. For N with n = log2 N (at least 16) and m = log2 n, take a = m / 2, y = 2^a,
L = n + 1 and K = (n + 1) / a. Then N < 2^L and N < y^(K + 1), y^2 is at most n, and
log n is at most 4 a log 2. The logarithm of the cost is y log(n + 2) + log(K + 1) + K log C.
The first two terms are at most n / log(n + 1) once (log(n + 2))^4 is at most n / 4, and
K log C is at most 16 log 2 log C n / log(n + 1). Since log N is at least n log 2 and
log log N is at most log(n + 1), the constant c = (1 + 16 log 2 log C) / log 2 works.
-/

open Filter Real

namespace OMA.Helpers

lemma asymp : ∃ n0 : ℕ, ∀ n ≥ n0, ∀ y : ℕ, y ^ 2 ≤ n →
    ((y : ℝ) + 1) * Real.log ((n : ℝ) + 2) * Real.log ((n : ℝ) + 1) ≤ n := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 4)).bound (show (0 : ℝ) < 1 / 8 by norm_num)
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 (h2.eventually h)
  refine ⟨max n0 2, fun n hn y hy => ?_⟩
  have hb := hn0 n (le_trans (le_max_left _ _) hn)
  simp only [Real.norm_eq_abs, id] at hb
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_right _ _) hn)
  have hl1 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hl2 : Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hl2' : 0 ≤ Real.log ((n : ℝ) + 2) := le_trans hl1 hl2
  have hP : Real.log ((n : ℝ) + 2) ^ 4 ≤ (n : ℝ) / 4 := by
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at hb
    linarith
  have hy' : ((y : ℝ) + 1) ^ 2 ≤ 4 * n := by
    have : (y : ℝ) ^ 2 ≤ n := by exact_mod_cast hy
    nlinarith [sq_nonneg ((y : ℝ) - 1)]
  have e1 : Real.log ((n : ℝ) + 1) ^ 2 ≤ Real.log ((n : ℝ) + 2) ^ 2 :=
    pow_le_pow_left₀ hl1 hl2 2
  have hX : (((y : ℝ) + 1) * Real.log ((n : ℝ) + 2) * Real.log ((n : ℝ) + 1)) ^ 2 ≤ (n : ℝ) ^ 2 := by
    calc (((y : ℝ) + 1) * Real.log ((n : ℝ) + 2) * Real.log ((n : ℝ) + 1)) ^ 2
        = ((y : ℝ) + 1) ^ 2 * (Real.log ((n : ℝ) + 2) ^ 2 * Real.log ((n : ℝ) + 1) ^ 2) := by ring
      _ ≤ (4 * n) * (Real.log ((n : ℝ) + 2) ^ 2 * Real.log ((n : ℝ) + 2) ^ 2) := by
          gcongr
      _ = (4 * n) * (Real.log ((n : ℝ) + 2) ^ 4) := by ring
      _ ≤ (4 * n) * ((n : ℝ) / 4) := by gcongr
      _ = (n : ℝ) ^ 2 := by ring
  have hpos : 0 ≤ ((y : ℝ) + 1) * Real.log ((n : ℝ) + 2) * Real.log ((n : ℝ) + 1) := by
    positivity
  nlinarith

theorem cutoff (C : ℝ) (hC : 1 ≤ C) : ∃ c > (0 : ℝ),
    ∀ᶠ (N : ℕ) in atTop,
      ∃ (y L K : ℕ), 2 ≤ y ∧ N < 2 ^ L ∧ N < y ^ (K + 1) ∧
        ((((L + 1) ^ y * (K + 1) : ℕ) : ℝ) * C ^ K) ≤
          (N : ℝ) ^ (c / log (log (N : ℝ))) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; norm_num at this; linarith
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hCpos : 0 < C := by linarith
  set c := (1 + 16 * Real.log 2 * Real.log C) / Real.log 2 with hc
  refine ⟨c, by positivity, ?_⟩
  obtain ⟨n0, hn0⟩ := asymp
  rw [eventually_atTop]
  refine ⟨2 ^ (max n0 16), fun N hN => ?_⟩
  have hN0 : N ≠ 0 := by
    have := Nat.one_le_two_pow (n := max n0 16)
    omega
  set n := Nat.log 2 N with hn_def
  have hn : max n0 16 ≤ n := Nat.le_log_of_pow_le one_lt_two hN
  have hn16 : 16 ≤ n := le_trans (le_max_right _ _) hn
  have hNlo : 2 ^ n ≤ N := Nat.pow_log_le_self 2 hN0
  have hNhi : N < 2 ^ (n + 1) := Nat.lt_pow_succ_log_self one_lt_two N
  set m := Nat.log 2 n with hm_def
  have hn0' : n ≠ 0 := by omega
  have hmlo : 2 ^ m ≤ n := Nat.pow_log_le_self 2 hn0'
  have hmhi : n < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self one_lt_two n
  have hm2 : 2 ≤ m := Nat.le_log_of_pow_le one_lt_two (by omega)
  set a := m / 2 with ha_def
  have ha1 : 1 ≤ a := by omega
  set K := (n + 1) / a with hK_def
  have hy2 : (2 ^ a) ^ 2 ≤ n := by
    rw [← pow_mul]
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hmlo
  have hKle : K ≤ n + 1 := Nat.div_le_self _ _
  refine ⟨2 ^ a, n + 1, K, ?_, ?_, ?_, ?_⟩
  · calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha1
  · exact hNhi
  · rw [← pow_mul]
    have h1 : n + 1 < K * a + a := Nat.lt_div_mul_add (by omega)
    calc N < 2 ^ (n + 1) := hNhi
      _ ≤ 2 ^ (a * (K + 1)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  · -- the analytic inequality
    set y := 2 ^ a with hy_def
    have hnr : (16 : ℝ) ≤ n := by exact_mod_cast hn16
    have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
    -- left side as an exponential
    have hL : ((((n + 1 + 1) ^ y * (K + 1) : ℕ) : ℝ) * C ^ K) =
        Real.exp (y * Real.log ((n : ℝ) + 2) + Real.log ((K : ℝ) + 1) + K * Real.log C) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log (by positivity), Real.exp_log (by positivity), Real.exp_log hCpos]
      push_cast
      ring
    have hR : (N : ℝ) ^ (c / log (log (N : ℝ))) =
        Real.exp (Real.log N * (c / log (log (N : ℝ)))) := Real.rpow_def_of_pos hNpos _
    rw [hL, hR, Real.exp_le_exp]
    -- bounds on log N
    have hlogN_lo : (n : ℝ) * Real.log 2 ≤ Real.log N := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (by exact_mod_cast hNlo)
    have hlogN_hi : Real.log N ≤ (n : ℝ) + 1 := by
      have : Real.log N < ((n : ℝ) + 1) * Real.log 2 := by
        rw [← Nat.cast_succ, ← Real.log_pow]
        exact Real.log_lt_log hNpos (by exact_mod_cast hNhi)
      nlinarith
    have hlogN_gt1 : 1 < Real.log N := by
      have : (1 : ℝ) < 16 * Real.log 2 := by
        have := Real.log_two_gt_d9; norm_num at this; linarith
      nlinarith
    have hll_pos : 0 < Real.log (Real.log N) := Real.log_pos hlogN_gt1
    have hll_le : Real.log (Real.log N) ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log (by linarith) hlogN_hi
    have hln1_pos : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
    -- the target lower bound
    have hT : c * Real.log 2 * ((n : ℝ) / Real.log ((n : ℝ) + 1)) ≤
        Real.log N * (c / Real.log (Real.log N)) := by
      have hc0 : 0 ≤ c := by positivity
      have : (n : ℝ) * Real.log 2 / Real.log ((n : ℝ) + 1) ≤
          Real.log N / Real.log (Real.log N) :=
        div_le_div₀ (by linarith) hlogN_lo hll_pos hll_le
      calc c * Real.log 2 * ((n : ℝ) / Real.log ((n : ℝ) + 1))
          = c * ((n : ℝ) * Real.log 2 / Real.log ((n : ℝ) + 1)) := by ring
        _ ≤ c * (Real.log N / Real.log (Real.log N)) := mul_le_mul_of_nonneg_left this hc0
        _ = Real.log N * (c / Real.log (Real.log N)) := by ring
    refine le_trans ?_ hT
    have hceq : c * Real.log 2 = 1 + 16 * Real.log 2 * Real.log C := by
      rw [hc]; field_simp
    rw [hceq]
    -- first two terms
    have h12 : (y : ℝ) * Real.log ((n : ℝ) + 2) + Real.log ((K : ℝ) + 1) ≤
        (n : ℝ) / Real.log ((n : ℝ) + 1) := by
      have hA := hn0 n (le_trans (le_max_left _ _) hn) y hy2
      have hK1 : Real.log ((K : ℝ) + 1) ≤ Real.log ((n : ℝ) + 2) :=
        Real.log_le_log (by positivity) (by
          have : (K : ℝ) ≤ n + 1 := by exact_mod_cast hKle
          linarith)
      rw [le_div_iff₀ hln1_pos]
      nlinarith
    -- the K term
    have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hlogn_le : Real.log (n : ℝ) ≤ 4 * a * Real.log 2 := by
      have h1 : n < 2 ^ (4 * a) := lt_of_lt_of_le hmhi (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h2 : Real.log (n : ℝ) < Real.log ((2 : ℝ) ^ (4 * a)) :=
        Real.log_lt_log (by linarith) (by exact_mod_cast h1)
      rw [Real.log_pow] at h2
      push_cast at h2
      linarith
    have har : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have hKr : (K : ℝ) ≤ ((n : ℝ) + 1) / a := by
      have := (Nat.cast_div_le : ((((n + 1) / a : ℕ)) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) / (a : ℝ))
      push_cast at this
      exact this
    have hlog_n1 : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log (n : ℝ) := by
      rw [← Real.log_rpow (by linarith)]
      apply Real.log_le_log (by linarith)
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      nlinarith
    have hK3 : (K : ℝ) ≤ 16 * Real.log 2 * ((n : ℝ) / Real.log ((n : ℝ) + 1)) := by
      calc (K : ℝ) ≤ ((n : ℝ) + 1) / a := hKr
        _ ≤ 2 * n / a := by
            apply div_le_div_of_nonneg_right (by linarith) (by linarith)
        _ ≤ 2 * n * (4 * Real.log 2 / Real.log (n : ℝ)) := by
            rw [div_eq_mul_inv]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [le_div_iff₀ hlogn_pos]
            calc (a : ℝ)⁻¹ * Real.log n ≤ (a : ℝ)⁻¹ * (4 * a * Real.log 2) :=
                  mul_le_mul_of_nonneg_left hlogn_le (by positivity)
              _ = 4 * Real.log 2 := by field_simp
        _ = 8 * Real.log 2 * ((n : ℝ) / Real.log (n : ℝ)) := by ring
        _ ≤ 16 * Real.log 2 * ((n : ℝ) / Real.log ((n : ℝ) + 1)) := by
            have : (n : ℝ) / Real.log (n : ℝ) ≤ 2 * ((n : ℝ) / Real.log ((n : ℝ) + 1)) := by
              rw [div_le_iff₀ hlogn_pos]
              have := hlog_n1
              calc (n : ℝ) = 2 * ((n : ℝ) / Real.log ((n : ℝ) + 1)) * (Real.log ((n : ℝ) + 1) / 2) := by
                    field_simp
                _ ≤ 2 * ((n : ℝ) / Real.log ((n : ℝ) + 1)) * Real.log n := by
                    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            nlinarith
    have hKC : (K : ℝ) * Real.log C ≤
        16 * Real.log 2 * Real.log C * ((n : ℝ) / Real.log ((n : ℝ) + 1)) := by
      have := mul_le_mul_of_nonneg_right hK3 hlogC
      linarith
    have hexp : (1 + 16 * Real.log 2 * Real.log C) * ((n : ℝ) / Real.log ((n : ℝ) + 1)) =
        (n : ℝ) / Real.log ((n : ℝ) + 1) +
          16 * Real.log 2 * Real.log C * ((n : ℝ) / Real.log ((n : ℝ) + 1)) := by ring
    rw [hexp]
    linarith

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos535_erdos_535_R1.H3 := by
  intro C hC
  exact OMA.Helpers.cutoff C hC
