import OMAReductions.R_Erdos890_erdos_890_parts_b_R1

/-!
# Step H2 of the reduction Erdos890.erdos_890.parts.b.R1

The distinct prime factors of N that exceed y have product at most N, so there are at most
log N / log y of them. With y = (log n)^B and N = n + i at most n^2, each of the k numbers
contributes at most 2 log n / (B log log n) such primes, and the weighted sum is at most 2k/B.
-/

namespace OMA.Helpers

open Finset Real

theorem e890_card_large_factors (N : ℕ) (hN : 0 < N) (y : ℝ) (hy : 1 < y) :
    ((N.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y)).card : ℝ) * log y ≤ log N := by
  set S := N.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ y) with hS
  have hdvd : (∏ p ∈ S, p) ∣ N :=
    (prod_dvd_prod_of_subset S N.primeFactors (fun p => p) (filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd N)
  have hle : (∏ p ∈ S, p) ≤ N := Nat.le_of_dvd hN hdvd
  have hleR : (∏ p ∈ S, (p : ℝ)) ≤ (N : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast hle
  have hy0 : 0 < y := by linarith
  have hpow : y ^ S.card ≤ ∏ p ∈ S, (p : ℝ) := by
    rw [← prod_const]
    apply prod_le_prod
    · intro p _
      exact hy0.le
    · intro p hp
      have := (mem_filter.mp hp).2
      linarith [not_le.mp this]
  have hpos : 0 < y ^ S.card := pow_pos hy0 _
  have h := Real.log_le_log hpos (hpow.trans hleR)
  rw [Real.log_pow] at h
  exact h

end OMA.Helpers

open Finset Real Filter in
theorem OMA.solution : OMA.R_Erdos890_erdos_890_parts_b_R1.H2 := by
  intro k hk ε hε
  refine ⟨⌈2 * (k : ℝ) / ε⌉₊ + 1, by omega, ?_⟩
  set B : ℕ := ⌈2 * (k : ℝ) / ε⌉₊ + 1 with hBdef
  have hBpos : (0 : ℝ) < B := by positivity
  have hBge : 2 * (k : ℝ) / ε ≤ B := by
    have h := Nat.le_ceil (2 * (k : ℝ) / ε)
    have : ((⌈2 * (k : ℝ) / ε⌉₊ : ℕ) : ℝ) ≤ (B : ℝ) := by
      rw [hBdef]; push_cast; linarith
    linarith
  filter_upwards [eventually_ge_atTop (max 16 k)] with n hn
  have hn16 : 16 ≤ n := le_of_max_le_left hn
  have hnk : k ≤ n := le_of_max_le_right hn
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn16
  have hnpos : (0 : ℝ) < n := by linarith
  have hL1 : 1 < log (n : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hnpos]
    have := Real.exp_one_lt_d9
    linarith
  have hLpos : 0 < log (n : ℝ) := by linarith
  have hLL : 0 < log (log (n : ℝ)) := Real.log_pos hL1
  have hy : 1 < (log (n : ℝ)) ^ B := one_lt_pow₀ hL1 (by omega)
  have hlogy : log ((log (n : ℝ)) ^ B) = B * log (log (n : ℝ)) := Real.log_pow _ _
  -- Each of the k numbers has few large prime factors.
  have hterm (i : ℕ) (hi : i ∈ range k) :
      (((n + i).primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ (log n) ^ B)).card : ℝ) *
        (B * log (log (n : ℝ))) ≤ 2 * log (n : ℝ) := by
    have hik : i < k := mem_range.mp hi
    have h := OMA.Helpers.e890_card_large_factors (n + i) (by omega) _ hy
    rw [hlogy] at h
    refine h.trans ?_
    have hsq : ((n + i : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : n + i ≤ n ^ 2 := by nlinarith
      exact_mod_cast this
    have hpos' : (0 : ℝ) < ((n + i : ℕ) : ℝ) := by positivity
    have := Real.log_le_log hpos' hsq
    rw [Real.log_pow, Nat.cast_ofNat] at this
    linarith
  have hsum :
      (∑ i ∈ range k, (((n + i).primeFactors.filter
        (fun p : ℕ => ¬ (p : ℝ) ≤ (log n) ^ B)).card : ℝ)) * (B * log (log (n : ℝ))) ≤
        k * (2 * log (n : ℝ)) := by
    rw [sum_mul]
    have := sum_le_sum hterm
    simpa using this
  set T := ∑ i ∈ range k, (((n + i).primeFactors.filter
        (fun p : ℕ => ¬ (p : ℝ) ≤ (log n) ^ B)).card : ℝ) with hT
  have hT0 : 0 ≤ T := sum_nonneg (fun i _ => Nat.cast_nonneg _)
  rw [mul_div_assoc', div_le_iff₀ hLpos]
  have hkε : 2 * (k : ℝ) ≤ ε * B := by
    rw [div_le_iff₀ hε] at hBge
    linarith
  have h1 : T * log (log (n : ℝ)) * B ≤ k * (2 * log (n : ℝ)) := by nlinarith
  have h2 : k * (2 * log (n : ℝ)) ≤ ε * B * log (n : ℝ) := by nlinarith
  have h3 : T * log (log (n : ℝ)) * B ≤ ε * log (n : ℝ) * B := by nlinarith
  exact le_of_mul_le_mul_right h3 hBpos
