import OMAReductions.R_Erdos687_erdos_687_variants_iwaniec_R1

namespace OMA.Helpers

/-- Primes up to `n`. -/
def PS (n : ℕ) : Finset ℕ := (Finset.range (n + 1)).filter Nat.Prime

theorem mem_PS {n p : ℕ} : p ∈ PS n ↔ p ≤ n ∧ p.Prime := by
  simp [PS]

theorem sum_PS_succ (n : ℕ) (f : ℕ → ℝ) :
    Finset.sum (PS (n + 1)) f =
      Finset.sum (PS n) f + (if (n + 1).Prime then f (n + 1) else 0) := by
  unfold PS
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.sum_insert (by simp), add_comm]
  · simp

theorem prod_pow_dvd_of_primes (k : ℕ → ℕ) (N : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) (hd : ∀ p ∈ s, p ^ k p ∣ N) :
    ∏ p ∈ s, p ^ k p ∣ N := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hsa : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime (a ^ k a) (∏ p ∈ s, p ^ k p) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact Nat.coprime_pow_primes _ _ (hs a (Finset.mem_insert_self a s)) (hsa q hq)
        (fun h => ha (h ▸ hq))
    exact hcop.mul_dvd_of_dvd_of_dvd (hd a (Finset.mem_insert_self a s))
      (ih hsa (fun p hp => hd p (Finset.mem_insert_of_mem hp)))

theorem pow_div_dvd_factorial {p : ℕ} (hp : p.Prime) (n : ℕ) :
    p ^ (n / p) ∣ n.factorial := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [hp.pow_dvd_factorial_iff (b := n + 1)
    (lt_of_le_of_lt (Nat.log_le_self p n) (Nat.lt_succ_self n))]
  have h1 : (1 : ℕ) ∈ Finset.Ico 1 (n + 1) := by
    rw [Finset.mem_Ico]; omega
  have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun i _ => Nat.zero_le _) h1
  simpa using this

/-- Elementary upper bound of Mertens type. -/
theorem mertens1 (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ PS n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : ∀ p ∈ PS n, (0 : ℝ) < p := fun p hp => by exact_mod_cast (mem_PS.mp hp).2.pos
  have hdvd : ∏ p ∈ PS n, p ^ (n / p) ∣ n.factorial :=
    prod_pow_dvd_of_primes _ _ _ (fun p hp => (mem_PS.mp hp).2)
      (fun p hp => pow_div_dvd_factorial (mem_PS.mp hp).2 n)
  have hle : ∏ p ∈ PS n, p ^ (n / p) ≤ n.factorial := Nat.le_of_dvd (Nat.factorial_pos n) hdvd
  have hprodpos : 0 < ∏ p ∈ PS n, p ^ (n / p) :=
    Finset.prod_pos (fun p hp => pow_pos (mem_PS.mp hp).2.pos _)
  have hA : ∑ p ∈ PS n, ((n / p : ℕ) : ℝ) * Real.log p ≤ Real.log (n.factorial) := by
    have h1 : Real.log ((∏ p ∈ PS n, p ^ (n / p) : ℕ) : ℝ) ≤ Real.log (n.factorial) :=
      Real.log_le_log (by exact_mod_cast hprodpos) (by exact_mod_cast hle)
    rw [Nat.cast_prod, Real.log_prod] at h1
    · simpa [Real.log_pow] using h1
    · intro p hp
      exact_mod_cast (pow_pos (mem_PS.mp hp).2.pos _).ne'
  have hB : Real.log (n.factorial) ≤ (n : ℝ) * Real.log n := by
    have h1 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have h2 := Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) h1
    rwa [Real.log_pow] at h2
  have hC : ∑ p ∈ PS n, Real.log p ≤ (n : ℝ) * Real.log 4 := by
    have h1 : ((primorial n : ℕ) : ℝ) ≤ (4 : ℝ) ^ n := by exact_mod_cast primorial_le_four_pow n
    have h2 := Real.log_le_log (by exact_mod_cast primorial_pos n) h1
    rw [Real.log_pow] at h2
    have h3 : primorial n = ∏ p ∈ PS n, p := rfl
    rw [h3, Nat.cast_prod, Real.log_prod] at h2
    · exact h2
    · intro p hp
      exact (hpos p hp).ne'
  have hkey : (n : ℝ) * ∑ p ∈ PS n, Real.log p / p ≤ (n : ℝ) * (Real.log n + Real.log 4) := by
    rw [Finset.mul_sum]
    calc ∑ p ∈ PS n, (n : ℝ) * (Real.log p / p)
        ≤ ∑ p ∈ PS n, (((n / p : ℕ) : ℝ) * Real.log p + Real.log p) := by
          apply Finset.sum_le_sum
          intro p hp
          have hp0 := hpos p hp
          have hlog : 0 ≤ Real.log p :=
            Real.log_nonneg (by exact_mod_cast (mem_PS.mp hp).2.one_lt.le)
          have hfl : (n : ℝ) / p < ((n / p : ℕ) : ℝ) + 1 := by
            have := Nat.lt_floor_add_one ((n : ℝ) / p)
            rwa [Nat.floor_div_eq_div] at this
          have e : (n : ℝ) * (Real.log p / p) = ((n : ℝ) / p) * Real.log p := by ring
          rw [e]
          have := mul_le_mul_of_nonneg_right hfl.le hlog
          linarith
      _ = ∑ p ∈ PS n, ((n / p : ℕ) : ℝ) * Real.log p + ∑ p ∈ PS n, Real.log p :=
          Finset.sum_add_distrib
      _ ≤ (n : ℝ) * Real.log n + (n : ℝ) * Real.log 4 := add_le_add (hA.trans hB) hC
      _ = (n : ℝ) * (Real.log n + Real.log 4) := by ring
  exact le_of_mul_le_mul_left hkey hnpos

theorem key_ineq {n : ℕ} (hn : 2 ≤ n) :
    1 - Real.log n / Real.log ((n + 1 : ℕ) : ℝ) ≤
      Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log n) := by
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hL' : 0 < Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hL' hL)
  rw [Real.log_div hL'.ne' hL.ne', inv_div] at h
  exact h

theorem step_real (W S L L' A c B : ℝ) (hL : 0 < L) (hLL : L < L') (hS : S ≤ L + A)
    (IH : W - S / L ≤ Real.log L - c + B - A / L + 1)
    (key : 1 - L / L' ≤ Real.log L' - Real.log L) :
    W - S / L' ≤ Real.log L' - c + B - A / L' + 1 := by
  have hL' : 0 < L' := lt_trans hL hLL
  have hd : 0 ≤ 1 / L - 1 / L' := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le hL hLL.le
  have h1 : S * (1 / L - 1 / L') ≤ (L + A) * (1 / L - 1 / L') :=
    mul_le_mul_of_nonneg_right hS hd
  have e1 : S / L - S / L' = S * (1 / L - 1 / L') := by ring
  have e2 : (L + A) * (1 / L - 1 / L') = 1 - L / L' + A / L - A / L' := by
    field_simp
    ring
  linarith

theorem invariant (n : ℕ) (hn : 2 ≤ n) :
    (∑ p ∈ PS n, ((p : ℝ) - 1)⁻¹) + 1 / (n : ℝ) - (∑ p ∈ PS n, Real.log p / p) / Real.log n
      ≤ Real.log (Real.log n) - Real.log (Real.log 2) + Real.log 4 / Real.log 2
        - Real.log 4 / Real.log n + 1 := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h2 : PS 2 = {2} := by decide
    rw [h2, Finset.sum_singleton, Finset.sum_singleton]
    have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have e : Real.log (2 : ℝ) / 2 / Real.log 2 = 1 / 2 := by
      field_simp
    push_cast
    rw [e]
    norm_num
  | succ n hn ih =>
    have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hLL : Real.log (n : ℝ) < Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_lt_log (by exact_mod_cast (by omega : 0 < n))
        (by exact_mod_cast (by omega : n < n + 1))
    have hL' : 0 < Real.log ((n + 1 : ℕ) : ℝ) := lt_trans hL hLL
    have hS := mertens1 n (by omega)
    have key := key_ineq hn
    have hstep := step_real _ _ _ _ _ _ _ hL hLL hS ih key
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n + 1)
    rw [sum_PS_succ n (fun p => ((p : ℝ) - 1)⁻¹), sum_PS_succ n (fun p => Real.log p / p)]
    split_ifs with hp
    · have e1 : (((n + 1 : ℕ) : ℝ) - 1)⁻¹ = 1 / (n : ℝ) := by
        rw [Nat.cast_succ, add_sub_cancel_right, one_div]
      have e2 : Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) / Real.log ((n + 1 : ℕ) : ℝ)
          = 1 / ((n + 1 : ℕ) : ℝ) := by
        field_simp
      have e3 : ((∑ p ∈ PS n, Real.log p / p) + Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
          / Real.log ((n + 1 : ℕ) : ℝ) = (∑ p ∈ PS n, Real.log p / p) / Real.log ((n + 1 : ℕ) : ℝ)
            + Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) / Real.log ((n + 1 : ℕ) : ℝ) := by
        rw [add_div]
      rw [e3, e2, e1]
      linarith
    · have h1 : 1 / ((n + 1 : ℕ) : ℝ) ≤ 1 / (n : ℝ) :=
        one_div_le_one_div_of_le hnpos (by exact_mod_cast (by omega : n ≤ n + 1))
      simp only [add_zero]
      linarith

theorem log_one_sub_inv_ge {p : ℕ} (hp : 2 ≤ p) :
    -((p : ℝ) - 1)⁻¹ ≤ Real.log (1 - (p : ℝ)⁻¹) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpos : 0 < 1 - (p : ℝ)⁻¹ := by
    have : (p : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hp2
    linarith [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1 : (p : ℝ) - 1 ≠ 0 := by intro h; linarith
  have e : 1 - (1 - (p : ℝ)⁻¹)⁻¹ = -((p : ℝ) - 1)⁻¹ := by
    field_simp
    ring
  rw [e] at h
  exact h

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_iwaniec_R1.H2 := by
  refine ⟨Real.exp (-(2 - Real.log (Real.log 2) + Real.log 4 / Real.log 2)), Real.exp_pos _, ?_⟩
  intro x hx
  change _ ≤ ∏ p ∈ PS x, (1 - (p : ℝ)⁻¹)
  set K := 2 - Real.log (Real.log 2) + Real.log 4 / Real.log 2 with hK
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hinv := invariant x hx
  have hS := mertens1 x (by omega)
  have hSdiv : (∑ p ∈ PS x, Real.log p / p) / Real.log x ≤ 1 + Real.log 4 / Real.log x := by
    rw [div_le_iff₀ hL]
    have : (1 + Real.log 4 / Real.log x) * Real.log x = Real.log x + Real.log 4 := by
      field_simp
    rw [this]
    exact hS
  have hx1 : 0 ≤ 1 / (x : ℝ) := by positivity
  have hV : ∑ p ∈ PS x, ((p : ℝ) - 1)⁻¹ ≤ Real.log (Real.log x) + K := by
    rw [hK]
    linarith
  have hlogsum : -(∑ p ∈ PS x, ((p : ℝ) - 1)⁻¹) ≤ ∑ p ∈ PS x, Real.log (1 - (p : ℝ)⁻¹) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro p hp
    exact log_one_sub_inv_ge (mem_PS.mp hp).2.two_le
  have hprod : ∏ p ∈ PS x, (1 - (p : ℝ)⁻¹) =
      Real.exp (∑ p ∈ PS x, Real.log (1 - (p : ℝ)⁻¹)) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_PS.mp hp).2.two_le
    have hpos : 0 < 1 - (p : ℝ)⁻¹ := by
      have : (p : ℝ)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hp2
      linarith [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
    rw [Real.exp_log hpos]
  rw [hprod]
  have h1 : Real.exp (-(Real.log (Real.log x) + K)) ≤
      Real.exp (∑ p ∈ PS x, Real.log (1 - (p : ℝ)⁻¹)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(Real.log (Real.log x) + K)) = Real.exp (-K) / Real.log x := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log (Real.log x)), Real.exp_log hL]
    field_simp
  rw [h2] at h1
  exact h1
