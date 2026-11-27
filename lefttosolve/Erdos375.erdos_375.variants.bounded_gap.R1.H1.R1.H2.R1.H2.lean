import OMAReductions.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1_H2_R1

/-!
# Step H2 of the reduction Erdos375.erdos_375.variants.bounded_gap.R1.H1.R1.H2.R1

Split the second prime variable q into blocks of N ^ 40 consecutive integers (fibres of
q / N ^ 40). For a block Q, Cauchy-Schwarz in the first variable p, extended from the primes
to the whole interval J, gives

  (sum over p in P of the norm of T(p)) ^ 2 is at most #J times the sum over p in J of the
  squared norm of T(p), where T(p) is the sum over q in Q of e(h u(p, q)).

Expanding the squared norm gives a double sum over pairs (q, q') of the sum over p in J of
e(h (u(p, q) - u(p, q'))). The diagonal pairs contribute #Q #J, and every other pair is bounded
by the hypothesis (for q > q' after complex conjugation). With #J at most N ^ 252 and #Q at
most N ^ 40 each block contributes at most 2 N ^ 272, and there are at most N ^ 212 + 1 blocks.
-/

open Finset

namespace OMA.Helpers

/-- The additive character x to exp(2 pi i x). -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

theorem ee_zero : ee 0 = 1 := by simp [ee]

theorem ee_mul_conj (x y : ℝ) : ee x * (starRingEnd ℂ) (ee y) = ee (x - y) := by
  unfold ee
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem ee_conj (x : ℝ) : (starRingEnd ℂ) (ee x) = ee (-x) := by
  unfold ee
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem norm_sq_sum_ee (Q : Finset ℕ) (g : ℕ → ℝ) :
    ‖∑ q ∈ Q, ee (g q)‖ ^ 2 = (∑ q ∈ Q, ∑ q' ∈ Q, ee (g q - g q')).re := by
  have h1 : ∑ q ∈ Q, ∑ q' ∈ Q, ee (g q - g q') =
      (∑ q ∈ Q, ee (g q)) * (starRingEnd ℂ) (∑ q ∈ Q, ee (g q)) := by
    rw [map_sum, Finset.sum_mul_sum]
    simp only [ee_mul_conj]
  rw [h1, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

theorem sum_norm_sq_le (J Q : Finset ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ p ∈ J, ‖∑ q ∈ Q, ee (f p q)‖ ^ 2 ≤
      ∑ q ∈ Q, ∑ q' ∈ Q, ‖∑ p ∈ J, ee (f p q - f p q')‖ := by
  rw [sum_congr rfl (fun p _ => norm_sq_sum_ee Q (f p)), ← Complex.re_sum]
  have hcomm : ∑ p ∈ J, ∑ q ∈ Q, ∑ q' ∈ Q, ee (f p q - f p q') =
      ∑ q ∈ Q, ∑ q' ∈ Q, ∑ p ∈ J, ee (f p q - f p q') := by
    calc ∑ p ∈ J, ∑ q ∈ Q, ∑ q' ∈ Q, ee (f p q - f p q')
        = ∑ q ∈ Q, ∑ p ∈ J, ∑ q' ∈ Q, ee (f p q - f p q') := Finset.sum_comm
      _ = ∑ q ∈ Q, ∑ q' ∈ Q, ∑ p ∈ J, ee (f p q - f p q') :=
          sum_congr rfl (fun q _ => Finset.sum_comm)
  rw [hcomm]
  calc (∑ q ∈ Q, ∑ q' ∈ Q, ∑ p ∈ J, ee (f p q - f p q')).re
      ≤ ‖∑ q ∈ Q, ∑ q' ∈ Q, ∑ p ∈ J, ee (f p q - f p q')‖ := Complex.re_le_norm _
    _ ≤ ∑ q ∈ Q, ‖∑ q' ∈ Q, ∑ p ∈ J, ee (f p q - f p q')‖ := norm_sum_le _ _
    _ ≤ _ := sum_le_sum (fun q _ => norm_sum_le _ _)

theorem block_bound (J P Q : Finset ℕ) (f : ℕ → ℕ → ℝ) (L : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hPJ : P ⊆ J) (hQJ : Q ⊆ J)
    (hQ : ∀ a ∈ Q, ∀ b ∈ Q, a < b → b - a ≤ L)
    (hyp : ∀ a ∈ J, ∀ b ∈ J, a < b → b - a ≤ L → ‖∑ p ∈ J, ee (f p a - f p b)‖ ≤ B) :
    (∑ p ∈ P, ‖∑ q ∈ Q, ee (f p q)‖) ^ 2 ≤
      (J.card : ℝ) * ((Q.card : ℝ) * J.card + (Q.card : ℝ) ^ 2 * B) := by
  have step1 : ∑ p ∈ P, ‖∑ q ∈ Q, ee (f p q)‖ ≤ ∑ p ∈ J, ‖∑ q ∈ Q, ee (f p q)‖ :=
    sum_le_sum_of_subset_of_nonneg hPJ (fun _ _ _ => norm_nonneg _)
  have step2 := sq_sum_le_card_mul_sum_sq (s := J) (f := fun p => ‖∑ q ∈ Q, ee (f p q)‖)
  have step3 := sum_norm_sq_le J Q f
  have pair : ∀ a ∈ Q, ∀ b ∈ Q,
      ‖∑ p ∈ J, ee (f p a - f p b)‖ ≤ (if a = b then (J.card : ℝ) else 0) + B := by
    intro a ha b hb
    rcases lt_trichotomy a b with hab | rfl | hab
    · rw [if_neg hab.ne, zero_add]
      exact hyp a (hQJ ha) b (hQJ hb) hab (hQ a ha b hb hab)
    · rw [if_pos rfl]
      simp only [sub_self, ee_zero, sum_const, nsmul_eq_mul, mul_one, Complex.norm_natCast]
      linarith
    · rw [if_neg hab.ne', zero_add]
      have hc : ∑ p ∈ J, ee (f p a - f p b) =
          (starRingEnd ℂ) (∑ p ∈ J, ee (f p b - f p a)) := by
        rw [map_sum]
        refine sum_congr rfl (fun p _ => ?_)
        rw [ee_conj, neg_sub]
      rw [hc, Complex.norm_conj]
      exact hyp b (hQJ hb) a (hQJ ha) hab (hQ b hb a ha hab)
  have step4 : ∑ q ∈ Q, ∑ q' ∈ Q, ‖∑ p ∈ J, ee (f p q - f p q')‖ ≤
      (Q.card : ℝ) * J.card + (Q.card : ℝ) ^ 2 * B := by
    have hrow : ∀ q ∈ Q, ∑ q' ∈ Q, ((if q = q' then (J.card : ℝ) else 0) + B) =
        J.card + Q.card * B := by
      intro q hq
      rw [sum_add_distrib, sum_ite_eq, if_pos hq, sum_const, nsmul_eq_mul]
    calc ∑ q ∈ Q, ∑ q' ∈ Q, ‖∑ p ∈ J, ee (f p q - f p q')‖
        ≤ ∑ q ∈ Q, ∑ q' ∈ Q, ((if q = q' then (J.card : ℝ) else 0) + B) :=
          sum_le_sum (fun q hq => sum_le_sum (fun q' hq' => pair q hq q' hq'))
      _ = (Q.card : ℝ) * J.card + (Q.card : ℝ) ^ 2 * B := by
          rw [sum_congr rfl hrow, sum_const, nsmul_eq_mul]
          ring
  have h0 : 0 ≤ ∑ p ∈ P, ‖∑ q ∈ Q, ee (f p q)‖ := sum_nonneg (fun _ _ => norm_nonneg _)
  calc (∑ p ∈ P, ‖∑ q ∈ Q, ee (f p q)‖) ^ 2
      ≤ (∑ p ∈ J, ‖∑ q ∈ Q, ee (f p q)‖) ^ 2 := pow_le_pow_left₀ h0 step1 2
    _ ≤ J.card * ∑ p ∈ J, ‖∑ q ∈ Q, ee (f p q)‖ ^ 2 := step2
    _ ≤ J.card * (∑ q ∈ Q, ∑ q' ∈ Q, ‖∑ p ∈ J, ee (f p q - f p q')‖) :=
        mul_le_mul_of_nonneg_left step3 (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left step4 (Nat.cast_nonneg _)

theorem main_bound (N : ℕ) (hN : 2 ≤ N) (f : ℕ → ℕ → ℝ)
    (hyp : ∀ a ∈ Ioc (N ^ 251) (N ^ 252), ∀ b ∈ Ioc (N ^ 251) (N ^ 252), a < b →
      b - a ≤ N ^ 40 →
      ‖∑ p ∈ Ioc (N ^ 251) (N ^ 252), ee (f p a - f p b)‖ ≤ 16 * (N : ℝ) ^ 188) :
    ‖∑ w ∈ ((Ioc (N ^ 251) (N ^ 252)).filter Nat.Prime) ×ˢ
        ((Ioc (N ^ 251) (N ^ 252)).filter Nat.Prime), ee (f w.1 w.2)‖ ≤
      10 * (N : ℝ) ^ 484 := by
  set J := Ioc (N ^ 251) (N ^ 252) with hJdef
  set P := J.filter Nat.Prime with hPdef
  set L := N ^ 40 with hLdef
  have hL : 0 < L := by positivity
  have hPJ : P ⊆ J := filter_subset _ _
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hJcard : (J.card : ℝ) ≤ (N : ℝ) ^ 252 := by
    have : J.card ≤ N ^ 252 := by
      rw [hJdef, Nat.card_Ioc]
      exact Nat.sub_le _ _
    exact_mod_cast this
  have hmaps : ∀ q ∈ P, q / L ∈ range (N ^ 212 + 1) := by
    intro q hq
    have hqJ := hPJ hq
    rw [hJdef, mem_Ioc] at hqJ
    rw [mem_range, Nat.lt_succ_iff]
    apply Nat.div_le_of_le_mul
    calc q ≤ N ^ 252 := hqJ.2
      _ = L * N ^ 212 := by rw [hLdef, ← pow_add]
  have hblock : ∀ k, (∑ p ∈ P, ‖∑ q ∈ P.filter (fun q => q / L = k), ee (f p q)‖) ≤
      2 * (N : ℝ) ^ 272 := by
    intro k
    set Q := P.filter (fun q => q / L = k) with hQdef
    have hQJ : Q ⊆ J := (filter_subset _ _).trans hPJ
    have hQblock : ∀ a ∈ Q, ∀ b ∈ Q, a < b → b - a ≤ L := by
      intro a ha b hb hab
      rw [hQdef, mem_filter] at ha hb
      have h1 := Nat.div_add_mod a L
      have h2 := Nat.div_add_mod b L
      have h3 := Nat.mod_lt a hL
      have h4 := Nat.mod_lt b hL
      rw [ha.2] at h1
      rw [hb.2] at h2
      generalize L * k = c at h1 h2
      generalize a % L = r at h1 h3
      generalize b % L = s at h2 h4
      omega
    have hQcard : (Q.card : ℝ) ≤ (N : ℝ) ^ 40 := by
      have hc : Q.card ≤ L := by
        calc Q.card ≤ (range L).card := by
              apply card_le_card_of_injOn (fun q => q % L)
              · intro q _
                exact mem_range.mpr (Nat.mod_lt q hL)
              · intro a ha b hb hab
                have ha' := (mem_filter.mp ha).2
                have hb' := (mem_filter.mp hb).2
                have h1 := Nat.div_add_mod a L
                have h2 := Nat.div_add_mod b L
                have hab' : a % L = b % L := hab
                rw [ha'] at h1
                rw [hb'] at h2
                omega
          _ = L := card_range L
      rw [hLdef] at hc
      exact_mod_cast hc
    have hX := block_bound J P Q f L (16 * (N : ℝ) ^ 188) (by positivity) hPJ hQJ hQblock hyp
    have hbound : (∑ p ∈ P, ‖∑ q ∈ Q, ee (f p q)‖) ^ 2 ≤ (2 * (N : ℝ) ^ 272) ^ 2 := by
      refine hX.trans ?_
      calc (J.card : ℝ) * ((Q.card : ℝ) * J.card + (Q.card : ℝ) ^ 2 * (16 * (N : ℝ) ^ 188))
          ≤ (N : ℝ) ^ 252 * ((N : ℝ) ^ 40 * (N : ℝ) ^ 252 +
              ((N : ℝ) ^ 40) ^ 2 * (16 * (N : ℝ) ^ 188)) := by
            have hQ0 : (0 : ℝ) ≤ Q.card := Nat.cast_nonneg _
            have hJ0 : (0 : ℝ) ≤ J.card := Nat.cast_nonneg _
            have a1 : (Q.card : ℝ) * J.card ≤ (N : ℝ) ^ 40 * (N : ℝ) ^ 252 :=
              mul_le_mul hQcard hJcard hJ0 (by positivity)
            have a2 : (Q.card : ℝ) ^ 2 * (16 * (N : ℝ) ^ 188) ≤
                ((N : ℝ) ^ 40) ^ 2 * (16 * (N : ℝ) ^ 188) :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hQ0 hQcard 2) (by positivity)
            have h16 : (0 : ℝ) ≤ 16 * (N : ℝ) ^ 188 := by positivity
            have hc0 : (0 : ℝ) ≤ (Q.card : ℝ) * J.card + (Q.card : ℝ) ^ 2 * (16 * (N : ℝ) ^ 188) :=
              add_nonneg (mul_nonneg hQ0 hJ0) (mul_nonneg (sq_nonneg _) h16)
            have hb0 : (0 : ℝ) ≤ (N : ℝ) ^ 252 := pow_nonneg (Nat.cast_nonneg _) _
            exact mul_le_mul hJcard (add_le_add a1 a2) hc0 hb0
        _ = (N : ℝ) ^ 520 * (N : ℝ) ^ 24 + 16 * (N : ℝ) ^ 520 := by ring
        _ ≤ (2 * (N : ℝ) ^ 272) ^ 2 := by
          have h24 : (2 : ℝ) ^ 24 ≤ (N : ℝ) ^ 24 := pow_le_pow_left₀ (by norm_num) hn 24
          have h520 : (0 : ℝ) ≤ (N : ℝ) ^ 520 := by positivity
          have key := mul_le_mul_of_nonneg_left h24 h520
          have e1 : (2 * (N : ℝ) ^ 272) ^ 2 = 4 * ((N : ℝ) ^ 520 * (N : ℝ) ^ 24) := by ring
          rw [e1]
          norm_num at key
          linarith
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hbound
  rw [sum_product]
  have hsplit : ∀ p ∈ P, ∑ q ∈ P, ee (f p q) =
      ∑ k ∈ range (N ^ 212 + 1), ∑ q ∈ P.filter (fun q => q / L = k), ee (f p q) :=
    fun p _ => (sum_fiberwise_of_maps_to hmaps _).symm
  rw [sum_congr rfl hsplit, Finset.sum_comm]
  calc ‖∑ k ∈ range (N ^ 212 + 1), ∑ p ∈ P, ∑ q ∈ P.filter (fun q => q / L = k), ee (f p q)‖
      ≤ ∑ k ∈ range (N ^ 212 + 1),
          ‖∑ p ∈ P, ∑ q ∈ P.filter (fun q => q / L = k), ee (f p q)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range (N ^ 212 + 1),
          ∑ p ∈ P, ‖∑ q ∈ P.filter (fun q => q / L = k), ee (f p q)‖ :=
        sum_le_sum (fun k _ => norm_sum_le _ _)
    _ ≤ ∑ k ∈ range (N ^ 212 + 1), 2 * (N : ℝ) ^ 272 := sum_le_sum (fun k _ => hblock k)
    _ = ((N : ℝ) ^ 212 + 1) * (2 * (N : ℝ) ^ 272) := by
        rw [sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ 10 * (N : ℝ) ^ 484 := by
        have h1 : (N : ℝ) ^ 272 ≤ (N : ℝ) ^ 484 := pow_le_pow_right₀ (by linarith) (by norm_num)
        have e1 : ((N : ℝ) ^ 212 + 1) * (2 * (N : ℝ) ^ 272) =
            2 * (N : ℝ) ^ 484 + 2 * (N : ℝ) ^ 272 := by ring
        rw [e1]
        have h0 : 0 ≤ (N : ℝ) ^ 484 := by positivity
        linarith

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1_H2_R1.H2 := by
  intro N t h hN _ _ _ _ J u e P hyp
  have hyp' : ∀ a ∈ Ioc (N ^ 251) (N ^ 252), ∀ b ∈ Ioc (N ^ 251) (N ^ 252), a < b →
      b - a ≤ N ^ 40 →
      ‖∑ p ∈ Ioc (N ^ 251) (N ^ 252),
          OMA.Helpers.ee ((h : ℝ) * u p a - (h : ℝ) * u p b)‖ ≤ 16 * (N : ℝ) ^ 188 := by
    intro a ha b hb hab hd
    have h2 : ∀ p, (h : ℝ) * u p a - (h : ℝ) * u p b = (h : ℝ) * (u p a - u p b) :=
      fun p => by ring
    simp only [h2]
    exact hyp a ha b hb hab hd
  exact OMA.Helpers.main_bound N hN (fun p q => (h : ℝ) * u p q) hyp'
