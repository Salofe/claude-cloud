import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1
import Mathlib

/-!
# Step H3 of the reduction Erdos338.erdos_338.variants.triangular.R1.H1.R1.H1.R1.H1.R1.H1.R1.H2.R1

For s with s mod 8 = 3 the Jacobi symbol a to (a | s) is periodic with period s and its sum over a
full period vanishes (multiplication by 2 permutes the residues and (2 | s) = -1). Hence its running
sums are bounded by s. Writing the divisor sum up to n as the sum over a of (a | s) times n / a,
we split at a cutoff Y: the terms with a at most Y differ from n times (a | s) / a by at most Y in
total, and the tail is bounded by Abel summation by 4 s n / (Y + 1). So the average of the divisor
sums minus the sum of (a | s) / a for a up to n tends to zero, which gives the claimed limit.
Only Mathlib and the definition of the step are used.
-/
namespace OMA.Helpers
open Finset Filter
open scoped Topology

theorem jac_two (s : ℕ) (h8 : s % 8 = 3) : jacobiSym 2 s = -1 := by
  have hodd : Odd s := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
  have h2 : s % 2 = 1 := by omega
  simp [h2, h8]

theorem period_sum (s : ℕ) (hs : 0 < s) (h8 : s % 8 = 3) :
    ∑ i ∈ range s, jacobiSym (i:ℤ) s = 0 := by
  set k := (s+1)/2 with hk
  have hk2 : 2 * k = s + 1 := by omega
  have perm : ∑ i ∈ range s, jacobiSym ((2*i : ℕ):ℤ) s = ∑ i ∈ range s, jacobiSym (i:ℤ) s := by
    apply Finset.sum_nbij' (fun i => 2*i % s) (fun i => k*i % s)
    · intro a _; exact mem_range.mpr (Nat.mod_lt _ hs)
    · intro a _; exact mem_range.mpr (Nat.mod_lt _ hs)
    · intro a ha
      replace ha := mem_range.mp ha
      have h1 : k * (2 * a % s) ≡ k * (2 * a) [MOD s] := Nat.ModEq.mul_left k (Nat.mod_modEq _ _)
      have h2 : k * (2 * a) = s * a + a := by rw [← mul_assoc, mul_comm k 2, hk2]; ring
      have h3 : k * (2 * a % s) % s = a % s := by
        rw [h1, h2]; simp
      rw [h3, Nat.mod_eq_of_lt ha]
    · intro a ha
      replace ha := mem_range.mp ha
      have h1 : 2 * (k * a % s) ≡ 2 * (k * a) [MOD s] := Nat.ModEq.mul_left 2 (Nat.mod_modEq _ _)
      have h2 : 2 * (k * a) = s * a + a := by rw [← mul_assoc, hk2]; ring
      have h3 : 2 * (k * a % s) % s = a % s := by
        rw [h1, h2]; simp
      rw [h3, Nat.mod_eq_of_lt ha]
    · intro a _
      apply jacobiSym.mod_left'
      push_cast
      rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
  have neg : ∑ i ∈ range s, jacobiSym ((2*i : ℕ):ℤ) s = - ∑ i ∈ range s, jacobiSym (i:ℤ) s := by
    rw [← Finset.sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    push_cast
    rw [jacobiSym.mul_left, jac_two s h8]
    ring
  rw [perm] at neg
  linarith

theorem seg_bound (s : ℕ) (hs : 0 < s) (h8 : s % 8 = 3) (t : ℕ) :
    |∑ i ∈ range t, (jacobiSym (i:ℤ) s : ℝ)| ≤ s := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht : t < s
    · calc |∑ i ∈ range t, (jacobiSym (i:ℤ) s : ℝ)|
          ≤ ∑ i ∈ range t, |(jacobiSym (i:ℤ) s : ℝ)| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ range t, (1:ℝ) := by
          apply sum_le_sum
          intro i _
          rcases jacobiSym.trichotomy (i:ℤ) s with h | h | h <;> simp [h]
        _ = t := by simp
        _ ≤ s := by exact_mod_cast ht.le
    · have e : t = s + (t - s) := by omega
      rw [e, sum_range_add]
      have h0 : ∑ i ∈ range s, (jacobiSym (i:ℤ) s : ℝ) = 0 := by
        exact_mod_cast period_sum s hs h8
      have hsh : ∑ i ∈ range (t-s), (jacobiSym ((s+i : ℕ):ℤ) s : ℝ)
          = ∑ i ∈ range (t-s), (jacobiSym (i:ℤ) s : ℝ) := by
        apply sum_congr rfl
        intro i _
        congr 1
        apply jacobiSym.mod_left'
        push_cast
        simp
      rw [h0, zero_add, hsh]
      exact ih _ (by omega)

theorem divsum (c : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Icc 1 n, ∑ a ∈ k.divisors, c a = ∑ a ∈ Icc 1 n, c a * ((n / a : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ih, sum_Icc_succ_top (by omega) (fun a => c a * (((n+1) / a : ℕ) : ℝ))]
    have hd : ∑ a ∈ (n+1).divisors, c a
        = ∑ a ∈ Icc 1 n, (if a ∣ n+1 then c a else 0) + c (n+1) := by
      have e : (n+1).divisors = (Icc 1 (n+1)).filter (fun a => a ∣ n+1) := by
        ext a
        simp only [Nat.mem_divisors, mem_filter, mem_Icc]
        constructor
        · rintro ⟨h, -⟩
          exact ⟨⟨Nat.pos_of_dvd_of_pos h (by omega), Nat.le_of_dvd (by omega) h⟩, h⟩
        · rintro ⟨-, h⟩
          exact ⟨h, by omega⟩
      rw [e, sum_filter, sum_Icc_succ_top (by omega), if_pos (dvd_refl _)]
    have hs : ∀ a ∈ Icc 1 n, c a * (((n+1)/a : ℕ) : ℝ)
        = c a * ((n/a : ℕ):ℝ) + (if a ∣ n+1 then c a else 0) := by
      intro a _
      by_cases h : a ∣ n + 1
      · rw [Nat.succ_div_of_dvd h, if_pos h]; push_cast; ring
      · rw [Nat.succ_div_of_not_dvd h, if_neg h]; ring
    rw [hd, sum_congr rfl hs, sum_add_distrib, Nat.div_self (by omega)]
    push_cast
    ring

theorem abel_bound (g w : ℕ → ℝ) (B : ℝ) (hB : ∀ k, |∑ i ∈ range k, g i| ≤ B) (m : ℕ)
    (hw0 : ∀ i, m ≤ i → 0 ≤ w i) (hw1 : ∀ i, m ≤ i → w (i+1) ≤ w i) (n : ℕ) (hmn : m ≤ n) :
    |∑ i ∈ Ico m n, w i * g i| ≤ 2 * B * w m := by
  set G : ℕ → ℝ := fun k => ∑ i ∈ range k, g i with hG
  have key : ∀ n, m ≤ n →
      |∑ i ∈ Ico m n, w i * g i - w n * G n + w m * G m| ≤ B * (w m - w n) := by
    intro n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [sum_Ico_succ_top hmn]
      have hg : g n = G (n+1) - G n := by simp [G, sum_range_succ]
      have e : ∑ i ∈ Ico m n, w i * g i + w n * g n - w (n+1) * G (n+1) + w m * G m
          = (∑ i ∈ Ico m n, w i * g i - w n * G n + w m * G m) + (w n - w (n+1)) * G (n+1) := by
        rw [hg]; ring
      rw [e]
      have d0 : 0 ≤ w n - w (n+1) := by linarith [hw1 n hmn]
      calc _ ≤ |∑ i ∈ Ico m n, w i * g i - w n * G n + w m * G m| + |(w n - w (n+1)) * G (n+1)| :=
            abs_add_le _ _
        _ ≤ B * (w m - w n) + (w n - w (n+1)) * B := by
          gcongr
          rw [abs_mul, abs_of_nonneg d0]
          gcongr
          exact hB _
        _ = _ := by ring
  have h1 := abs_le.mp (key n hmn)
  have wn := hw0 n hmn
  have wm := hw0 m le_rfl
  have hn := abs_le.mp (hB n)
  have hm := abs_le.mp (hB m)
  have a1 : |w n * G n| ≤ w n * B := by
    rw [abs_mul, abs_of_nonneg wn]; exact mul_le_mul_of_nonneg_left (hB n) wn
  have a2 : |w m * G m| ≤ w m * B := by
    rw [abs_mul, abs_of_nonneg wm]; exact mul_le_mul_of_nonneg_left (hB m) wm
  have b1 := abs_le.mp a1
  have b2 := abs_le.mp a2
  rw [abs_le]
  constructor <;> nlinarith

theorem term_bound (n a : ℕ) (ha : 0 < a) (hn : 0 < n) (x : ℝ) (hx : |x| ≤ 1) :
    |x * ((n/a : ℕ) : ℝ) / n - x / a| ≤ 1 / n := by
  have han : (0:ℝ) < a := by exact_mod_cast ha
  have hnn : (0:ℝ) < n := by exact_mod_cast hn
  have q1 : (a:ℝ) * ((n/a : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.mul_div_le n a
  have q2 : (n:ℝ) < a * (((n/a : ℕ) : ℝ) + 1) := by exact_mod_cast Nat.lt_mul_div_succ n ha
  have e : x * ((n/a : ℕ) : ℝ) / n - x / a = x * ((a * ((n/a : ℕ) : ℝ) - n) / (a * n)) := by
    field_simp
  rw [e, abs_mul]
  have hy : |(a * ((n/a : ℕ) : ℝ) - n) / (a * n)| ≤ 1 / n := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < a * n), div_le_div_iff₀ (by positivity) hnn]
    have hab : |(a:ℝ) * ((n/a : ℕ) : ℝ) - n| ≤ a := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    have := mul_le_mul_of_nonneg_right hab hnn.le
    linarith
  calc |x| * |(a * ((n/a : ℕ) : ℝ) - n) / (a * n)| ≤ 1 * (1 / n) := by
        apply mul_le_mul hx hy (abs_nonneg _) zero_le_one
    _ = 1 / n := one_mul _

theorem err_bound (c : ℕ → ℝ) (s : ℝ) (hc : ∀ a, |c a| ≤ 1)
    (hB : ∀ k, |∑ i ∈ range k, c i| ≤ s) (Y n : ℕ) (hYn : Y ≤ n) (hn : 0 < n) :
    |(∑ a ∈ Icc 1 n, c a * ((n / a : ℕ) : ℝ)) / n - ∑ a ∈ Icc 1 n, c a / a|
      ≤ Y / n + 4 * s / (Y + 1) := by
  have hnn : (0:ℝ) < n := by exact_mod_cast hn
  have hY1 : (0:ℝ) < (Y:ℝ) + 1 := by positivity
  have s0 : 0 ≤ s := le_trans (abs_nonneg _) (hB 0)
  rw [sum_div, ← sum_sub_distrib]
  have e1 : Icc 1 n = Ico 1 (n+1) := rfl
  rw [e1, ← sum_Ico_consecutive _ (by omega : 1 ≤ Y + 1) (by omega : Y + 1 ≤ n + 1)]
  have A1 : |∑ a ∈ Ico 1 (Y+1), (c a * ((n / a : ℕ) : ℝ) / n - c a / a)| ≤ Y / n := by
    calc _ ≤ ∑ a ∈ Ico 1 (Y+1), |c a * ((n / a : ℕ) : ℝ) / n - c a / a| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ Ico 1 (Y+1), (1 / (n:ℝ)) := by
        apply sum_le_sum
        intro a ha
        exact term_bound n a (mem_Ico.mp ha).1 hn (c a) (hc a)
      _ = Y / n := by simp [div_eq_mul_inv]
  have e2 : ∑ a ∈ Ico (Y+1) (n+1), (c a * ((n / a : ℕ) : ℝ) / n - c a / a)
      = ∑ a ∈ Ico (Y+1) (n+1), (((n / a : ℕ) : ℝ) / n) * c a
        - ∑ a ∈ Ico (Y+1) (n+1), (1 / (a:ℝ)) * c a := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro a _
    ring
  have A2 : |∑ a ∈ Ico (Y+1) (n+1), (((n / a : ℕ) : ℝ) / n) * c a| ≤ 2 * s / (Y + 1) := by
    have h := abel_bound c (fun a => ((n / a : ℕ) : ℝ) / n) s hB (Y+1)
      (fun i _ => by positivity)
      (fun i hi => by
        apply div_le_div_of_nonneg_right _ hnn.le
        exact_mod_cast Nat.div_le_div_left (by omega) (by omega))
      (n+1) (by omega)
    refine h.trans ?_
    have w1 : ((n / (Y+1) : ℕ) : ℝ) / n ≤ 1 / (Y + 1) := by
      calc ((n / (Y+1) : ℕ) : ℝ) / n ≤ ((n:ℝ) / ((Y+1 : ℕ) : ℝ)) / n := by
            gcongr
            exact Nat.cast_div_le
        _ = 1 / (Y + 1) := by push_cast; field_simp
    calc 2 * s * (((n / (Y+1) : ℕ) : ℝ) / n) ≤ 2 * s * (1 / (Y + 1)) := by gcongr
      _ = 2 * s / (Y + 1) := by ring
  have A3 : |∑ a ∈ Ico (Y+1) (n+1), (1 / (a:ℝ)) * c a| ≤ 2 * s / (Y + 1) := by
    have h := abel_bound c (fun a => 1 / (a:ℝ)) s hB (Y+1)
      (fun i _ => by positivity)
      (fun i hi => by
        apply one_div_le_one_div_of_le
        · have : (1:ℝ) ≤ i := by exact_mod_cast (by omega : 1 ≤ i)
          linarith
        · push_cast; linarith)
      (n+1) (by omega)
    refine h.trans ?_
    push_cast
    rw [mul_one_div]
  rw [e2]
  calc _ ≤ |∑ a ∈ Ico 1 (Y+1), (c a * ((n / a : ℕ) : ℝ) / n - c a / a)|
        + (|∑ a ∈ Ico (Y+1) (n+1), (((n / a : ℕ) : ℝ) / n) * c a|
        + |∑ a ∈ Ico (Y+1) (n+1), (1 / (a:ℝ)) * c a|) := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ Y / n + (2 * s / (Y + 1) + 2 * s / (Y + 1)) := by gcongr
    _ = Y / n + 4 * s / (Y + 1) := by ring

theorem h3_main (s : ℕ) (hs : 0 < s) (h8 : s % 8 = 3) (L : ℝ)
    (hL : Tendsto (fun n:ℕ => ∑ a∈Icc 1 n,(jacobiSym a s:ℝ)/(a:ℝ)) atTop (𝓝 L)) :
    Tendsto (fun n:ℕ => (∑ k∈Icc 1 n,∑ a∈k.divisors,(jacobiSym a s:ℝ))/(n:ℝ)) atTop (𝓝 L) := by
  set c : ℕ → ℝ := fun a => (jacobiSym a s : ℝ) with hcdef
  have hc : ∀ a, |c a| ≤ 1 := by
    intro a
    rcases jacobiSym.trichotomy (a:ℤ) s with h | h | h <;> simp [c, h]
  have hB : ∀ k, |∑ i ∈ range k, c i| ≤ (s:ℝ) := seg_bound s hs h8
  have hE : Tendsto (fun n:ℕ => (∑ a ∈ Icc 1 n, c a * ((n / a : ℕ) : ℝ)) / n
      - ∑ a ∈ Icc 1 n, c a / a) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨Y, hY⟩ := exists_nat_gt (8 * s / ε)
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * Y / ε)
    refine ⟨N + Y + 1, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero]
    have hn0 : 0 < n := by omega
    have hnn : (0:ℝ) < n := by exact_mod_cast hn0
    refine (err_bound c s hc hB Y n (by omega) hn0).trans_lt ?_
    have hY1 : (0:ℝ) < (Y:ℝ) + 1 := by positivity
    have t1 : (Y:ℝ) / n < ε / 2 := by
      rw [div_lt_iff₀ hnn]
      have : (N:ℝ) + Y + 1 ≤ n := by exact_mod_cast hn
      rw [div_lt_iff₀ hε] at hN
      nlinarith
    have t2 : 4 * (s:ℝ) / (Y + 1) < ε / 2 := by
      rw [div_lt_iff₀ hY1]
      rw [div_lt_iff₀ hε] at hY
      nlinarith
    linarith
  have h := hE.add hL
  rw [zero_add] at h
  refine h.congr (fun n => ?_)
  rw [divsum c n]
  ring

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1.H3 := by
  intro s hs h8 L hL
  exact OMA.Helpers.h3_main s hs h8 L hL
