import OMAReductions.R_FlintCooksonHills_cookson_hills_series_converges_R1
import Mathlib

/-! Step H2 of reduction FlintCooksonHills.cookson_hills_series_converges.R1.

Write e(q) = q a - round(q a), so |e(q)| is the distance from q a to the nearest integer, and
assume c q^(1-v) <= |e(q)| for every q >= 1, with c > 0 and 1 < v < 5/2.

* Dyadic block [2^K, 2^(K+1)): put s = 2^(1-v) and d = c s^(K+1). Each |e(q)| in the block is at
  least d, and for q' < q in the block e(q) - e(q') differs from (q - q') a by an integer, hence
  |e(q) - e(q')| >= |e(q - q')| >= c (q - q')^(1-v) >= d.
* Separated values: values that are all >= d and pairwise at least d apart have their k-th
  smallest member >= k d, so their inverse squares add up to at most (1 + 1/4 + 1/9 + ...) / d^2,
  which is <= 2 / d^2. Using this for the nonnegative and for the negative e(q) separately, the
  block total of e(q)^(-2) is at most 4 / d^2.
* As q^3 >= 8^K on the block, the block contributes at most (4 / (c^2 s^2)) r^K where
  r = 1 / (8 s^2) = 2^(2v-5) < 1, so the sums over range N stay below a geometric bound. -/

open Finset

namespace OMA.Helpers

/-- Values at least `δ`, pairwise `δ`-separated: the inverse squares are dominated by
`δ⁻² Σ_{k < n} (k+1)⁻²`.  The second conjunct is the induction invariant. -/
theorem inv_sq_sum_of_separated {ι : Type*} [DecidableEq ι] (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (s : Finset ι) :
    (∀ i ∈ s, δ ≤ x i) → (∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |x i - x j|) →
      (∑ i ∈ s, 1 / x i ^ 2 ≤ (1 / δ ^ 2) * ∑ k ∈ range s.card, 1 / ((k : ℝ) + 1) ^ 2) ∧
      (∀ y : ℝ, δ ≤ y → (∀ i ∈ s, x i + δ ≤ y) → ((s.card : ℝ) + 1) * δ ≤ y) := by
  induction s using Finset.induction_on_max_value x with
  | empty =>
    intro _ _
    refine ⟨by simp, fun y hy _ => ?_⟩
    simpa using hy
  | insert a s ha hmax ih =>
    intro hlow hsep
    obtain ⟨hsum, hgap⟩ := ih (fun i hi => hlow i (mem_insert_of_mem hi))
      (fun i hi j hj hij => hsep i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)
    have hxa : δ ≤ x a := hlow a (mem_insert_self a s)
    have hbelow : ∀ i ∈ s, x i + δ ≤ x a := by
      intro i hi
      have hne : a ≠ i := fun h => ha (by rw [h]; exact hi)
      have h1 := hsep a (mem_insert_self a s) i (mem_insert_of_mem hi) hne
      have h2 := hmax i hi
      rw [abs_of_nonneg (show 0 ≤ x a - x i by linarith)] at h1
      linarith
    have hbig : ((s.card : ℝ) + 1) * δ ≤ x a := hgap (x a) hxa hbelow
    rw [card_insert_of_notMem ha]
    push_cast
    refine ⟨?_, fun y _ hall => ?_⟩
    · rw [sum_insert ha, sum_range_succ, mul_add]
      have hpos : 0 < ((s.card : ℝ) + 1) * δ := by positivity
      have h3 : 1 / x a ^ 2 ≤ 1 / δ ^ 2 * (1 / ((s.card : ℝ) + 1) ^ 2) := by
        have e : 1 / δ ^ 2 * (1 / ((s.card : ℝ) + 1) ^ 2) =
            1 / (((s.card : ℝ) + 1) * δ) ^ 2 := by
          rw [one_div_mul_one_div, mul_pow, mul_comm (δ ^ 2)]
        rw [e]
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hpos.le hbig 2)
      linarith
    · have := hall a (mem_insert_self a s)
      linarith

theorem basel_head_le_two (n : ℕ) : ∑ k ∈ range n, 1 / ((k : ℝ) + 1) ^ 2 ≤ 2 := by
  have key : ∀ m : ℕ, ∑ k ∈ range (m + 1), 1 / ((k : ℝ) + 1) ^ 2 + 1 / ((m : ℝ) + 1) ≤ 2 := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [sum_range_succ]
      have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have step : 1 / (((m + 1 : ℕ) : ℝ) + 1) ^ 2 + 1 / (((m + 1 : ℕ) : ℝ) + 1) ≤
          1 / ((m : ℝ) + 1) := by
        push_cast
        rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) hm]
        nlinarith
      linarith
  cases n with
  | zero => simp
  | succ m =>
    have h1 := key m
    have h2 : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := by positivity
    linarith

theorem gap_of_hyp (α c ν : ℝ)
    (hyp : ∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - ν) ≤ |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)|)
    (q q' : ℕ) (h : q' < q) :
    c * ((q - q' : ℕ) : ℝ) ^ (1 - ν) ≤
      |((q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)) - ((q' : ℝ) * α - (round ((q' : ℝ) * α) : ℝ))| := by
  have h1 := hyp (q - q') (Nat.sub_pos_of_lt h)
  have h2 := round_le (((q - q' : ℕ) : ℝ) * α) (round ((q : ℝ) * α) - round ((q' : ℝ) * α))
  have e : ((q - q' : ℕ) : ℝ) * α - ((round ((q : ℝ) * α) - round ((q' : ℝ) * α) : ℤ) : ℝ) =
      ((q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)) - ((q' : ℝ) * α - (round ((q' : ℝ) * α) : ℝ)) := by
    rw [Nat.cast_sub h.le]
    push_cast
    ring
  rw [e] at h2
  linarith

theorem rpow_block_lower (ν : ℝ) (hν : 1 < ν) (K m : ℕ) (hm0 : 0 < m) (hm : m ≤ 2 ^ (K + 1)) :
    ((2 : ℝ) ^ (1 - ν)) ^ (K + 1) ≤ (m : ℝ) ^ (1 - ν) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmle : (m : ℝ) ≤ (2 : ℝ) ^ (K + 1) := by exact_mod_cast hm
  have e : ((2 : ℝ) ^ (1 - ν)) ^ (K + 1) = ((2 : ℝ) ^ (K + 1)) ^ (1 - ν) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (1 - ν)), ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast (2 : ℝ), ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [e]
  exact Real.rpow_le_rpow_of_nonpos hmpos hmle (by linarith)

theorem one_lt_eight_mul_sq (ν : ℝ) (hν : ν < 5 / 2) : 1 < 8 * ((2 : ℝ) ^ (1 - ν)) ^ 2 := by
  have e : (8 : ℝ) * ((2 : ℝ) ^ (1 - ν)) ^ 2 = (2 : ℝ) ^ (5 - 2 * ν) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (1 - ν)) 2, ← Real.rpow_mul (by norm_num),
      show (5 - 2 * ν) = (3 : ℝ) + (1 - ν) * ((2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add (by norm_num), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [e]
  exact Real.one_lt_rpow (by norm_num) (by linarith)

theorem block_sum_le (α c ν : ℝ) (hc : 0 < c) (hν : 1 < ν)
    (hyp : ∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - ν) ≤ |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)|) (K : ℕ) :
    ∑ q ∈ Ico (2 ^ K : ℕ) (2 ^ (K + 1)),
        1 / ((q : ℝ) ^ 3 * |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| ^ 2) ≤
      (4 / (c ^ 2 * ((2 : ℝ) ^ (1 - ν)) ^ 2)) * (1 / (8 * ((2 : ℝ) ^ (1 - ν)) ^ 2)) ^ K := by
  set s : ℝ := (2 : ℝ) ^ (1 - ν) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos (by norm_num) _
  set δ : ℝ := c * s ^ (K + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  set B : Finset ℕ := Ico (2 ^ K : ℕ) (2 ^ (K + 1)) with hB
  set e : ℕ → ℝ := fun q => (q : ℝ) * α - (round ((q : ℝ) * α) : ℝ) with he
  have hlow : ∀ q ∈ B, δ ≤ |e q| := by
    intro q hq
    rw [hB, mem_Ico] at hq
    have hq0 : 0 < q := lt_of_lt_of_le (Nat.two_pow_pos K) hq.1
    calc δ = c * s ^ (K + 1) := rfl
      _ ≤ c * (q : ℝ) ^ (1 - ν) :=
          mul_le_mul_of_nonneg_left (rpow_block_lower ν hν K q hq0 hq.2.le) hc.le
      _ ≤ |e q| := hyp q hq0
  have hsep : ∀ q ∈ B, ∀ q' ∈ B, q ≠ q' → δ ≤ |e q - e q'| := by
    have key : ∀ q ∈ B, ∀ q' ∈ B, q' < q → δ ≤ |e q - e q'| := by
      intro q hq q' hq' hlt
      rw [hB, mem_Ico] at hq hq'
      calc δ = c * s ^ (K + 1) := rfl
        _ ≤ c * ((q - q' : ℕ) : ℝ) ^ (1 - ν) :=
            mul_le_mul_of_nonneg_left
              (rpow_block_lower ν hν K (q - q') (Nat.sub_pos_of_lt hlt) (by omega)) hc.le
        _ ≤ |e q - e q'| := gap_of_hyp α c ν hyp q q' hlt
    intro q hq q' hq' hne
    rcases lt_or_gt_of_ne hne with h | h
    · rw [abs_sub_comm]
      exact key q' hq' q hq h
    · exact key q hq q' hq' h
  have hstep : ∑ q ∈ B, 1 / ((q : ℝ) ^ 3 * |e q| ^ 2) ≤
      ∑ q ∈ B, (1 / (8 : ℝ) ^ K) * (1 / e q ^ 2) := by
    apply sum_le_sum
    intro q hq
    have hq' := mem_Ico.mp hq
    have hpow : (8 : ℝ) ^ K = ((2 : ℝ) ^ K) ^ 3 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have h8 : (8 : ℝ) ^ K ≤ (q : ℝ) ^ 3 := by
      rw [hpow]
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hq'.1) 3
    have he0 : 0 < e q ^ 2 := by
      have := hδ0.trans_le (hlow q hq)
      rw [← sq_abs]
      positivity
    rw [sq_abs, one_div_mul_one_div]
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_right h8 he0.le)
  have hsplit : ∑ q ∈ B, 1 / e q ^ 2 ≤ 4 / δ ^ 2 := by
    rw [← sum_filter_add_sum_filter_not B (fun q => 0 ≤ e q)]
    have hP := (inv_sq_sum_of_separated e δ hδ0 (B.filter (fun q => 0 ≤ e q))
      (fun q hq => by
        obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
        have := hlow q hq1
        rwa [abs_of_nonneg hq2] at this)
      (fun q hq q' hq' hne => hsep q (mem_filter.mp hq).1 q' (mem_filter.mp hq').1 hne)).1
    have hN := (inv_sq_sum_of_separated (fun q => -e q) δ hδ0 (B.filter (fun q => ¬ 0 ≤ e q))
      (fun q hq => by
        obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
        have := hlow q hq1
        rwa [abs_of_neg (lt_of_not_ge hq2)] at this)
      (fun q hq q' hq' hne => by
        have := hsep q (mem_filter.mp hq).1 q' (mem_filter.mp hq').1 hne
        rwa [show -e q - -e q' = -(e q - e q') by ring, abs_neg])).1
    simp only [neg_sq] at hN
    have hd : 0 ≤ 1 / δ ^ 2 := by positivity
    have hb1 := mul_le_mul_of_nonneg_left
      (basel_head_le_two (B.filter (fun q => 0 ≤ e q)).card) hd
    have hb2 := mul_le_mul_of_nonneg_left
      (basel_head_le_two (B.filter (fun q => ¬ 0 ≤ e q)).card) hd
    have h4 : 4 / δ ^ 2 = 1 / δ ^ 2 * 2 + 1 / δ ^ 2 * 2 := by ring
    linarith
  calc ∑ q ∈ B, 1 / ((q : ℝ) ^ 3 * |e q| ^ 2)
      ≤ ∑ q ∈ B, (1 / (8 : ℝ) ^ K) * (1 / e q ^ 2) := hstep
    _ = (1 / (8 : ℝ) ^ K) * ∑ q ∈ B, 1 / e q ^ 2 := by rw [mul_sum]
    _ ≤ (1 / (8 : ℝ) ^ K) * (4 / δ ^ 2) := by gcongr
    _ = (4 / (c ^ 2 * s ^ 2)) * (1 / (8 * s ^ 2)) ^ K := by
        have hsK : (s ^ 2) ^ K = (s ^ K) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
        have hs' : s ≠ 0 := hs0.ne'
        have hc' : c ≠ 0 := hc.ne'
        have hsK0 : s ^ K ≠ 0 := pow_ne_zero K hs'
        rw [hδ]
        simp only [one_div_pow, mul_pow]
        rw [hsK, pow_succ]
        field_simp
        ring

theorem dyadic_partial_le (f : ℕ → ℝ) (hf0 : f 0 = 0) (A ρ : ℝ)
    (hblock : ∀ K : ℕ, ∑ q ∈ Ico (2 ^ K) (2 ^ (K + 1)), f q ≤ A * ρ ^ K) (n : ℕ) :
    ∑ q ∈ range (2 ^ n), f q ≤ ∑ K ∈ range n, A * ρ ^ K := by
  induction n with
  | zero => simp [hf0]
  | succ n ih =>
    have hsplit : ∑ q ∈ range (2 ^ (n + 1)), f q =
        ∑ q ∈ range (2 ^ n), f q + ∑ q ∈ Ico (2 ^ n) (2 ^ (n + 1)), f q := by
      rw [range_eq_Ico, range_eq_Ico, sum_Ico_consecutive f (Nat.zero_le _)
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n))]
    rw [hsplit, sum_range_succ]
    linarith [hblock n]

theorem geom_head_le (A ρ : ℝ) (hA : 0 ≤ A) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (n : ℕ) :
    ∑ K ∈ range n, A * ρ ^ K ≤ A / (1 - ρ) := by
  have h1 : 0 < 1 - ρ := by linarith
  have hg := geom_sum_mul ρ n
  have hpow : 0 ≤ ρ ^ n := pow_nonneg hρ0 n
  have hS : ∑ K ∈ range n, ρ ^ K ≤ 1 / (1 - ρ) := by
    rw [le_div_iff₀ h1]
    linarith
  calc ∑ K ∈ range n, A * ρ ^ K = A * ∑ K ∈ range n, ρ ^ K := by rw [mul_sum]
    _ ≤ A * (1 / (1 - ρ)) := mul_le_mul_of_nonneg_left hS hA
    _ = A / (1 - ρ) := by ring

theorem summable_of_dist_bound (α c ν : ℝ) (hc : 0 < c) (hν : 1 < ν) (hν2 : ν < 5 / 2)
    (hyp : ∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - ν) ≤ |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)|) :
    Summable (fun q : ℕ =>
      1 / ((q : ℝ) ^ 3 * |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| ^ 2)) := by
  set s : ℝ := (2 : ℝ) ^ (1 - ν) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos (by norm_num) _
  have h8 : 1 < 8 * s ^ 2 := one_lt_eight_mul_sq ν hν2
  set A : ℝ := 4 / (c ^ 2 * s ^ 2) with hA
  set ρ : ℝ := 1 / (8 * s ^ 2) with hρ
  have hA0 : 0 ≤ A := by positivity
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by
    rw [hρ, div_lt_one (by positivity)]
    exact h8
  set f : ℕ → ℝ := fun q =>
    1 / ((q : ℝ) ^ 3 * |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| ^ 2) with hf
  have hf0 : ∀ q, 0 ≤ f q := fun q => by
    simp only [hf]
    positivity
  have hf00 : f 0 = 0 := by simp [hf]
  apply summable_of_sum_range_le hf0 (c := A / (1 - ρ))
  intro N
  calc ∑ q ∈ range N, f q ≤ ∑ q ∈ range (2 ^ N), f q :=
        sum_le_sum_of_subset_of_nonneg
          (range_subset_range.mpr (Nat.lt_two_pow_self (n := N)).le) (fun q _ _ => hf0 q)
    _ ≤ ∑ K ∈ range N, A * ρ ^ K :=
        dyadic_partial_le f hf00 A ρ (fun K => block_sum_le α c ν hc hν hyp K) N
    _ ≤ A / (1 - ρ) := geom_head_le A ρ hA0 hρ0 hρ1 N

end OMA.Helpers

theorem OMA.solution : OMA.R_FlintCooksonHills_cookson_hills_series_converges_R1.H2 :=
  fun α c ν hc hν hν2 hyp => OMA.Helpers.summable_of_dist_bound α c ν hc hν hν2 hyp
