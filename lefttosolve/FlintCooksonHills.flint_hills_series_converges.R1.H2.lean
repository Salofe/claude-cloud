import OMAReductions.R_FlintCooksonHills_flint_hills_series_converges_R1
import Mathlib

/-! Step H2 of reduction FlintCooksonHills.flint_hills_series_converges.R1: a uniform bound ||q a|| >= c q^(1-v) with v < 5/2
makes the series of 1/(q^3 ||q a||^2) converge. On each dyadic block [2^K, 2^(K+1)) the
values ||q a|| are at least d_K = c 2^((K+1)(1-v)) and pairwise d_K-separated on each side of
zero, so the block sum is at most 4 / (8^K d_K^2), a geometric sequence of ratio 2^(2v-5). -/

open Finset

namespace OMA.Helpers


/-- Positive values with pairwise gaps at least `δ` and all at least `δ`:
their inverse squares sum to at most `2 / δ ^ 2`. -/
theorem sep_sum_le (S : Finset ℕ) (x : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hlow : ∀ q ∈ S, δ ≤ x q)
    (hsep : ∀ q ∈ S, ∀ q' ∈ S, q ≠ q' → δ ≤ |x q - x q'|) :
    ∑ q ∈ S, 1 / (x q) ^ 2 ≤ 2 / δ ^ 2 := by
  set j : ℕ → ℕ := fun q => ⌊x q / δ⌋₊ with hj
  have hj1 : ∀ q ∈ S, 1 ≤ j q := by
    intro q hq
    simp only [hj]
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ hδ, one_mul]
    exact hlow q hq
  have hjle : ∀ q ∈ S, (j q : ℝ) * δ ≤ x q := by
    intro q hq
    have h0 : 0 ≤ x q / δ := div_nonneg (hδ.le.trans (hlow q hq)) hδ.le
    have := Nat.floor_le h0
    rwa [le_div_iff₀ hδ] at this
  have hjlt : ∀ q ∈ S, x q < ((j q : ℝ) + 1) * δ := by
    intro q hq
    have := Nat.lt_floor_add_one (x q / δ)
    rwa [div_lt_iff₀ hδ] at this
  have hinj : Set.InjOn j S := by
    intro q hq q' hq' hjq
    by_contra hne
    have h1 := hsep q hq q' hq' hne
    have a1 := hjle q hq
    have a2 := hjlt q hq
    have a3 := hjle q' hq'
    have a4 := hjlt q' hq'
    rw [hjq] at a1 a2
    have : |x q - x q'| < δ := by
      rw [abs_lt]
      constructor <;> nlinarith
    linarith
  set n : ℕ := (S.image j).sup id + 1 with hn
  have hsub : S.image j ⊆ Ioo 0 n := by
    intro m hm
    rw [mem_Ioo]
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hm
    refine ⟨hj1 q hq, ?_⟩
    have : j q ≤ (S.image j).sup id := le_sup (f := id) hm
    omega
  calc ∑ q ∈ S, 1 / (x q) ^ 2 ≤ ∑ q ∈ S, (1 / δ ^ 2) * ((j q : ℝ) ^ 2)⁻¹ := by
        apply sum_le_sum
        intro q hq
        have hjpos : (0 : ℝ) < j q := by exact_mod_cast hj1 q hq
        have hsq : ((j q : ℝ) * δ) ^ 2 ≤ (x q) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (hjle q hq) 2
        calc 1 / (x q) ^ 2 ≤ 1 / ((j q : ℝ) * δ) ^ 2 :=
              one_div_le_one_div_of_le (by positivity) hsq
          _ = (1 / δ ^ 2) * ((j q : ℝ) ^ 2)⁻¹ := by
              field_simp
    _ = (1 / δ ^ 2) * ∑ m ∈ S.image j, ((m : ℝ) ^ 2)⁻¹ := by
        rw [← mul_sum, sum_image hinj]
    _ ≤ (1 / δ ^ 2) * ∑ m ∈ Ioo 0 n, ((m : ℝ) ^ 2)⁻¹ := by
        gcongr
    _ ≤ (1 / δ ^ 2) * 2 := by
        gcongr
        have := sum_Ioo_inv_sq_le (α := ℝ) 0 n
        simpa using this
    _ = 2 / δ ^ 2 := by ring

theorem sep_of_hyp (α c ν : ℝ) (hc : 0 < c) (hν : 1 < ν)
    (hyp : ∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - ν) ≤ |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)|)
    (B : ℝ) (q q' : ℕ) (hlt : q' < q) (hB : ((q - q' : ℕ) : ℝ) ≤ B) :
    c * B ^ (1 - ν) ≤ |((q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)) -
      ((q' : ℝ) * α - (round ((q' : ℝ) * α) : ℝ))| := by
  have hk : 0 < q - q' := by omega
  have h1 := hyp (q - q') hk
  have hkpos : (0 : ℝ) < ((q - q' : ℕ) : ℝ) := by exact_mod_cast hk
  have h2 : B ^ (1 - ν) ≤ ((q - q' : ℕ) : ℝ) ^ (1 - ν) :=
    Real.rpow_le_rpow_of_nonpos hkpos hB (by linarith)
  have h3 := round_le (((q - q' : ℕ) : ℝ) * α) (round ((q : ℝ) * α) - round ((q' : ℝ) * α))
  have hcast : ((q - q' : ℕ) : ℝ) = (q : ℝ) - q' := by
    rw [Nat.cast_sub hlt.le]
  rw [hcast] at h3 h1
  have heq : (q : ℝ) * α - (round ((q : ℝ) * α) : ℝ) -
      ((q' : ℝ) * α - (round ((q' : ℝ) * α) : ℝ)) =
      ((q : ℝ) - q') * α - ((round ((q : ℝ) * α) - round ((q' : ℝ) * α) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [heq]
  calc c * B ^ (1 - ν) ≤ c * ((q - q' : ℕ) : ℝ) ^ (1 - ν) := by gcongr
    _ = c * ((q : ℝ) - q') ^ (1 - ν) := by rw [hcast]
    _ ≤ _ := h1
    _ ≤ _ := h3

theorem block_bound (α c ν : ℝ) (hc : 0 < c) (hν : 1 < ν)
    (hyp : ∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - ν) ≤ |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)|) (K : ℕ) :
    ∑ q ∈ (Ico (2 ^ K) (2 ^ (K + 1)) : Finset ℕ),
        1 / (((q : ℕ) : ℝ) ^ 3 * |((q : ℕ) : ℝ) * α - (round (((q : ℕ) : ℝ) * α) : ℝ)| ^ 2) ≤
      (1 / ((2 : ℝ) ^ K) ^ 3) * (4 / (c * ((2 : ℝ) ^ (K + 1)) ^ (1 - ν)) ^ 2) := by
  set e : ℕ → ℝ := fun q => (q : ℝ) * α - (round ((q : ℝ) * α) : ℝ) with he
  set δ : ℝ := c * ((2 : ℝ) ^ (K + 1)) ^ (1 - ν) with hδ
  set Bk := Ico (2 ^ K) (2 ^ (K + 1)) with hBk
  have hδpos : 0 < δ := by positivity
  have hlow : ∀ q ∈ Bk, δ ≤ |e q| := by
    intro q hq
    rw [hBk, mem_Ico] at hq
    have hq0 : 0 < q := lt_of_lt_of_le (Nat.two_pow_pos K) hq.1
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq0
    have hqle : (q : ℝ) ≤ (2 : ℝ) ^ (K + 1) := by exact_mod_cast hq.2.le
    have := Real.rpow_le_rpow_of_nonpos hqpos hqle (show 1 - ν ≤ 0 by linarith)
    calc δ ≤ c * (q : ℝ) ^ (1 - ν) := by rw [hδ]; gcongr
      _ ≤ |e q| := hyp q hq0
  have hsep : ∀ q ∈ Bk, ∀ q' ∈ Bk, q ≠ q' → δ ≤ |e q - e q'| := by
    have key : ∀ q ∈ Bk, ∀ q' ∈ Bk, q' < q → δ ≤ |e q - e q'| := by
      intro q hq q' hq' hlt
      rw [hBk, mem_Ico] at hq hq'
      have hB : ((q - q' : ℕ) : ℝ) ≤ (2 : ℝ) ^ (K + 1) := by
        have : q - q' ≤ 2 ^ (K + 1) := by omega
        exact_mod_cast this
      exact sep_of_hyp α c ν hc hν hyp _ q q' hlt hB
    intro q hq q' hq' hne
    rcases lt_or_gt_of_ne hne with h | h
    · rw [abs_sub_comm]
      exact key q' hq' q hq h
    · exact key q hq q' hq' h
  have hstep : ∑ q ∈ Bk, 1 / ((q : ℝ) ^ 3 * |e q| ^ 2) ≤
      ∑ q ∈ Bk, (1 / ((2 : ℝ) ^ K) ^ 3) * (1 / |e q| ^ 2) := by
    apply sum_le_sum
    intro q hq
    have hq' := mem_Ico.mp hq
    have hq2 : ((2 : ℝ) ^ K) ^ 3 ≤ (q : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hq'.1) 3
    have he0 : 0 < |e q| := hδpos.trans_le (hlow q hq)
    rw [one_div_mul_one_div]
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  have hsum2 : ∑ q ∈ Bk, 1 / |e q| ^ 2 ≤ 4 / δ ^ 2 := by
    rw [← sum_filter_add_sum_filter_not Bk (fun q => 0 ≤ e q)]
    have h1 : ∑ q ∈ Bk.filter (fun q => 0 ≤ e q), 1 / |e q| ^ 2 ≤ 2 / δ ^ 2 :=
      sep_sum_le _ (fun q => |e q|) δ hδpos (fun q hq => hlow q (mem_filter.mp hq).1)
        (fun q hq q' hq' hne => by
          have hq1 := mem_filter.mp hq
          have hq2 := mem_filter.mp hq'
          rw [abs_of_nonneg hq1.2, abs_of_nonneg hq2.2]
          exact hsep q hq1.1 q' hq2.1 hne)
    have h2 : ∑ q ∈ Bk.filter (fun q => ¬ 0 ≤ e q), 1 / |e q| ^ 2 ≤ 2 / δ ^ 2 :=
      sep_sum_le _ (fun q => |e q|) δ hδpos (fun q hq => hlow q (mem_filter.mp hq).1)
        (fun q hq q' hq' hne => by
          have hq1 := mem_filter.mp hq
          have hq2 := mem_filter.mp hq'
          rw [abs_of_neg (lt_of_not_ge hq1.2), abs_of_neg (lt_of_not_ge hq2.2),
            show -e q - -e q' = -(e q - e q') by ring, abs_neg]
          exact hsep q hq1.1 q' hq2.1 hne)
    have h4 : (4 : ℝ) / δ ^ 2 = 2 / δ ^ 2 + 2 / δ ^ 2 := by ring
    linarith
  calc ∑ q ∈ Bk, 1 / ((q : ℝ) ^ 3 * |e q| ^ 2)
      ≤ ∑ q ∈ Bk, (1 / ((2 : ℝ) ^ K) ^ 3) * (1 / |e q| ^ 2) := hstep
    _ = (1 / ((2 : ℝ) ^ K) ^ 3) * ∑ q ∈ Bk, 1 / |e q| ^ 2 := by rw [mul_sum]
    _ ≤ (1 / ((2 : ℝ) ^ K) ^ 3) * (4 / δ ^ 2) := by gcongr

theorem block_geom (c ν : ℝ) (hc : 0 < c) (K : ℕ) :
    (1 / ((2 : ℝ) ^ K) ^ 3) * (4 / (c * ((2 : ℝ) ^ (K + 1)) ^ (1 - ν)) ^ 2) =
      (4 / c ^ 2 * (2 : ℝ) ^ (2 * ν - 2)) * ((2 : ℝ) ^ (2 * ν - 5)) ^ K := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have e1 : ((2 : ℝ) ^ K) ^ 3 = (2 : ℝ) ^ (((3 * K : ℕ)) : ℝ) := by
    rw [Real.rpow_natCast]
    ring
  have e2 : ((2 : ℝ) ^ (K + 1)) ^ (1 - ν) = (2 : ℝ) ^ (((K + 1 : ℕ) : ℝ) * (1 - ν)) := by
    rw [Real.rpow_mul h2.le, Real.rpow_natCast]
  have e3 : ((2 : ℝ) ^ (2 * ν - 5)) ^ K = (2 : ℝ) ^ ((2 * ν - 5) * (K : ℝ)) := by
    rw [Real.rpow_mul_natCast h2.le]
  rw [e1, e2, e3, mul_pow, ← Real.rpow_mul_natCast h2.le]
  set X := (2 : ℝ) ^ (((3 * K : ℕ)) : ℝ) with hX
  set Y := (2 : ℝ) ^ (((K + 1 : ℕ) : ℝ) * (1 - ν) * ((2 : ℕ) : ℝ)) with hY
  set Z := (2 : ℝ) ^ (2 * ν - 2) with hZ
  set W := (2 : ℝ) ^ ((2 * ν - 5) * (K : ℝ)) with hW
  have hXp : 0 < X := Real.rpow_pos_of_pos h2 _
  have hYp : 0 < Y := Real.rpow_pos_of_pos h2 _
  have key : X * Y * (Z * W) = 1 := by
    rw [hX, hY, hZ, hW, ← Real.rpow_add h2, ← Real.rpow_add h2, ← Real.rpow_add h2]
    have : ((3 * K : ℕ) : ℝ) + ((K + 1 : ℕ) : ℝ) * (1 - ν) * ((2 : ℕ) : ℝ) +
        ((2 * ν - 2) + (2 * ν - 5) * (K : ℝ)) = 0 := by
      push_cast
      ring
    rw [this, Real.rpow_zero]
  have hZW : Z * W = 1 / (X * Y) := by
    rw [eq_div_iff (by positivity)]
    linarith [key, mul_comm (X * Y) (Z * W)]
  rw [mul_assoc (4 / c ^ 2), hZW]
  field_simp

theorem flint_H2 : ∀ α c ν : ℝ, 0 < c → 1 < ν → ν < 5 / 2 →
    (∀ q : ℕ, 0 < q →
      c * (q : ℝ) ^ (1 - ν) ≤ |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)|) →
    Summable (fun q : ℕ =>
      1 / ((q : ℝ) ^ 3 * |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| ^ 2)) := by
  intro α c ν hc hν hν2 hyp
  set f : ℕ → ℝ := fun q =>
    1 / ((q : ℝ) ^ 3 * |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| ^ 2) with hf
  have hf0 : ∀ q, 0 ≤ f q := fun q => by
    simp only [hf]
    positivity
  set A : ℝ := 4 / c ^ 2 * (2 : ℝ) ^ (2 * ν - 2) with hA
  set ρ : ℝ := (2 : ℝ) ^ (2 * ν - 5) with hρ
  have hA0 : 0 ≤ A := by positivity
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hblock : ∀ K, ∑ q ∈ Ico (2 ^ K) (2 ^ (K + 1)), f q ≤ A * ρ ^ K := fun K =>
    (block_bound α c ν hc hν hyp K).trans (block_geom c ν hc K).le
  have hdecomp : ∀ n, ∑ q ∈ range (2 ^ n), f q =
      f 0 + ∑ K ∈ range n, ∑ q ∈ Ico (2 ^ K) (2 ^ (K + 1)), f q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ← add_assoc, ← ih,
        sum_range_add_sum_Ico _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n))]
  have hf00 : f 0 = 0 := by simp [hf]
  apply summable_of_sum_range_le hf0 (c := A * (1 - ρ)⁻¹)
  intro n
  calc ∑ i ∈ range n, f i ≤ ∑ i ∈ range (2 ^ n), f i :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.2 n.lt_two_pow_self.le)
          (fun i _ _ => hf0 i)
    _ = ∑ K ∈ range n, ∑ q ∈ Ico (2 ^ K) (2 ^ (K + 1)), f q := by
        rw [hdecomp, hf00, zero_add]
    _ ≤ ∑ K ∈ range n, A * ρ ^ K := sum_le_sum (fun K _ => hblock K)
    _ = A * ∑ K ∈ range n, ρ ^ K := by rw [mul_sum]
    _ ≤ A * (1 - ρ)⁻¹ := by
        gcongr
        rw [← tsum_geometric_of_lt_one hρ0 hρ1]
        exact (summable_geometric_of_lt_one hρ0 hρ1).sum_le_tsum _ (fun i _ => pow_nonneg hρ0 i)

end OMA.Helpers

theorem OMA.solution : OMA.R_FlintCooksonHills_flint_hills_series_converges_R1.H2 :=
  OMA.Helpers.flint_H2
