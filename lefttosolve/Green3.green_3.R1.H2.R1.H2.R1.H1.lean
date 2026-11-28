import OMAReductions.R_Green3_green_3_R1_H2_R1_H2_R1
import Mathlib

/-!
# Step H1 of the reduction Green3.green_3.R1.H2.R1.H2.R1

By inner regularity of Lebesgue measure the open set U contains a compact set K of measure
larger than 1/3, and some thickening of K of radius delta still lies in U. Points of U are
strictly between 0 and 1, so K is bounded below by its least element rho. Take q close to 1
with 1-q below delta, and N with q^N below rho. The cells [q^(i+1), q^i] with i below N that
meet K cover K, and each of them lies in the thickening of K, hence in U; their total length
(1-q) times the sum of the q^i is at least the measure of K. If three selected cells i, j, l
had l between i+j-1 and i+j+2, then q^i q^j (when l is at most i+j) or q^(i+1) q^(j+1)
(otherwise) would be a product of two points of U lying in the cell l, hence in U.
-/

open MeasureTheory

namespace OMA.Helpers

/-- Points of an open subset of the unit interval lie strictly inside it. -/
lemma green3H1_interior (U : Set ℝ) (hU : IsOpen U) (hsub : U ⊆ Set.Icc 0 1) (x : ℝ)
    (hx : x ∈ U) : 0 < x ∧ x < 1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  have h1 : x - ε/2 ∈ U := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  have h2 : x + ε/2 ∈ U := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  have a1 := (hsub h1).1
  have a2 := (hsub h2).2
  constructor <;> linarith

end OMA.Helpers

open MeasureTheory in
theorem OMA.solution : OMA.R_Green3_green_3_R1_H2_R1_H2_R1.H1 := by
  classical
  intro U hU hsub hvol hpf
  obtain ⟨K, hKU, hKc, hKvol⟩ := hU.exists_lt_isCompact hvol
  obtain ⟨δ, hδ, hthick⟩ := hKc.exists_thickening_subset_open hU hKU
  have hKne : K.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, measure_empty] at hKvol
    simp at hKvol
  obtain ⟨ρ, hρK, hρmin⟩ := hKc.exists_isMinOn hKne continuousOn_id
  have hρ : 0 < ρ := (OMA.Helpers.green3H1_interior U hU hsub ρ (hKU hρK)).1
  set q : ℝ := max (1/2) (1 - δ/2) with hqdef
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hq1 : q < 1 := max_lt (by norm_num) (by linarith)
  have hqδ : 1 - q < δ := by
    have := le_max_right (1/2 : ℝ) (1 - δ/2)
    linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hρ hq1
  let cell : ℕ → Set ℝ := fun i => Set.Icc (q^(i+1)) (q^i)
  let T : Finset ℕ := (Finset.range N).filter (fun i => (cell i ∩ K).Nonempty)
  have anti : ∀ m n : ℕ, m ≤ n → q^n ≤ q^m := fun m n h =>
    pow_le_pow_of_le_one hq0.le hq1.le h
  -- every selected cell lies in U
  have hcell : ∀ i ∈ T, cell i ⊆ U := by
    intro i hi z hz
    obtain ⟨y, hyc, hyK⟩ := (Finset.mem_filter.mp hi).2
    apply hthick
    rw [Metric.mem_thickening_iff]
    refine ⟨y, hyK, ?_⟩
    rw [Real.dist_eq, abs_lt]
    have hz1 := hz.1
    have hz2 := hz.2
    have hy1 := hyc.1
    have hy2 := hyc.2
    have hqi : q^i ≤ 1 := pow_le_one₀ hq0.le hq1.le
    have e : q^(i+1) = q * q^i := by ring
    rw [e] at hz1 hy1
    have hw : q^i - q * q^i ≤ 1 - q := by nlinarith
    constructor <;> linarith
  -- K is covered by the selected cells
  have hcover : K ⊆ ⋃ i ∈ T, cell i := by
    intro x hx
    have hxρ : ρ ≤ x := hρmin hx
    have hx01 := OMA.Helpers.green3H1_interior U hU hsub x (hKU hx)
    have hex : ∃ n : ℕ, q^n ≤ x := ⟨N, by linarith⟩
    let n := Nat.find hex
    have hn : q^n ≤ x := Nat.find_spec hex
    have hn0 : n ≠ 0 := by
      intro h0
      have : q^n = 1 := by rw [h0, pow_zero]
      linarith [hx01.2]
    obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hlt : x < q^i := by
      have := Nat.find_min hex (show i < n by omega)
      push Not at this
      exact this
    have hnN : n ≤ N := Nat.find_min' hex (by linarith)
    have hxc : x ∈ cell i := ⟨by rw [show i + 1 = n by omega]; exact hn, hlt.le⟩
    refine Set.mem_iUnion₂.mpr ⟨i, ?_, hxc⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨x, hxc, hx⟩⟩
  -- the measure estimate
  have hmeas : volume K ≤ ENNReal.ofReal ((1-q) * ∑ i ∈ T, q^i) := by
    calc volume K ≤ volume (⋃ i ∈ T, cell i) := measure_mono hcover
      _ ≤ ∑ i ∈ T, volume (cell i) := measure_biUnion_finset_le T cell
      _ = ∑ i ∈ T, ENNReal.ofReal (q^i - q^(i+1)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact Real.volume_Icc
      _ = ENNReal.ofReal (∑ i ∈ T, (q^i - q^(i+1))) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro i _
          linarith [anti i (i+1) (by omega)]
      _ = ENNReal.ofReal ((1-q) * ∑ i ∈ T, q^i) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
  have hthird : (1/3 : ENNReal) = ENNReal.ofReal (1/3) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  have hbig : (1/3 : ℝ) < (1-q) * ∑ i ∈ T, q^i := by
    have h := lt_of_lt_of_le hKvol hmeas
    rw [hthird] at h
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mp h
  refine ⟨q, hq0, hq1, T, ?_, ?_, hbig⟩
  · rw [Finset.nonempty_iff_ne_empty]
    intro hT
    rw [hT, Finset.sum_empty, mul_zero] at hbig
    linarith
  · intro i hi j hj l hl
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    by_cases hc : l ≤ i + j
    · have hx : q^i ∈ U := hcell i hi ⟨anti i (i+1) (by omega), le_refl _⟩
      have hy : q^j ∈ U := hcell j hj ⟨anti j (j+1) (by omega), le_refl _⟩
      apply hpf _ hx _ hy
      have e : q^i * q^j = q^(i+j) := by ring
      rw [e]
      exact hcell l hl ⟨anti (i+j) (l+1) h1, anti l (i+j) hc⟩
    · have hx : q^(i+1) ∈ U := hcell i hi ⟨le_refl _, anti i (i+1) (by omega)⟩
      have hy : q^(j+1) ∈ U := hcell j hj ⟨le_refl _, anti j (j+1) (by omega)⟩
      apply hpf _ hx _ hy
      have e : q^(i+1) * q^(j+1) = q^(i+j+2) := by ring
      rw [e]
      exact hcell l hl ⟨anti (i+j+2) (l+1) (by omega), anti l (i+j+2) h2⟩
