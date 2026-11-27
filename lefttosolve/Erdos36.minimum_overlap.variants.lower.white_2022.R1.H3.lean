import OMAReductions.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1
import Mathlib

/-!
# Step H3 of the reduction Erdos36.minimum_overlap.variants.lower.white_2022.R1

Given a balanced partition (A, B) of {1, ..., 2n}, we split (-1, 1] into the 2n cells
(-1 + (a - 1)/n, -1 + a/n] and take f to be 1 on the cells indexed by A and 0 elsewhere.
Then f is measurable, takes values in [0, 1] and has integral n * (1/n) = 1.

For the overlap integral we bound the integrand pointwise by the sum, over (a, b) in A x B,
of the indicator of the set of t lying in the cell of a with x + t in the cell of b, plus the
indicator of the single point t = -1 - x (where x + t is the left end of [-1, 1] and lies in no
cell). The integral of each such indicator is at most the length of the intersection of two
intervals of length 1/n, namely max 0 (1 - |(b - a) - n x|) / n, and the single point has
measure zero.
-/

namespace OMA.Helpers

open MeasureTheory Set

/-- Left endpoint of the cell of index `a` (cells have length `1 / n` and tile `(-1, 1]`). -/
noncomputable def lo (n : ℕ) (a : ℤ) : ℝ := -1 + ((a : ℝ) - 1) / n

/-- The cell of index `a`. -/
noncomputable def cell (n : ℕ) (a : ℤ) : Set ℝ := Ioc (lo n a) (lo n a + 1 / n)

theorem mem_cell {n : ℕ} (hn : 0 < n) (a : ℤ) (t : ℝ) :
    t ∈ cell n a ↔ ⌈(n : ℝ) * (t + 1)⌉ = a := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Int.ceil_eq_iff, cell, mem_Ioc, lo]
  have e1 : (-1 : ℝ) + ((a : ℝ) - 1) / n < t ↔ (a : ℝ) - 1 < n * (t + 1) := by
    have e : (-1 : ℝ) + ((a : ℝ) - 1) / n < t ↔ ((a : ℝ) - 1) / n < t + 1 :=
      ⟨fun h => by linarith, fun h => by linarith⟩
    rw [e, div_lt_iff₀ hn']
    constructor <;> intro h <;> linarith
  have e2 : t ≤ (-1 : ℝ) + ((a : ℝ) - 1) / n + 1 / n ↔ n * (t + 1) ≤ (a : ℝ) := by
    have : (-1 : ℝ) + ((a : ℝ) - 1) / n + 1 / n = -1 + (a : ℝ) / n := by
      field_simp
      ring
    have e : t ≤ (-1 : ℝ) + (a : ℝ) / n ↔ t + 1 ≤ (a : ℝ) / n :=
      ⟨fun h => by linarith, fun h => by linarith⟩
    rw [this, e, le_div_iff₀ hn']
    constructor <;> intro h <;> linarith
  rw [e1, e2]

theorem measurableSet_cell (n : ℕ) (a : ℤ) : MeasurableSet (cell n a) := measurableSet_Ioc

theorem cell_subset {n : ℕ} (hn : 0 < n) {a : ℤ} (ha : a ∈ Finset.Icc (1 : ℤ) (2 * n)) :
    cell n a ⊆ Ioc (-1 : ℝ) 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Finset.mem_Icc] at ha
  have h1 : (1 : ℝ) ≤ a := by exact_mod_cast ha.1
  have h2 : (a : ℝ) ≤ 2 * n := by exact_mod_cast ha.2
  intro t ht
  rw [cell, mem_Ioc, lo] at ht
  have e : (-1 : ℝ) + ((a : ℝ) - 1) / n + 1 / n = -1 + (a : ℝ) / n := by
    field_simp
    ring
  rw [e] at ht
  have h3 : 0 ≤ ((a : ℝ) - 1) / n := div_nonneg (by linarith) hn'.le
  have h4 : (a : ℝ) / n ≤ 2 := by rw [div_le_iff₀ hn']; linarith
  constructor <;> linarith [ht.1, ht.2]

theorem volume_real_cell (n : ℕ) (hn : 0 < n) (a : ℤ) : volume.real (cell n a) = 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [cell, Real.volume_real_Ioc]
  have : lo n a + 1 / n - lo n a = 1 / n := by ring
  rw [this]
  exact max_eq_left (by positivity)

/-- The step function: `1` on the cells indexed by `A`, `0` elsewhere. -/
noncomputable def stepFn (n : ℕ) (A : Finset ℤ) (t : ℝ) : ℝ :=
  ∑ a ∈ A, (cell n a).indicator 1 t

theorem stepFn_eq {n : ℕ} (hn : 0 < n) (A : Finset ℤ) (t : ℝ) :
    stepFn n A t = if ⌈(n : ℝ) * (t + 1)⌉ ∈ A then 1 else 0 := by
  unfold stepFn
  have : ∀ a ∈ A, (cell n a).indicator (1 : ℝ → ℝ) t =
      if ⌈(n : ℝ) * (t + 1)⌉ = a then 1 else 0 := by
    intro a _
    by_cases h : ⌈(n : ℝ) * (t + 1)⌉ = a
    · rw [if_pos h, indicator_of_mem ((mem_cell hn a t).mpr h), Pi.one_apply]
    · rw [if_neg h, indicator_of_notMem (fun h' => h ((mem_cell hn a t).mp h'))]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]

theorem stepFn_measurable (n : ℕ) (A : Finset ℤ) : Measurable (stepFn n A) := by
  unfold stepFn
  exact Finset.measurable_sum _ fun a _ => measurable_one.indicator (measurableSet_cell n a)

theorem stepFn_bounds {n : ℕ} (hn : 0 < n) (A : Finset ℤ) (t : ℝ) :
    0 ≤ stepFn n A t ∧ stepFn n A t ≤ 1 := by
  rw [stepFn_eq hn]
  split_ifs <;> norm_num

theorem integrable_indicator_one (s : Set ℝ) (hs : MeasurableSet s) :
    Integrable (s.indicator (1 : ℝ → ℝ)) (volume.restrict (Ioc (-1 : ℝ) 1)) :=
  (integrable_const (1 : ℝ)).indicator hs

theorem stepFn_integral {n : ℕ} (hn : 0 < n) (A : Finset ℤ)
    (hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n)) (hcard : A.card = n) :
    (∫ t in (-1 : ℝ)..1, stepFn n A t) = 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [intervalIntegral.integral_of_le (by norm_num)]
  unfold stepFn
  rw [integral_finsetSum A fun a _ => integrable_indicator_one _ (measurableSet_cell n a)]
  have : ∀ a ∈ A, ∫ t in Ioc (-1 : ℝ) 1, (cell n a).indicator (1 : ℝ → ℝ) t = 1 / (n : ℝ) := by
    intro a ha
    rw [integral_indicator_one (measurableSet_cell n a),
      measureReal_restrict_apply (measurableSet_cell n a),
      inter_eq_left.mpr (cell_subset hn (hA ha)), volume_real_cell n hn]
  rw [Finset.sum_congr rfl this, Finset.sum_const, hcard, nsmul_eq_mul]
  field_simp

theorem overlap_cells (n : ℕ) (hn : 0 < n) (a b : ℤ) (x : ℝ) :
    volume.real (cell n a ∩ Ioc (lo n b - x) (lo n b - x + 1 / n)) ≤
      max 0 (1 - |((b - a : ℤ) : ℝ) - n * x|) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [cell, Ioc_inter_Ioc, Real.volume_real_Ioc, min_add_add_right]
  set u := lo n a
  set v := lo n b - x
  have huv : u - v = -((((b - a : ℤ) : ℝ) - n * x) / n) := by
    simp only [u, v, lo]
    push_cast
    field_simp
    ring
  have key : min u v + 1 / n - max u v = (1 - |((b - a : ℤ) : ℝ) - n * x|) / n := by
    have h : max u v - min u v = |u - v| := max_sub_min_eq_abs' u v
    rw [huv, abs_neg, abs_div, abs_of_pos hn'] at h
    rw [sub_div, ← h]
    ring
  rw [key]
  exact max_le (div_le_div_of_nonneg_right (le_max_right _ _) hn'.le)
    (div_nonneg (le_max_left _ _) hn'.le)

theorem overlap_bound {n : ℕ} (hn : 0 < n) (A B : Finset ℤ)
    (hu : A ∪ B = Finset.Icc (1 : ℤ) (2 * n)) (x : ℝ) :
    (∫ t in (-1 : ℝ)..1, stepFn n A t *
        (Icc (-1 : ℝ) 1).indicator (fun y => 1 - stepFn n A y) (x + t)) ≤
      (∑ p ∈ A ×ˢ B, max 0 (1 - |((p.2 - p.1 : ℤ) : ℝ) - n * x|)) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set S : ℤ × ℤ → Set ℝ := fun p => cell n p.1 ∩ Ioc (lo n p.2 - x) (lo n p.2 - x + 1 / n)
    with hS
  have hSm : ∀ p, MeasurableSet (S p) := fun p => (measurableSet_cell n p.1).inter measurableSet_Ioc
  set G : ℝ → ℝ := fun t => (∑ p ∈ A ×ˢ B, (S p).indicator 1 t) +
    ({-1 - x} : Set ℝ).indicator 1 t with hG
  have hGnn : ∀ t, 0 ≤ G t := by
    intro t
    apply add_nonneg
    · exact Finset.sum_nonneg fun p _ => indicator_nonneg (fun _ _ => zero_le_one) _
    · exact indicator_nonneg (fun _ _ => zero_le_one) _
  have hFG : ∀ t, stepFn n A t *
      (Icc (-1 : ℝ) 1).indicator (fun y => 1 - stepFn n A y) (x + t) ≤ G t := by
    intro t
    rw [stepFn_eq hn A t]
    split_ifs with ha
    · rw [one_mul]
      by_cases hxt : x + t ∈ Icc (-1 : ℝ) 1
      · rw [indicator_of_mem hxt, stepFn_eq hn A (x + t)]
        split_ifs with hb
        · rw [sub_self]
          exact hGnn t
        · rw [sub_zero]
          rcases eq_or_lt_of_le hxt.1 with h | h
          · have ht : t = -1 - x := by linarith
            have : ({-1 - x} : Set ℝ).indicator (1 : ℝ → ℝ) t = 1 := by
              rw [indicator_of_mem (by simp [ht]), Pi.one_apply]
            have h0 : 0 ≤ ∑ p ∈ A ×ˢ B, (S p).indicator (1 : ℝ → ℝ) t :=
              Finset.sum_nonneg fun p _ => indicator_nonneg (fun _ _ => zero_le_one) _
            simp only [hG]
            linarith
          · set b := ⌈(n : ℝ) * (x + t + 1)⌉ with hbdef
            have hbI : b ∈ Finset.Icc (1 : ℤ) (2 * n) := by
              rw [Finset.mem_Icc]
              constructor
              · rw [Int.one_le_ceil_iff]
                have : 0 < x + t + 1 := by linarith
                positivity
              · rw [Int.ceil_le]
                push_cast
                have := hxt.2
                nlinarith
            have hbB : b ∈ B := by
              rw [← hu, Finset.mem_union] at hbI
              exact hbI.resolve_left hb
            set a := ⌈(n : ℝ) * (t + 1)⌉ with hadef
            have hmem : (a, b) ∈ A ×ˢ B := Finset.mem_product.mpr ⟨ha, hbB⟩
            have htS : t ∈ S (a, b) := by
              refine ⟨(mem_cell hn a t).mpr rfl, ?_⟩
              have h2 := (mem_cell hn b (x + t)).mpr rfl
              rw [cell, mem_Ioc] at h2
              rw [mem_Ioc]
              constructor <;> linarith [h2.1, h2.2]
            have h1 : (1 : ℝ) ≤ ∑ p ∈ A ×ˢ B, (S p).indicator (1 : ℝ → ℝ) t := by
              have := Finset.single_le_sum (f := fun p => (S p).indicator (1 : ℝ → ℝ) t)
                (fun p _ => indicator_nonneg (fun _ _ => zero_le_one) _) hmem
              rw [indicator_of_mem htS, Pi.one_apply] at this
              exact this
            have h0 : 0 ≤ ({-1 - x} : Set ℝ).indicator (1 : ℝ → ℝ) t :=
              indicator_nonneg (fun _ _ => zero_le_one) _
            simp only [hG]
            linarith
      · rw [indicator_of_notMem hxt]
        exact hGnn t
    · rw [zero_mul]
      exact hGnn t
  have hFnn : ∀ t, 0 ≤ stepFn n A t *
      (Icc (-1 : ℝ) 1).indicator (fun y => 1 - stepFn n A y) (x + t) := by
    intro t
    apply mul_nonneg (stepFn_bounds hn A t).1
    apply indicator_nonneg
    intro y _
    linarith [(stepFn_bounds hn A y).2]
  have hGi : Integrable G (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    apply Integrable.add
    · exact integrable_finsetSum _ fun p _ => integrable_indicator_one _ (hSm p)
    · exact integrable_indicator_one _ (measurableSet_singleton _)
  rw [intervalIntegral.integral_of_le (by norm_num)]
  calc _ ≤ ∫ t in Ioc (-1 : ℝ) 1, G t :=
        integral_mono_of_nonneg (ae_of_all _ hFnn) hGi (ae_of_all _ hFG)
    _ = (∑ p ∈ A ×ˢ B, (volume.restrict (Ioc (-1 : ℝ) 1)).real (S p)) +
          (volume.restrict (Ioc (-1 : ℝ) 1)).real {-1 - x} := by
        simp only [hG]
        rw [integral_add (integrable_finsetSum _ fun p _ => integrable_indicator_one _ (hSm p))
          (integrable_indicator_one _ (measurableSet_singleton _)),
          integral_finsetSum (A ×ˢ B) fun p _ => integrable_indicator_one _ (hSm p),
          integral_indicator_one (measurableSet_singleton _)]
        congr 1
        exact Finset.sum_congr rfl fun p _ => integral_indicator_one (hSm p)
    _ ≤ (∑ p ∈ A ×ˢ B, max 0 (1 - |((p.2 - p.1 : ℤ) : ℝ) - n * x|) / n) + 0 := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro p _
          rw [measureReal_restrict_apply (hSm p)]
          exact (measureReal_mono inter_subset_left
            ((measure_mono inter_subset_right).trans_lt measure_Ioc_lt_top).ne).trans
            (overlap_cells n hn p.1 p.2 x)
        · rw [measureReal_restrict_apply (measurableSet_singleton _)]
          exact (measureReal_mono inter_subset_left (by simp)).trans
            (le_of_eq (by simp [measureReal_def]))
    _ = _ := by rw [add_zero, Finset.sum_div]

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1.H3 := by
  intro n hn A B hd hu hc
  have hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n) := hu ▸ Finset.subset_union_left
  have hcard : A.card = n := by
    have h1 : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hd
    rw [hu, Int.card_Icc] at h1
    omega
  exact ⟨stepFn n A, stepFn_measurable n A, stepFn_bounds hn A, stepFn_integral hn A hA hcard,
    overlap_bound hn A B hu⟩
