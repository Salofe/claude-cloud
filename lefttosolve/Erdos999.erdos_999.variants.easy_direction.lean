import FormalConjectures.ErdosProblems.«999»

/-!
Easy direction of the Duffin–Schaeffer conjecture (Erdős Problem 999), via Borel–Cantelli.

Suppose `a q := φ(q) f(q) / q` were summable. Let `E q` be the set of `x` with
`|x - p/q| < f(q)/q` for some `p` coprime to `q` (empty for `q = 0`), so that `x` is approximable
iff `x ∈ E q` for infinitely many `q`. Work with Lebesgue measure restricted to `[0, 1]`.

For `q ≥ 1` we have `vol (E q ∩ [0, 1]) ≤ 6 a q`:
* if `a q ≥ 1` this is trivial, since `vol [0, 1] = 1`;
* otherwise `f(q)/q ≤ a q < 1` (as `φ(q) ≥ 1`), so a point `x ∈ [0, 1]` of `E q` is within
  `f(q)/q` of `p/q` with `-q < p < 2q`. Writing `p = q k + m` with `0 ≤ m < q`, `m` is coprime to `q`
  and `k ∈ {-1, 0, 1}`. Hence `E q ∩ [0, 1]` is covered by `3 φ(q)` balls of radius `f(q)/q`.

So `∑ vol (E q ∩ [0, 1]) < ∞`, and by Borel–Cantelli almost every `x ∈ [0, 1]` lies in only finitely
many `E q`, i.e. is not approximable. Together with the hypothesis (approximable almost everywhere)
this forces `vol [0, 1] = 0`, a contradiction.
-/

open MeasureTheory Filter

namespace OMA.Helpers

/-- The approximation set for denominator `q`. -/
def E (f : ℕ → ℝ) (q : ℕ) : Set ℝ :=
  {x | 0 < q ∧ ∃ p : ℤ, Int.gcd p q = 1 ∧ |x - p / q| < f q / q}

theorem approx_iff (f : ℕ → ℝ) (x : ℝ) :
    Erdos999.IsApproximable f x ↔ {q | x ∈ E f q}.Infinite := Iff.rfl

/-- Covering of `E q ∩ [0, 1]` by `3 φ(q)` balls when `f q ≤ q`. -/
theorem E_subset (f : ℕ → ℝ) (q : ℕ) (hq : 0 < q) (hfq : f q ≤ q) :
    E f q ∩ Set.Icc 0 1 ⊆ ⋃ m ∈ (Finset.range q).filter (Nat.Coprime q),
      ⋃ k ∈ Finset.Icc (-1 : ℤ) 1, Metric.ball (((m : ℝ) + k * q) / q) (f q / q) := by
  rintro x ⟨⟨-, p, hp, hx⟩, hx0, hx1⟩
  have hqpos : (0:ℝ) < q := by exact_mod_cast hq
  have hqz : (0:ℤ) < q := by exact_mod_cast hq
  set r := p % (q:ℤ) with hr
  set k := p / (q:ℤ) with hk
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hqz.ne'
  have hrq : r < q := Int.emod_lt_of_pos _ hqz
  have hpkr : (q:ℤ) * k + r = p := Int.mul_ediv_add_emod p q
  have hrad : f q / q ≤ 1 := by rw [div_le_one hqpos]; exact hfq
  have habs := abs_lt.mp (lt_of_lt_of_le hx hrad)
  have hp1 : (p:ℝ) < 2 * q := by
    have : (p:ℝ) / q < 2 := by linarith [habs.1]
    rwa [div_lt_iff₀ hqpos] at this
  have hp2 : -(q:ℝ) < p := by
    have : -1 < (p:ℝ) / q := by linarith [habs.2]
    rwa [lt_div_iff₀ hqpos, neg_one_mul] at this
  have hp1' : p < 2 * q := by exact_mod_cast hp1
  have hp2' : -(q:ℤ) < p := by exact_mod_cast hp2
  have hk1 : -1 ≤ k := by nlinarith
  have hk2 : k ≤ 1 := by nlinarith
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, exists_prop]
  refine ⟨r.toNat, ⟨?_, ?_⟩, k, ⟨hk1, hk2⟩, ?_⟩
  · omega
  · have hg : Int.gcd r q = 1 := by rw [hr, Int.gcd_emod]; exact hp
    have h' : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg hr0
    rw [Nat.Coprime, Nat.gcd_comm]
    rw [← h', Int.gcd_natCast_natCast] at hg
    exact hg
  · rw [Metric.mem_ball, Real.dist_eq]
    have h' : ((r.toNat : ℕ) : ℝ) = (r : ℝ) := by
      have h := Int.toNat_of_nonneg hr0
      exact_mod_cast h
    rw [h']
    have hp' : (p:ℝ) = q * k + r := by exact_mod_cast hpkr.symm
    rw [hp'] at hx
    have h3 : ((r:ℝ) + k * q) = q * k + r := by ring
    rw [h3]
    exact hx

/-- `vol (E q ∩ [0, 1]) ≤ 6 φ(q) f(q) / q` for every `q`. -/
theorem vol_le (f : ℕ → ℝ) (hf : ∀ q, 0 ≤ f q) (q : ℕ) :
    volume (E f q ∩ Set.Icc 0 1) ≤ ENNReal.ofReal (6 * ((Nat.totient q : ℝ) * f q / q)) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have h0 : E f 0 = ∅ := by
      ext x; simp [E]
    simp [h0]
  by_cases ha : 1 ≤ (Nat.totient q : ℝ) * f q / q
  · calc volume (E f q ∩ Set.Icc 0 1) ≤ volume (Set.Icc (0:ℝ) 1) :=
          measure_mono Set.inter_subset_right
      _ = 1 := by simp [Real.volume_Icc]
      _ ≤ ENNReal.ofReal (6 * ((Nat.totient q : ℝ) * f q / q)) := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        linarith
  · rw [not_le] at ha
    have hqpos : (0:ℝ) < q := by exact_mod_cast hq
    have htot : (1:ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
    have hfq : f q ≤ q := by
      have h1 : f q / q ≤ (Nat.totient q : ℝ) * f q / q := by
        apply div_le_div_of_nonneg_right _ hqpos.le
        nlinarith [hf q]
      have h2 : f q / q < 1 := lt_of_le_of_lt h1 ha
      rw [div_lt_one hqpos] at h2
      exact h2.le
    calc volume (E f q ∩ Set.Icc 0 1)
        ≤ volume (⋃ m ∈ (Finset.range q).filter (Nat.Coprime q),
            ⋃ k ∈ Finset.Icc (-1 : ℤ) 1, Metric.ball (((m : ℝ) + k * q) / q) (f q / q)) :=
          measure_mono (E_subset f q hq hfq)
      _ ≤ ∑ m ∈ (Finset.range q).filter (Nat.Coprime q), ∑ k ∈ Finset.Icc (-1 : ℤ) 1,
            volume (Metric.ball (((m : ℝ) + k * q) / q) (f q / q)) := by
          refine (measure_biUnion_finset_le _ _).trans ?_
          gcongr with m hm
          exact measure_biUnion_finset_le _ _
      _ = ∑ m ∈ (Finset.range q).filter (Nat.Coprime q), ∑ k ∈ Finset.Icc (-1 : ℤ) 1,
            ENNReal.ofReal (2 * (f q / q)) := by
          simp only [Real.volume_ball]
      _ = ENNReal.ofReal (6 * ((Nat.totient q : ℝ) * f q / q)) := by
          rw [Finset.sum_const, Finset.sum_const, ← Nat.totient_eq_card_coprime]
          have hc : (Finset.Icc (-1 : ℤ) 1).card = 3 := by rfl
          rw [hc, nsmul_eq_mul, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          push_cast
          ring

end OMA.Helpers

theorem OMA.solution : type_of% @Erdos999.erdos_999.variants.easy_direction := by
  intro f hf h hsum
  set μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1) with hμ
  have hE : ∑' q, μ (OMA.Helpers.E f q) ≠ ⊤ := by
    have h1 : ∀ q, μ (OMA.Helpers.E f q) ≤
        ENNReal.ofReal (6 * ((Nat.totient q : ℝ) * f q / q)) := by
      intro q
      rw [hμ, Measure.restrict_apply' measurableSet_Icc]
      exact OMA.Helpers.vol_le f hf q
    have h2 : ∑' q, ENNReal.ofReal (6 * ((Nat.totient q : ℝ) * f q / q)) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg]
      · exact ENNReal.ofReal_ne_top
      · intro q
        have := hf q
        positivity
      · exact hsum.mul_left 6
    exact ne_top_of_le_ne_top h2 (ENNReal.tsum_le_tsum h1)
  have h1 : ∀ᵐ x ∂μ, ∀ᶠ q in atTop, x ∉ OMA.Helpers.E f q := ae_eventually_notMem hE
  have h2 : ∀ᵐ x ∂μ, Erdos999.IsApproximable f x := ae_restrict_of_ae h
  have h3 : ∀ᵐ x ∂μ, False := by
    filter_upwards [h1, h2] with x hx1 hx2
    rw [OMA.Helpers.approx_iff, ← Nat.frequently_atTop_iff_infinite] at hx2
    exact hx2 hx1
  rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot, hμ, Measure.restrict_eq_zero,
    Real.volume_Icc] at h3
  norm_num at h3
