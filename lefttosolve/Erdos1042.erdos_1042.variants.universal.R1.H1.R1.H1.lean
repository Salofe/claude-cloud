import OMAReductions.R_Erdos1042_erdos_1042_variants_universal_R1_H1_R1
import Mathlib

/-!
# Step H1 of the reduction Erdos1042.erdos_1042.variants.universal.R1.H1.R1

The hypotheses of H1 are contradictory, so the step holds vacuously: a set `G` contained in
`[0,a] ∪ [b,4]` with `0 < a < b < 4` has transfinite diameter strictly smaller than one.

Construction. Write `x = 2 + 2 cos θ` on `[0,4]`. The shifted Chebyshev polynomials
`P(x) = C_{m+1}(x-2)` and `S(x) = S_m(x-2)` satisfy the Pell identity
`P^2 + x (4-x) S^2 = 4`. Choose `m` so that a node `x* = 2 + 2 cos θ*` with
`sin((m+1) θ*) = 0` lies in the gap `(a,b)`, at distance at least `h` from `[0,a] ∪ [b,4]`.
Then `W = x (x-4) S / (x - x*)` is a monic polynomial of degree `m+1`, and by Cauchy–Schwarz
the monic polynomial `T = (1-ε) P + ε W` with `ε = h^2/(h^2+4)` satisfies
`T^2 ≤ 4 (1-ε)` on `[0,a] ∪ [b,4]`. Composing with a Chebyshev polynomial gives a monic
polynomial `Q` of degree `k ≥ 1` with `|Q| ≤ ρ < 1` there.

Estimate. For points `z_1, …, z_n` of `G`, the Vandermonde determinant equals the
determinant of `(P_j(z_i))` for the monic polynomials `P_j = Q^(j/k) X^(j%k)`, which is at most
`n! ∏_j 4^k ρ^(j/k)`. Taking the root of order `n choose 2` gives
`nthDiameter G n ≤ ((4^k/ρ) n)^(2/(n-1)) ρ^(1/k) → ρ^(1/k) < 1`.

Only the upstream definitions `Erdos1042.nthDiameter` and `Erdos1042.transfiniteDiameter` are
used, together with Mathlib.
-/

open Polynomial Set Filter
open scoped Topology ENNReal

namespace OMA.Helpers

/-- Degree and monicity along the three-term recursion `p (m+2) = X * p (m+1) - p m`. -/
theorem rec_monic (p : ℕ → ℝ[X]) (h0 : (p 0).natDegree = 0) (h1 : p 1 = X)
    (hrec : ∀ m, p (m + 2) = X * p (m + 1) - p m) :
    ∀ m, (p (m + 1)).Monic ∧ (p (m + 1)).natDegree = m + 1 ∧ (p m).natDegree = m := by
  intro m
  induction m with
  | zero => exact ⟨by rw [h1]; exact monic_X, by rw [h1, natDegree_X], h0⟩
  | succ m ih =>
    obtain ⟨hm, hd, hd0⟩ := ih
    have hXm : (X * p (m + 1)).Monic := monic_X.mul hm
    have hXd : (X * p (m + 1)).natDegree = m + 2 := by
      rw [monic_X.natDegree_mul hm, natDegree_X, hd]; ring
    have hlt : (p m).natDegree < (X * p (m + 1)).natDegree := by
      omega
    show (p (m + 2)).Monic ∧ (p (m + 2)).natDegree = m + 2 ∧ (p (m + 1)).natDegree = m + 1
    rw [hrec m]
    exact ⟨hXm.sub_of_left (degree_lt_degree hlt),
      by rw [natDegree_sub_eq_left_of_natDegree_lt hlt, hXd], hd⟩

theorem chebC_monic (m : ℕ) :
    (Polynomial.Chebyshev.C ℝ ((m + 1 : ℕ) : ℤ)).Monic ∧
      (Polynomial.Chebyshev.C ℝ ((m + 1 : ℕ) : ℤ)).natDegree = m + 1 := by
  have h := rec_monic (fun j : ℕ => Polynomial.Chebyshev.C ℝ (j : ℤ))
    (by simp [Polynomial.Chebyshev.C_zero])
    (by simp [Polynomial.Chebyshev.C_one])
    (fun j => by
      have := Polynomial.Chebyshev.C_add_two ℝ (j : ℤ)
      push_cast
      exact this) m
  exact ⟨h.1, h.2.1⟩

theorem chebS_monic (m : ℕ) :
    (Polynomial.Chebyshev.S ℝ (m : ℤ)).Monic ∧
      (Polynomial.Chebyshev.S ℝ (m : ℤ)).natDegree = m := by
  cases m with
  | zero => simp [Polynomial.Chebyshev.S_zero]
  | succ m =>
    have h := rec_monic (fun j : ℕ => Polynomial.Chebyshev.S ℝ (j : ℤ))
      (by simp [Polynomial.Chebyshev.S_zero])
      (by simp [Polynomial.Chebyshev.S_one])
      (fun j => by
        have := Polynomial.Chebyshev.S_add_two ℝ (j : ℤ)
        push_cast
        exact this) m
    exact ⟨h.1, h.2.1⟩

/-- The Pell identity for the rescaled Chebyshev polynomials on `[0,4]`. -/
theorem cheb_pell (m : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx4 : x ≤ 4) :
    ((Polynomial.Chebyshev.C ℝ ((m + 1 : ℕ) : ℤ)).eval (x - 2)) ^ 2 +
      (x * (4 - x)) * ((Polynomial.Chebyshev.S ℝ (m : ℤ)).eval (x - 2)) ^ 2 = 4 := by
  set θ := Real.arccos ((x - 2) / 2)
  have hc : Real.cos θ = (x - 2) / 2 := Real.cos_arccos (by linarith) (by linarith)
  have hx2 : x - 2 = 2 * Real.cos θ := by rw [hc]; ring
  have hu : x * (4 - x) = 4 * Real.sin θ ^ 2 := by
    have := Real.sin_sq_add_cos_sq θ
    rw [hc] at this
    nlinarith
  have hC := Polynomial.Chebyshev.C_two_mul_real_cos θ ((m + 1 : ℕ) : ℤ)
  have hS := Polynomial.Chebyshev.S_two_mul_real_cos θ (m : ℤ)
  push_cast at hC hS ⊢
  rw [hu, hx2, hC]
  have key : 4 * Real.sin θ ^ 2 * ((Polynomial.Chebyshev.S ℝ (m : ℤ)).eval (2 * Real.cos θ)) ^ 2
      = 4 * (Real.sin (((m : ℝ) + 1) * θ)) ^ 2 := by rw [← hS]; ring
  rw [key]
  have := Real.sin_sq_add_cos_sq (((m : ℝ) + 1) * θ)
  linear_combination 4 * this

/-- A node of the Chebyshev polynomial inside the gap. -/
theorem node_exists {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 4) :
    ∃ m : ℕ, ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi ∧ Real.sin (((m : ℝ) + 1) * θ) = 0 ∧
      a < 2 + 2 * Real.cos θ ∧ 2 + 2 * Real.cos θ < b := by
  set α := Real.arccos ((b - 2) / 2)
  set β := Real.arccos ((a - 2) / 2)
  have hαβ : α < β := Real.arccos_lt_arccos (by linarith) (by linarith) (by linarith)
  have hα0 : 0 ≤ α := Real.arccos_nonneg _
  have hβπ : β ≤ Real.pi := Real.arccos_le_pi _
  have hcα : Real.cos α = (b - 2) / 2 := Real.cos_arccos (by linarith) (by linarith)
  have hcβ : Real.cos β = (a - 2) / 2 := Real.cos_arccos (by linarith) (by linarith)
  obtain ⟨m, hm⟩ := exists_nat_gt (Real.pi / (β - α))
  set N : ℝ := (m : ℝ) + 1 with hNdef
  have hN : 0 < N := by positivity
  have hpi := Real.pi_pos
  have hstep : Real.pi / N < β - α := by
    rw [div_lt_iff₀ hN]
    rw [div_lt_iff₀ (by linarith)] at hm
    nlinarith
  set y : ℝ := α * N / Real.pi
  have hy0 : 0 ≤ y := by positivity
  set k : ℕ := ⌊y⌋₊ + 1
  have hk1 : y < k := by
    have := Nat.lt_floor_add_one y
    simp only [k]; push_cast; linarith
  have hk2 : (k : ℝ) ≤ y + 1 := by
    have := Nat.floor_le hy0
    simp only [k]; push_cast; linarith
  have hθ1 : α < k * Real.pi / N := by
    rw [lt_div_iff₀ hN]
    have : α * N = y * Real.pi := by simp only [y]; field_simp
    rw [this]; nlinarith
  have hθ2 : k * Real.pi / N < β := by
    have h1 : k * Real.pi / N ≤ α + Real.pi / N := by
      rw [div_le_iff₀ hN, add_mul, div_mul_cancel₀ _ hN.ne']
      have : α * N = y * Real.pi := by simp only [y]; field_simp
      rw [this]; nlinarith
    linarith
  refine ⟨m, k * Real.pi / N, by linarith, by linarith, ?_, ?_, ?_⟩
  · have : ((m : ℝ) + 1) * (k * Real.pi / N) = (k : ℕ) * Real.pi := by
      rw [← hNdef]; field_simp
    rw [this]; exact Real.sin_nat_mul_pi k
  · have := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) hβπ hθ2
    linarith
  · have := Real.cos_lt_cos_of_nonneg_of_le_pi hα0 (by linarith) hθ1
    linarith


/-- The Chebyshev bound on `[-2,2]`. -/
theorem chebC_abs_le (M : ℤ) (y : ℝ) (hy : |y| ≤ 2) :
    |(Polynomial.Chebyshev.C ℝ M).eval y| ≤ 2 := by
  obtain ⟨h1, h2⟩ := abs_le.mp hy
  set φ := Real.arccos (y / 2)
  have hc : Real.cos φ = y / 2 := Real.cos_arccos (by linarith) (by linarith)
  have hy2 : y = 2 * Real.cos φ := by rw [hc]; ring
  rw [hy2, Polynomial.Chebyshev.C_two_mul_real_cos, abs_mul, abs_two]
  have := Real.abs_cos_le_one ((M : ℝ) * φ)
  linarith

/-- A monic real polynomial of positive degree which is smaller than one in absolute value on
`[0,a] ∪ [b,4]`. -/
theorem good_poly {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 4) :
    ∃ (k : ℕ) (Q : ℝ[X]) (ρ : ℝ), 0 < k ∧ Q.Monic ∧ Q.natDegree = k ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ x : ℝ, (x ∈ Icc 0 a ∨ x ∈ Icc b 4) → |Q.eval x| ≤ ρ := by
  obtain ⟨m, θ, hθ0, hθπ, hsin, hxa, hxb⟩ := node_exists ha hab hb
  set xs := 2 + 2 * Real.cos θ with hxs
  set Pn : ℝ[X] := (Polynomial.Chebyshev.C ℝ ((m + 1 : ℕ) : ℤ)).comp (X - Polynomial.C 2)
  set Sp : ℝ[X] := (Polynomial.Chebyshev.S ℝ (m : ℤ)).comp (X - Polynomial.C 2)
  set ω : ℝ[X] := X * (X - Polynomial.C 4) * Sp
  have hX2 : (X - Polynomial.C (2:ℝ)).Monic ∧ (X - Polynomial.C (2:ℝ)).natDegree = 1 :=
    ⟨monic_X_sub_C 2, natDegree_X_sub_C 2⟩
  have hPn : Pn.Monic ∧ Pn.natDegree = m + 1 := by
    obtain ⟨h1, h2⟩ := chebC_monic m
    exact ⟨h1.comp hX2.1 (by rw [hX2.2]; norm_num), by rw [natDegree_comp, h2, hX2.2, mul_one]⟩
  have hSp : Sp.Monic ∧ Sp.natDegree = m := by
    obtain ⟨h1, h2⟩ := chebS_monic m
    exact ⟨h1.comp hX2.1 (by rw [hX2.2]; norm_num), by rw [natDegree_comp, h2, hX2.2, mul_one]⟩
  have hω : ω.Monic ∧ ω.natDegree = m + 2 := by
    have h1 : (X * (X - Polynomial.C (4:ℝ))).Monic := monic_X.mul (monic_X_sub_C 4)
    refine ⟨h1.mul hSp.1, ?_⟩
    rw [h1.natDegree_mul hSp.1, monic_X.natDegree_mul (monic_X_sub_C 4), natDegree_X,
      natDegree_X_sub_C, hSp.2]
    ring
  have hSz : Sp.eval xs = 0 := by
    have hS := Polynomial.Chebyshev.S_two_mul_real_cos θ (m : ℤ)
    push_cast at hS
    rw [hsin] at hS
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
    simp only [Sp, eval_comp, eval_sub, eval_X, eval_C]
    have : xs - 2 = 2 * Real.cos θ := by rw [hxs]; ring
    rw [this]
    rcases mul_eq_zero.mp hS with h | h
    · exact h
    · exact absurd h hs.ne'
  have hroot : ω.IsRoot xs := by
    simp only [IsRoot, ω, eval_mul, hSz, mul_zero]
  set W : ℝ[X] := ω /ₘ (X - Polynomial.C xs)
  have hW : (X - Polynomial.C xs) * W = ω := mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hWm : W.Monic := (monic_X_sub_C xs).of_mul_monic_left (by rw [hW]; exact hω.1)
  have hWd : W.natDegree = m + 1 := by
    have := (monic_X_sub_C xs).natDegree_mul hWm
    rw [hW, hω.2, natDegree_X_sub_C] at this
    omega
  set h := min (xs - a) (b - xs)
  have hh : 0 < h := lt_min (by linarith) (by linarith)
  set ε := h ^ 2 / (h ^ 2 + 4)
  have hε0 : 0 < ε := by positivity
  have hε1 : ε < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hεe : ε * (h ^ 2 + 4) = h ^ 2 := by simp only [ε]; field_simp
  set T : ℝ[X] := Pn + Polynomial.C ε * (W - Pn)
  have hdeg : (Polynomial.C ε * (W - Pn)).degree < Pn.degree := by
    rw [degree_C_mul hε0.ne']
    have hd : W.degree = Pn.degree := by
      rw [degree_eq_natDegree hWm.ne_zero, degree_eq_natDegree hPn.1.ne_zero, hWd, hPn.2]
    have := degree_sub_lt_left hd hWm.ne_zero (by rw [hWm.leadingCoeff, hPn.1.leadingCoeff])
    rwa [hd] at this
  have hT : T.Monic ∧ T.natDegree = m + 1 :=
    ⟨hPn.1.add_of_left hdeg, by rw [natDegree_add_eq_left_of_degree_lt hdeg, hPn.2]⟩
  have hTb : ∀ x : ℝ, (x ∈ Icc 0 a ∨ x ∈ Icc b 4) → (T.eval x) ^ 2 ≤ 4 * (1 - ε) := by
    intro x hx
    have hx0 : 0 ≤ x := by rcases hx with hx | hx <;> linarith [hx.1, hx.2]
    have hx4 : x ≤ 4 := by rcases hx with hx | hx <;> linarith [hx.1, hx.2]
    have hd2 : h ^ 2 ≤ (x - xs) ^ 2 := by
      rcases hx with hx | hx
      · have : h ≤ xs - x := (min_le_left _ _).trans (by linarith [hx.2])
        nlinarith
      · have : h ≤ x - xs := (min_le_right _ _).trans (by linarith [hx.1])
        nlinarith
    have hpell := cheb_pell m x hx0 hx4
    have hWx : (x - xs) * W.eval x = x * (x - 4) * Sp.eval x := by
      have := congrArg (Polynomial.eval x) hW
      simpa [ω, eval_mul, eval_sub, eval_X, eval_C, mul_assoc] using this
    have hPx : Pn.eval x = (Polynomial.Chebyshev.C ℝ ((m + 1 : ℕ) : ℤ)).eval (x - 2) := by
      simp [Pn, eval_comp]
    have hSx : Sp.eval x = (Polynomial.Chebyshev.S ℝ (m : ℤ)).eval (x - 2) := by
      simp [Sp, eval_comp]
    have hTx : T.eval x = Pn.eval x + ε * (W.eval x - Pn.eval x) := by
      simp [T, eval_add, eval_mul, eval_sub, eval_C]
    rw [← hPx, ← hSx] at hpell
    have hu4 : x * (4 - x) ≤ 4 := by nlinarith [sq_nonneg (x - 2)]
    have hu0 : 0 ≤ x * (4 - x) := mul_nonneg hx0 (by linarith)
    have hWx' : (x - xs) * W.eval x = -(x * (4 - x) * Sp.eval x) := by rw [hWx]; ring
    rw [hTx]
    clear hWx hTx hPx hSx
    generalize Pn.eval x = P at hpell ⊢
    generalize Sp.eval x = S at hpell hWx' ⊢
    generalize W.eval x = Wv at hWx' ⊢
    generalize x - xs = d at hWx' hd2 ⊢
    generalize x * (4 - x) = u at hpell hWx' hu4 hu0 ⊢
    have e1 : d * (P + ε * (Wv - P)) = (1 - ε) * d * P - ε * u * S := by
      linear_combination ε * hWx'
    have e2 : ((1 - ε) ^ 2 * d ^ 2 + ε ^ 2 * u) * (P ^ 2 + u * S ^ 2) -
        (d * (P + ε * (Wv - P))) ^ 2 = u * ((1 - ε) * d * S + ε * P) ^ 2 := by rw [e1]; ring
    have e3 : (d * (P + ε * (Wv - P))) ^ 2 ≤ 4 * ((1 - ε) ^ 2 * d ^ 2 + ε ^ 2 * u) := by
      rw [hpell] at e2
      have := mul_nonneg hu0 (sq_nonneg ((1 - ε) * d * S + ε * P))
      linarith
    have h1 : (1 - ε) * (h ^ 2 + 4) = 4 := by linarith [hεe]
    have e5 : ε * u ≤ (1 - ε) * d ^ 2 := by
      have hA : (ε * u) * (h ^ 2 + 4) = h ^ 2 * u := by
        rw [mul_comm ε u, mul_assoc, hεe]; ring
      have hB : ((1 - ε) * d ^ 2) * (h ^ 2 + 4) = 4 * d ^ 2 := by
        rw [show ((1 - ε) * d ^ 2) * (h ^ 2 + 4) = d ^ 2 * ((1 - ε) * (h ^ 2 + 4)) by ring, h1]
        ring
      have hC : h ^ 2 * u ≤ h ^ 2 * 4 := mul_le_mul_of_nonneg_left hu4 (sq_nonneg h)
      have : (ε * u) * (h ^ 2 + 4) ≤ ((1 - ε) * d ^ 2) * (h ^ 2 + 4) := by
        rw [hA, hB]; linarith
      exact le_of_mul_le_mul_right this (by positivity)
    have e4 : (1 - ε) ^ 2 * d ^ 2 + ε ^ 2 * u ≤ (1 - ε) * d ^ 2 := by
      have := mul_le_mul_of_nonneg_left e5 hε0.le
      nlinarith
    have hdpos : 0 < d ^ 2 := lt_of_lt_of_le (by positivity) hd2
    have : d ^ 2 * (P + ε * (Wv - P)) ^ 2 ≤ d ^ 2 * (4 * (1 - ε)) := by
      have : d ^ 2 * (P + ε * (Wv - P)) ^ 2 = (d * (P + ε * (Wv - P))) ^ 2 := by ring
      rw [this]
      nlinarith
    exact le_of_mul_le_mul_left this hdpos
  set l := 1 - ε / 2 with hl
  have hl0 : 0 < l := by rw [hl]; linarith
  have hl1 : l < 1 := by rw [hl]; linarith
  have hTl : ∀ x, (x ∈ Icc 0 a ∨ x ∈ Icc b 4) → |1 / l * T.eval x| ≤ 2 := by
    intro x hx
    have h1 := hTb x hx
    have h2 : (T.eval x) ^ 2 ≤ (2 * l) ^ 2 := by rw [hl]; nlinarith
    have h3 : |T.eval x| ≤ 2 * l := by
      have := sq_le_sq.mp h2
      rwa [abs_of_pos (by linarith : 0 < 2 * l)] at this
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / l), one_div, inv_mul_le_iff₀ hl0]
    linarith
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (by norm_num : (0:ℝ) < 1 / 2) hl1
  have hM1 : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · rw [h0, pow_zero] at hM; norm_num at hM
    · exact h0
  obtain ⟨j, rfl⟩ : ∃ j, M = j + 1 := ⟨M - 1, by omega⟩
  set inner : ℝ[X] := Polynomial.C (1 / l) * T
  have hinner : inner.natDegree = m + 1 ∧ inner.leadingCoeff = 1 / l := by
    constructor
    · rw [natDegree_C_mul (by positivity), hT.2]
    · rw [leadingCoeff_mul, leadingCoeff_C, hT.1.leadingCoeff, mul_one]
  obtain ⟨hCm, hCd⟩ := chebC_monic j
  set Q : ℝ[X] := Polynomial.C (l ^ (j + 1)) *
    (Polynomial.Chebyshev.C ℝ ((j + 1 : ℕ) : ℤ)).comp inner
  refine ⟨(j + 1) * (m + 1), Q, 2 * l ^ (j + 1), by positivity, ?_, ?_, by positivity,
    by linarith, ?_⟩
  · show Q.leadingCoeff = 1
    rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_comp (by rw [hinner.1]; omega),
      hCm.leadingCoeff, hinner.2, hCd, one_mul, ← mul_pow, mul_one_div_cancel hl0.ne', one_pow]
  · rw [natDegree_C_mul (by positivity), natDegree_comp, hCd, hinner.1]
  · intro x hx
    have hev : Q.eval x = l ^ (j + 1) *
        (Polynomial.Chebyshev.C ℝ ((j + 1 : ℕ) : ℤ)).eval (1 / l * T.eval x) := by
      simp only [Q, inner, eval_mul, eval_C, eval_comp]
    rw [hev, abs_mul, abs_of_pos (by positivity)]
    have h5 := chebC_abs_le ((j + 1 : ℕ) : ℤ) _ (hTl x hx)
    have hp := pow_pos hl0 (j + 1)
    calc l ^ (j + 1) * |(Polynomial.Chebyshev.C ℝ ((j + 1 : ℕ) : ℤ)).eval (1 / l * T.eval x)|
        ≤ l ^ (j + 1) * 2 := mul_le_mul_of_nonneg_left h5 hp.le
      _ = 2 * l ^ (j + 1) := by ring


/-- The product of the mutual distances is the modulus of the Vandermonde determinant. -/
theorem edist_prod_vdm {n : ℕ} (z : Fin n → ℂ) :
    (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, edist (z i) (z j)) =
      ENNReal.ofReal ‖(Matrix.vandermonde z).det‖ := by
  rw [Matrix.det_vandermonde, norm_prod,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_prod, ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [edist_dist, dist_eq_norm, norm_sub_rev]

/-- Column-wise bound for a Vandermonde determinant through monic polynomials. -/
theorem vdm_bound {n : ℕ} {G : Set ℂ} (P : ℕ → ℂ[X])
    (hP : ∀ j, (P j).Monic ∧ (P j).natDegree = j)
    (B : ℕ → ℝ) (hB0 : ∀ j, 0 < B j) (hB : ∀ j, ∀ z ∈ G, ‖(P j).eval z‖ ≤ B j)
    (z : Fin n → ℂ) (hz : ∀ i, z i ∈ G) :
    ‖(Matrix.vandermonde z).det‖ ≤ n.factorial * ∏ j : Fin n, B j := by
  classical
  have hdet := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde z (fun j : Fin n => P j)
    (fun j => (hP j).2) (fun j => (hP j).1)
  let N : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i j => (P j).eval (z i) / (B j : ℂ))
  have hMN : (Matrix.of (fun i j : Fin n => (P j).eval (z i))) =
      Matrix.of (fun (i j : Fin n) => (B j : ℂ) * N i j) := by
    ext i j
    simp only [N, Matrix.of_apply]
    have : (B j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hB0 j).ne'
    field_simp
  rw [hdet, hMN, Matrix.det_mul_row]
  have hN : ∀ i j, (IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ)) (N i j) ≤ 1 := by
    intro i j
    change ‖(P j).eval (z i) / (B j : ℂ)‖ ≤ 1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hB0 j), div_le_one (hB0 j)]
    exact hB j (z i) (hz i)
  have hle := Matrix.det_le hN
  change ‖N.det‖ ≤ _ at hle
  simp only [Fintype.card_fin, one_pow, nsmul_eq_mul, mul_one] at hle
  rw [norm_mul, norm_prod]
  have hprod : ∏ j : Fin n, ‖(B j : ℂ)‖ = ∏ j : Fin n, B j := by
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hB0 j)]
  rw [hprod, mul_comm]
  exact mul_le_mul_of_nonneg_right hle (Finset.prod_nonneg fun j _ => (hB0 j).le)

/-- The root of `(c n)^n` of order `n choose 2` tends to one. -/
theorem root_lim (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => ((c * n) ^ n) ^ (1 / ((n.choose 2 : ℕ) : ℝ))) atTop (𝓝 1) := by
  have hscale : Tendsto (fun n : ℕ => c * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hlog : Tendsto (fun n : ℕ => Real.log (c * n) / ((n : ℝ) - 1)) atTop (𝓝 0) := by
    refine ((Real.tendsto_pow_log_div_mul_add_atTop (1 / c) (-1) 1
      (by positivity)).comp hscale).congr ?_
    intro n
    simp only [Function.comp_apply, pow_one]
    congr 1
    field_simp
    ring
  have hexp : Tendsto (fun n : ℕ => Real.exp (2 * (Real.log (c * n) / ((n : ℝ) - 1))))
      atTop (𝓝 1) := by
    have := hlog.const_mul 2
    rw [mul_zero] at this
    have h2 := (Real.continuous_exp.tendsto 0).comp this
    rw [Real.exp_zero] at h2
    exact h2
  refine hexp.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (c * n) ^ n := by positivity
  rw [Real.rpow_def_of_pos hpos, Real.log_pow, Nat.cast_choose_two]
  have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (n : ℝ) ≠ 0 := by linarith
  congr 1
  field_simp

/-- The key estimate: a compact part of `[0,a] ∪ [b,4]` has transfinite diameter below one. -/
theorem td_lt_one {G : Set ℂ} {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 4)
    (hsub : G ⊆ (Complex.ofReal '' Icc 0 a) ∪ (Complex.ofReal '' Icc b 4)) :
    Erdos1042.transfiniteDiameter G < 1 := by
  obtain ⟨k, Q, ρ, hk, hQm, hQd, hρ0, hρ1, hQb⟩ := good_poly ha hab hb
  set Qc : ℂ[X] := Q.map (algebraMap ℝ ℂ)
  have hQcm : Qc.Monic := hQm.map _
  have hQcd : Qc.natDegree = k := by rw [natDegree_map, hQd]
  have hpt : ∀ z ∈ G, ∃ x : ℝ, (x ∈ Icc 0 a ∨ x ∈ Icc b 4) ∧ z = x := by
    intro z hz
    rcases hsub hz with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · exact ⟨x, Or.inl hx, rfl⟩
    · exact ⟨x, Or.inr hx, rfl⟩
  set P : ℕ → ℂ[X] := fun j => Qc ^ (j / k) * X ^ (j % k)
  have hP : ∀ j, (P j).Monic ∧ (P j).natDegree = j := by
    intro j
    refine ⟨(hQcm.pow _).mul (monic_X_pow _), ?_⟩
    simp only [P]
    rw [(hQcm.pow _).natDegree_mul (monic_X_pow _), hQcm.natDegree_pow, natDegree_X_pow, hQcd]
    exact Nat.div_add_mod' j k
  set B : ℕ → ℝ := fun j => 4 ^ k * ρ ^ (j / k)
  have hB0 : ∀ j, 0 < B j := fun j => by positivity
  have hB : ∀ j, ∀ z ∈ G, ‖(P j).eval z‖ ≤ B j := by
    intro j z hz
    obtain ⟨x, hx, rfl⟩ := hpt z hz
    have hx0 : 0 ≤ x := by rcases hx with hx | hx <;> linarith [hx.1, hx.2]
    have hx4 : x ≤ 4 := by rcases hx with hx | hx <;> linarith [hx.1, hx.2]
    have hQx : Qc.eval (x : ℂ) = ((Q.eval x : ℝ) : ℂ) := by
      simp only [Qc, eval_map]
      exact eval₂_at_apply (algebraMap ℝ ℂ) x
    simp only [P, B, eval_mul, eval_pow, eval_X, norm_mul, norm_pow, hQx, Complex.norm_real,
      Real.norm_eq_abs]
    have h1 : |Q.eval x| ^ (j / k) ≤ ρ ^ (j / k) :=
      pow_le_pow_left₀ (abs_nonneg _) (hQb x hx) _
    have h2 : |x| ^ (j % k) ≤ 4 ^ k := by
      rw [abs_of_nonneg hx0]
      calc x ^ (j % k) ≤ 4 ^ (j % k) := pow_le_pow_left₀ hx0 hx4 _
        _ ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) (Nat.mod_lt j hk).le
    calc |Q.eval x| ^ (j / k) * |x| ^ (j % k) ≤ ρ ^ (j / k) * 4 ^ k :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 4 ^ k * ρ ^ (j / k) := by ring
  set c : ℝ := 4 ^ k / ρ
  have hc : 0 < c := by positivity
  have hnd : ∀ n : ℕ, 2 ≤ n → Erdos1042.nthDiameter G n ≤
      ENNReal.ofReal (((c * n) ^ n) ^ (1 / ((n.choose 2 : ℕ) : ℝ)) * ρ ^ (1 / (k : ℝ))) := by
    intro n hn
    unfold Erdos1042.nthDiameter
    refine iSup_le fun z => iSup_le fun hz => ?_
    have hDpos : 0 < n.choose 2 := Nat.choose_pos hn
    have hD : (0:ℝ) < ((n.choose 2 : ℕ) : ℝ) := by exact_mod_cast hDpos
    rw [edist_prod_vdm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hdet := vdm_bound P hP B hB0 hB z hz
    set D : ℕ := n.choose 2
    have hsum : D ≤ k * (∑ j : Fin n, (j : ℕ) / k) + n * k := by
      have hgauss : ∑ j : Fin n, (j : ℕ) = D := by
        rw [Fin.sum_univ_eq_sum_range (fun j => j) n, Finset.sum_range_id]
        exact (Nat.choose_two_right n).symm
      have hle : ∀ j : Fin n, (j : ℕ) ≤ k * ((j : ℕ) / k) + k := by
        intro j
        have := Nat.lt_div_mul_add (a := (j : ℕ)) hk
        rw [mul_comm k]
        omega
      calc D = ∑ j : Fin n, (j : ℕ) := hgauss.symm
        _ ≤ ∑ j : Fin n, (k * ((j : ℕ) / k) + k) := Finset.sum_le_sum fun j _ => hle j
        _ = k * (∑ j : Fin n, (j : ℕ) / k) + n * k := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          simp
    set Sm : ℕ := ∑ j : Fin n, (j : ℕ) / k
    have hkR : (0:ℝ) < k := by exact_mod_cast hk
    have hSm : (D : ℝ) / k - n ≤ (Sm : ℝ) := by
      have : (D : ℝ) ≤ k * Sm + n * k := by exact_mod_cast hsum
      rw [div_sub' hkR.ne', div_le_iff₀ hkR]
      linarith
    have hprod : ∏ j : Fin n, B j = 4 ^ (k * n) * ρ ^ Sm := by
      simp only [B, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, Finset.prod_pow_eq_pow_sum, Sm, pow_mul]
    have hρS : ρ ^ Sm ≤ ρ ^ ((D : ℝ) / k) / ρ ^ n := by
      rw [← Real.rpow_natCast ρ Sm, ← Real.rpow_natCast ρ n, ← Real.rpow_sub hρ0]
      exact Real.rpow_le_rpow_of_exponent_ge hρ0 hρ1.le hSm
    have hfac : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have key : (n.factorial : ℝ) * ∏ j : Fin n, B j ≤ (c * n) ^ n * ρ ^ ((D : ℝ) / k) := by
      rw [hprod]
      calc (n.factorial : ℝ) * (4 ^ (k * n) * ρ ^ Sm)
          ≤ (n : ℝ) ^ n * (4 ^ (k * n) * (ρ ^ ((D : ℝ) / k) / ρ ^ n)) := by
            apply mul_le_mul hfac _ (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left hρS (by positivity)
        _ = (c * n) ^ n * ρ ^ ((D : ℝ) / k) := by
            simp only [c]
            rw [mul_pow, div_pow, ← pow_mul]
            field_simp
    calc ‖(Matrix.vandermonde z).det‖ ^ (1 / (D : ℝ))
        ≤ ((c * n) ^ n * ρ ^ ((D : ℝ) / k)) ^ (1 / (D : ℝ)) :=
          Real.rpow_le_rpow (norm_nonneg _) (hdet.trans key) (by positivity)
      _ = ((c * n) ^ n) ^ (1 / (D : ℝ)) * ρ ^ (1 / (k : ℝ)) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hρ0.le]
          congr 2
          field_simp
  set r : ℝ := ρ ^ (1 / (k : ℝ))
  have hr1 : r < 1 := Real.rpow_lt_one hρ0.le hρ1 (by positivity)
  have hg : Tendsto (fun n : ℕ => ENNReal.ofReal (((c * n) ^ n) ^
      (1 / ((n.choose 2 : ℕ) : ℝ)) * r)) atTop (𝓝 (ENNReal.ofReal r)) := by
    have := (root_lim c hc).mul_const r
    rw [one_mul] at this
    exact (ENNReal.continuous_ofReal.tendsto r).comp this
  have hle : Erdos1042.transfiniteDiameter G ≤ ENNReal.ofReal r := by
    unfold Erdos1042.transfiniteDiameter
    rw [← hg.limsup_eq]
    exact limsup_le_limsup ((eventually_ge_atTop 2).mono fun n hn => hnd n hn)
  calc Erdos1042.transfiniteDiameter G ≤ ENNReal.ofReal r := hle
    _ < 1 := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hr1

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos1042_erdos_1042_variants_universal_R1_H1_R1.H1 := by
  intro G r _ hcap _ _ a b ha hab hb hsub _ _
  exfalso
  have h := OMA.Helpers.td_lt_one ha hab hb hsub
  rw [hcap] at h
  exact lt_irrefl _ h
