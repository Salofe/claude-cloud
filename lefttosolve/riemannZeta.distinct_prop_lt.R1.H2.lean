import OMAReductions.R_riemannZeta_distinct_prop_lt_R1
import Mathlib

/-!
# Step H2 of the reduction riemannZeta.distinct_prop_lt.R1

The finite packing problem for the Montgomery-Taylor kernel
`K x = (sinc (pi x - c) + sinc (pi x + c)) / (2 sinc c)` with `c = 1 / sqrt 2`.

Mathematics.
* Zeros of `K`. For `u = pi x > 0`, `sinc (u - c) + sinc (u + c) = 0` forces
  `u sin u cos c = c cos u sin c` (the case `u = c` is impossible), hence `cos u` is nonzero and
  `tan u = k / u` with `k = c tan c > 0`.
* No three zeros `s, t, s + t` with `s, t > 0`: reduce `pi s` and `pi t` modulo `pi` to
  `alpha, beta` in `(0, pi / 2)` (the tangent is positive). If `alpha + beta < pi / 2`, strict
  monotonicity of `tan` gives `k / (u + v) > k / u`, impossible; otherwise `tan (alpha + beta)`
  is at most zero, impossible as well. Since `K 0 = 1`, the continuous function
  `K s ^ 2 + K t ^ 2 + K (s + t) ^ 2` is positive on the compact square `[0, 100] ^ 2`, so it has
  a positive minimum `beta` there.
* Packing. Sort `Y` increasingly and cut it into consecutive triples. Their diameters add up to
  at most the length `4 |Y|` of the interval, so at most `|Y| / 25` of them have diameter above
  100. The remaining triples are disjoint, have diameter at most 100 and each contributes at
  least `beta`, which gives the bound with `b = beta / 400` once `|Y| >= 10`.

Only upstream definitions are used, together with Mathlib.
-/

namespace OMA.Helpers
noncomputable def Kf (x : ℝ) : ℝ :=
  (Real.sinc (Real.pi * x - 1 / Real.sqrt 2) + Real.sinc (Real.pi * x + 1 / Real.sqrt 2)) /
      (2 * Real.sinc (1 / Real.sqrt 2))

lemma c_pos : 0 < 1 / Real.sqrt 2 := by positivity

lemma c_lt_one : 1 / Real.sqrt 2 < 1 := by
  have hs : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [div_lt_one (by positivity)]
  exact hs

lemma sin_c_pos : 0 < Real.sin (1 / Real.sqrt 2) :=
  Real.sin_pos_of_pos_of_lt_pi c_pos (by linarith [c_lt_one, Real.pi_gt_three])

lemma cos_c_pos : 0 < Real.cos (1 / Real.sqrt 2) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [c_pos, Real.pi_gt_three],
    by linarith [c_lt_one, Real.pi_gt_three]⟩

lemma sinc_c_pos : 0 < Real.sinc (1 / Real.sqrt 2) := by
  rw [Real.sinc_of_ne_zero c_pos.ne']
  exact div_pos sin_c_pos c_pos

lemma Kf_neg (x : ℝ) : Kf (-x) = Kf x := by
  unfold Kf
  rw [show Real.pi * -x - 1 / Real.sqrt 2 = -(Real.pi * x + 1 / Real.sqrt 2) by ring,
    show Real.pi * -x + 1 / Real.sqrt 2 = -(Real.pi * x - 1 / Real.sqrt 2) by ring,
    Real.sinc_neg, Real.sinc_neg, add_comm]

lemma Kf_zero : Kf 0 = 1 := by
  unfold Kf
  rw [mul_zero, zero_sub, zero_add, Real.sinc_neg]
  have := sinc_c_pos
  field_simp
  ring

lemma Kf_continuous : Continuous Kf := by
  unfold Kf
  fun_prop

/-- A positive zero of the numerator satisfies `tan u = k / u`. -/
lemma zero_eq {u : ℝ} (hu : 0 < u)
    (h : Real.sinc (u - 1 / Real.sqrt 2) + Real.sinc (u + 1 / Real.sqrt 2) = 0) :
    Real.tan u = (1 / Real.sqrt 2 * Real.sin (1 / Real.sqrt 2) /
      Real.cos (1 / Real.sqrt 2)) / u := by
  have c0 := c_pos
  have c1 := c_lt_one
  have sc := sin_c_pos
  have cc := cos_c_pos
  set c := 1 / Real.sqrt 2 with hc
  by_cases huc : u = c
  · exfalso
    rw [huc, sub_self, Real.sinc_zero, show c + c = 2 * c by ring,
      Real.sinc_of_ne_zero (by positivity)] at h
    have : 0 < Real.sin (2 * c) / (2 * c) :=
      div_pos (Real.sin_pos_of_pos_of_lt_pi (by positivity)
        (by linarith [Real.pi_gt_three])) (by positivity)
    linarith
  have e1 : u - c ≠ 0 := sub_ne_zero.mpr huc
  have e2 : u + c ≠ 0 := by positivity
  rw [Real.sinc_of_ne_zero e1, Real.sinc_of_ne_zero e2, div_add_div _ _ e1 e2,
    div_eq_zero_iff] at h
  have h2 : Real.sin (u - c) * (u + c) + (u - c) * Real.sin (u + c) = 0 := by
    rcases h with h | h
    · exact h
    · exact absurd h (mul_ne_zero e1 e2)
  rw [Real.sin_sub, Real.sin_add] at h2
  have key : u * Real.sin u * Real.cos c = c * Real.cos u * Real.sin c := by
    linear_combination h2 / 2
  have hcos : Real.cos u ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_mul] at key
    have hs : Real.sin u = 0 := by
      rcases mul_eq_zero.mp key with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h hu.ne'
        · exact h
      · exact absurd h cc.ne'
    have := Real.sin_sq_add_cos_sq u
    rw [hs, h0] at this
    norm_num at this
  rw [Real.tan_eq_sin_div_cos, div_div, div_eq_div_iff hcos (by positivity)]
  field_simp
  linear_combination key

/-- A reduction modulo `π` of a point with positive tangent. -/
lemma reduce {w : ℝ} (hw : 0 < Real.tan w) :
    ∃ m : ℤ, ∃ α : ℝ, 0 < α ∧ α < Real.pi / 2 ∧ w = α + m * Real.pi := by
  have hpi := Real.pi_pos
  refine ⟨⌊w / Real.pi⌋, w - ⌊w / Real.pi⌋ * Real.pi, ?_, ?_, by ring⟩
  · have h1 : (⌊w / Real.pi⌋ : ℝ) ≤ w / Real.pi := Int.floor_le _
    have h2 : (⌊w / Real.pi⌋ : ℝ) * Real.pi ≤ w := by
      rwa [le_div_iff₀ hpi] at h1
    rcases h2.lt_or_eq with h2 | h2
    · linarith
    · exfalso
      have : Real.tan w = Real.tan (w - ⌊w / Real.pi⌋ * Real.pi) :=
        (Real.tan_sub_int_mul_pi w _).symm
      have h0 : w - ⌊w / Real.pi⌋ * Real.pi = 0 := by linarith
      rw [h0, Real.tan_zero] at this
      linarith
  · by_contra hge
    push_neg at hge
    have h1 : w / Real.pi < ⌊w / Real.pi⌋ + 1 := Int.lt_floor_add_one _
    have h2 : w < (⌊w / Real.pi⌋ + 1) * Real.pi := by
      rwa [div_lt_iff₀ hpi] at h1
    have h3 : (⌊w / Real.pi⌋ : ℝ) * Real.pi ≤ w := by
      have h1 : (⌊w / Real.pi⌋ : ℝ) ≤ w / Real.pi := Int.floor_le _
      rwa [le_div_iff₀ hpi] at h1
    set α := w - ⌊w / Real.pi⌋ * Real.pi with hα
    have hc : Real.cos α ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hge (by nlinarith)
    have hs : 0 ≤ Real.sin α := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by nlinarith)
    have ht : Real.tan α ≤ 0 := by
      rw [Real.tan_eq_sin_div_cos]
      exact div_nonpos_of_nonneg_of_nonpos hs hc
    rw [hα, Real.tan_sub_int_mul_pi] at ht
    linarith

lemma no_triple {k u v : ℝ} (hk : 0 < k) (hu : 0 < u) (hv : 0 < v)
    (h1 : Real.tan u = k / u) (h2 : Real.tan v = k / v)
    (h3 : Real.tan (u + v) = k / (u + v)) : False := by
  have hpi := Real.pi_pos
  obtain ⟨m, α, hα0, hα1, rfl⟩ := reduce (show 0 < Real.tan u by rw [h1]; positivity)
  obtain ⟨m', β, hβ0, hβ1, rfl⟩ := reduce (show 0 < Real.tan v by rw [h2]; positivity)
  rw [Real.tan_add_int_mul_pi] at h1
  have e : α + m * Real.pi + (β + m' * Real.pi) = (α + β) + ((m + m' : ℤ) : ℝ) * Real.pi := by
    push_cast; ring
  rw [e, Real.tan_add_int_mul_pi] at h3
  have hlt : k / (α + β + ((m + m' : ℤ) : ℝ) * Real.pi) < k / (α + m * Real.pi) :=
    div_lt_div_of_pos_left hk (by linarith) (by rw [← e]; linarith)
  by_cases hs : α + β < Real.pi / 2
  · have := Real.strictMonoOn_tan ⟨by linarith, hα1⟩ ⟨by linarith, hs⟩
      (show α < α + β by linarith)
    rw [h1, h3] at this
    linarith
  · push_neg at hs
    have hc : Real.cos (α + β) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hs (by linarith)
    have hsn : 0 ≤ Real.sin (α + β) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have ht : Real.tan (α + β) ≤ 0 := by
      rw [Real.tan_eq_sin_div_cos]
      exact div_nonpos_of_nonneg_of_nonpos hsn hc
    rw [h3] at ht
    have : 0 < k / (α + β + ((m + m' : ℤ) : ℝ) * Real.pi) := by
      apply div_pos hk; rw [← e]; linarith
    linarith

lemma Kf_zero_tan {x : ℝ} (hx : 0 < x) (h : Kf x = 0) :
    Real.tan (Real.pi * x) = (1 / Real.sqrt 2 * Real.sin (1 / Real.sqrt 2) /
      Real.cos (1 / Real.sqrt 2)) / (Real.pi * x) := by
  apply zero_eq (by positivity)
  unfold Kf at h
  rcases div_eq_zero_iff.mp h with h | h
  · exact h
  · exact absurd h (by have := sinc_c_pos; positivity)

lemma Phi_pos {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 < Kf s ^ 2 + Kf t ^ 2 + Kf (s + t) ^ 2 := by
  by_contra hle
  push_neg at hle
  have a1 : Kf s = 0 := by
    nlinarith [sq_nonneg (Kf s), sq_nonneg (Kf t), sq_nonneg (Kf (s + t))]
  have a2 : Kf t = 0 := by
    nlinarith [sq_nonneg (Kf s), sq_nonneg (Kf t), sq_nonneg (Kf (s + t))]
  have a3 : Kf (s + t) = 0 := by
    nlinarith [sq_nonneg (Kf s), sq_nonneg (Kf t), sq_nonneg (Kf (s + t))]
  have hs' : 0 < s := by
    rcases hs.lt_or_eq with h | h
    · exact h
    · rw [← h, Kf_zero] at a1; norm_num at a1
  have ht' : 0 < t := by
    rcases ht.lt_or_eq with h | h
    · exact h
    · rw [← h, Kf_zero] at a2; norm_num at a2
  have hk : 0 < 1 / Real.sqrt 2 * Real.sin (1 / Real.sqrt 2) / Real.cos (1 / Real.sqrt 2) :=
    div_pos (mul_pos c_pos sin_c_pos) cos_c_pos
  have b1 := Kf_zero_tan hs' a1
  have b2 := Kf_zero_tan ht' a2
  have b3 := Kf_zero_tan (by positivity) a3
  rw [mul_add] at b3
  exact no_triple hk (by positivity) (by positivity) b1 b2 b3

lemma exists_beta : ∃ β : ℝ, 0 < β ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ 100 → 0 ≤ t → t ≤ 100 →
    β ≤ Kf s ^ 2 + Kf t ^ 2 + Kf (s + t) ^ 2 := by
  have hc : IsCompact (Set.Icc ((0 : ℝ), (0 : ℝ)) ((100 : ℝ), (100 : ℝ))) := isCompact_Icc
  have hne : (Set.Icc ((0 : ℝ), (0 : ℝ)) ((100 : ℝ), (100 : ℝ))).Nonempty := by
    apply Set.nonempty_Icc.mpr
    exact Prod.mk_le_mk.mpr ⟨by norm_num, by norm_num⟩
  have hcont : Continuous (fun p : ℝ × ℝ => Kf p.1 ^ 2 + Kf p.2 ^ 2 + Kf (p.1 + p.2) ^ 2) := by
    have := Kf_continuous
    fun_prop
  obtain ⟨p, hp, hmin⟩ := hc.exists_isMinOn hne hcont.continuousOn
  have hp' : 0 ≤ p.1 ∧ 0 ≤ p.2 := hp.1
  have hpos : 0 < Kf p.1 ^ 2 + Kf p.2 ^ 2 + Kf (p.1 + p.2) ^ 2 := Phi_pos hp'.1 hp'.2
  refine ⟨Kf p.1 ^ 2 + Kf p.2 ^ 2 + Kf (p.1 + p.2) ^ 2, hpos, fun s t hs0 hs1 ht0 ht1 => ?_⟩
  have hmem : (s, t) ∈ Set.Icc ((0 : ℝ), (0 : ℝ)) ((100 : ℝ), (100 : ℝ)) :=
    Set.mem_Icc.mpr ⟨Prod.mk_le_mk.mpr ⟨hs0, ht0⟩, Prod.mk_le_mk.mpr ⟨hs1, ht1⟩⟩
  have := (isMinOn_iff.mp hmin) (s, t) hmem
  exact this

lemma packing (Φ3 : ℝ → ℝ → ℝ → ℝ) (β : ℝ) (hβ : 0 < β)
    (hΦ : ∀ p0 p1 p2 : ℝ, p0 ≤ p1 → p1 ≤ p2 → p2 - p0 ≤ 100 → β ≤ Φ3 p0 p1 p2)
    (Y : Finset ℝ) (a : ℝ) (hY : 10 ≤ Y.card)
    (hab : ∀ y ∈ Y, a ≤ y ∧ y ≤ a + 4 * Y.card) :
    ∃ (n : ℕ) (x : Fin n → Fin 3 → ℝ),
      (∀ i j, x i j ∈ Y) ∧ Function.Injective (fun p : Fin n × Fin 3 => x p.1 p.2) ∧
      (∀ i j k, |x i j - x i k| ≤ 100) ∧
      β / 400 * Y.card ≤ (∑ i, Φ3 (x i 0) (x i 1) (x i 2)) / 4 := by
  classical
  set N := Y.card with hN
  have hN0 : 0 < N := by omega
  let f := Y.orderEmbOfFin hN.symm
  let g : ℕ → ℝ := fun j => f ⟨min j (N - 1), by omega⟩
  have g_mem : ∀ j, g j ∈ Y := fun j => Y.orderEmbOfFin_mem hN.symm _
  have g_mono : Monotone g := by
    intro i j hij
    apply f.monotone
    show min i (N - 1) ≤ min j (N - 1)
    omega
  have g_inj : ∀ i j, i < N → j < N → g i = g j → i = j := by
    intro i j hi hj h
    have h1 := congrArg Fin.val (f.injective h)
    simp only at h1
    omega
  have g_bound : ∀ i j, g j - g i ≤ 4 * N := by
    intro i j
    have h1 := hab _ (g_mem i)
    have h2 := hab _ (g_mem j)
    linarith [h1.1, h2.2]
  set q := N / 3 with hq
  let D : ℕ → ℝ := fun i => g (3 * i + 2) - g (3 * i)
  have D_nonneg : ∀ i, 0 ≤ D i := fun i => sub_nonneg.mpr (g_mono (by omega))
  have sumD : ∑ i ∈ Finset.range q, D i ≤ 4 * N := by
    have h1 : ∑ i ∈ Finset.range q, D i ≤
        ∑ i ∈ Finset.range q, (g (3 * (i + 1)) - g (3 * i)) :=
      Finset.sum_le_sum fun i _ => by
        simp only [D]
        linarith [g_mono (show 3 * i + 2 ≤ 3 * (i + 1) by omega)]
    have h2 := Finset.sum_range_sub (fun i => g (3 * i)) q
    rw [h2] at h1
    linarith [g_bound (3 * 0) (3 * q)]
  let G := (Finset.range q).filter (fun i => D i ≤ 100)
  let B := (Finset.range q).filter (fun i => ¬ D i ≤ 100)
  have hGB : G.card + B.card = q := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.range q) (fun i => D i ≤ 100)
    rw [Finset.card_range] at this
    exact this
  have hB : 25 * B.card ≤ N := by
    have h1 : B.card • (100 : ℝ) ≤ ∑ i ∈ B, D i := by
      apply Finset.card_nsmul_le_sum
      intro i hi
      have := (Finset.mem_filter.mp hi).2
      linarith
    have h2 : ∑ i ∈ B, D i ≤ ∑ i ∈ Finset.range q, D i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => D_nonneg i)
    rw [nsmul_eq_mul] at h1
    have h3 : ((25 * B.card : ℕ) : ℝ) ≤ (N : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h3
  set n := G.card with hn
  let e : Fin n → ℕ := fun j => G.orderEmbOfFin hn.symm j
  have e_mem : ∀ j, e j ∈ G := fun j => G.orderEmbOfFin_mem hn.symm j
  have e_lt : ∀ j, e j < q := fun j => by
    have := e_mem j
    simp only [G, Finset.mem_filter, Finset.mem_range] at this
    exact this.1
  have e_D : ∀ j, D (e j) ≤ 100 := fun j => by
    have := e_mem j
    simp only [G, Finset.mem_filter, Finset.mem_range] at this
    exact this.2
  have e_inj : Function.Injective e := (G.orderEmbOfFin hn.symm).injective
  have h3q : 3 * q ≤ N := by omega
  refine ⟨n, fun j k => g (3 * e j + k), ?_, ?_, ?_, ?_⟩
  · intro i j
    exact g_mem _
  · rintro ⟨j, k⟩ ⟨j', k'⟩ h
    simp only at h
    have hk := k.isLt
    have hk' := k'.isLt
    have hj := e_lt j
    have hj' := e_lt j'
    have h1 := g_inj _ _ (by omega) (by omega) h
    have h2 : e j = e j' := by omega
    have h3 : (k : ℕ) = k' := by omega
    rw [e_inj h2, Fin.ext h3]
  · intro i j k
    have hj := j.isLt
    have hk := k.isLt
    have a1 := g_mono (show 3 * e i ≤ 3 * e i + (j : ℕ) by omega)
    have a2 := g_mono (show 3 * e i + (j : ℕ) ≤ 3 * e i + 2 by omega)
    have a3 := g_mono (show 3 * e i ≤ 3 * e i + (k : ℕ) by omega)
    have a4 := g_mono (show 3 * e i + (k : ℕ) ≤ 3 * e i + 2 by omega)
    have a5 := e_D i
    simp only [D] at a5
    rw [abs_le]
    constructor <;> linarith
  · have hterm : ∀ j : Fin n, β ≤ Φ3 (g (3 * e j + ((0 : Fin 3) : ℕ)))
        (g (3 * e j + ((1 : Fin 3) : ℕ))) (g (3 * e j + ((2 : Fin 3) : ℕ))) := by
      intro j
      have v0 : ((0 : Fin 3) : ℕ) = 0 := rfl
      have v1 : ((1 : Fin 3) : ℕ) = 1 := rfl
      have v2 : ((2 : Fin 3) : ℕ) = 2 := rfl
      rw [v0, v1, v2, Nat.add_zero]
      have a5 := e_D j
      simp only [D] at a5
      exact hΦ _ _ _ (g_mono (by omega)) (g_mono (by omega)) a5
    have hsum : ∑ j : Fin n, β ≤ ∑ j : Fin n, Φ3 (g (3 * e j + ((0 : Fin 3) : ℕ)))
        (g (3 * e j + ((1 : Fin 3) : ℕ))) (g (3 * e j + ((2 : Fin 3) : ℕ))) :=
      Finset.sum_le_sum fun j _ => hterm j
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hn100 : N ≤ 100 * n := by omega
    have hn100' : (N : ℝ) ≤ 100 * n := by exact_mod_cast hn100
    show β / 400 * N ≤ (∑ j : Fin n, Φ3 (g (3 * e j + ((0 : Fin 3) : ℕ)))
        (g (3 * e j + ((1 : Fin 3) : ℕ))) (g (3 * e j + ((2 : Fin 3) : ℕ)))) / 4
    nlinarith

end OMA.Helpers

theorem OMA.solution : OMA.R_riemannZeta_distinct_prop_lt_R1.H2 := by
  obtain ⟨β, hβ, hβle⟩ := OMA.Helpers.exists_beta
  unfold OMA.R_riemannZeta_distinct_prop_lt_R1.H2
  dsimp only
  refine ⟨β / 400, by positivity, 10, fun Y a hY hab => ?_⟩
  have hΦ : ∀ p0 p1 p2 : ℝ, p0 ≤ p1 → p1 ≤ p2 → p2 - p0 ≤ 100 →
      β ≤ OMA.Helpers.Kf (p0 - p1) ^ 2 + OMA.Helpers.Kf (p1 - p2) ^ 2 +
        OMA.Helpers.Kf (p0 - p2) ^ 2 := by
    intro p0 p1 p2 h01 h12 h02
    have e1 : p0 - p1 = -(p1 - p0) := by ring
    have e2 : p1 - p2 = -(p2 - p1) := by ring
    have e3 : p0 - p2 = -(p1 - p0 + (p2 - p1)) := by ring
    rw [e1, e2, e3, OMA.Helpers.Kf_neg, OMA.Helpers.Kf_neg, OMA.Helpers.Kf_neg]
    exact hβle (p1 - p0) (p2 - p1) (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨n, x, h1, h2, h3, h4⟩ := OMA.Helpers.packing
    (fun p0 p1 p2 => OMA.Helpers.Kf (p0 - p1) ^ 2 + OMA.Helpers.Kf (p1 - p2) ^ 2 +
      OMA.Helpers.Kf (p0 - p2) ^ 2) β hβ hΦ Y a hY hab
  exact ⟨n, x, h1, h2, h3, h4⟩
