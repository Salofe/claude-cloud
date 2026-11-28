import OMAStatements.S_oeis_a274479
import Mathlib

namespace OMA.Helpers

open PowerSeries Finset

/-- Truncated composition `F(G)` over `ZMod 3`, coefficientwise. -/
noncomputable def a274479Comp (F G : PowerSeries (ZMod 3)) : PowerSeries (ZMod 3) :=
  PowerSeries.mk fun n => ∑ k ∈ Finset.range (n + 1), coeff k F * coeff n (G ^ k)

/-- The candidate residue series `x / (1 - x)` over `ZMod 3`. -/
noncomputable def a274479Ones : PowerSeries (ZMod 3) :=
  PowerSeries.mk fun n => if n = 0 then 0 else 1

theorem a274479_comp_eq_subst (F G : PowerSeries (ZMod 3)) (hG : constantCoeff G = 0) :
    a274479Comp F G = F.subst G := by
  ext n
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hG), a274479Comp, coeff_mk]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · simp [smul_eq_mul]
  · intro d hd
    simp only [Function.mem_support] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hd
    obtain ⟨H, hH⟩ := pow_dvd_pow_of_dvd (X_dvd_iff.mpr hG) d
    rw [hH, coeff_X_pow_mul', if_neg (by omega), smul_zero]

theorem a274479_pow_coeff (G : PowerSeries (ZMod 3)) (hG : X ^ 2 ∣ G) (k n : ℕ) (h : n < 2 * k) :
    coeff n (G ^ k) = 0 := by
  obtain ⟨H, rfl⟩ := hG
  rw [mul_pow, ← pow_mul, coeff_X_pow_mul', if_neg (by omega)]

theorem a274479_unique (P Q G : PowerSeries (ZMod 3))
    (hG : ∀ k n, n < 2 * k → coeff n (G ^ k) = 0)
    (hP0 : coeff 0 P = 0) (hP1 : coeff 1 P = 1) (hQ0 : coeff 0 Q = 0) (hQ1 : coeff 1 Q = 1)
    (hP : P ^ 2 = a274479Comp P G) (hQ : Q ^ 2 = a274479Comp Q G) :
    ∀ m, coeff m P = coeff m Q := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => rw [hP0, hQ0]
    | 1 => rw [hP1, hQ1]
    | m + 2 =>
      have hD : ∀ i < m + 2, coeff i (P - Q) = 0 := by
        intro i hi; rw [map_sub, ih i hi, sub_self]
      have e2 : a274479Comp P G - a274479Comp Q G = a274479Comp (P - Q) G := by
        ext n; simp [a274479Comp, ← Finset.sum_sub_distrib, sub_mul]
      have e3 : (P - Q) * (P + Q) = a274479Comp (P - Q) G := by
        rw [← e2, ← hP, ← hQ]; ring
      have e4 := congrArg (coeff (m + 3)) e3
      have hR : coeff (m + 3) (a274479Comp (P - Q) G) = 0 := by
        rw [a274479Comp, coeff_mk]
        apply Finset.sum_eq_zero
        intro k _
        by_cases hk : k < m + 2
        · rw [hD k hk, zero_mul]
        · rw [hG k (m + 3) (by omega), mul_zero]
      have hL : coeff (m + 3) ((P - Q) * (P + Q)) = coeff (m + 2) (P - Q) * 2 := by
        rw [coeff_mul, Finset.sum_eq_single (m + 2, 1)]
        · congr 1
          rw [map_add, hP1, hQ1]; norm_num
        · rintro ⟨i, j⟩ hij hne
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
          simp only at hij
          by_cases hi : i < m + 2
          · rw [hD i hi, zero_mul]
          · have hj : j = 0 := by
              by_contra hj0
              apply hne
              have : j = 1 := by omega
              subst this
              have : i = m + 2 := by omega
              rw [this]
            rw [hj, map_add, hP0, hQ0, add_zero, mul_zero]
        · intro h
          exfalso; apply h
          rw [Finset.HasAntidiagonal.mem_antidiagonal]
          rfl
      rw [hL, hR] at e4
      have key : ∀ x : ZMod 3, x * 2 = 0 → x = 0 := by decide
      have := key _ e4
      rw [map_sub, sub_eq_zero] at this
      exact this

theorem a274479_ones_mul : a274479Ones * (1 - X) = X := by
  ext n
  rcases n with _ | n
  · simp [a274479Ones]
  · rw [mul_sub, mul_one, map_sub, coeff_succ_mul_X]
    rcases n with _ | n <;> simp [a274479Ones, coeff_X]

theorem a274479_three : (3 : PowerSeries (ZMod 3)) = 0 := by
  have h : (3 : ZMod 3) = 0 := by decide
  calc (3 : PowerSeries (ZMod 3)) = C (3 : ZMod 3) := (map_ofNat C 3).symm
    _ = 0 := by rw [h, map_zero]

theorem a274479_ones_eq (G : PowerSeries (ZMod 3)) (hG0 : constantCoeff G = 0)
    (hG : G * (1 - 2 * X - 4 * X ^ 2) = X ^ 2) :
    a274479Ones ^ 2 = a274479Comp a274479Ones G := by
  rw [a274479_comp_eq_subst _ _ hG0]
  have hs := HasSubst.of_constantCoeff_zero' hG0
  set S := a274479Ones.subst G with hSdef
  have hS : S * (1 - G) = G := by
    have := congrArg (substAlgHom hs) a274479_ones_mul
    rw [map_mul, map_sub, map_one, substAlgHom_X, coe_substAlgHom] at this
    exact this
  have hu : IsUnit ((1 - X : PowerSeries (ZMod 3)) ^ 2) :=
    (isUnit_iff_constantCoeff.mpr (by simp)).pow 2
  apply hu.mul_right_cancel
  have h3 := a274479_three
  have e1 : a274479Ones ^ 2 * (1 - X) ^ 2 = X ^ 2 := by
    rw [← mul_pow, a274479_ones_mul]
  rw [e1]
  linear_combination (-(1 - 2 * X - 4 * X ^ 2)) * hS - (1 + S) * hG - 2 * S * X ^ 2 * h3

end OMA.Helpers

open OMA.Helpers PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a274479.main := by
  intro A hA n hn
  obtain ⟨h0, h1, G, hG, hAG⟩ := hA
  have hGm : map (Int.castRingHom (ZMod 3)) G * (1 - 2 * X - 4 * X ^ 2) = X ^ 2 := by
    have := congrArg (map (Int.castRingHom (ZMod 3))) hG
    simp only [map_mul, map_sub, map_one, map_pow, map_X, map_ofNat] at this
    exact this

  have hc0 : coeff 0 (map (Int.castRingHom (ZMod 3)) G) = 0 := by
    have := congrArg (coeff 0) hGm
    simpa [coeff_mul] using this
  have hc1 : coeff 1 (map (Int.castRingHom (ZMod 3)) G) = 0 := by
    have := congrArg (coeff 1) hGm
    have hc0' : ((constantCoeff G : ℤ) : ZMod 3) = 0 := by simpa using hc0
    simp [coeff_mul, Finset.Nat.antidiagonal_succ, hc0', coeff_X, coeff_X_pow] at this
    simpa using this
  have hdvd : X ^ 2 ∣ map (Int.castRingHom (ZMod 3)) G := by
    rw [X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · exact hc0
    · exact hc1
  have hAm : (map (Int.castRingHom (ZMod 3)) A) ^ 2 = a274479Comp (map (Int.castRingHom (ZMod 3)) A) (map (Int.castRingHom (ZMod 3)) G) := by
    have := congrArg (map (Int.castRingHom (ZMod 3))) hAG
    rw [map_pow] at this
    rw [this]
    ext m
    simp [OMA.S_oeis_a274479.psComp, a274479Comp, coeff_map, ← map_pow]
  have hB := a274479_ones_eq (map (Int.castRingHom (ZMod 3)) G) (by rw [← coeff_zero_eq_constantCoeff_apply]; exact hc0) hGm
  have hu := a274479_unique (map (Int.castRingHom (ZMod 3)) A) a274479Ones (map (Int.castRingHom (ZMod 3)) G) (a274479_pow_coeff _ hdvd)
    (by simp [coeff_map, h0]) (by simp [coeff_map, h1]) (by simp [a274479Ones])
    (by simp [a274479Ones]) hAm hB n
  have hn' : n ≠ 0 := by omega
  simp only [coeff_map, a274479Ones, coeff_mk, hn', if_false] at hu
  have : ((PowerSeries.coeff n A : ℤ) : ZMod 3) = ((1 : ℤ) : ZMod 3) := by
    rw [Int.cast_one]; exact hu
  exact (ZMod.intCast_eq_intCast_iff _ _ 3).mp this
