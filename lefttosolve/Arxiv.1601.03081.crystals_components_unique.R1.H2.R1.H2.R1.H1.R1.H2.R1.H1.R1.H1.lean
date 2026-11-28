import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1
import Mathlib

/-!
# Step H1 of the reduction Arxiv.1601.03081.crystals_components_unique.R1.H2.R1.H2.R1.H1.R1.H2.R1.H1.R1

This step is the branch where k divides y. Write D = y^2 - 1. The exact gcd gives g*y + z = D*s and g + y*z = D*t,
hence g = y*s - t and z = y*t - s; the lcm cofactor gives D*t*s*k = g*y*z + 1 and the quotient
equation then gives D*s = q*(t*k + 1). With F = s*(y - k) - t these become
(y^2*(y - k) - y - k)*s*F = k^2*s^2 + y^2*F^2 - 1 and s*(q*k*(y - k) - D) = q*(k*F - 1).
The first forces F to be positive, the second gives s at most q*k*F, the ordering g*y at most z
gives 2*F*y at most s*(y^2 - 2*k*y - 1), and k*y*q < D + 2*k*y gives k*(q - 2) < y. Together
they force y^3 - y - 2*k < 2*k^3*q, which is impossible since 27*q*k^3 is at most
5*(k*(q - 2))^3 for q at least 5. The divisibility of y by k is not needed.
-/

namespace OMA.Helpers

set_option maxHeartbeats 1000000 in
/-- The integer core: the two quadratic relations, the ordering of the pair and the size of the
quotient are incompatible. -/
theorem crystal_core_int (Y S F K Q : ℤ) (hY : 33 ≤ Y) (hK : 3 ≤ K) (hQ : 5 ≤ Q) (hS : 0 < S)
    (hi : (Y^2*(Y-K)-Y-K)*S*F = K^2*S^2+Y^2*F^2-1)
    (hii : S*(Q*K*(Y-K)-(Y^2-1)) = Q*(K*F-1))
    (hiii : 2*F*Y ≤ S*(Y^2-2*K*Y-1))
    (hiv : K*(Q-2) < Y) : False := by
  have h3K : 3*K < Y := by nlinarith
  have hYK : 0 < Y - K := by linarith
  have hN : 0 < Y^2*(Y-K)-Y-K := by nlinarith
  have hF : 1 ≤ F := by
    by_contra! h
    have hNS : 0 ≤ (Y^2*(Y-K)-Y-K)*S := mul_nonneg hN.le hS.le
    have h1 : (Y^2*(Y-K)-Y-K)*S*F ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hNS (by linarith)
    have hKS0 : 3 ≤ K*S := by nlinarith
    have hKS : 9 ≤ K^2*S^2 := by nlinarith
    nlinarith [sq_nonneg F]
  have hKF : 3 ≤ K*F := by nlinarith
  have hP : 1 ≤ Q*K*(Y-K)-(Y^2-1) := by
    by_contra! h
    have h1 : S*(Q*K*(Y-K)-(Y^2-1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hS.le (by linarith)
    have h2 : 0 < Q*(K*F-1) := mul_pos (by linarith) (by linarith)
    linarith
  have hSle : S ≤ Q*K*F := by nlinarith
  have hSF : 0 < S*F := mul_pos hS (by linarith)
  have hYpos : 0 < Y := by linarith
  have e1 : K^2*S^2*Y ≤ K^3*Q*S*F*Y := by
    have h0 : 0 ≤ K^2*S*Y := by positivity
    have := mul_le_mul_of_nonneg_left hSle h0
    nlinarith
  have e2 : 2*Y^3*F^2 ≤ Y^2*F*S*(Y^2-2*K*Y-1) := by
    have h0 : 0 ≤ Y^2*F := by positivity
    have := mul_le_mul_of_nonneg_left hiii h0
    nlinarith
  have e3 : S*F*(2*Y*(Y^2*(Y-K)-Y-K) - 2*K^3*Q*Y - Y^2*(Y^2-2*K*Y-1)) < 0 := by
    have hi2 : 2*Y*((Y^2*(Y-K)-Y-K)*S*F) = 2*Y*(K^2*S^2+Y^2*F^2-1) := by rw [hi]
    nlinarith
  have e4 : 2*Y*(Y^2*(Y-K)-Y-K) - 2*K^3*Q*Y - Y^2*(Y^2-2*K*Y-1) < 0 := by
    by_contra! h
    nlinarith [mul_nonneg hSF.le h]
  have hmain : Y^3 - Y - 2*K < 2*K^3*Q := by
    by_contra! h
    have h0 : 0 ≤ Y*(Y^3 - Y - 2*K - 2*K^3*Q) := mul_nonneg hYpos.le (by linarith)
    nlinarith
  have hq5 : 0 ≤ Q - 5 := by linarith
  have hq' : 27*Q ≤ 5*(Q-2)^3 := by
    nlinarith [mul_nonneg (mul_nonneg hq5 hq5) hq5, mul_nonneg hq5 hq5]
  have hcube : 27*Q*K^3 ≤ 5*(K*(Q-2))^3 := by
    have h1 : (K*(Q-2))^3 = K^3*(Q-2)^3 := by ring
    have h2 : 0 ≤ K^3 := by positivity
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_left hq' h2]
  have hlt3 : (K*(Q-2))^3 < Y^3 := by
    have h0 : 0 ≤ K*(Q-2) := by nlinarith
    exact pow_lt_pow_left₀ hiv h0 (by norm_num)
  have hY3 : 1089*Y ≤ Y^3 := by nlinarith
  nlinarith

set_option maxHeartbeats 1000000 in
/-- The shared contradiction behind both cofactor branches: it only uses the ordering, the
quotient equation, the exact gcd, the lcm cofactor and the upper bound on the quotient. -/
theorem crystal_core (g y z q k : ℕ) (hg : 1 < g) (hy : 33 ≤ y) (hq : 5 ≤ q) (hk : 3 ≤ k)
    (ho : g*y ≤ z) (hquot : (g*y+z)^2 = q*((g*y+1)*(z+1)))
    (hD : Nat.gcd (g+y*z) (g*y+z) = y^2-1)
    (hlcm : (g+y*z).lcm (g*y+z)*k = g*y*z+1)
    (hup : k*y*q < (y^2-1)+2*k*y) : False := by
  have hy2 : 1 ≤ y^2 := by nlinarith
  have hDpos : 0 < y^2-1 := by
    have : 33*33 ≤ y^2 := by nlinarith
    omega
  obtain ⟨t, ht⟩ : y^2-1 ∣ g+y*z := hD ▸ Nat.gcd_dvd_left _ _
  obtain ⟨s, hs⟩ : y^2-1 ∣ g*y+z := hD ▸ Nat.gcd_dvd_right _ _
  have h1 : (y^2-1) * (g+y*z).lcm (g*y+z) = (y^2-1) * ((y^2-1)*t*s) := by
    calc (y^2-1) * (g+y*z).lcm (g*y+z)
        = Nat.gcd (g+y*z) (g*y+z) * (g+y*z).lcm (g*y+z) := by rw [hD]
      _ = (g+y*z)*(g*y+z) := Nat.gcd_mul_lcm _ _
      _ = ((y^2-1)*t)*((y^2-1)*s) := by rw [ht, hs]
      _ = (y^2-1) * ((y^2-1)*t*s) := by ring
  have hL := Nat.eq_of_mul_eq_mul_left hDpos h1
  rw [hL] at hlcm
  have hzpos : 0 < z := by nlinarith
  zify [hy2] at ht hs hlcm hup hquot ho hDpos
  have hY : (33:ℤ) ≤ y := by exact_mod_cast hy
  have hK : (3:ℤ) ≤ k := by exact_mod_cast hk
  have hQ : (5:ℤ) ≤ q := by exact_mod_cast hq
  have hzZ : (0:ℤ) < z := by exact_mod_cast hzpos
  have hgZ : (0:ℤ) ≤ g := by positivity
  have hgD : ((y:ℤ)^2-1) * g = ((y:ℤ)^2-1) * (y*s - t) := by
    linear_combination (y:ℤ) * hs - ht
  have hgE : (g:ℤ) = y*s - t := mul_left_cancel₀ hDpos.ne' hgD
  have hzE : (z:ℤ) = y*t - s := by linear_combination hs - (y:ℤ) * hgE
  have hSpos : (0:ℤ) < s := by
    by_contra! h
    have : ((y:ℤ)^2-1) * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hDpos.le h
    nlinarith
  rw [hgE, hzE] at hquot hlcm ho
  have key : ((y:ℤ)^2-1)*s * (((y:ℤ)^2-1)*s - q*(t*k+1)) = 0 := by
    linear_combination hquot - (q:ℤ) * hlcm
  have hDS : ((y:ℤ)^2-1)*s ≠ 0 := (mul_pos hDpos hSpos).ne'
  have hq2 : ((y:ℤ)^2-1)*s = q*(t*k+1) := by
    have := (mul_eq_zero.mp key).resolve_left hDS
    linarith
  obtain ⟨F, hF⟩ : ∃ F : ℤ, (t:ℤ) = s*(y-k) - F := ⟨s*(y-k) - t, by ring⟩
  rw [hF] at hlcm hq2 ho
  refine crystal_core_int y s F k q hY hK hQ hSpos ?_ ?_ ?_ ?_
  · linear_combination -hlcm
  · linear_combination -hq2
  · nlinarith
  · by_contra! h
    have hm : (y:ℤ) * y ≤ y * (k*(q-2)) := mul_le_mul_of_nonneg_left h (by positivity)
    have h2 : (y:ℤ) * (k*(q-2)) = k*y*q - 2*k*y := by ring
    have h3 : (y:ℤ) * y = y^2 := by ring
    clear hquot hlcm key hq2 hF ho hgD hgE hzE hs ht hL h1 hDS
    linarith

end OMA.Helpers

theorem OMA.solution : OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1.H1 := by
  intro g y z d q k hg hy _ _ _ ho _ _ _ _ _ _ hq hquot _ _ _ _ _ hD _ _ _ hk hlcm _ _ hup _ _ _
  exact OMA.Helpers.crystal_core g y z q k hg hy hq hk ho hquot hD hlcm hup
