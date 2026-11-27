import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1_H2_R1

/-!
# Step H1 of the reduction Arxiv.1601.03081.crystals_components_unique.R1.H2.R1.H2.R1.H1.R1.H2.R1.H2.R1

Write A = g + y z, B = g y + z and D = gcd(A, B). With lcm(A, B) = g y z + 1 we get
A = D r and B = q (r + 1) where g y z + 1 = B r. Put t = y (q - 1) - D, so 1 <= t < y and
y^2 - 1 = D m with m >= 2. Eliminating z and r gives a quadratic C2 g^2 - C1 g + C0 = 0 whose
leading coefficient is y^2 D E + q (t y + 1) with E = q m - y - t. If E > 0 the leading term is
too large, if E < 0 it is negative while C1 g > C0, and if E = 0 then m divides y and y^2 - 1,
so m = 1. All three cases are impossible. The core argument is proved for a general odd
cofactor k (here k = 1).
-/

namespace OMA.Helpers

theorem crystal_lower_g (g y z : ℤ) (hg : 2 ≤ g) (hy : 0 ≤ y) (ho : g*y ≤ z)
    (hdiv : g + y*z ∣ g*y*z+1) : y^2 < g := by
  have h1 : g + y*z ∣ g^2 - 1 := by
    have h2 : g + y*z ∣ g*(g + y*z) - (g*y*z+1) := dvd_sub (dvd_mul_left _ _) hdiv
    have h3 : g*(g + y*z) - (g*y*z+1) = g^2 - 1 := by ring
    rwa [h3] at h2
  have h4 : g + y*z ≤ g^2 - 1 := Int.le_of_dvd (by nlinarith) h1
  have h5 : g*y^2 ≤ y*z := by nlinarith [mul_le_mul_of_nonneg_left ho hy]
  by_contra! h6
  nlinarith [mul_le_mul_of_nonneg_left h6 (by omega : (0:ℤ) ≤ g)]

theorem crystal_basic (y q k t D : ℤ) (hk : 1 ≤ k) (hy : 33 ≤ y) (hq : 5 ≤ q)
    (ht1 : 1 ≤ t) (htk : t < k*y) (htq : (q-3)*t < k*y) (hD : D = k*y*(q-1)-t) :
    33 ≤ k*y ∧ k*y*(q-2) < D ∧ D < k*q*y ∧ 3*(k*y) < D ∧ q*t < 4*(k*y) := by
  have hky : 33 ≤ k*y := by nlinarith
  have hDlo : k*y*(q-2) < D := by rw [hD]; linarith
  have hDhi : D < k*q*y := by rw [hD]; linarith
  have hq2 : 3*(k*y) ≤ k*y*(q-2) := by nlinarith
  have hqt : q*t < 4*(k*y) := by linarith
  exact ⟨hky, hDlo, hDhi, by linarith, hqt⟩

theorem crystal_C0_pos (y q k t D : ℤ) (hq : 5 ≤ q) (ht1 : 1 ≤ t) (htk : t < k*y)
    (hky : 33 ≤ k*y) (hD3 : 3*(k*y) < D) : (k*y+t)^2 < k*q^2*y*D := by
  have h1 : (k*y+t)^2 < 4*(k*y)^2 := by nlinarith
  have hq2 : 25 ≤ q^2 := by nlinarith
  have h6 : 25*(k*y) ≤ q^2*D := by nlinarith
  have h7 := mul_le_mul_of_nonneg_left h6 (by linarith : (0:ℤ) ≤ k*y)
  have h8 : k*q^2*y*D = (k*y)*(q^2*D) := by ring
  nlinarith

theorem crystal_neg_case (g y q k t D E C0 C1 C2 : ℤ) (hk : 1 ≤ k) (hy : 33 ≤ y)
    (hq : 5 ≤ q) (hg : y^2 < g) (h3k : 3*k < y) (hqy : q ≤ y) (ht1 : 1 ≤ t)
    (htk : t < k*y) (htq : (q-3)*t < k*y) (hD : D = k*y*(q-1)-t)
    (hC2 : C2 = y^2*D*E + k*q*(t*y+k))
    (hC1 : C1 = q*(k^2*q*y^3 - (q-1)*k*t*y^2 + t^2*y - (2*q-1)*k^2*y + k*t))
    (hC0 : C0 = k*q^2*y*D - (k*y+t)^2)
    (hT : C2*g^2 - C1*g + C0 = 0) (hneg : E < 0) : False := by
  obtain ⟨hky, hDlo, hDhi, hD3, hqt⟩ := crystal_basic y q k t D hk hy hq ht1 htk htq hD
  have hgpos : 0 < g := by nlinarith
  have hy0 : 0 < y := by linarith
  have hk0 : 0 < k := by linarith
  have hDpos : 0 < D := by linarith
  have hyD : 0 < y^2*D := by positivity
  have hE1 : y^2*D*E ≤ y^2*D*(-1) := mul_le_mul_of_nonneg_left (by omega) hyD.le
  have hsmall : k*q*(t*y+k) < y^2*D := by
    have h1 : k*q*(t*y+k) = (q*t)*(k*y) + k^2*q := by ring
    have h2 : (q*t)*(k*y) < 4*(k*y)*(k*y) := by
      have := mul_lt_mul_of_pos_right hqt (by linarith : (0:ℤ) < k*y)
      linarith
    have h3 : k^2*q ≤ k^2*y := mul_le_mul_of_nonneg_left hqy (by positivity)
    have h4 : k^2*y ≤ (k*y)*(k*y) := by nlinarith
    have h5 : 5*((k*y)*(k*y)) ≤ y^2*(3*(k*y)) := by nlinarith
    have h6 : y^2*(3*(k*y)) < y^2*D := mul_lt_mul_of_pos_left hD3 (by positivity)
    linarith
  have hC2neg : C2 < 0 := by rw [hC2]; linarith
  have hg2 : 0 < g^2 := pow_pos hgpos 2
  have hC1g : C1*g < C0 := by linarith [mul_neg_of_neg_of_pos hC2neg hg2]
  have hsq : 0 < (k*y+t)^2 := pow_pos (by linarith) 2
  have hC0hi : C0 < k*q^2*y*D := by rw [hC0]; linarith
  have hC0hi2 : k*q^2*y*D ≤ k*q^2*y*(k*q*y) :=
    mul_le_mul_of_nonneg_left hDhi.le (by positivity)
  have hinner : k^2*y^3 ≤
      k^2*q*y^3 - (q-1)*k*t*y^2 + t^2*y - (2*q-1)*k^2*y + k*t := by
    have h1 : (q-1)*t < 3*(k*y) := by linarith
    have h2 : (q-1)*k*t*y^2 ≤ 3*k^2*y^3 := by
      have := mul_le_mul_of_nonneg_left h1.le (by positivity : (0:ℤ) ≤ k*y^2)
      have e1 : k*y^2*((q-1)*t) = (q-1)*k*t*y^2 := by ring
      have e2 : k*y^2*(3*(k*y)) = 3*k^2*y^3 := by ring
      linarith
    have h3 : (2*q-1)*k^2*y ≤ 2*k^2*y^2 := by
      have h31 : (2*q-1) ≤ 2*y := by linarith
      have := mul_le_mul_of_nonneg_right h31 (by positivity : (0:ℤ) ≤ k^2*y)
      have e1 : 2*y*(k^2*y) = 2*k^2*y^2 := by ring
      linarith
    have h4 : 0 ≤ t^2*y := by positivity
    have h5 : 0 ≤ k*t := by positivity
    have h6 : 3*k^2*y^3 + 2*k^2*y^2 + k^2*y^3 ≤ k^2*q*y^3 := by
      have h61 : 0 ≤ k^2*y^2 := by positivity
      have h62 : k^2*y^2*2 ≤ k^2*y^2*y := mul_le_mul_of_nonneg_left (by linarith) h61
      have h63 : 5*(k^2*y^2*y) ≤ q*(k^2*y^2*y) :=
        mul_le_mul_of_nonneg_right hq (by positivity)
      have e1 : k^2*y^2*y = k^2*y^3 := by ring
      have e2 : q*(k^2*y^2*y) = k^2*q*y^3 := by ring
      linarith
    linarith
  have hC1lo : q*(k^2*y^3) ≤ C1 := by
    rw [hC1]; exact mul_le_mul_of_nonneg_left hinner (by linarith)
  have hC1g2 : q*(k^2*y^3)*g ≤ C1*g := mul_le_mul_of_nonneg_right hC1lo hgpos.le
  have hfin : k*q^2*y*(k*q*y) ≤ q*(k^2*y^3)*g := by
    have h1 : q^2 ≤ y*g := by nlinarith
    have h2 : 0 ≤ q*k^2*y^2 := by positivity
    have := mul_le_mul_of_nonneg_left h1 h2
    have e1 : q*k^2*y^2*q^2 = k*q^2*y*(k*q*y) := by ring
    have e2 : q*k^2*y^2*(y*g) = q*(k^2*y^3)*g := by ring
    linarith
  linarith

theorem crystal_pos_case (g y q k t D E C0 C1 C2 : ℤ) (hk : 1 ≤ k) (hy : 33 ≤ y)
    (hq : 5 ≤ q) (hg : y^2 < g) (h3k : 3*k < y) (hqy : q ≤ y) (ht1 : 1 ≤ t)
    (htk : t < k*y) (htq : (q-3)*t < k*y) (hD : D = k*y*(q-1)-t)
    (hC2 : C2 = y^2*D*E + k*q*(t*y+k))
    (hC1 : C1 = q*(k^2*q*y^3 - (q-1)*k*t*y^2 + t^2*y - (2*q-1)*k^2*y + k*t))
    (hC0 : C0 = k*q^2*y*D - (k*y+t)^2)
    (hT : C2*g^2 - C1*g + C0 = 0) (hpos : 0 < E) : False := by
  obtain ⟨hky, hDlo, hDhi, hD3, hqt⟩ := crystal_basic y q k t D hk hy hq ht1 htk htq hD
  have hgpos : 0 < g := by nlinarith
  have hy0 : 0 < y := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hDpos : 0 < D := by linarith
  have hyD : 0 < y^2*D := by positivity
  have hC0pos : 0 < C0 := by
    have := crystal_C0_pos y q k t D hq ht1 htk hky hD3
    rw [hC0]; linarith
  have hC2lo : y^2*D ≤ C2 := by
    rw [hC2]
    have h1 : y^2*D*1 ≤ y^2*D*E := mul_le_mul_of_nonneg_left (by omega) hyD.le
    have h2 : 0 ≤ k*q*(t*y+k) := by
      have : 0 ≤ t*y+k := by positivity
      have : 0 ≤ q := by linarith
      positivity
    linarith
  have hinner : k^2*q*y^3 - (q-1)*k*t*y^2 + t^2*y - (2*q-1)*k^2*y + k*t ≤
      (q+2)*k^2*y^3 := by
    have h1 : t^2 ≤ (k*y)^2 := by nlinarith
    have h2 : t^2*y ≤ (k*y)^2*y := mul_le_mul_of_nonneg_right h1 hy0.le
    have h3 : k*t ≤ k*(k*y) := mul_le_mul_of_nonneg_left htk.le hk0
    have h3' : k*(k*y) ≤ k^2*y^3 := by
      have : k^2*y*1 ≤ k^2*y*(y^2) := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      have e1 : k*(k*y) = k^2*y*1 := by ring
      have e2 : k^2*y*(y^2) = k^2*y^3 := by ring
      linarith
    have h4 : 0 ≤ (q-1)*k*t*y^2 := by
      have : 0 ≤ q-1 := by linarith
      positivity
    have h5 : 0 ≤ (2*q-1)*k^2*y := by
      have : 0 ≤ 2*q-1 := by linarith
      positivity
    have e1 : (k*y)^2*y = k^2*y^3 := by ring
    have e2 : (q+2)*k^2*y^3 = k^2*q*y^3 + 2*(k^2*y^3) := by ring
    linarith
  have hC1hi : C1 ≤ q*((q+2)*k^2*y^3) := by
    rw [hC1]; exact mul_le_mul_of_nonneg_left hinner (by linarith)
  have hC2g : C2*g < C1 := by
    have h1 : 0 < g*(C1 - C2*g) := by
      have e : g*(C1 - C2*g) = C0 := by linear_combination -hT
      linarith
    have h2 := pos_of_mul_pos_right h1 hgpos.le
    linarith
  have hyDg : y^2*D*g ≤ C2*g := mul_le_mul_of_nonneg_right hC2lo hgpos.le
  have h5 : (q+7)*k < g := by nlinarith
  have h6 : q*(q+2) ≤ (q-2)*(q+7) := by nlinarith
  have h7 : q*(q+2)*k < (q-2)*g := by
    have h8 := mul_le_mul_of_nonneg_right h6 hk0
    have h9 := mul_lt_mul_of_pos_left h5 (by linarith : (0:ℤ) < q-2)
    have e1 : (q-2)*(q+7)*k = (q-2)*((q+7)*k) := by ring
    linarith
  have hA1 : 0 < y^2*g*(D - k*y*(q-2)) := by
    have : 0 < D - k*y*(q-2) := by linarith
    positivity
  have hA2 : 0 < k*y^3*((q-2)*g - q*(q+2)*k) := by
    have : 0 < (q-2)*g - q*(q+2)*k := by linarith
    have : 0 < k := by linarith
    positivity
  have e1 : y^2*g*(D - k*y*(q-2)) + k*y^3*((q-2)*g - q*(q+2)*k)
      = y^2*D*g - q*((q+2)*k^2*y^3) := by ring
  linarith

theorem crystal_core (g y z q k t m r : ℤ) (hk : 1 ≤ k) (hy : 33 ≤ y) (hq : 5 ≤ q)
    (hg : y^2 < g) (h3k : 3*k < y) (hqy : q ≤ y) (ht1 : 1 ≤ t) (htk : t < k*y)
    (htq : (q-3)*t < k*y) (hm2 : 2 ≤ m)
    (hm : y^2 - 1 = (k*y*(q-1)-t)*m)
    (hkA : k*(g+y*z) = (k*y*(q-1)-t)*r)
    (hB : g*y + z = q*(r+1))
    (hG2 : k*(g+y*z)*(g*y+z) = (k*y*(q-1)-t)*(g*y*z+1)) : False := by
  have hG1 : z*(k*y+t) = g*((k*y*(q-1)-t)*y - q*k) - q*(k*y*(q-1)-t) := by
    linear_combination q*hkA - (k*y*(q-1)-t)*hB
  have hPk : k^2*y^2 - k*(q-2)*t*y + t^2 - k^2*q =
      (k*y*(q-1)-t)*(k^2*q*m - k*y - t) := by
    linear_combination k^2*q*hm
  obtain ⟨D, hD⟩ : ∃ D, D = k*y*(q-1)-t := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = k^2*q*m - k*y - t := ⟨_, rfl⟩
  obtain ⟨C2, hC2⟩ : ∃ C2, C2 = y^2*D*E + k*q*(t*y+k) := ⟨_, rfl⟩
  obtain ⟨C1, hC1⟩ : ∃ C1, C1 =
      q*(k^2*q*y^3 - (q-1)*k*t*y^2 + t^2*y - (2*q-1)*k^2*y + k*t) := ⟨_, rfl⟩
  obtain ⟨C0, hC0⟩ : ∃ C0, C0 = k*q^2*y*D - (k*y+t)^2 := ⟨_, rfl⟩
  have hDT : D*(C2*g^2 - C1*g + C0) = 0 := by
    rw [hC2, hC1, hC0, hE, hD]
    linear_combination (k*y+t)^2*hG2
      - (k*y*(z*(k*y+t) + (g*((k*y*(q-1)-t)*y - q*k) - q*(k*y*(q-1)-t)))
          + g*(k*y^2+k-(k*y*(q-1)-t)*y)*(k*y+t))*hG1
      - (k*y*(q-1)-t)*y^2*g^2*hPk
  obtain ⟨hky, hDlo, hDhi, hD3, hqt⟩ := crystal_basic y q k t D hk hy hq ht1 htk htq hD
  have hT : C2*g^2 - C1*g + C0 = 0 := by
    rcases mul_eq_zero.mp hDT with h | h
    · linarith
    · exact h
  rcases lt_trichotomy E 0 with hneg | hzero | hpos
  · exact crystal_neg_case g y q k t D E C0 C1 C2 hk hy hq hg h3k hqy ht1 htk htq hD
      hC2 hC1 hC0 hT hneg
  · have hI1 : k*g*D*m = k*y*q*(r+1) - D*r := by
      rw [hD]; linear_combination (-k*g)*hm + k*y*hB - hkA
    have hgoal0 : k*q*(k*g*(y-k*m)*m - y - k*m*r) = 0 := by
      rw [hE] at hzero
      rw [hD] at hI1
      linear_combination hI1 - (g*k*m + r)*hzero
    have hkq : k*q ≠ 0 := by positivity
    have h0 : k*g*(y-k*m)*m - y - k*m*r = 0 := by
      rcases mul_eq_zero.mp hgoal0 with h | h
      · exact absurd h hkq
      · exact h
    have hmy : m ∣ y := ⟨k*g*(y-k*m) - k*r, by linear_combination -h0⟩
    have hmy2 : m ∣ y^2 - 1 := ⟨D, by rw [hm, hD]; ring⟩
    have hm1 : m ∣ 1 := by
      have h1 : m ∣ y*y := Dvd.dvd.mul_left hmy y
      have h2 := dvd_sub h1 hmy2
      have h3 : y*y - (y^2-1) = 1 := by ring
      rwa [h3] at h2
    have := Int.le_of_dvd one_pos hm1
    omega
  · exact crystal_pos_case g y q k t D E C0 C1 C2 hk hy hq hg h3k hqy ht1 htk htq hD
      hC2 hC1 hC0 hT hpos

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1_H2_R1.H1 := by
  intro g y z d q hg hy _ _ _ ho _ _ _ _ _ _ hq hquot _ _ _ hfirst hsecond
  intro D hDd hDl hlcm _ hlo hhi _ hgap _ _ hqy
  have hgcd : D * (g*y*z+1) = (g+y*z)*(g*y+z) := by
    rw [← hlcm]; exact Nat.gcd_mul_lcm _ _
  obtain ⟨r, hr⟩ := hsecond
  have hBpos : 0 < g*y+z := by positivity
  have hA : g + y*z = D*r := by
    apply Nat.eq_of_mul_eq_mul_right hBpos
    rw [← hgcd, hr]; ring
  have hBq : g*y+z = q*(r+1) := by
    apply Nat.eq_of_mul_eq_mul_left hBpos
    have h1 : (g*y+1)*(z+1) = (g*y*z+1) + (g*y+z) := by ring
    calc (g*y+z)*(g*y+z) = (g*y+z)^2 := by ring
      _ = q*((g*y+1)*(z+1)) := hquot
      _ = (g*y+z)*(q*(r+1)) := by rw [h1, hr]; ring
  obtain ⟨m, hm⟩ := hDd
  have hy2 : 1089 ≤ y^2 := by nlinarith
  have hm2 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m
      · rw [mul_zero] at hm; omega
      · rw [mul_one] at hm; omega
    · exact h
  have hq1 : 1 ≤ q := by omega
  have hq3 : 3 ≤ q := by omega
  have hyq : y*(q-1) + y = y*q := by
    rw [← Nat.mul_succ]; congr 1; omega
  have hle : D ≤ y*(q-1) := by omega
  have hgapZ : ((q:ℤ)-3)*((y:ℤ)*((q:ℤ)-1) - D) < y := by
    have h := (Nat.cast_lt (α := ℤ)).mpr hgap
    push_cast [Nat.cast_sub hle, Nat.cast_sub hq1, Nat.cast_sub hq3] at h
    exact h
  have hmZ : (y:ℤ)^2 - 1 = (D:ℤ)*m := by
    have h := congrArg (fun n : ℕ => (n:ℤ)) hm
    push_cast [Nat.cast_sub (by omega : 1 ≤ y^2)] at h
    exact h
  have hAZ : (g:ℤ) + y*z = (D:ℤ)*r := by exact_mod_cast hA
  have hBZ : (g:ℤ)*y + z = (q:ℤ)*(r+1) := by exact_mod_cast hBq
  have hgcdZ : (D:ℤ)*(g*y*z+1) = ((g:ℤ)+y*z)*(g*y+z) := by exact_mod_cast hgcd
  have hloZ : (D:ℤ) + y < y*q := by exact_mod_cast hlo
  have hhiZ : (y:ℤ)*q < D + 2*y := by exact_mod_cast hhi
  have hfirstZ : (g:ℤ) + y*z ∣ g*y*z+1 := by exact_mod_cast hfirst
  have hgy : (y:ℤ)^2 < g :=
    crystal_lower_g g y z (by exact_mod_cast hg) (by positivity) (by exact_mod_cast ho) hfirstZ
  exact crystal_core g y z q 1 ((y:ℤ)*((q:ℤ)-1) - D) m r le_rfl (by exact_mod_cast hy)
    (by exact_mod_cast hq) hgy (by push_cast; omega) (by push_cast; omega)
    (by linarith) (by linarith) (by linarith) (by exact_mod_cast hm2)
    (by linear_combination hmZ) (by linear_combination hAZ) hBZ
    (by linear_combination -hgcdZ)
