import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1

/-! Parity obstruction when the gcd of the two component sums is the full value y^2-1.

Both sums divide n+1 with odd cofactors, so after dividing by their gcd both reduced
sums are odd. With gcd equal to y^2-1 the identity y*s2 - s1 = g*(y^2-1) then
forces g = y*alpha - beta to be even, contradicting the oddness of g. -/

namespace OMA.Helpers

theorem odd_reduced_sums {s₁ s₂ r₁ r₂ : ℕ} (hs : 0 < s₁) (hr₁ : Odd r₁) (hr₂ : Odd r₂)
    (h : s₁ * r₁ = s₂ * r₂) :
    s₁ = Nat.gcd s₁ s₂ * (s₁ / Nat.gcd s₁ s₂) ∧ s₂ = Nat.gcd s₁ s₂ * (s₂ / Nat.gcd s₁ s₂) ∧
      Odd (s₁ / Nat.gcd s₁ s₂) ∧ Odd (s₂ / Nat.gcd s₁ s₂) := by
  have hD : 0 < Nat.gcd s₁ s₂ := Nat.gcd_pos_of_pos_left _ hs
  have hcop : Nat.Coprime (s₁ / Nat.gcd s₁ s₂) (s₂ / Nat.gcd s₁ s₂) :=
    Nat.coprime_div_gcd_div_gcd hD
  have hβ : s₁ = Nat.gcd s₁ s₂ * (s₁ / Nat.gcd s₁ s₂) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
  have hα : s₂ = Nat.gcd s₁ s₂ * (s₂ / Nat.gcd s₁ s₂) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
  generalize Nat.gcd s₁ s₂ = D at hD hcop hβ hα ⊢
  generalize s₁ / D = β at hcop hβ ⊢
  generalize s₂ / D = α at hcop hα ⊢
  have hrel : β * r₁ = α * r₂ := by
    have h' : D * (β * r₁) = D * (α * r₂) := by
      calc D * (β * r₁) = (D * β) * r₁ := by ring
        _ = s₁ * r₁ := by rw [← hβ]
        _ = s₂ * r₂ := h
        _ = (D * α) * r₂ := by rw [← hα]
        _ = D * (α * r₂) := by ring
    exact Nat.eq_of_mul_eq_mul_left hD h'
  have hnr₁ : ¬ Even r₁ := Nat.not_even_iff_odd.mpr hr₁
  have hnr₂ : ¬ Even r₂ := Nat.not_even_iff_odd.mpr hr₂
  have hβo : Odd β := by
    rcases Nat.even_or_odd β with he | ho
    · exfalso
      have h1 : Even (α * r₂) := by rw [← hrel]; exact he.mul_right r₁
      rcases Nat.even_mul.mp h1 with hae | hre
      · have h2 : (2 : ℕ) = 1 :=
          Nat.eq_one_of_dvd_coprimes hcop (even_iff_two_dvd.mp he) (even_iff_two_dvd.mp hae)
        omega
      · exact hnr₂ hre
    · exact ho
  have hαo : Odd α := by
    rcases Nat.even_or_odd α with he | ho
    · exfalso
      have h1 : Even (β * r₁) := by rw [hrel]; exact he.mul_right r₂
      rcases Nat.even_mul.mp h1 with hbe | hre
      · exact (Nat.not_even_iff_odd.mpr hβo) hbe
      · exact hnr₁ hre
    · exact ho
  exact ⟨hβ, hα, hβo, hαo⟩

end OMA.Helpers

theorem OMA.solution :
    OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1.H1 := by
  intro g y z d q hg hy hgo hyo hzo horder hdiv hd hdup hde hgd hgd' hq hqeq
    hcy hcz hyz hfirst hsecond hD hzD hqD
  have hy1 : 1 ≤ y := by omega
  have hgy1 : 1 < g * y := by
    have := Nat.mul_le_mul_right y (show 2 ≤ g by omega)
    omega
  have hz1 : 1 < z := by omega
  have hyz1 : 1 < y * z := by
    have := Nat.mul_le_mul_left y (show 2 ≤ z by omega)
    omega
  obtain ⟨p, hp⟩ := hdiv
  have hpeq : (g + y * z) ^ 2 = p * ((g + 1) * (y * z + 1)) := by
    rw [hp, Nat.mul_comm]
  have hp2 := OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1_H2_R1.crystal_quotient_ge_two
    hg hyz1 hpeq
  obtain ⟨r₁, hr₁o, hr₁, -⟩ := CrystalVieta.odd_crystal_factor hgo (hyo.mul hzo) hg hyz1 hp2 hpeq
  obtain ⟨r₂, hr₂o, hr₂, -⟩ := CrystalVieta.odd_crystal_factor (hgo.mul hyo) hzo hgy1 hz1
    (by omega) hqeq
  have hrel : (g + y * z) * r₁ = (g * y + z) * r₂ := by
    rw [hr₁, hr₂]; ring
  obtain ⟨hβ, hα, hβo, hαo⟩ := OMA.Helpers.odd_reduced_sums (by omega) hr₁o hr₂o hrel
  rw [hD] at hβ hα hβo hαo
  generalize (g + y * z) / (y ^ 2 - 1) = β at hβ hβo
  generalize (g * y + z) / (y ^ 2 - 1) = α at hα hαo
  obtain ⟨e, he⟩ : ∃ e, y ^ 2 = e + 1 := ⟨y ^ 2 - 1, by
    have : 1 ≤ y ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega⟩
  have hee : y ^ 2 - 1 = e := by omega
  rw [hee] at hβ hα
  have hepos : 0 < e := by
    have : 33 * 33 ≤ y ^ 2 := by
      rw [pow_two]; exact Nat.mul_le_mul hy hy
    omega
  have hid : y * (g * y + z) = (g + y * z) + g * e := by
    have h1 : y * (g * y + z) = g * y ^ 2 + y * z := by ring
    rw [h1, he]; ring
  rw [hα, hβ] at hid
  have hcancel : e * (y * α) = e * (β + g) := by
    calc e * (y * α) = y * (e * α) := by ring
      _ = e * β + g * e := hid
      _ = e * (β + g) := by ring
  have hfin : y * α = β + g := Nat.eq_of_mul_eq_mul_left hepos hcancel
  have hodd : Odd (y * α) := hyo.mul hαo
  have heven : Even (β + g) := hβo.add_odd hgo
  rw [hfin] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) heven
