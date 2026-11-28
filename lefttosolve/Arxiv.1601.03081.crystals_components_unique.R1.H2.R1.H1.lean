import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1

/-!
# Step H1 of the reduction Arxiv.1601.03081.crystals_components_unique.R1.H2.R1

Write a = x g and c = y g with g = gcd a c and x, y coprime; g > 1 since a and c are not
coprime. Cancelling g in a b = c d gives x b = y d, so y divides x b, hence y divides b;
put b = y z. Then x y z = y d and y > 0 give d = x z.
-/

theorem OMA.solution : OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1.H1 := by
  intro a b c d ha hc hprod hnc
  obtain ⟨x, y, hxy, hax, hcy⟩ := Nat.exists_coprime a c
  set g := Nat.gcd a c with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left c ha
  have hg1 : 1 < g := by
    rcases Nat.lt_or_ge 1 g with h | h
    · exact h
    · exact absurd (show Nat.gcd a c = 1 by omega) hnc
  have hypos : 0 < y := by
    rcases Nat.eq_zero_or_pos y with h | h
    · rw [h, zero_mul] at hcy
      omega
    · exact h
  have hcancel : x * b = y * d := by
    apply Nat.eq_of_mul_eq_mul_left hgpos
    calc g * (x * b) = (x * g) * b := by ring
      _ = c * d := by rw [← hax, hprod]
      _ = g * (y * d) := by rw [hcy]; ring
  have hyb : y ∣ b := hxy.symm.dvd_of_dvd_mul_left ⟨d, hcancel⟩
  obtain ⟨z, hz⟩ := hyb
  have hd : d = x * z := by
    apply Nat.eq_of_mul_eq_mul_left hypos
    rw [← hcancel, hz]
    ring
  exact ⟨g, x, y, z, hg1, by rw [hax, mul_comm], by rw [hcy, mul_comm], hz, hd, hxy⟩
