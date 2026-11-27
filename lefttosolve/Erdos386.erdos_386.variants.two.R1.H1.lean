import OMAReductions.R_Erdos386_erdos_386_variants_two_R1

/-!
# Step H1 of the reduction Erdos386.erdos_386.variants.two.R1

If 8 P + 1 = r * r then r is odd, say r = 2 k + 1, so k (k + 1) = 2 P and
P = (k + 1) choose 2. Taking n = k + 1, the bound 6 ≤ P forces 4 ≤ n, and
2 P = k (k + 1) ≤ 2 (k + 1) ^ 2 gives P ≤ n ^ 2.
-/

namespace OMA.Helpers

theorem erdos386_square_odd (P r : ℕ) (hr : 8 * P + 1 = r * r) : ∃ k, r = 2 * k + 1 := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' r
  · exfalso
    subst hk
    have h : 8 * P + 1 = 2 * (2 * k * k) := by rw [hr]; ring
    omega
  · exact ⟨k, hk⟩

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos386_erdos_386_variants_two_R1.H1 := by
  intro P hP hsq
  obtain ⟨r, hr⟩ := hsq
  obtain ⟨k, rfl⟩ := OMA.Helpers.erdos386_square_odd P r hr
  have hk : k * (k + 1) = 2 * P := by nlinarith
  refine ⟨k + 1, ?_, ?_, ?_⟩
  · by_contra hlt
    have hk2 : k ≤ 2 := by omega
    have : k * (k + 1) ≤ 2 * 3 := Nat.mul_le_mul hk2 (by omega)
    omega
  · rw [Nat.choose_two_right]
    have h2 : (k + 1) * (k + 1 - 1) = 2 * P := by
      rw [Nat.add_sub_cancel, Nat.mul_comm]; exact hk
    rw [h2]
    omega
  · nlinarith
