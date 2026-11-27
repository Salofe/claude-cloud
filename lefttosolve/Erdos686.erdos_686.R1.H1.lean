import OMAReductions.R_Erdos686_erdos_686_R1

/-!
Step H1 of reduction Erdos686.erdos_686.R1: every non-square N at least 2 is a ratio of
two products of two consecutive integers. Take a nontrivial solution of the Pell equation
x^2 - N y^2 = 1 (x at least 2, y at least 1) and set n = x^2 + x y - 2, m = x^2 + N x y - 2.
Then (m+1)(m+2) = N (n+1)(n+2) because the difference is (1 - N) x^2 (x^2 - N y^2 - 1).
-/

namespace OMA.Helpers

theorem key (N x y : ℕ) (hN : 2 ≤ N) (hx : 2 ≤ x) (hy : 1 ≤ y)
    (h : x ^ 2 = 1 + N * y ^ 2) :
    ∃ᵉ (k ≥ 2) (n : ℕ) (m ≥ n + k),
      (N : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i)) / (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  have hxy : 1 ≤ x * y := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hNxy : x * y + 2 ≤ N * (x * y) := by nlinarith
  have hx2 : 4 ≤ x ^ 2 := by nlinarith
  refine ⟨2, le_rfl, x ^ 2 + x * y - 2, x ^ 2 + N * (x * y) - 2, by omega, ?_⟩
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hI, Finset.prod_pair (by norm_num), Finset.prod_pair (by norm_num)]
  have c1 : ((x ^ 2 + x * y - 2 : ℕ) : ℚ) = (x : ℚ) ^ 2 + x * y - 2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have c2 : ((x ^ 2 + N * (x * y) - 2 : ℕ) : ℚ) = (x : ℚ) ^ 2 + N * (x * y) - 2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hq : (x : ℚ) ^ 2 = 1 + N * y ^ 2 := by exact_mod_cast h
  push_cast
  rw [c1, c2]
  have hxq : (2 : ℚ) ≤ x := by exact_mod_cast hx
  have hyq : (1 : ℚ) ≤ y := by exact_mod_cast hy
  have hpos : (0 : ℚ) < ((x : ℚ) ^ 2 + x * y - 2 + 1) * ((x : ℚ) ^ 2 + x * y - 2 + 2) := by
    apply mul_pos <;> nlinarith
  rw [eq_div_iff hpos.ne']
  linear_combination ((N : ℚ) - 1) * (x : ℚ) ^ 2 * hq

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos686_erdos_686_R1.H1 := by
  intro N hN hns
  have hd : ¬ IsSquare (N : ℤ) := fun h => hns (Int.isSquare_natCast_iff.mp h)
  obtain ⟨a, ha1, hay⟩ := Pell.Solution₁.exists_pos_of_not_isSquare
    (d := (N : ℤ)) (by exact_mod_cast (show 0 < N by omega)) hd
  have hp := a.prop
  obtain ⟨x, hx⟩ : ∃ x : ℕ, (x : ℤ) = a.x := ⟨a.x.toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ, (y : ℤ) = a.y := ⟨a.y.toNat, Int.toNat_of_nonneg (by omega)⟩
  rw [← hx, ← hy] at hp
  rw [← hx] at ha1
  rw [← hy] at hay
  apply OMA.Helpers.key N x y hN (by omega) (by omega)
  have : ((x ^ 2 : ℕ) : ℤ) = ((1 + N * y ^ 2 : ℕ) : ℤ) := by push_cast; linarith
  exact_mod_cast this
