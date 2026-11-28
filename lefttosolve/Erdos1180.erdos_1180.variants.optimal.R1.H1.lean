import OMAReductions.R_Erdos1180_erdos_1180_variants_optimal_R1
import Mathlib

/-!
# Step H1 of the reduction Erdos1180.erdos_1180.variants.optimal.R1

Take V to be the whole set of reciprocals of 1, ..., M with M the floor of p^(eps/2).
Since 2M < p, the residues 1..M are distinct and nonzero, so the reciprocals are M
distinct elements, and a + b is never divisible by p, so no two reciprocals cancel.
Finally M > p^(eps/4) once p^(eps/4) is at least 2.
-/

namespace OMA.Helpers

/-- Reciprocals of distinct small positive integers are distinct, and no two of them
(equal or not) sum to zero, once twice the bound is below the prime. -/
theorem small_recips (p M : ℕ) (hp : p.Prime) (hM : 2 * M < p) :
    (((Finset.Icc 1 M).filter (fun n => n.Coprime p)).image
        (fun n : ℕ => (n : ZMod p)⁻¹)).card = M ∧
    ∀ x ∈ ((Finset.Icc 1 M).filter (fun n => n.Coprime p)).image
        (fun n : ℕ => (n : ZMod p)⁻¹),
      ∀ y ∈ ((Finset.Icc 1 M).filter (fun n => n.Coprime p)).image
        (fun n : ℕ => (n : ZMod p)⁻¹), x + y ≠ 0 := by
  have := Fact.mk hp
  have hfilt : (Finset.Icc 1 M).filter (fun n => n.Coprime p) = Finset.Icc 1 M := by
    apply Finset.filter_true_of_mem
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hne (n : ℕ) (hn : n ∈ Finset.Icc 1 M) : ((n : ℕ) : ZMod p) ≠ 0 := by
    have hn' := Finset.mem_Icc.mp hn
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  rw [hfilt]
  refine ⟨?_, ?_⟩
  · rw [Finset.card_image_of_injOn]
    · simp
    · intro a ha b hb hab
      have ha' := Finset.mem_Icc.mp (Finset.mem_coe.mp ha)
      have hb' := Finset.mem_Icc.mp (Finset.mem_coe.mp hb)
      have h2 : (a : ZMod p) = (b : ZMod p) := inv_inj.mp hab
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at h2
      exact h2
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have ha0 := hne a ha
    have hb0 := hne b hb
    have ha' := Finset.mem_Icc.mp ha
    have hb' := Finset.mem_Icc.mp hb
    have hsum : ((a + b : ℕ) : ZMod p) = 0 := by
      have e : ((a + b : ℕ) : ZMod p) = ((a : ZMod p) * (b : ZMod p)) *
          ((a : ZMod p)⁻¹ + (b : ZMod p)⁻¹) := by
        have e2 : ((a : ZMod p) * (b : ZMod p)) * ((a : ZMod p)⁻¹ + (b : ZMod p)⁻¹) =
            (b : ZMod p) * ((a : ZMod p) * (a : ZMod p)⁻¹) +
              (a : ZMod p) * ((b : ZMod p) * (b : ZMod p)⁻¹) := by ring
        rw [e2, mul_inv_cancel₀ ha0, mul_inv_cancel₀ hb0, mul_one, mul_one]
        push_cast
        ring
      rw [e, hxy, mul_zero]
    rw [ZMod.natCast_eq_zero_iff] at hsum
    have := Nat.le_of_dvd (by omega) hsum
    omega

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos1180_erdos_1180_variants_optimal_R1.H1 := by
  intro ε hε hε1
  refine ⟨max 5 ⌈(2 : ℝ) ^ (4 / ε)⌉₊, ?_⟩
  intro p hP hp
  dsimp only
  have hp5 : 5 ≤ p := le_trans (le_max_left _ _) hP
  have hpR : (2 : ℝ) ^ (4 / ε) ≤ (p : ℝ) := by
    have h1 : ⌈(2 : ℝ) ^ (4 / ε)⌉₊ ≤ p := le_trans (le_max_right _ _) hP
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  set y : ℝ := (p : ℝ) ^ (ε / 4) with hy
  have hy2 : (2 : ℝ) ≤ y := by
    have h := Real.rpow_le_rpow (by positivity) hpR (show (0 : ℝ) ≤ ε / 4 by positivity)
    rw [← Real.rpow_mul (by norm_num)] at h
    have e : 4 / ε * (ε / 4) = 1 := by field_simp
    rw [e, Real.rpow_one] at h
    exact h
  have hsq : (p : ℝ) ^ (ε / 2) = y * y := by
    rw [hy, ← Real.rpow_add hp0]
    ring_nf
  set M := ⌊(p : ℝ) ^ (ε / 2)⌋₊ with hMdef
  have hMlt : (p : ℝ) ^ (ε / 2) < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hMle : (M : ℝ) ≤ (p : ℝ) ^ (ε / 2) := Nat.floor_le (by positivity)
  have hMsq : (M : ℝ) * M ≤ p := by
    have h1 : (M : ℝ) * M ≤ (p : ℝ) ^ (ε / 2) * (p : ℝ) ^ (ε / 2) :=
      mul_le_mul hMle hMle (by positivity) (by positivity)
    have h2 : (p : ℝ) ^ (ε / 2) * (p : ℝ) ^ (ε / 2) = (p : ℝ) ^ ε := by
      rw [← Real.rpow_add hp0]; ring_nf
    have h3 : (p : ℝ) ^ ε ≤ (p : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hp1 hε1
    rw [Real.rpow_one] at h3
    linarith
  have hMsqN : M * M ≤ p := by exact_mod_cast hMsq
  have h2M : 2 * M < p := by nlinarith
  obtain ⟨hcard, hanti⟩ := small_recips p M hp h2M
  refine ⟨_, subset_refl _, ?_, hanti⟩
  rw [hcard]
  nlinarith
