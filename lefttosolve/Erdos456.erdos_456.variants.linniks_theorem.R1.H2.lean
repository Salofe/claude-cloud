import OMAReductions.R_Erdos456_erdos_456_variants_linniks_theorem_R1
import Mathlib

/-!
# Step H2 of the reduction Erdos456.erdos_456.variants.linniks_theorem.R1

If for every `M ≥ 1` there is a prime `ℓ` with `M ∣ ℓ - 1` and `ℓ ≤ C * M ^ L`, then the least
prime congruent to one modulo `n` is at most `C * n ^ L` for every `n ≥ 1`, which is the
required big-O bound with constant `C`.
-/

namespace OMA.Helpers

/-- A prime `ℓ` with `n ∣ ℓ - 1` bounds the least prime congruent to one modulo `n`. -/
theorem erdos456_p_le {n ℓ : ℕ} (hℓ : ℓ.Prime) (hd : n ∣ ℓ - 1) : Erdos456.p n ≤ ℓ := by
  have h1 : 1 ≤ ℓ := hℓ.one_lt.le
  have hmod : ℓ ≡ 1 [MOD n] := ((Nat.modEq_iff_dvd' h1).mpr hd).symm
  exact Nat.sInf_le ⟨hℓ, hmod⟩

end OMA.Helpers

open Filter Asymptotics in
theorem OMA.solution : OMA.R_Erdos456_erdos_456_variants_linniks_theorem_R1.H2 := by
  intro C L hLin
  refine IsBigO.of_bound C (eventually_atTop.2 ⟨1, fun m hm => ?_⟩)
  obtain ⟨q, hq, hqd, hqC⟩ := hLin m hm
  have hpq : Erdos456.p m ≤ q := OMA.Helpers.erdos456_p_le hq hqd
  have hpow : ((m : ℝ) ^ (L : ℝ)) = (m : ℝ) ^ L := Real.rpow_natCast _ _
  rw [hpow, Real.norm_natCast, Real.norm_of_nonneg (pow_nonneg m.cast_nonneg L)]
  exact (Nat.cast_le.2 hpq).trans hqC
