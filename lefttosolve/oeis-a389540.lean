import OMAStatements.S_oeis_a389540
import Mathlib

namespace OMA.Helpers

open PowerSeries

/-- Modulo 2 the square of a series only keeps the squares of its coefficients, at even places. -/
theorem a389540_sq (H : PowerSeries ℤ) (n : ℕ) : ∃ c : ℤ,
    coeff n (H ^ 2) = 2 * c + (if n % 2 = 0 then coeff (n / 2) H ^ 2 else 0) := by
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · refine ⟨∑ i ∈ Finset.range m, coeff i H * coeff (2 * m - i) H, ?_⟩
    rw [Nat.succ_eq_add_one, show 2 * m + 1 = (m + 1) + m by ring, Finset.sum_range_add,
      Finset.sum_range_succ]
    have hr : ∑ x ∈ Finset.range m, coeff (m + 1 + x) H * coeff (2 * m - (m + 1 + x)) H =
        ∑ i ∈ Finset.range m, coeff i H * coeff (2 * m - i) H := by
      rw [← Finset.sum_range_reflect (fun i => coeff i H * coeff (2 * m - i) H) m]
      refine Finset.sum_congr rfl (fun x hx => ?_)
      have hx' := Finset.mem_range.1 hx
      rw [show 2 * m - (m + 1 + x) = m - 1 - x by omega, show 2 * m - (m - 1 - x) = m + 1 + x by omega,
        mul_comm]
    rw [hr, if_pos (by omega), show 2 * m / 2 = m by omega, show 2 * m - m = m by omega]
    ring
  · refine ⟨∑ i ∈ Finset.range (m + 1), coeff i H * coeff (2 * m + 1 - i) H, ?_⟩
    rw [Nat.succ_eq_add_one, show 2 * m + 1 + 1 = (m + 1) + (m + 1) by ring, Finset.sum_range_add]
    have hr : ∑ x ∈ Finset.range (m + 1),
        coeff (m + 1 + x) H * coeff (2 * m + 1 - (m + 1 + x)) H =
        ∑ i ∈ Finset.range (m + 1), coeff i H * coeff (2 * m + 1 - i) H := by
      rw [← Finset.sum_range_reflect (fun i => coeff i H * coeff (2 * m + 1 - i) H) (m + 1)]
      refine Finset.sum_congr rfl (fun x hx => ?_)
      have hx' := Finset.mem_range.1 hx
      rw [show 2 * m + 1 - (m + 1 + x) = m + 1 - 1 - x by omega,
        show 2 * m + 1 - (m + 1 - 1 - x) = m + 1 + x by omega, mul_comm]
    rw [hr, if_neg (by omega)]
    ring

/-- Parity bookkeeping: adding an even number and squaring do not change parity. -/
theorem a389540_odd (d y : ℤ) : Odd (2 * d + y ^ 2) ↔ Odd y := by
  rw [← Int.not_even_iff_odd, ← Int.not_even_iff_odd, Int.even_add, Int.even_pow]
  simp

theorem a389540_pow2_of_odd {k n : ℕ} (h : n = 2 ^ k) (ho : n % 2 = 1) : n = 1 := by
  rcases k with _ | k
  · simpa using h
  · rw [h, pow_succ] at ho
    omega

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a389540.main := by
  intro A h0 h1 hE
  set G : PowerSeries ℤ := PowerSeries.X - A with hGdef
  have hG0 : PowerSeries.coeff 0 G = 0 := by
    simp [hGdef]
    simpa using h0
  have hG1 : PowerSeries.coeff 1 G = 0 := by
    simp [hGdef, h1]
  obtain ⟨K, hK⟩ : (PowerSeries.X : PowerSeries ℤ) ^ 2 ∣ G := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · exact hG0
    · exact hG1
  have hsub : PowerSeries.HasSubst (2 * PowerSeries.X - 2 * A : PowerSeries ℤ) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    simp [h0]
  have h2G : (2 * PowerSeries.X - 2 * A : PowerSeries ℤ) = 2 * G := by
    rw [hGdef]; ring
  have hA : A = PowerSeries.X - PowerSeries.X ^ 2 * K := by
    rw [← hK, hGdef]; ring
  have hS : PowerSeries.subst (2 * PowerSeries.X - 2 * A) A =
      2 * G - (2 * G) ^ 2 * PowerSeries.subst (2 * PowerSeries.X - 2 * A) K := by
    rw [congrArg (PowerSeries.subst (2 * PowerSeries.X - 2 * A)) hA]
    rw [PowerSeries.subst_sub hsub, PowerSeries.subst_mul hsub, PowerSeries.subst_pow hsub,
      PowerSeries.subst_X hsub, h2G]
  rw [hS] at hE
  set S := PowerSeries.subst (2 * PowerSeries.X - 2 * A) K with hSdef
  -- coefficientwise form of the functional equation
  have key : ∀ n : ℕ, ∃ d : ℤ, PowerSeries.coeff n G = 2 * d + (if n = 2 then 1 else 0) +
      (if n % 2 = 0 then PowerSeries.coeff (n / 2) G ^ 2 else 0) := by
    intro n
    have hn := congrArg (PowerSeries.coeff n) hE
    obtain ⟨c, hc⟩ := OMA.Helpers.a389540_sq G n
    have hAG : A = PowerSeries.X - G := by rw [hGdef]; ring
    rw [hAG] at hn
    have e1 : (2 * G - (2 * G) ^ 2 * S : PowerSeries ℤ) =
        2 * G - PowerSeries.C (4 : ℤ) * (G ^ 2 * S) := by
      simp only [map_ofNat]; ring
    have e2 : (2 * (PowerSeries.X - G) ^ 2 : PowerSeries ℤ) =
        PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 2 - PowerSeries.C (4 : ℤ) * (PowerSeries.X * G) +
          PowerSeries.C (2 : ℤ) * G ^ 2 := by
      simp only [map_ofNat]; ring
    rw [e1, e2] at hn
    have e3 : (2 * G : PowerSeries ℤ) = PowerSeries.C (2 : ℤ) * G := by simp only [map_ofNat]
    rw [e3] at hn
    simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow] at hn
    rw [hc] at hn
    rcases n with _ | n
    · refine ⟨0, ?_⟩
      simp [hG0]
    · rw [PowerSeries.coeff_succ_X_mul] at hn
      refine ⟨PowerSeries.coeff (n + 1) (G ^ 2 * S) +
        c - PowerSeries.coeff n G, ?_⟩
      split_ifs at hn ⊢ <;> linarith
  intro n hn
  -- parity of the coefficients of G
  have par : ∀ n : ℕ, (Odd (PowerSeries.coeff n G) ↔ (2 ≤ n ∧ ∃ k : ℕ, n = 2 ^ k)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      obtain ⟨d, hd⟩ := key n
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · interval_cases n
        · rw [hG0]; simp
        · rw [hG1]; simp
      · rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
        · rcases Nat.lt_or_ge m 2 with hm | hm
          · have hm1 : m = 1 := by omega
            subst hm1
            have e : (2 : ℤ) * d + (if 2 * 1 = 2 then 1 else 0) +
                (if 2 * 1 % 2 = 0 then PowerSeries.coeff (2 * 1 / 2) G ^ 2 else 0) = 2 * d + 1 := by
              norm_num [hG1]
            rw [hd, e]
            refine ⟨fun _ => ⟨le_refl _, 1, by norm_num⟩, fun _ => ⟨d, rfl⟩⟩
          · rw [hd, if_neg (by omega), if_pos (by omega), show 2 * m / 2 = m by omega, add_zero,
              OMA.Helpers.a389540_odd, ih m (by omega)]
            constructor
            · rintro ⟨_, k, hk⟩
              exact ⟨by omega, k + 1, by rw [hk, pow_succ]; ring⟩
            · rintro ⟨_, k, hk⟩
              rcases k with _ | k
              · rw [pow_zero] at hk; omega
              · refine ⟨hm, k, ?_⟩
                rw [pow_succ] at hk
                omega
        · rw [hd, if_neg (by omega), if_neg (by omega), add_zero, add_zero]
          constructor
          · rintro ⟨r, hr⟩
            omega
          · rintro ⟨_, k, hk⟩
            have := OMA.Helpers.a389540_pow2_of_odd hk (by omega)
            omega
  have hAn : PowerSeries.coeff n A = (if n = 1 then 1 else 0) - PowerSeries.coeff n G := by
    rw [hGdef, map_sub, PowerSeries.coeff_X]
    ring
  show Odd (PowerSeries.coeff n A) ↔ _
  rw [hAn]
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · have hn1 : n = 1 := by omega
    subst hn1
    rw [hG1]
    simp only [if_true, sub_zero, odd_one, true_iff]
    exact ⟨0, rfl⟩
  · rw [if_neg (by omega), zero_sub, odd_neg, par n]
    exact ⟨fun h => h.2, fun h => ⟨hge, h⟩⟩

