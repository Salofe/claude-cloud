import OMAReductions.R_Green47_green_47_variants_finite_exceptions_R1
import Mathlib

namespace OMA.Helpers

open Filter

theorem g47_jac_mod (t b p : ℕ) (hb : Odd b) (hp : Odd p) (hmod : p ≡ b [MOD 4 * t]) :
    jacobiSym (t : ℤ) p = jacobiSym (t : ℤ) b := by
  rw [jacobiSym.mod_right (t : ℤ) hp, jacobiSym.mod_right (t : ℤ) hb]
  have h1 : (t : ℤ).natAbs = t := Int.natAbs_natCast t
  rw [h1]
  rw [show p % (4 * t) = b % (4 * t) from hmod]

theorem g47_frequently (t b : ℕ) (ht : t ≠ 0) (hb : Odd b) (hcop : Nat.Coprime b (4 * t))
    (hJ : jacobiSym (t : ℤ) b = -1) :
    ∃ᶠ p in atTop, p.Prime ∧ jacobiSym (t : ℤ) p = -1 := by
  have hfr := Nat.frequently_atTop_prime_and_modEq (q := 4 * t) (a := b) (by omega) hcop
  refine hfr.mono ?_
  rintro p ⟨hp, hmod⟩
  refine ⟨hp, ?_⟩
  have h4 : p ≡ b [MOD 4] := Nat.ModEq.of_mul_right t hmod
  have h2 : p ≡ b [MOD 2] := Nat.ModEq.of_mul_right 2 (show p ≡ b [MOD 2 * 2] from h4)
  have hpodd : Odd p := by
    rw [Nat.odd_iff] at hb ⊢
    have h2' : p % 2 = b % 2 := h2
    omega
  rw [g47_jac_mod t b p hb hpodd hmod, hJ]

theorem g47_exists_b (t : ℕ) (ht : Squarefree t) (ht1 : t ≠ 1) :
    ∃ b : ℕ, Odd b ∧ Nat.Coprime b (4 * t) ∧ jacobiSym (t : ℤ) b = -1 := by
  have ht0 : t ≠ 0 := ht.ne_zero
  by_cases hq : ∃ q, q.Prime ∧ q ∣ t ∧ q ≠ 2
  · obtain ⟨q, hqp, hqt, hq2⟩ := hq
    obtain ⟨m, rfl⟩ := hqt
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact ht0 (by simp)
    have hqm : ¬ q ∣ m := by
      rintro ⟨k, rfl⟩
      have hu := ht q ⟨k, by ring⟩
      exact hqp.not_isUnit hu
    have := Fact.mk hqp
    have hchar : ringChar (ZMod q) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      exact hq2
    obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare hchar
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx ⟨0, by simp⟩
    have hqodd : Odd q := hqp.odd_of_ne_two hq2
    have hcop : Nat.Coprime (4 * m) q := by
      apply Nat.Coprime.symm
      rw [Nat.Prime.coprime_iff_not_dvd hqp]
      intro h
      rcases (Nat.Prime.dvd_mul hqp).1 h with h4 | hm
      · have h22 : q ∣ 2 ^ 2 := by simpa using h4
        have hq2' := Nat.Prime.dvd_of_dvd_pow hqp h22
        have hle := Nat.le_of_dvd (by norm_num) hq2'
        have := hqp.two_le
        omega
      · exact hqm hm
    obtain ⟨b, hb1, hbq⟩ := Nat.chineseRemainder hcop 1 x.val
    have hb1' : b % (4 * m) = 1 := by
      have h : b % (4 * m) = 1 % (4 * m) := hb1
      rw [h]
      apply Nat.mod_eq_of_lt
      omega
    have hb4 : b % 4 = 1 := by
      have h : b ≡ 1 [MOD 4] := Nat.ModEq.of_mul_right m hb1
      exact h
    have hbodd : Odd b := Nat.odd_iff.mpr (by omega)
    have hbx : (b : ZMod q) = x := by
      rw [(ZMod.natCast_eq_natCast_iff b x.val q).mpr hbq, ZMod.natCast_zmod_val]
    refine ⟨b, hbodd, ?_, ?_⟩
    · have hc1 : Nat.Coprime b (4 * m) := by
        unfold Nat.Coprime
        rw [Nat.ModEq.gcd_eq hb1]
        simp
      have hc2 : Nat.Coprime b q := by
        apply Nat.Coprime.symm
        rw [Nat.Prime.coprime_iff_not_dvd hqp]
        intro hdvd
        apply hx0
        rw [← hbx]
        exact (ZMod.natCast_eq_zero_iff b q).mpr hdvd
      have hc := Nat.Coprime.mul_right hc1 hc2
      have he : 4 * (q * m) = 4 * m * q := by ring
      rw [he]
      exact hc
    · have hsplit : ((q * m : ℕ) : ℤ) = (q : ℤ) * (m : ℤ) := by push_cast; ring
      rw [hsplit, jacobiSym.mul_left]
      have hJm : jacobiSym (m : ℤ) b = 1 := by
        rw [jacobiSym.mod_right (m : ℤ) hbodd, Int.natAbs_natCast, hb1']
        exact jacobiSym.one_right _
      have hJq : jacobiSym (q : ℤ) b = -1 := by
        rw [jacobiSym.quadratic_reciprocity_one_mod_four' hqodd hb4]
        rw [ZMod.nonsquare_iff_jacobiSym_eq_neg_one]
        rw [Int.cast_natCast, hbx]
        exact hx
      rw [hJm, hJq]
      norm_num
  · push Not at hq
    have ht2 : t = 2 := by
      have hmin := Nat.minFac_prime ht1
      have h2 : t.minFac = 2 := hq _ hmin (Nat.minFac_dvd t)
      have h2t : 2 ∣ t := h2 ▸ Nat.minFac_dvd t
      obtain ⟨u, rfl⟩ := h2t
      by_cases hu1 : u = 1
      · rw [hu1]
      · exfalso
        have hu0 : u ≠ 0 := by
          rintro rfl
          exact ht0 (by simp)
        have humin := Nat.minFac_prime hu1
        have hu2 : u.minFac = 2 := hq _ humin (Dvd.dvd.mul_left (Nat.minFac_dvd u) 2)
        have h2u : 2 ∣ u := hu2 ▸ Nat.minFac_dvd u
        obtain ⟨w, rfl⟩ := h2u
        have hu := ht 2 ⟨w, by ring⟩
        exact Nat.prime_two.not_isUnit hu
    subst ht2
    have h3 : ¬IsSquare (((2 : ℕ) : ℤ) : ZMod 3) := by decide
    refine ⟨3, by decide, by decide, ?_⟩
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    rw [ZMod.nonsquare_iff_jacobiSym_eq_neg_one]
    exact h3

end OMA.Helpers

open Filter in
theorem OMA.solution : OMA.R_Green47_green_47_variants_finite_exceptions_R1.H1 := by
  intro d hd
  by_contra hns
  obtain ⟨t, s, hst, htsq⟩ := Nat.sq_mul_squarefree d
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hns ⟨0, by simp⟩
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hd0
    rw [← hst]
    simp
  have ht0 : t ≠ 0 := htsq.ne_zero
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hns
    exact ⟨s, by rw [← hst]; ring⟩
  obtain ⟨b, hbodd, hbcop, hJ⟩ := OMA.Helpers.g47_exists_b t htsq ht1
  have hfr := OMA.Helpers.g47_frequently t b ht0 hbodd hbcop hJ
  obtain ⟨p, ⟨hsq, hpd⟩, hp, hJp⟩ :=
    ((hd.and (eventually_gt_atTop d)).and_frequently hfr).exists
  have := Fact.mk hp
  have hsqp := hsq hp
  apply (ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mp hJp)
  obtain ⟨x, hx⟩ := hsqp
  have hsle : s ≤ d := by
    rw [← hst]
    have h1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
    have h2 : s ≤ s ^ 2 := by nlinarith [Nat.one_le_iff_ne_zero.mpr hs0]
    nlinarith
  have hsne : (s : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hs0) h
    omega
  refine ⟨x / (s : ZMod p), ?_⟩
  rw [Int.cast_natCast]
  have hx' : (s : ZMod p) ^ 2 * (t : ZMod p) = x * x := by
    rw [← hx, ← hst]
    push_cast
    ring
  field_simp
  linear_combination hx'
