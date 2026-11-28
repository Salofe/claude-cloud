import OMAStatements.S_oeis_a079665
import Mathlib


namespace OMA.Helpers

/-- If `b ^ r + 1` divides `b ^ s + 1` then `s` is an odd multiple of `r`. -/
theorem odd_mul_of_dvd {b r s : ℕ} (hb : 2 ≤ b) (hr : 1 ≤ r)
    (h : b ^ r + 1 ∣ b ^ s + 1) : ∃ q, Odd q ∧ s = r * q := by
  set q := s / r with hq
  set e := s % r with he
  have hs : s = r * q + e := (Nat.div_add_mod s r).symm
  have her : e < r := Nat.mod_lt s (by omega)
  have hlt : b ^ e < b ^ r := Nat.pow_lt_pow_right (by omega) her
  have hpos : 1 ≤ b ^ e := Nat.one_le_pow _ _ (by omega)
  -- work over the integers
  have hZ : ((b : ℤ) ^ r + 1) ∣ (b : ℤ) ^ s + 1 := by exact_mod_cast h
  have hgeo : ((b : ℤ) ^ r + 1) ∣ ((b : ℤ) ^ r) ^ q - (-1) ^ q := by
    have := sub_dvd_pow_sub_pow ((b : ℤ) ^ r) (-1) q
    simpa [sub_neg_eq_add] using this
  have hsplit : (b : ℤ) ^ s + 1 =
      (b : ℤ) ^ e * (((b : ℤ) ^ r) ^ q - (-1) ^ q) + ((b : ℤ) ^ e * (-1) ^ q + 1) := by
    rw [hs, pow_add, pow_mul]; ring
  have hrest : ((b : ℤ) ^ r + 1) ∣ (b : ℤ) ^ e * (-1) ^ q + 1 := by
    have h2 := dvd_sub hZ (Dvd.dvd.mul_left hgeo ((b : ℤ) ^ e))
    rw [hsplit] at h2
    simpa using h2
  rcases Nat.even_or_odd q with hev | hodd
  · exfalso
    rw [hev.neg_one_pow, mul_one] at hrest
    have hN : b ^ r + 1 ∣ b ^ e + 1 := by exact_mod_cast hrest
    have := Nat.le_of_dvd (by omega) hN
    omega
  · rw [hodd.neg_one_pow, mul_neg_one] at hrest
    have hz : -(b : ℤ) ^ e + 1 = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd hrest
      have h1 : (1 : ℤ) ≤ (b : ℤ) ^ e := by exact_mod_cast hpos
      have h2 : (b : ℤ) ^ e < (b : ℤ) ^ r := by exact_mod_cast hlt
      rw [abs_lt]; constructor <;> linarith
    have hbe : b ^ e = 1 := by
      have : (b : ℤ) ^ e = 1 := by linarith
      exact_mod_cast this
    have he0 : e = 0 := by
      rcases Nat.pow_eq_one.1 hbe with h1 | h1
      · omega
      · exact h1
    exact ⟨q, hodd, by omega⟩

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a079665.main := by
  intro b hb s r hr hrs
  constructor
  · intro h
    obtain ⟨q, hq, hsq⟩ := OMA.Helpers.odd_mul_of_dvd hb hr h
    refine ⟨?_, fun _ => ⟨q, hsq⟩, ?_⟩
    · obtain ⟨m, rfl⟩ := hq
      have hm : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · subst h0; simp at hsq; omega
        · exact h0
      rw [hsq]; nlinarith
    · intro k t hk _
      have hcop : Nat.Coprime (2 ^ t) q := Nat.Coprime.pow_left t (Nat.coprime_two_left.2 hq)
      have hdvd : 2 ^ t ∣ r * q := ⟨k, by rw [← hsq, hk, mul_comm]⟩
      obtain ⟨u, rfl⟩ := hcop.dvd_of_dvd_mul_right hdvd
      refine ⟨u, rfl, q, ?_⟩
      have hpos : 0 < 2 ^ t := by positivity
      apply Nat.eq_of_mul_eq_mul_left hpos
      rw [mul_comm (2 ^ t) k, ← hk, hsq]; ring
  · rintro ⟨_, _, h3⟩
    obtain ⟨t, m, hm, hsm⟩ := Nat.exists_eq_two_pow_mul_odd (n := s) (by omega)
    have hcop : Nat.Coprime m (2 ^ t) := Nat.Coprime.pow_right t (Nat.coprime_two_right.2 hm)
    obtain ⟨u, hru, q, hq⟩ := h3 m t (by rw [hsm, mul_comm]) hcop
    have hqodd : Odd q := by
      have hum : Odd (u * q) := hq ▸ hm
      exact (Nat.odd_mul.1 hum).2
    have hs : s = r * q := by rw [hsm, hru, hq]; ring
    rw [hs, pow_mul]
    simpa using hqodd.nat_add_dvd_pow_add_pow (b ^ r) 1
