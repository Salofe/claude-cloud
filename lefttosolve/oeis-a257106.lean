import OMAStatements.S_oeis_a257106
import Mathlib

/-!
From `sum_bernoulli'` one gets `c n = B(n) - (-1)^n n / 6`. For odd `n = 2m+1 ≥ 3` this is
`(2m+1)/6`, whose denominator is `2` or `6`. For `n = 2m`, `m ≥ 1`, von Staudt-Clausen gives
that `y = B(2m) + 1/3` has denominator prime to `3`; then `B(2m) = y - 1/3` has denominator
`3 y.den`, and `c(2m) = y - (m+1)/3` has denominator `y.den` when `3 ∣ m+1` and `3 y.den`
otherwise.
-/

namespace OMA.Helpers

open OMA.S_oeis_a257106 Finset

/-- Inverse binomial transform of Mathlib's Bernoulli numbers. -/
theorem inv_binom_bernoulli (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * bernoulli k =
      bernoulli n + (-1) ^ n * n := by
  have hB : ∀ k, bernoulli k = (-1) ^ k * bernoulli' k := by
    intro k
    rw [bernoulli'_eq_bernoulli, ← mul_assoc, ← mul_pow]
    norm_num
  have h1 : ∀ k ∈ range (n + 1), (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * bernoulli k =
      (-1) ^ n * ((n.choose k : ℚ) * bernoulli' k) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
    rw [hB k]
    have : (-1 : ℚ) ^ (n - k) * (-1) ^ k = (-1) ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hkn]
    calc (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * ((-1) ^ k * bernoulli' k)
        = ((-1 : ℚ) ^ (n - k) * (-1) ^ k) * ((n.choose k : ℚ) * bernoulli' k) := by ring
      _ = _ := by rw [this]
  rw [sum_congr rfl h1, ← mul_sum, sum_range_succ, sum_bernoulli', Nat.choose_self,
    Nat.cast_one, one_mul, hB n]
  ring

theorem c_eq (n : ℕ) : c n = bernoulli n - (-1) ^ n * n / 6 := by
  have hb : ∀ k, b k = bernoulli k + (if k = 1 then 7 / 6 else 0) := by
    intro k
    unfold b
    split_ifs with h
    · subst h
      rw [bernoulli_one]
      norm_num
    · ring
  unfold c
  simp only [hb, mul_add, sum_add_distrib, inv_binom_bernoulli]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : ∑ k ∈ range (n + 1), (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) *
        (if k = 1 then 7 / 6 else 0) = (-1 : ℚ) ^ (n - 1) * n * (7 / 6) := by
      rw [sum_eq_single 1]
      · simp
      · intro k _ hk
        simp [hk]
      · intro h
        exact absurd (mem_range.2 (by omega)) h
    rw [this]
    have e : (-1 : ℚ) ^ n = - (-1) ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ]
      ring
    rw [e]
    ring

/-- The denominator of `r / 3` when `3 ∤ r`. -/
theorem den_div_three (r : ℤ) (hr : ¬ (3 : ℤ) ∣ r) : ((r : ℚ) / 3).den = 3 := by
  have hc : Nat.Coprime r.natAbs (3 : ℤ).natAbs := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ?_)
    intro h
    exact hr (Int.ofNat_dvd_left.2 h)
  have := Rat.den_div_eq_of_coprime (by norm_num : (0 : ℤ) < 3) hc
  have h' : ((r : ℚ) / ((3 : ℤ) : ℚ)) = (r : ℚ) / 3 := by norm_num
  rw [h'] at this
  omega

theorem den_add_div_three (y : ℚ) (r : ℤ) (hy : ¬ 3 ∣ y.den) (hr : ¬ (3 : ℤ) ∣ r) :
    (y + (r : ℚ) / 3).den = 3 * y.den := by
  set z := y + (r : ℚ) / 3 with hz
  have ha : z.den ∣ y.den * 3 := by
    have := Rat.add_den_dvd y ((r : ℚ) / 3)
    rwa [den_div_three r hr] at this
  have hb : y.den ∣ z.den * 3 := by
    have e : y = z + ((-r : ℤ) : ℚ) / 3 := by
      rw [hz]
      push_cast
      ring
    have := Rat.add_den_dvd z (((-r : ℤ) : ℚ) / 3)
    rw [den_div_three (-r) (by rwa [Int.dvd_neg]), ← e] at this
    exact this
  have hc : 3 ∣ z.den * y.den := by
    have e : (r : ℚ) / 3 = z - y := by
      rw [hz]
      ring
    have := Rat.sub_den_dvd z y
    rw [← e, den_div_three r hr] at this
    exact this
  have hd : 3 ∣ z.den := ((Nat.Prime.dvd_mul Nat.prime_three).1 hc).resolve_right hy
  obtain ⟨e, he⟩ := hd
  have hcop : Nat.Coprime y.den 3 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hy)
  have h1 : y.den ∣ e := by
    have hb' : y.den ∣ 3 * (3 * e) := by
      rw [he] at hb
      rw [show 3 * (3 * e) = 3 * e * 3 by ring]
      exact hb
    exact hcop.dvd_of_dvd_mul_left (hcop.dvd_of_dvd_mul_left hb')
  apply Nat.dvd_antisymm
  · rw [mul_comm]
    exact ha
  · rw [he]
    exact Nat.mul_dvd_mul_left 3 h1

theorem den_add_div_three' (y : ℚ) (r : ℤ) (hr : (3 : ℤ) ∣ r) :
    (y + (r : ℚ) / 3).den = y.den := by
  obtain ⟨t, rfl⟩ := hr
  have : (((3 * t : ℤ) : ℚ) / 3) = ((t : ℤ) : ℚ) := by
    push_cast
    ring
  rw [this, Rat.add_intCast_den]

theorem den_sum_dvd (T : Finset ℕ) (f : ℕ → ℚ) :
    (∑ i ∈ T, f i).den ∣ ∏ i ∈ T, (f i).den := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [sum_insert hx, prod_insert hx]
    exact (Rat.add_den_dvd _ _).trans (Nat.mul_dvd_mul_left _ ih)

/-- From von Staudt-Clausen: `3` does not divide the denominator of `B(2m) + 1/3`. -/
theorem three_not_dvd (m : ℕ) (hm : 1 ≤ m) : ¬ 3 ∣ (bernoulli (2 * m) + 1 / 3).den := by
  obtain ⟨N, hN⟩ := Bernoulli.vonStaudt_clausen m
  set F := (range (2 * m + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ 2 * m) with hF
  have h3F : 3 ∈ F := by
    rw [hF, mem_filter, mem_range]
    exact ⟨by omega, Nat.prime_three, ⟨m, by omega⟩⟩
  rw [← add_sum_erase F _ h3F] at hN
  have key : bernoulli (2 * m) + 1 / 3 =
      (N : ℚ) - ∑ p ∈ F.erase 3, (1 : ℚ) / (p : ℚ) := by
    rw [hN]
    push_cast
    ring
  rw [key, Rat.intCast_sub_den]
  intro h
  have h2 := h.trans (den_sum_dvd (F.erase 3) (fun p => (1 : ℚ) / (p : ℚ)))
  obtain ⟨p, hp, hdvd⟩ := (Nat.prime_three.prime.dvd_finsetProd_iff _).1 h2
  have hp3 : p ≠ 3 := (mem_erase.1 hp).1
  have hpF : p ∈ F := (mem_erase.1 hp).2
  rw [hF, mem_filter] at hpF
  have hpp : p.Prime := hpF.2.1
  have : ((1 : ℚ) / (p : ℚ)).den = p := by
    rw [one_div]
    exact Rat.inv_natCast_den_of_pos hpp.pos
  rw [this] at hdvd
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).1 hdvd).symm

theorem den_natCast_div (a b : ℕ) (hb : 0 < b) (h : Nat.Coprime a b) :
    ((a : ℚ) / (b : ℚ)).den = b := by
  have := Rat.den_div_eq_of_coprime (a := (a : ℤ)) (b := (b : ℤ)) (by exact_mod_cast hb)
    (by simpa using h)
  have h' : (((a : ℤ) : ℚ) / ((b : ℤ) : ℚ)) = (a : ℚ) / (b : ℚ) := by push_cast; rfl
  rw [h'] at this
  omega

theorem odd_part (n : ℕ) : a (2 * n + 1) = if n = 0 then 3 else if n % 3 = 1 then 2 else 6 := by
  unfold a
  rw [c_eq]
  have hs : (-1 : ℚ) ^ (2 * n + 1) = -1 := by
    rw [pow_succ, pow_mul]
    norm_num
  rw [hs]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have e : bernoulli (2 * 0 + 1) - -1 * ((2 * 0 + 1 : ℕ) : ℚ) / 6 = ((-1 : ℤ) : ℚ) / 3 := by
      rw [show 2 * 0 + 1 = 1 by rfl, bernoulli_one]
      norm_num
    rw [e, den_div_three (-1) (by omega)]
    rfl
  · rw [bernoulli_eq_zero_of_odd ⟨n, rfl⟩ (by omega), if_neg (by omega)]
    split_ifs with h1
    · obtain ⟨j, hj⟩ : ∃ j, n = 3 * j + 1 := ⟨n / 3, by omega⟩
      have e : (0 : ℚ) - -1 * ((2 * n + 1 : ℕ) : ℚ) / 6 = ((2 * j + 1 : ℕ) : ℚ) / ((2 : ℕ) : ℚ) := by
        rw [hj]
        push_cast
        ring
      rw [e, den_natCast_div _ _ (by norm_num)]
      have : Nat.gcd 2 (2 * j + 1) = 1 := by
        rw [Nat.gcd_rec, show (2 * j + 1) % 2 = 1 by omega]
        rfl
      exact (show Nat.Coprime 2 (2 * j + 1) from this).symm
    · have e : (0 : ℚ) - -1 * ((2 * n + 1 : ℕ) : ℚ) / 6 = ((2 * n + 1 : ℕ) : ℚ) / ((6 : ℕ) : ℚ) := by
        push_cast
        ring
      rw [e, den_natCast_div _ _ (by norm_num)]
      have : Nat.gcd 6 (2 * n + 1) = 1 := by
        rw [Nat.gcd_rec]
        rcases (by omega : (2 * n + 1) % 6 = 1 ∨ (2 * n + 1) % 6 = 5) with h | h <;> rw [h] <;> rfl
      exact (show Nat.Coprime 6 (2 * n + 1) from this).symm

theorem even_part (n : ℕ) :
    (a (2 * n) : ℚ) = (A002445 n : ℚ) / (if n % 3 = 2 then 3 else 1) := by
  unfold a A002445
  rw [c_eq]
  have hs : (-1 : ℚ) ^ (2 * n) = 1 := by
    rw [pow_mul]
    norm_num
  rw [hs]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hy := three_not_dvd n hn
    set y := bernoulli (2 * n) + 1 / 3 with hydef
    have hB : bernoulli (2 * n) = y + ((-1 : ℤ) : ℚ) / 3 := by
      rw [hydef]
      push_cast
      ring
    have hBd : (bernoulli (2 * n)).den = 3 * y.den := by
      rw [hB]
      exact den_add_div_three y (-1) hy (by omega)
    have hc : bernoulli (2 * n) - 1 * ((2 * n : ℕ) : ℚ) / 6 = y + ((-((n : ℤ) + 1) : ℤ) : ℚ) / 3 := by
      rw [hB]
      push_cast
      ring
    rw [hc, hBd]
    split_ifs with h2
    · rw [den_add_div_three' y (-((n : ℤ) + 1)) (by omega)]
      push_cast
      ring
    · rw [den_add_div_three y (-((n : ℤ) + 1)) hy (by omega)]
      push_cast
      ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a257106.main :=
  ⟨OMA.Helpers.odd_part, OMA.Helpers.even_part⟩
