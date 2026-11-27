import OMAReductions.R_OeisA2426_conjecture_R1

/-!
# Step H1 of reduction OeisA2426.conjecture.R1

Every prime `p > 3` satisfies `a(p) = 1 mod p^2`, where `a(n)` is the central trinomial
coefficient (Z.-W. Sun's observation).

Proof. Over the integers, `(X - 1)^p * (1 + X + X^2)^p = (X^3 - 1)^p = expand 3 ((X - 1)^p)`,
whose `X^p` coefficient is `0` because `3` does not divide `p`. Expanding the left-hand side, the
`X^p` coefficient is the sum over `i + j = p` of `c_i * d_j`, with `c` the coefficients of
`(X - 1)^p` and `d` those of `(1 + X + X^2)^p`. By Frobenius in `(ZMod p)[X]`, every coefficient
of a `p`-th power whose index is not a multiple of `p` is divisible by `p`, so each middle term
(`0 < i < p`) is divisible by `p^2`. The two outer terms are `c_0 * d_p = -a(p)` (`p` is odd, and
`d_p = a(p)` by the binomial expansion of `((1 + X^2) + X)^n`) and `c_p * d_0 = 1`. Hence `p^2`
divides `a(p) - 1`.
-/

open Polynomial Finset

namespace OMA.Helpers.A2426

/-- Frobenius: if `p` is prime and `p` does not divide `j`, then `p` divides the `j`-th
coefficient of `f ^ p` for every integer polynomial `f`. -/
theorem dvd_coeff_pow (f : ℤ[X]) (p : ℕ) [hp : Fact p.Prime] (j : ℕ) (hj : ¬ p ∣ j) :
    (p : ℤ) ∣ (f ^ p).coeff j := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h1 : (((f ^ p).coeff j : ℤ) : ZMod p) =
      ((f ^ p).map (Int.castRingHom (ZMod p))).coeff j := by
    rw [Polynomial.coeff_map]; rfl
  rw [h1, Polynomial.map_pow, ← ZMod.expand_card, Polynomial.coeff_expand hp.out.pos, if_neg hj]

/-- Summing a function over the even indices `m ≤ n` is summing it at `2 * k` for `k ≤ n / 2`. -/
theorem sum_even (g : ℕ → ℕ) : ∀ n : ℕ,
    ∑ m ∈ range (n + 1), (if 2 ∣ m then g m else 0) = ∑ k ∈ range (n / 2 + 1), g (2 * k)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_even g n]
    by_cases h : 2 ∣ n + 1
    · have h1 : (n + 1) / 2 + 1 = (n / 2 + 1) + 1 := by omega
      rw [h1, Finset.sum_range_succ (fun k => g (2 * k)) (n / 2 + 1), if_pos h]
      have h2 : n + 1 = 2 * (n / 2 + 1) := by omega
      rw [← h2]
    · have h1 : (n + 1) / 2 = n / 2 := by omega
      rw [h1, if_neg h, add_zero]

/-- The `m`-th coefficient of `(1 + X^2)^m`. -/
theorem coeff_one_add_X_sq_pow (m : ℕ) :
    ((1 + X ^ 2 : ℤ[X]) ^ m).coeff m = if 2 ∣ m then (m.choose (m / 2) : ℤ) else 0 := by
  have h : (1 + X ^ 2 : ℤ[X]) ^ m = expand ℤ 2 ((1 + X) ^ m) := by
    simp [map_pow, map_add, expand_X]
  rw [h, coeff_expand (by norm_num), coeff_one_add_X_pow]

/-- The central trinomial coefficient is the `n`-th coefficient of `(1 + X + X^2)^n`. -/
theorem coeff_trinomial (n : ℕ) :
    ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff n = (OeisA2426.a n : ℤ) := by
  have e : (1 + X + X ^ 2 : ℤ[X]) = (1 + X ^ 2) + X := by ring
  rw [e, add_pow, finsetSum_coeff]
  have h : ∀ m ∈ range (n + 1),
      (((1 + X ^ 2 : ℤ[X]) ^ m * X ^ (n - m) * (n.choose m : ℤ[X])).coeff n)
        = ((if 2 ∣ m then n.choose m * m.choose (m / 2) else 0 : ℕ) : ℤ) := by
    intro m hm
    have hm' : m ≤ n := by simpa [Nat.lt_succ_iff] using hm
    rw [← Polynomial.C_eq_natCast, Polynomial.coeff_mul_C, coeff_mul_X_pow',
      if_pos (Nat.sub_le n m), Nat.sub_sub_self hm', coeff_one_add_X_sq_pow]
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl h, ← Nat.cast_sum, sum_even]
  unfold OeisA2426.a
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.mul_div_cancel_left k (by norm_num)]

/-- For `p` prime, the `p`-th coefficient of `f^p * g^p` agrees modulo `p^2` with its two
outer terms. -/
theorem key (f g : ℤ[X]) (p : ℕ) [hp : Fact p.Prime] :
    ((p : ℤ) ^ 2) ∣ (f ^ p * g ^ p).coeff p -
      ((f ^ p).coeff 0 * (g ^ p).coeff p + (f ^ p).coeff p * (g ^ p).coeff 0) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (f ^ p).coeff i * (g ^ p).coeff j)]
  rw [Finset.range_eq_Ico, Finset.sum_Ico_succ_top (Nat.zero_le p),
    Finset.sum_eq_sum_Ico_succ_bot hp.out.pos]
  have hmid : ((p : ℤ) ^ 2) ∣ ∑ k ∈ Ico (0 + 1) p, (f ^ p).coeff k * (g ^ p).coeff (p - k) := by
    apply Finset.dvd_sum
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [pow_two]
    apply mul_dvd_mul
    · apply dvd_coeff_pow
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    · apply dvd_coeff_pow
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
  simp only [Nat.sub_zero, Nat.sub_self]
  convert hmid using 1
  ring

/-- Sun's congruence for the central trinomial coefficients at primes `p > 3`. -/
theorem main_thm (p : ℕ) (h3 : 3 < p) (hp : p.Prime) : OeisA2426.a p ≡ 1 [MOD p ^ 2] := by
  have := Fact.mk hp
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h3p : ¬ 3 ∣ p := by
    intro h
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp 3 h) with h' | h' <;> omega
  have hk := key (X - 1) (1 + X + X ^ 2) p
  have e1 : (X - 1 : ℤ[X]) ^ p * (1 + X + X ^ 2) ^ p = expand ℤ 3 ((X - 1) ^ p) := by
    rw [← mul_pow]; simp only [map_pow, map_sub, expand_X, map_one]; ring
  have e2 : ((X - 1 : ℤ[X]) ^ p * (1 + X + X ^ 2) ^ p).coeff p = 0 := by
    rw [e1, coeff_expand (by norm_num), if_neg h3p]
  have e3 : ((X - 1 : ℤ[X]) ^ p).coeff 0 = -1 := by
    rw [coeff_zero_eq_eval_zero]; simp [hodd.neg_one_pow]
  have e4 : ((X - 1 : ℤ[X]) ^ p).coeff p = 1 := by
    have : (X - 1 : ℤ[X]) = X + C (-1) := by simp [sub_eq_add_neg]
    rw [this, coeff_X_add_C_pow]; simp
  have e5 : ((1 + X + X ^ 2 : ℤ[X]) ^ p).coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero]; simp
  rw [e2, e3, e4, e5, coeff_trinomial] at hk
  rw [Nat.modEq_iff_dvd]
  push_cast
  have : (1 : ℤ) - (OeisA2426.a p : ℤ) = -(0 - (-1 * (OeisA2426.a p : ℤ) + 1 * 1)) := by ring
  rw [this]; exact dvd_neg.mpr hk

end OMA.Helpers.A2426

theorem OMA.solution : OMA.R_OeisA2426_conjecture_R1.H1 := by
  intro p h3 hp
  exact OMA.Helpers.A2426.main_thm p h3 hp
