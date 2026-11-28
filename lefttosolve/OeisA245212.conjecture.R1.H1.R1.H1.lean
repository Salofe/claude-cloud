import OMAReductions.R_OeisA245212_conjecture_R1_H1_R1

/-!
# Step H1 of the reduction OeisA245212.conjecture.R1.H1.R1

Let n > 1 be odd, not a prime power, not of the form p^e q^f, and with n <= 2 phi(n).
Then n has k >= 3 distinct prime factors, all odd, and a(n) differs from sigma(n).

Write M(n) for the sum of d tau(d) over the divisors d of n and C(n) = n tau(n), so that
a(n) = 2 C(n) - M(n); it suffices to show M(n) + sigma(n) < 2 C(n). The functions M, sigma
and C are multiplicative, so after dividing by C(n) the left side is a sum of two products
over the prime factors p of n of the local ratios x_p = M(p^e)/C(p^e) and
y_p = sigma(p^e)/C(p^e). With c_p = 1/(p-1) one has (p-1) M(p^e) + sigma(p^e) = p C(p^e)
and 2 (p-1) sigma(p^e) <= p C(p^e), that is x_p = 1 + c_p - c_p y_p and
0 <= y_p <= (1 + c_p)/2, and 0 < c_p <= 1/2 because p >= 3.

Since n is odd, n <= 2 phi(n) forces n < 2 phi(n), which by Euler's product formula reads
Q < 2 for Q, the product of the 1 + c_p. Put u_p = y_p/(1 + c_p) in [0, 1/2], t_p = 2 u_p
in [0, 1] and a_p = 1 - c_p/2 in [0, 1]. Then x_p = (1 + c_p)(1 - t_p + t_p a_p), and an
induction over the prime factors gives the product of the 1 - t_p + t_p a_p at most
1 - T (1 - A), where T and A are the products of the t_p and of the a_p. The product of
the y_p equals Q T / 2^k <= Q T / 8. Moreover (Q A)^2 <= Q < 2 factor by factor, because
(1 + c)(1 - c/2)^2 <= 1, so Q A < 3/2. Altogether the normalised sum is at most
Q (1 - T) + T (Q A + Q/8), a convex combination of Q < 2 and Q A + Q/8 < 7/4, hence below 2.

Only the upstream definition OeisA245212.a is used, together with Mathlib.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OMA.Helpers

/-- A product of convex combinations `1 - t + t a` of `1` and `a` is bounded by the convex
combination of `1` and the product of the `a` with weight the product of the `t`. -/
theorem a245212_multiaffine (S : Finset ℕ) (t a : ℕ → ℚ)
    (ht : ∀ p ∈ S, 0 ≤ t p ∧ t p ≤ 1) (ha : ∀ p ∈ S, 0 ≤ a p ∧ a p ≤ 1) :
    ∏ p ∈ S, (1 - t p + t p * a p) ≤ 1 - (∏ p ∈ S, t p) * (1 - ∏ p ∈ S, a p) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [prod_insert hj, prod_insert hj, prod_insert hj]
    have ht' : ∀ p ∈ S, 0 ≤ t p ∧ t p ≤ 1 := fun p hp => ht p (mem_insert_of_mem hp)
    have ha' : ∀ p ∈ S, 0 ≤ a p ∧ a p ≤ 1 := fun p hp => ha p (mem_insert_of_mem hp)
    have ih' := ih ht' ha'
    obtain ⟨htj0, htj1⟩ := ht j (mem_insert_self j S)
    obtain ⟨haj0, haj1⟩ := ha j (mem_insert_self j S)
    have hT0 : 0 ≤ ∏ p ∈ S, t p := prod_nonneg fun p hp => (ht' p hp).1
    have hT1 : ∏ p ∈ S, t p ≤ 1 :=
      prod_le_one (fun p hp => (ht' p hp).1) fun p hp => (ht' p hp).2
    have hA1 : ∏ p ∈ S, a p ≤ 1 :=
      prod_le_one (fun p hp => (ha' p hp).1) fun p hp => (ha' p hp).2
    have hf0 : 0 ≤ 1 - t j + t j * a j := by nlinarith
    calc (1 - t j + t j * a j) * ∏ p ∈ S, (1 - t p + t p * a p)
        ≤ (1 - t j + t j * a j) * (1 - (∏ p ∈ S, t p) * (1 - ∏ p ∈ S, a p)) :=
          mul_le_mul_of_nonneg_left ih' hf0
      _ ≤ 1 - t j * (∏ p ∈ S, t p) * (1 - a j * ∏ p ∈ S, a p) := by
          nlinarith [mul_nonneg (mul_nonneg htj0 (sub_nonneg.2 haj1)) (sub_nonneg.2 hT1),
            mul_nonneg (mul_nonneg hT0 (sub_nonneg.2 hA1)) (sub_nonneg.2 htj1)]

/-- The normalised inequality: with `x_p = 1 + c_p - c_p y_p`, `0 ≤ y_p ≤ (1 + c_p) / 2`,
`0 < c_p ≤ 1 / 2`, at least three factors and `∏ (1 + c_p) < 2`, we get
`∏ x_p + ∏ y_p < 2`. -/
theorem a245212_key (S : Finset ℕ) (c x y : ℕ → ℚ)
    (hc : ∀ p ∈ S, 0 < c p ∧ c p ≤ 1 / 2)
    (hy : ∀ p ∈ S, 0 ≤ y p ∧ 2 * y p ≤ 1 + c p)
    (hx : ∀ p ∈ S, x p = 1 + c p - c p * y p)
    (hk : 3 ≤ S.card) (hQ : ∏ p ∈ S, (1 + c p) < 2) :
    ∏ p ∈ S, x p + ∏ p ∈ S, y p < 2 := by
  set u : ℕ → ℚ := fun p => y p / (1 + c p) with hu
  set t : ℕ → ℚ := fun p => 2 * u p with htdef
  set a : ℕ → ℚ := fun p => 1 - c p / 2 with hadef
  have hyu : ∀ p ∈ S, y p = (1 + c p) * u p := by
    intro p hp
    have : (1 + c p) ≠ 0 := by linarith [(hc p hp).1]
    simp only [hu]
    field_simp
  have hxu : ∀ p ∈ S, x p = (1 + c p) * (1 - t p + t p * a p) := by
    intro p hp
    rw [hx p hp, hyu p hp]
    simp only [htdef, hadef]
    ring
  have ht : ∀ p ∈ S, 0 ≤ t p ∧ t p ≤ 1 := by
    intro p hp
    obtain ⟨hc0, hc1⟩ := hc p hp
    obtain ⟨hy0, hy1⟩ := hy p hp
    have hpos : 0 < 1 + c p := by linarith
    simp only [htdef, hu]
    constructor
    · positivity
    · rw [mul_div_assoc', div_le_one hpos]
      linarith
  have ha : ∀ p ∈ S, 0 ≤ a p ∧ a p ≤ 1 := by
    intro p hp
    obtain ⟨hc0, hc1⟩ := hc p hp
    simp only [hadef]
    constructor <;> linarith
  have hX : ∏ p ∈ S, x p = (∏ p ∈ S, (1 + c p)) * ∏ p ∈ S, (1 - t p + t p * a p) := by
    rw [prod_congr rfl hxu, prod_mul_distrib]
  have hY : ∏ p ∈ S, y p = (∏ p ∈ S, (1 + c p)) * ∏ p ∈ S, u p := by
    rw [prod_congr rfl hyu, prod_mul_distrib]
  have hTU : ∏ p ∈ S, t p = 2 ^ S.card * ∏ p ∈ S, u p := by
    simp only [htdef]
    rw [prod_mul_distrib, prod_const]
  have hG := a245212_multiaffine S t a ht ha
  have hQA : ((∏ p ∈ S, (1 + c p)) * ∏ p ∈ S, a p) ^ 2 ≤ ∏ p ∈ S, (1 + c p) := by
    rw [← prod_mul_distrib, ← prod_pow]
    apply prod_le_prod
    · intro p _
      positivity
    · intro p hp
      obtain ⟨hc0, hc1⟩ := hc p hp
      simp only [hadef]
      nlinarith [mul_nonneg (mul_nonneg (show (0 : ℚ) ≤ 1 + c p by linarith) (sq_nonneg (c p)))
        (show (0 : ℚ) ≤ 3 - c p by linarith)]
  set Q := ∏ p ∈ S, (1 + c p) with hQdef
  set T := ∏ p ∈ S, t p with hTdef
  set A := ∏ p ∈ S, a p with hAdef
  set U := ∏ p ∈ S, u p with hUdef
  have hT0 : 0 ≤ T := prod_nonneg fun p hp => (ht p hp).1
  have hT1 : T ≤ 1 := prod_le_one (fun p hp => (ht p hp).1) fun p hp => (ht p hp).2
  have hA0 : 0 ≤ A := prod_nonneg fun p hp => (ha p hp).1
  have hQ0 : 0 < Q := prod_pos fun p hp => by linarith [(hc p hp).1]
  have h8 : (8 : ℚ) ≤ 2 ^ S.card := by
    have : (2 : ℚ) ^ 3 ≤ 2 ^ S.card := pow_le_pow_right₀ (by norm_num) hk
    norm_num at this
    linarith
  have hU0 : 0 ≤ U := prod_nonneg fun p hp => by
    have h1 := (hy p hp).1
    have h2 : 0 < 1 + c p := by linarith [(hc p hp).1]
    simp only [hu]
    positivity
  have hQA' : Q * A < 3 / 2 := by
    nlinarith [mul_nonneg hQ0.le hA0]
  have hQG : Q * ∏ p ∈ S, (1 - t p + t p * a p) ≤ Q * (1 - T * (1 - A)) :=
    mul_le_mul_of_nonneg_left hG hQ0.le
  have hU8 : U * 8 ≤ T := by
    rw [hTU]
    nlinarith [mul_le_mul_of_nonneg_right h8 hU0]
  have hQU : Q * U * 8 ≤ Q * T := by
    nlinarith [mul_le_mul_of_nonneg_left hU8 hQ0.le]
  rw [hX, hY]
  have hW : Q * A + Q / 8 < 7 / 4 := by linarith
  rcases le_or_gt Q (7 / 4) with hQ74 | hQ74
  · nlinarith [mul_le_mul_of_nonneg_right hQ74 (sub_nonneg.2 hT1),
      mul_le_mul_of_nonneg_left hW.le hT0]
  · nlinarith [mul_le_mul_of_nonneg_left (show Q * A + Q / 8 ≤ Q by linarith) hT0]

theorem a245212_card_pp (p e : ℕ) (hp : p.Prime) : #(p ^ e).divisors = e + 1 := by
  rw [← sigma_zero_apply, sigma_zero_apply_prime_pow hp]

/-- The divisor moment `n ↦ ∑_{d ∣ n} d τ(d)` is multiplicative: the divisors of `u v` are the
products of a divisor of `u` and a divisor of `v`, uniquely, and such factors are coprime. -/
theorem a245212_moment_mul (u v : ℕ) (hc : u.Coprime v) :
    (∑ d ∈ (u * v).divisors, d * #d.divisors) =
      (∑ d ∈ u.divisors, d * #d.divisors) * (∑ d ∈ v.divisors, d * #d.divisors) := by
  rw [Nat.divisors_mul, Finset.mul_def, sum_image hc.mul_injOn_divisors, sum_product, sum_mul_sum]
  refine sum_congr rfl fun d1 h1 => sum_congr rfl fun d2 h2 => ?_
  have hcop : d1.Coprime d2 :=
    (hc.coprime_dvd_left (Nat.dvd_of_mem_divisors h1)).coprime_dvd_right
      (Nat.dvd_of_mem_divisors h2)
  rw [hcop.card_divisors_mul]
  ring

theorem a245212_moment_pp (p e : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p ^ e).divisors, d * #d.divisors) = ∑ j ∈ range (e + 1), p ^ j * (j + 1) := by
  rw [Nat.sum_divisors_prime_pow hp]
  exact sum_congr rfl fun j _ => by rw [a245212_card_pp p j hp]

theorem a245212_sigma_pp (p e : ℕ) (hp : p.Prime) :
    σ 1 (p ^ e) = ∑ j ∈ range (e + 1), p ^ j := by
  rw [sigma_apply_prime_pow hp]
  simp only [mul_one]

/-- `(p - 1) A + B = p C` with `p = s + 1`. -/
theorem a245212_ident (s e : ℕ) :
    s * (∑ j ∈ range (e + 1), (s + 1) ^ j * (j + 1)) + (∑ j ∈ range (e + 1), (s + 1) ^ j) =
      (s + 1) * ((s + 1) ^ e * (e + 1)) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ (fun j => (s + 1) ^ j * (j + 1)) (e + 1),
      sum_range_succ (fun j => (s + 1) ^ j) (e + 1)]
    calc s * ((∑ j ∈ range (e + 1), (s + 1) ^ j * (j + 1)) + (s + 1) ^ (e + 1) * (e + 1 + 1)) +
          ((∑ j ∈ range (e + 1), (s + 1) ^ j) + (s + 1) ^ (e + 1))
        = (s * (∑ j ∈ range (e + 1), (s + 1) ^ j * (j + 1)) +
            (∑ j ∈ range (e + 1), (s + 1) ^ j)) +
            (s * ((s + 1) ^ (e + 1) * (e + 1 + 1)) + (s + 1) ^ (e + 1)) := by ring
      _ = (s + 1) * ((s + 1) ^ e * (e + 1)) +
            (s * ((s + 1) ^ (e + 1) * (e + 1 + 1)) + (s + 1) ^ (e + 1)) := by rw [ih]
      _ = (s + 1) * ((s + 1) ^ (e + 1) * (e + 1 + 1)) := by ring

theorem a245212_geom (s e : ℕ) :
    s * (∑ j ∈ range (e + 1), (s + 1) ^ j) + 1 = (s + 1) ^ (e + 1) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ (fun j => (s + 1) ^ j) (e + 1)]
    calc s * ((∑ j ∈ range (e + 1), (s + 1) ^ j) + (s + 1) ^ (e + 1)) + 1
        = (s * (∑ j ∈ range (e + 1), (s + 1) ^ j) + 1) + s * (s + 1) ^ (e + 1) := by ring
      _ = (s + 1) ^ (e + 1) + s * (s + 1) ^ (e + 1) := by rw [ih]
      _ = (s + 1) ^ (e + 1 + 1) := by ring

/-- At a prime power `p ^ e` with `e ≥ 1`, with `A = ∑_{d ∣ p^e} d τ(d)`, `B = σ(p^e)` and
`C = p^e τ(p^e)`: `(p - 1) A + B = p C` and `2 (p - 1) B ≤ p C`. -/
theorem a245212_local (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    0 < p ^ e * #(p ^ e).divisors ∧
    (p - 1) * (∑ d ∈ (p ^ e).divisors, d * #d.divisors) + σ 1 (p ^ e) =
      p * (p ^ e * #(p ^ e).divisors) ∧
    2 * (p - 1) * σ 1 (p ^ e) ≤ p * (p ^ e * #(p ^ e).divisors) := by
  rw [a245212_moment_pp p e hp, a245212_sigma_pp p e hp, a245212_card_pp p e hp]
  obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  have hid := a245212_ident s e
  have hg := a245212_geom s e
  rw [Nat.add_sub_cancel]
  refine ⟨by positivity, hid, ?_⟩
  have hX : 0 < (s + 1) ^ e := by positivity
  have hpow : (s + 1) ^ (e + 1) = (s + 1) * (s + 1) ^ e := by ring
  rw [hpow] at hg
  have h2 : 2 ≤ e + 1 := by omega
  nlinarith [Nat.mul_le_mul_left ((s + 1) * (s + 1) ^ e) h2]

/-- The local data in normalised rational form, with `s = p - 1`. -/
theorem a245212_ratio (s A B C : ℚ) (hs : 2 ≤ s) (hC : 0 < C) (h1 : s * A + B = (s + 1) * C)
    (h2 : 2 * s * B ≤ (s + 1) * C) (hB : 0 ≤ B) :
    A / C = 1 + 1 / s - 1 / s * (B / C) ∧ 0 ≤ B / C ∧ 2 * (B / C) ≤ 1 + 1 / s := by
  have hs0 : 0 < s := by linarith
  refine ⟨?_, by positivity, ?_⟩
  · have hA : A = ((s + 1) * C - B) / s := by
      field_simp
      linear_combination h1
    rw [hA]
    field_simp
  · rw [show 1 + 1 / s = (s + 1) / s by field_simp]
    rw [mul_div_assoc', div_le_div_iff₀ hC hs0]
    linarith

theorem a245212_local_q (p e : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (he : 0 < e) (A B C : ℕ)
    (hA : ∑ d ∈ (p ^ e).divisors, d * #d.divisors = A) (hB : σ 1 (p ^ e) = B)
    (hC : p ^ e * #(p ^ e).divisors = C) :
    (A : ℚ) / C = 1 + 1 / ((p : ℚ) - 1) - 1 / ((p : ℚ) - 1) * ((B : ℚ) / C) ∧
      0 ≤ (B : ℚ) / C ∧ 2 * ((B : ℚ) / C) ≤ 1 + 1 / ((p : ℚ) - 1) := by
  obtain ⟨hC0, h1, h2⟩ := a245212_local p e hp he
  rw [hA, hB, hC] at h1
  rw [hB, hC] at h2
  rw [hC] at hC0
  obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h1 h2
  have hs : ((s + 1 : ℕ) : ℚ) - 1 = (s : ℚ) := by push_cast; ring
  rw [hs]
  have h1' : (s : ℚ) * A + B = ((s : ℚ) + 1) * C := by exact_mod_cast h1
  have h2' : 2 * (s : ℚ) * B ≤ ((s : ℚ) + 1) * C := by exact_mod_cast h2
  have hs2 : (2 : ℚ) ≤ s := by exact_mod_cast (show 2 ≤ s by omega)
  have hC0' : (0 : ℚ) < C := by exact_mod_cast hC0
  exact a245212_ratio s A B C hs2 hC0' h1' h2' (by positivity)

end OMA.Helpers

open OMA.Helpers

theorem OMA.solution : OMA.R_OeisA245212_conjecture_R1_H1_R1.H1 := by
  intro n hn1 hodd hpp hphi hform
  have hn0 : n ≠ 0 := by omega
  have hphi' : n < 2 * n.totient := by
    rcases hodd with ⟨k, hk⟩
    omega
  -- the prime factors are odd primes with positive exponent
  have hS : ∀ p ∈ n.primeFactors, p.Prime ∧ 3 ≤ p ∧ 0 < n.factorization p := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    refine ⟨hpr, ?_, hpr.factorization_pos_of_dvd hn0 hdvd⟩
    have h2 := hpr.two_le
    by_contra hlt
    have h2' : p = 2 := by omega
    subst h2'
    rcases hodd with ⟨k, hk⟩
    omega
  -- at least three distinct prime factors
  have hcard : 3 ≤ n.primeFactors.card := by
    by_contra hlt
    have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn1
    have h1 : n.primeFactors.card ≠ 1 := fun h =>
      hpp (isPrimePow_iff_card_primeFactors_eq_one.mpr h)
    have h0 : n.primeFactors.card ≠ 0 := by
      intro h
      rw [Finset.card_eq_zero] at h
      rw [h] at hne
      exact Finset.not_nonempty_empty hne
    have h2 : n.primeFactors.card = 2 := by omega
    obtain ⟨x, y, hxy, hxyS⟩ := Finset.card_eq_two.mp h2
    apply hform
    have hx := hS x (by rw [hxyS]; simp)
    have hy := hS y (by rw [hxyS]; simp)
    have hn_eq : n = x ^ n.factorization x * y ^ n.factorization y := by
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
      rw [Nat.prod_factorization_eq_prod_primeFactors, hxyS, Finset.prod_pair hxy]
    have five (q r : ℕ) (hq : q.Prime) (hr3 : 3 ≤ r) (hrq : r < q) : 5 ≤ q := by
      by_contra hlt
      have h4 : q = 4 := by omega
      subst h4
      norm_num at hq
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨x, y, _, _, hx.1, hy.1, h, hx.2.1, five y x hy.1 hx.2.1 h, hx.2.2, hy.2.2, hn_eq⟩
    · exact ⟨y, x, _, _, hy.1, hx.1, h, hy.2.1, five x y hx.1 hy.2.1 h, hy.2.2, hx.2.2,
        hn_eq.trans (mul_comm _ _)⟩
  -- per-prime data
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ → ℚ, ∀ p, c p = 1 / ((p : ℚ) - 1) := ⟨_, fun p => rfl⟩
  obtain ⟨Af, hAf⟩ : ∃ Af : ℕ → ℕ, ∀ p,
      Af p = ∑ d ∈ (p ^ n.factorization p).divisors, d * #d.divisors := ⟨_, fun p => rfl⟩
  obtain ⟨Bf, hBf⟩ : ∃ Bf : ℕ → ℕ, ∀ p, Bf p = σ 1 (p ^ n.factorization p) :=
    ⟨_, fun p => rfl⟩
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℕ → ℕ, ∀ p,
      Cf p = p ^ n.factorization p * #(p ^ n.factorization p).divisors := ⟨_, fun p => rfl⟩
  -- multiplicative decompositions over the prime factors
  have hMul : ∀ f : ℕ → ℕ, (∀ x y, x.Coprime y → f (x * y) = f x * f y) → f 1 = 1 →
      f n = ∏ p ∈ n.primeFactors, f (p ^ n.factorization p) := fun f hf h1 =>
    Nat.multiplicative_factorization f hf h1 hn0
  have hAprod : (∑ d ∈ n.divisors, d * #d.divisors) = ∏ p ∈ n.primeFactors, Af p := by
    rw [prod_congr rfl fun p _ => hAf p]
    exact hMul (fun m => ∑ d ∈ m.divisors, d * #d.divisors) a245212_moment_mul (by simp)
  have hBprod : σ 1 n = ∏ p ∈ n.primeFactors, Bf p := by
    rw [prod_congr rfl fun p _ => hBf p]
    exact hMul (σ 1) (fun x y h => isMultiplicative_sigma.map_mul_of_coprime h)
      isMultiplicative_sigma.map_one
  have hCprod : n * #n.divisors = ∏ p ∈ n.primeFactors, Cf p := by
    rw [prod_congr rfl fun p _ => hCf p]
    exact hMul (fun m => m * #m.divisors) (fun x y h => by
      rw [Nat.Coprime.card_divisors_mul h]
      ring) (by simp)
  -- local inequalities
  have hloc : ∀ p ∈ n.primeFactors, (Af p : ℚ) / Cf p = 1 + c p - c p * ((Bf p : ℚ) / Cf p) ∧
      0 ≤ (Bf p : ℚ) / Cf p ∧ 2 * ((Bf p : ℚ) / Cf p) ≤ 1 + c p := by
    intro p hp
    obtain ⟨hpr, hp3, he⟩ := hS p hp
    rw [hcdef]
    exact a245212_local_q p _ hpr hp3 he (Af p) (Bf p) (Cf p) (hAf p).symm (hBf p).symm
      (hCf p).symm
  have hc : ∀ p ∈ n.primeFactors, 0 < c p ∧ c p ≤ 1 / 2 := by
    intro p hp
    have hp3 : (3 : ℚ) ≤ p := by exact_mod_cast (hS p hp).2.1
    rw [hcdef]
    constructor
    · exact div_pos one_pos (by linarith)
    · rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
  -- the totient hypothesis in product form
  have hQ : ∏ p ∈ n.primeFactors, (1 + c p) < 2 := by
    have htot := Nat.totient_eq_mul_prod_factors n
    have hprod : (∏ p ∈ n.primeFactors, (1 + c p)) *
        ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) = 1 := by
      rw [← prod_mul_distrib]
      apply prod_eq_one
      intro p hp
      have hp3 : (3 : ℚ) ≤ p := by exact_mod_cast (hS p hp).2.1
      rw [hcdef]
      have h1 : (p : ℚ) - 1 ≠ 0 := by linarith
      have h2 : (p : ℚ) ≠ 0 := by linarith
      field_simp
      ring
    have hn' : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
    have hphiQ : (n : ℚ) < 2 * (n.totient : ℚ) := by exact_mod_cast hphi'
    rw [htot] at hphiQ
    have hP : 1 < 2 * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) := by
      by_contra hcon
      have hcon' := not_lt.mp hcon
      nlinarith [mul_le_mul_of_nonneg_left hcon' hn'.le]
    have hQ0 : 0 < ∏ p ∈ n.primeFactors, (1 + c p) :=
      prod_pos fun p hp => by linarith [(hc p hp).1]
    by_contra hcon
    have hcon' := not_lt.mp hcon
    nlinarith [mul_le_mul_of_nonneg_right hcon'
      (show (0 : ℚ) ≤ ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) by linarith)]
  have hkey := a245212_key n.primeFactors c (fun p => (Af p : ℚ) / Cf p)
    (fun p => (Bf p : ℚ) / Cf p) hc (fun p hp => (hloc p hp).2) (fun p hp => (hloc p hp).1)
    hcard hQ
  have hC0 : (0 : ℚ) < ((n * #n.divisors : ℕ) : ℚ) := by
    have : 0 < #n.divisors := card_pos.mpr ⟨n, Nat.mem_divisors.mpr ⟨dvd_refl _, hn0⟩⟩
    exact_mod_cast Nat.mul_pos (by omega) this
  have hsum : ((∑ d ∈ n.divisors, d * #d.divisors : ℕ) : ℚ) / ((n * #n.divisors : ℕ) : ℚ) +
      ((σ 1 n : ℕ) : ℚ) / ((n * #n.divisors : ℕ) : ℚ) < 2 := by
    rw [hAprod, hBprod, hCprod, Nat.cast_prod, Nat.cast_prod, Nat.cast_prod, ← prod_div_distrib,
      ← prod_div_distrib]
    exact hkey
  rw [← add_div, div_lt_iff₀ hC0] at hsum
  -- a n in terms of the full divisor moment
  have ha : OeisA245212.a n = 2 * (n : ℤ) * (#n.divisors : ℤ) -
      ((∑ d ∈ n.divisors, d * #d.divisors : ℕ) : ℤ) := by
    have hsplit : (∑ d ∈ n.divisors, d * #d.divisors) =
        n * #n.divisors + ∑ d ∈ n.properDivisors, d * #d.divisors := by
      conv_lhs => rw [← Nat.insert_self_properDivisors hn0]
      rw [sum_insert Nat.self_notMem_properDivisors]
    unfold OeisA245212.a
    rw [hsplit]
    push_cast
    ring
  intro heq
  rw [ha] at heq
  have heqQ : ((2 * (n : ℤ) * (#n.divisors : ℤ) -
      ((∑ d ∈ n.divisors, d * #d.divisors : ℕ) : ℤ) : ℤ) : ℚ) = (((σ 1 n : ℕ) : ℤ) : ℚ) := by
    rw [heq]
  push_cast at heqQ hsum
  linarith
