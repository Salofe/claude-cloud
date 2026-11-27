import OMAReductions.R_OeisA245212_conjecture_R1_H1_R1_H2_R1

/-!
# Step H3 of the reduction OeisA245212.conjecture.R1.H1.R1.H2.R1

For n = 3 p^e q^f r^g with primes 5 <= p < q < r and positive exponents, the gap
a(n) - sigma(n) is at least (37/288) n tau(n).

Write M(n) for the sum of d tau(d) over the divisors d of n, so that a(n) = 2 n tau(n) - M(n).
M, sigma and n tau(n) are multiplicative. At a prime power p^e put A = M(p^e), B = sigma(p^e)
and C = p^e (e+1); then (p-1) A + B = p C and 2 (p-1) B <= p C when e >= 1. After normalising
by C the claim becomes 336 a_p a_q a_r + 192 b_p b_q b_r <= 539, where (p-1) a + b = p.
For p = 5 or p = 7 the b-terms are traded against the a-term of p; for p >= 11 crude bounds
suffice. The constant is sharp: equality is approached for p, q, r = 5, 7, 11 and large exponents.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OMA.Helpers

/-- The divisor moment `n ↦ ∑_{d ∣ n} d τ(d)` is multiplicative. -/
theorem a245212_moment_mul (u v : ℕ) (hc : u.Coprime v) :
    (∑ d ∈ (u * v).divisors, d * #d.divisors) =
      (∑ d ∈ u.divisors, d * #d.divisors) * (∑ d ∈ v.divisors, d * #d.divisors) := by
  have hm : ((ArithmeticFunction.id.pmul (σ 0)) * ArithmeticFunction.zeta : ArithmeticFunction ℕ).IsMultiplicative :=
    (isMultiplicative_id.pmul isMultiplicative_sigma).mul isMultiplicative_zeta
  have he (n : ℕ) : ((ArithmeticFunction.id.pmul (σ 0)) * ArithmeticFunction.zeta : ArithmeticFunction ℕ) n =
      ∑ d ∈ n.divisors, d * #d.divisors := by
    rw [mul_zeta_apply]
    simp only [pmul_apply, id_apply, sigma_zero_apply]
  rw [← he, ← he, ← he]
  exact hm.map_mul_of_coprime hc

theorem a245212_moment_pp (p e : ℕ) (hp : p.Prime) :
    (∑ d ∈ (p ^ e).divisors, d * #d.divisors) = ∑ j ∈ range (e + 1), p ^ j * (j + 1) := by
  rw [Nat.sum_divisors_prime_pow hp]
  refine sum_congr rfl fun j _ => ?_
  rw [Nat.divisors_prime_pow hp, card_map, card_range]

theorem a245212_card_pp (p e : ℕ) (hp : p.Prime) : #(p ^ e).divisors = e + 1 := by
  rw [Nat.divisors_prime_pow hp, card_map, card_range]

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

theorem a245212_abound (x a b m : ℚ) (h : (x - 1) * a + b = x) (hb : 0 ≤ b) (ha : 0 ≤ a)
    (hm : 2 ≤ m) (hx : m ≤ x) : (m - 1) * a ≤ m := by
  nlinarith [mul_le_mul_of_nonneg_left (show (x - 1) * a ≤ x by linarith)
    (show (0 : ℚ) ≤ m - 1 by linarith)]

theorem a245212_bbound (x b m : ℚ) (h : 2 * (x - 1) * b ≤ x) (hb : 0 ≤ b)
    (hm : 2 ≤ m) (hx : m ≤ x) : 2 * (m - 1) * b ≤ m := by
  nlinarith [mul_le_mul_of_nonneg_left h (show (0 : ℚ) ≤ m - 1 by linarith)]

theorem a245212_core (p q r ap aq ar bp bq br : ℚ)
    (hp : (p - 1) * ap + bp = p) (hq : (q - 1) * aq + bq = q) (hr : (r - 1) * ar + br = r)
    (hbp : 0 ≤ bp) (hbq : 0 ≤ bq) (hbr : 0 ≤ br)
    (hbp' : 2 * (p - 1) * bp ≤ p) (hbq' : 2 * (q - 1) * bq ≤ q) (hbr' : 2 * (r - 1) * br ≤ r)
    (hap : 0 ≤ ap) (haq : 0 ≤ aq) (har : 0 ≤ ar)
    (hcase : (p = 5 ∧ 7 ≤ q ∧ 11 ≤ r) ∨ (p = 7 ∧ 8 ≤ q ∧ 9 ≤ r) ∨
      (11 ≤ p ∧ 12 ≤ q ∧ 13 ≤ r)) :
    336 * (ap * aq * ar) + 192 * (bp * bq * br) ≤ 539 := by
  rcases hcase with ⟨rfl, hq7, hr11⟩ | ⟨rfl, hq8, hr9⟩ | ⟨hp11, hq12, hr13⟩
  · have h1 := a245212_abound q aq bq 7 hq hbq haq (by norm_num) hq7
    have h2 := a245212_abound r ar br 11 hr hbr har (by norm_num) hr11
    have h3 := a245212_bbound q bq 7 hbq' hbq (by norm_num) hq7
    have h4 := a245212_bbound r br 11 hbr' hbr (by norm_num) hr11
    have hqr : aq * ar ≤ 77 / 60 := by
      calc aq * ar ≤ (7 / 6) * (11 / 10) :=
            mul_le_mul (by linarith) (by linarith) har (by norm_num)
        _ = 77 / 60 := by norm_num
    have hbqr : bq * br ≤ 77 / 240 := by
      calc bq * br ≤ (7 / 12) * (11 / 20) :=
            mul_le_mul (by linarith) (by linarith) hbr (by norm_num)
        _ = 77 / 240 := by norm_num
    have e1 : ap * aq * ar ≤ ap * (77 / 60) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hqr hap
    have e2 : bp * bq * br ≤ bp * (77 / 240) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hbqr hbp
    nlinarith
  · have h1 := a245212_abound q aq bq 8 hq hbq haq (by norm_num) hq8
    have h2 := a245212_abound r ar br 9 hr hbr har (by norm_num) hr9
    have h3 := a245212_bbound q bq 8 hbq' hbq (by norm_num) hq8
    have h4 := a245212_bbound r br 9 hbr' hbr (by norm_num) hr9
    have hqr : aq * ar ≤ 9 / 7 := by
      calc aq * ar ≤ (8 / 7) * (9 / 8) :=
            mul_le_mul (by linarith) (by linarith) har (by norm_num)
        _ = 9 / 7 := by norm_num
    have hbqr : bq * br ≤ 9 / 28 := by
      calc bq * br ≤ (4 / 7) * (9 / 16) :=
            mul_le_mul (by linarith) (by linarith) hbr (by norm_num)
        _ = 9 / 28 := by norm_num
    have e1 : ap * aq * ar ≤ ap * (9 / 7) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hqr hap
    have e2 : bp * bq * br ≤ bp * (9 / 28) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hbqr hbp
    nlinarith
  · have h0 := a245212_abound p ap bp 11 hp hbp hap (by norm_num) hp11
    have h1 := a245212_abound q aq bq 12 hq hbq haq (by norm_num) hq12
    have h2 := a245212_abound r ar br 13 hr hbr har (by norm_num) hr13
    have g0 := a245212_bbound p bp 11 hbp' hbp (by norm_num) hp11
    have g1 := a245212_bbound q bq 12 hbq' hbq (by norm_num) hq12
    have g2 := a245212_bbound r br 13 hbr' hbr (by norm_num) hr13
    have ha3 : ap * aq * ar ≤ (11 / 10) * (12 / 11) * (13 / 12) :=
      mul_le_mul (mul_le_mul (by linarith) (by linarith) haq (by norm_num)) (by linarith) har
        (by norm_num)
    have hb3 : bp * bq * br ≤ (11 / 20) * (12 / 22) * (13 / 24) :=
      mul_le_mul (mul_le_mul (by linarith) (by linarith) hbq (by norm_num)) (by linarith) hbr
        (by norm_num)
    nlinarith

end OMA.Helpers

open OMA.Helpers

theorem OMA.solution : OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1.H3 := by
  intro p q r e f g hp hq hr hp5 hpq hqr he hf hg n
  have h3 : Nat.Prime 3 := Nat.prime_three
  have c1 : (3 ^ 1).Coprime (p ^ e) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes h3 hp).2 (by omega))
  have c2 : (3 ^ 1 * p ^ e).Coprime (q ^ f) :=
    Nat.Coprime.mul_left (Nat.Coprime.pow _ _ ((Nat.coprime_primes h3 hq).2 (by omega)))
      (Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).2 (by omega)))
  have c3 : (3 ^ 1 * p ^ e * q ^ f).Coprime (r ^ g) :=
    Nat.Coprime.mul_left (Nat.Coprime.mul_left
      (Nat.Coprime.pow _ _ ((Nat.coprime_primes h3 hr).2 (by omega)))
      (Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hr).2 (by omega))))
      (Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hr).2 (by omega)))
  have hn : n = 3 ^ 1 * p ^ e * q ^ f * r ^ g := by simp [n]
  have hn0 : n ≠ 0 := by
    rw [hn]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (by norm_num)
      (pow_ne_zero _ hp.ne_zero)) (pow_ne_zero _ hq.ne_zero)) (pow_ne_zero _ hr.ne_zero)
  -- a in terms of the full divisor moment
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
  have hM : (∑ d ∈ n.divisors, d * #d.divisors) =
      7 * (∑ j ∈ range (e + 1), p ^ j * (j + 1)) * (∑ j ∈ range (f + 1), q ^ j * (j + 1)) *
        (∑ j ∈ range (g + 1), r ^ j * (j + 1)) := by
    rw [hn, a245212_moment_mul _ _ c3, a245212_moment_mul _ _ c2, a245212_moment_mul _ _ c1,
      a245212_moment_pp _ _ h3, a245212_moment_pp _ _ hp, a245212_moment_pp _ _ hq,
      a245212_moment_pp _ _ hr]
    simp [sum_range_succ]
  have hS : σ 1 n = 4 * (∑ j ∈ range (e + 1), p ^ j) * (∑ j ∈ range (f + 1), q ^ j) *
        (∑ j ∈ range (g + 1), r ^ j) := by
    rw [hn, isMultiplicative_sigma.map_mul_of_coprime c3,
      isMultiplicative_sigma.map_mul_of_coprime c2, isMultiplicative_sigma.map_mul_of_coprime c1,
      a245212_sigma_pp _ _ h3, a245212_sigma_pp _ _ hp, a245212_sigma_pp _ _ hq,
      a245212_sigma_pp _ _ hr]
    simp [sum_range_succ]
  have hT : #n.divisors = 2 * (e + 1) * (f + 1) * (g + 1) := by
    rw [hn, Nat.Coprime.card_divisors_mul c3, Nat.Coprime.card_divisors_mul c2,
      Nat.Coprime.card_divisors_mul c1, a245212_card_pp _ _ h3, a245212_card_pp _ _ hp,
      a245212_card_pp _ _ hq, a245212_card_pp _ _ hr]
  -- per prime power data
  have pp (x k : ℕ) (hx : 2 ≤ x) (hk : 0 < k) :
      ∃ A B C : ℚ, A = ((∑ j ∈ range (k + 1), x ^ j * (j + 1) : ℕ) : ℚ) ∧
        B = ((∑ j ∈ range (k + 1), x ^ j : ℕ) : ℚ) ∧ C = ((x ^ k * (k + 1) : ℕ) : ℚ) ∧
        0 < C ∧ ((x : ℚ) - 1) * (A / C) + B / C = x ∧ 0 ≤ B / C ∧
        2 * ((x : ℚ) - 1) * (B / C) ≤ x ∧ 0 ≤ A / C := by
    obtain ⟨s, rfl⟩ : ∃ s, x = s + 1 := ⟨x - 1, by omega⟩
    have hid := a245212_ident s k
    have hg := a245212_geom s k
    have hC : (0 : ℚ) < (((s + 1) ^ k * (k + 1) : ℕ) : ℚ) := by positivity
    refine ⟨_, _, _, rfl, rfl, rfl, hC, ?_, by positivity, ?_, by positivity⟩
    · have hid' : (s : ℚ) * ((∑ j ∈ range (k + 1), (s + 1) ^ j * (j + 1) : ℕ) : ℚ) +
          ((∑ j ∈ range (k + 1), (s + 1) ^ j : ℕ) : ℚ) =
          ((s : ℚ) + 1) * (((s + 1) ^ k * (k + 1) : ℕ) : ℚ) := by
        exact_mod_cast hid
      field_simp
      push_cast at hid' ⊢
      linarith
    · have hg' : (s : ℚ) * ((∑ j ∈ range (k + 1), (s + 1) ^ j : ℕ) : ℚ) + 1 =
          ((s : ℚ) + 1) ^ (k + 1) := by exact_mod_cast hg
      rw [mul_div_assoc', div_le_iff₀ hC]
      have hk1 : (2 : ℚ) ≤ (k : ℚ) + 1 := by
        have : (1 : ℚ) ≤ k := by exact_mod_cast hk
        linarith
      have hpow : (0 : ℚ) ≤ ((s : ℚ) + 1) ^ (k + 1) := by positivity
      push_cast at hg' ⊢
      have e1 : 2 * ((s : ℚ) + 1 - 1) * (∑ x ∈ range (k + 1), ((s : ℚ) + 1) ^ x) =
          2 * ((s : ℚ) + 1) ^ (k + 1) - 2 := by
        linear_combination 2 * hg'
      have e2 : ((s : ℚ) + 1) * (((s : ℚ) + 1) ^ k * ((k : ℚ) + 1)) =
          ((k : ℚ) + 1) * ((s : ℚ) + 1) ^ (k + 1) := by ring
      rw [e1, e2]
      nlinarith [mul_le_mul_of_nonneg_right hk1 hpow]
  obtain ⟨Ap, Bp, Cp, rAp, rBp, rCp, hCp, i1p, i2p, i3p, i4p⟩ := pp p e (by omega) he
  obtain ⟨Aq, Bq, Cq, rAq, rBq, rCq, hCq, i1q, i2q, i3q, i4q⟩ := pp q f (by omega) hf
  obtain ⟨Ar, Br, Cr, rAr, rBr, rCr, hCr, i1r, i2r, i3r, i4r⟩ := pp r g (by omega) hg
  have hcase : ((p : ℚ) = 5 ∧ 7 ≤ (q : ℚ) ∧ 11 ≤ (r : ℚ)) ∨
      ((p : ℚ) = 7 ∧ 8 ≤ (q : ℚ) ∧ 9 ≤ (r : ℚ)) ∨
      (11 ≤ (p : ℚ) ∧ 12 ≤ (q : ℚ) ∧ 13 ≤ (r : ℚ)) := by
    have hc : (p = 5 ∧ 7 ≤ q ∧ 11 ≤ r) ∨ (p = 7 ∧ 8 ≤ q ∧ 9 ≤ r) ∨
        (11 ≤ p ∧ 12 ≤ q ∧ 13 ≤ r) := by
      by_cases h11 : 11 ≤ p
      · right; right; omega
      · have hq7 : 7 ≤ q := by
          by_contra hcon
          have : q = 6 := by omega
          subst this; norm_num at hq
        interval_cases p <;> norm_num at hp
        · left
          refine ⟨rfl, hq7, ?_⟩
          by_contra hcon
          have hr8 : 8 ≤ r := by omega
          interval_cases r <;> norm_num at hr
        · right; left; omega
    rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · left; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
    · right; left; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
    · right; right; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
  have core := a245212_core p q r (Ap / Cp) (Aq / Cq) (Ar / Cr) (Bp / Cp) (Bq / Cq) (Br / Cr)
    i1p i1q i1r i2p i2q i2r i3p i3q i3r i4p i4q i4r hcase
  have key : 336 * (Ap * Aq * Ar) + 192 * (Bp * Bq * Br) ≤ 539 * (Cp * Cq * Cr) := by
    have hC3 : 0 < Cp * Cq * Cr := by positivity
    have : 336 * (Ap / Cp * (Aq / Cq) * (Ar / Cr)) + 192 * (Bp / Cp * (Bq / Cq) * (Br / Cr)) =
        (336 * (Ap * Aq * Ar) + 192 * (Bp * Bq * Br)) / (Cp * Cq * Cr) := by
      field_simp
    rw [this, div_le_iff₀ hC3] at core
    exact core
  -- transfer to the integer goal
  have keyQ : (37 : ℚ) * (n : ℚ) * (#n.divisors : ℚ) ≤
      288 * ((OeisA245212.a n : ℚ) - (σ 1 n : ℚ)) := by
    have haQ : (OeisA245212.a n : ℚ) = 2 * (n : ℚ) * (#n.divisors : ℚ) -
        ((∑ d ∈ n.divisors, d * #d.divisors : ℕ) : ℚ) := by
      rw [ha]; push_cast; ring
    have hM' : ((∑ d ∈ n.divisors, d * #d.divisors : ℕ) : ℚ) = 7 * (Ap * Aq * Ar) := by
      rw [hM, rAp, rAq, rAr]; push_cast; ring
    have hS' : ((σ 1 n : ℕ) : ℚ) = 4 * (Bp * Bq * Br) := by
      rw [hS, rBp, rBq, rBr]; push_cast; ring
    have hnt : (n : ℚ) * (#n.divisors : ℚ) = 6 * (Cp * Cq * Cr) := by
      rw [hT, rCp, rCq, rCr]
      have hnQ : (n : ℚ) = 3 * (p : ℚ) ^ e * (q : ℚ) ^ f * (r : ℚ) ^ g := by
        rw [hn]; push_cast; ring
      rw [hnQ]; push_cast; ring
    rw [haQ, hM', hS']
    linear_combination 6 * key - 539 * hnt
  have : ((37 * (n : ℤ) * (#n.divisors : ℤ) : ℤ) : ℚ) ≤
      ((288 * (OeisA245212.a n - (σ 1 n : ℤ)) : ℤ) : ℚ) := by
    push_cast; exact keyQ
  exact_mod_cast this

