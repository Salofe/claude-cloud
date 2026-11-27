import OMAReductions.R_Erdos700_erdos_700_parts_ii_R1

/-!
# Step H1 of the reduction Erdos700.erdos_700.parts.ii.R1

For primes `p < q < r` with `q - p < r - q` and `2 (r - p)^2 < p`, the number `n = p q r`
satisfies `f n ^ 2 > n`, where `f n` is the least value of `gcd(n, C(n, k))` over `1 < k ≤ n / 2`.

Write `q = p + a` and `r = p + b`, so that `1 ≤ a`, `2 a < b` and `2 b^2 < p`. The proof follows
the elementary Lucas-digit argument (A. Tresmontant): for every `0 < k` with `2 k ≤ n`, at least
two of the three primes divide `C(n, k)`. Then the product of these two primes divides the gcd,
so the gcd is at least `p q`, and `(p q)^2 > p q r` because `p q > r`.

To see the claim, suppose two of the primes, say `P1` and `P2`, do not divide `C(n, k)`. One step
of Lucas' theorem (`Choose.choose_modEq_choose_mod_mul_choose_div_nat`) shows that `P1 ∣ k` and
`P2 ∣ k`, so `k = P1 P2 j` with `1 ≤ j` and `2 j ≤ P3`. Comparing base-`P` digits, using

* `q r = p (p + a + b) + a b`,
* `p r = q (q + e) + s` where `b = 2 a + 1 + e` and `s + a (a + e) = p`,
* `p q = r w + b d` where `b = a + d` and `p = w + d`,

each of the three possible pairs leads to a contradiction (lemmas `e700_caseA`, `e700_caseB`,
`e700_caseC` below).

Only the upstream definition `Erdos700.f` is used (no upstream theorem).
-/

namespace OMA.Helpers

/-- One step of Lucas' theorem: if the prime `P` does not divide `C(m, i)` then the last base-`P`
digit of `i` is at most that of `m`, and `P` does not divide `C(m / P, i / P)`. -/
theorem e700_digit {P m i : ℕ} (hP : P.Prime) (h : ¬ P ∣ m.choose i) :
    i % P ≤ m % P ∧ ¬ P ∣ (m / P).choose (i / P) := by
  have := Fact.mk hP
  have hmod : m.choose i ≡ (m % P).choose (i % P) * (m / P).choose (i / P) [MOD P] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  constructor
  · by_contra hlt
    rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hlt), zero_mul] at hmod
    exact h ((Nat.modEq_zero_iff_dvd).1 hmod)
  · intro hd
    apply h
    have h0 : (m % P).choose (i % P) * (m / P).choose (i / P) ≡ 0 [MOD P] :=
      (Nat.modEq_zero_iff_dvd).2 (Dvd.dvd.mul_left hd _)
    exact (Nat.modEq_zero_iff_dvd).1 (hmod.trans h0)

/-- Lucas' theorem in digit form: with `R, J < P`, if `P ∤ C(P Q + R, P I + J)` then `J ≤ R` and
`P ∤ C(Q, I)`. -/
theorem e700_digit2 {P Q R I J : ℕ} (hP : P.Prime) (hR : R < P) (hJ : J < P)
    (h : ¬ P ∣ (P * Q + R).choose (P * I + J)) : J ≤ R ∧ ¬ P ∣ Q.choose I := by
  have hP0 : 0 < P := hP.pos
  have h1 := e700_digit hP h
  have e1 : (P * Q + R) % P = R := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hR]
  have e2 : (P * I + J) % P = J := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hJ]
  have e3 : (P * Q + R) / P = Q := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hP0, Nat.div_eq_of_lt hR, Nat.zero_add]
  have e4 : (P * I + J) / P = I := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hP0, Nat.div_eq_of_lt hJ, Nat.zero_add]
  rw [e1, e2, e3, e4] at h1
  exact h1

/-- Two-digit form: with `R, J < P`, if `P ∤ C(P + R, J)` then `J ≤ R`. -/
theorem e700_top {P R J : ℕ} (hP : P.Prime) (hR : R < P) (hJ : J < P)
    (h : ¬ P ∣ (P + R).choose J) : J ≤ R := by
  have h' : ¬ P ∣ (P * 1 + R).choose (P * 0 + J) := by
    rw [Nat.mul_one, Nat.mul_zero, Nat.zero_add]; exact h
  exact (e700_digit2 hP hR hJ h').1

/-- If `P ∤ C(P N, k)` then `P ∣ k` and `P ∤ C(N, k / P)`. -/
theorem e700_first {P N k : ℕ} (hP : P.Prime) (h : ¬ P ∣ (P * N).choose k) :
    P ∣ k ∧ ¬ P ∣ N.choose (k / P) := by
  have h1 := e700_digit hP h
  rw [Nat.mul_mod_right, Nat.mul_div_cancel_left _ hP.pos] at h1
  exact ⟨Nat.dvd_of_mod_eq_zero (Nat.le_zero.1 h1.1), h1.2⟩

/-- Case where `p` and `q = p + a` both fail to divide `C(n, k)`, so that `k = p q j`. -/
theorem e700_caseA (p a b j : ℕ) (hp : p.Prime) (hq : (p + a).Prime) (ha : 1 ≤ a)
    (hab : 2 * a < b) (hb : 2 * b ^ 2 < p) (hj : 1 ≤ j) (hj2 : 2 * j ≤ p + b)
    (h1 : ¬ p ∣ ((p + a) * (p + b)).choose ((p + a) * j))
    (h2 : ¬ (p + a) ∣ (p * (p + b)).choose (p * j)) : False := by
  have hsq : b ^ 2 = b * b := sq b
  have hbb : b * b < p := by omega
  have hb1 : b ≤ b * b := Nat.le_mul_of_pos_left b (by omega)
  have hab1 : a * b ≤ b * b := Nat.mul_le_mul_right b (by omega)
  -- digits in base p
  have e1 : (p + a) * (p + b) = p * (p + a + b) + a * b := by ring
  have e2 : (p + a) * j = p * (j + a * j / p) + a * j % p := by
    rw [Nat.mul_add, add_assoc, Nat.div_add_mod]; ring
  rw [e1, e2] at h1
  obtain ⟨-, h3⟩ := e700_digit2 hp (by omega : a * b < p) (Nat.mod_lt _ hp.pos) h1
  have hm : a * j / p ≤ a := Nat.div_le_of_le_mul (by nlinarith)
  have h4 : j + a * j / p ≤ a + b :=
    e700_top hp (by omega : a + b < p) (by omega) (by rwa [add_assoc] at h3)
  have hj3 : j ≤ a + b := by
    have := Nat.zero_le (a * j / p)
    omega
  -- digits in base q = p + a
  obtain ⟨e, he⟩ : ∃ e, b = 2 * a + 1 + e := ⟨b - (2 * a + 1), by omega⟩
  obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hae : a * (a + e) ≤ a * b := Nat.mul_le_mul_left a (by omega)
  obtain ⟨s, hs⟩ : ∃ s, s + a * (a + e) = p := ⟨p - a * (a + e), by omega⟩
  have haj : a * j' ≤ b * (b + b) := Nat.mul_le_mul (by omega) (by omega)
  have hbb2 : b * (b + b) = 2 * (b * b) := by ring
  obtain ⟨u, hu⟩ : ∃ u, u + a * j' = p := ⟨p - a * j', by omega⟩
  have e3 : p * (p + b) = (p + a) * (p + a + e) + s := by rw [he]; linarith
  have e4 : p * j = (p + a) * j' + u := by rw [hj']; linarith
  rw [e3, e4] at h2
  obtain ⟨h5, h6⟩ := e700_digit2 hq (by omega : s < p + a) (by omega : u < p + a) h2
  have h7 : j' ≤ e := e700_top hq (by omega) (by omega) h6
  have h8 : a * (a + e) ≤ a * j' := by omega
  have h9 : a + e ≤ j' := Nat.le_of_mul_le_mul_left h8 (by omega)
  omega

/-- Case where `p` and `r = p + b` both fail to divide `C(n, k)`, so that `k = p r j`. -/
theorem e700_caseB (p a b j : ℕ) (hp : p.Prime) (hr : (p + b).Prime) (ha : 1 ≤ a)
    (hab : 2 * a < b) (hb : 2 * b ^ 2 < p) (hj : 1 ≤ j) (hj2 : 2 * j ≤ p + a)
    (h1 : ¬ p ∣ ((p + a) * (p + b)).choose ((p + b) * j))
    (h2 : ¬ (p + b) ∣ (p * (p + a)).choose (p * j)) : False := by
  have hsq : b ^ 2 = b * b := sq b
  have hbb : b * b < p := by omega
  have hb1 : b ≤ b * b := Nat.le_mul_of_pos_left b (by omega)
  have hb3 : 3 * b ≤ b * b := Nat.mul_le_mul_right b (by omega)
  have hab1 : a * b ≤ b * b := Nat.mul_le_mul_right b (by omega)
  -- digits in base r = p + b
  obtain ⟨d, hd⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  obtain ⟨w, hw⟩ : ∃ w, p = w + d := ⟨p - d, by omega⟩
  have e1 : p * (p + a) = (p + b) * w + b * d := by subst hw; subst hd; ring
  have hbd : b * d ≤ b * b := Nat.mul_le_mul_left b (by omega)
  have e2 : p * j = (p + b) * (p * j / (p + b)) + p * j % (p + b) := (Nat.div_add_mod _ _).symm
  rw [e1, e2] at h2
  obtain ⟨hU, -⟩ := e700_digit2 hr (by omega : b * d < p + b) (Nat.mod_lt _ (by omega)) h2
  obtain ⟨W, U, hWU, hU'⟩ : ∃ W U, p * j = (p + b) * W + U ∧ U ≤ b * d := ⟨_, _, e2, hU⟩
  have hWj : W ≤ j := by
    have h' : (p + b) * W ≤ (p + b) * j := by nlinarith
    exact Nat.le_of_mul_le_mul_left h' (by omega)
  obtain ⟨m, hm⟩ : ∃ m, j = W + m := ⟨j - W, by omega⟩
  have hrm : (p + b) * m = U + b * j := by subst hm; linarith
  have hbj : 1 ≤ b * j := Nat.mul_pos (by omega) (by omega)
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, Nat.mul_zero] at hrm; omega
    · exact h0
  have hmb : m ≤ b := by
    have hbj' : b * j ≤ b * (p + b) := Nat.mul_le_mul_left b (by omega)
    have h' : (p + b) * m < (p + b) * (b + 1) := by nlinarith
    have := Nat.lt_of_mul_lt_mul_left h'
    omega
  have hbm : b * m ≤ b * b := Nat.mul_le_mul_left b hmb
  -- digits in base p
  have e3 : (p + a) * (p + b) = p * (p + a + b) + a * b := by ring
  rw [e3] at h1
  have hbsq : b * b = a * b + b * d := by rw [hd]; ring
  by_cases hc : U ≤ b * m
  · obtain ⟨V, hV⟩ : ∃ V, V + U = b * m := ⟨b * m - U, by omega⟩
    have e4 : (p + b) * j = p * (j + m) + V := by linarith
    rw [e4] at h1
    obtain ⟨-, h5⟩ := e700_digit2 hp (by omega : a * b < p) (by omega : V < p) h1
    have h6 : j + m ≤ a + b := e700_top hp (by omega) (by omega) (by rwa [add_assoc] at h5)
    have h7 : b * j ≤ b * (a + b) := Nat.mul_le_mul_left b (by omega)
    have h8 : p ≤ p * m := Nat.le_mul_of_pos_right p hm1
    have h9 : (p + b) * m = p * m + b * m := by ring
    have h10 : b * (a + b) = a * b + b * b := by ring
    omega
  · obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨V, hV⟩ : ∃ V, V + U = p + b * m := ⟨p + b * m - U, by omega⟩
    have e4 : (p + b) * j = p * (j + m') + V := by rw [hm'] at hrm hV; linarith
    rw [e4] at h1
    obtain ⟨h5, -⟩ := e700_digit2 hp (by omega : a * b < p) (by omega : V < p) h1
    omega

/-- Case where `q = p + a` and `r = p + b` both fail to divide `C(n, k)`, so that `k = q r j`. -/
theorem e700_caseC (p a b j : ℕ) (hp : p.Prime) (hq : (p + a).Prime) (hr : (p + b).Prime)
    (ha : 1 ≤ a) (hab : 2 * a < b) (hb : 2 * b ^ 2 < p) (hj : 1 ≤ j) (hj2 : 2 * j ≤ p)
    (h1 : ¬ (p + a) ∣ (p * (p + b)).choose ((p + b) * j))
    (h2 : ¬ (p + b) ∣ (p * (p + a)).choose ((p + a) * j)) : False := by
  have hsq : b ^ 2 = b * b := sq b
  have hbb : b * b < p := by omega
  have hb1 : b ≤ b * b := Nat.le_mul_of_pos_left b (by omega)
  have hab1 : a * b ≤ b * b := Nat.mul_le_mul_right b (by omega)
  -- digits in base q = p + a
  obtain ⟨e, he⟩ : ∃ e, b = 2 * a + 1 + e := ⟨b - (2 * a + 1), by omega⟩
  have hae : a * (a + e) ≤ a * b := Nat.mul_le_mul_left a (by omega)
  obtain ⟨s, hs⟩ : ∃ s, s + a * (a + e) = p := ⟨p - a * (a + e), by omega⟩
  have e1 : p * (p + b) = (p + a) * (p + a + e) + s := by rw [he]; linarith
  have e2 : (p + b) * j = (p + a) * ((p + b) * j / (p + a)) + (p + b) * j % (p + a) :=
    (Nat.div_add_mod _ _).symm
  rw [e1, e2] at h1
  obtain ⟨-, h3⟩ := e700_digit2 hq (by omega : s < p + a) (Nat.mod_lt _ (by omega)) h1
  have hlt : (p + b) * j / (p + a) < p + a := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    nlinarith
  have h4 : (p + b) * j / (p + a) ≤ e := e700_top hq (by omega) hlt h3
  have h5 : j ≤ (p + b) * j / (p + a) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    nlinarith
  -- digits in base r = p + b
  obtain ⟨d, hd⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  obtain ⟨w, hw⟩ : ∃ w, p = w + d := ⟨p - d, by omega⟩
  have e3 : p * (p + a) = (p + b) * w + b * d := by subst hw; subst hd; ring
  have hbd : b * d ≤ b * b := Nat.mul_le_mul_left b (by omega)
  obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hdj : d * j' ≤ b * b := Nat.mul_le_mul (by omega) (by omega)
  obtain ⟨z, hz⟩ : ∃ z, z + d * j' = p + a := ⟨p + a - d * j', by omega⟩
  have e4 : (p + a) * j = (p + b) * j' + z := by rw [hj', hd]; linarith
  rw [e3, e4] at h2
  obtain ⟨h6, -⟩ := e700_digit2 hr (by omega : b * d < p + b) (by omega : z < p + b) h2
  omega

/-- If two distinct primes divide both `n` and `c`, their product is at most `gcd n c`. -/
theorem e700_pair {P1 P2 n c : ℕ} (h1 : P1.Prime) (h2 : P2.Prime) (hne : P1 ≠ P2)
    (hn1 : P1 ∣ n) (hn2 : P2 ∣ n) (hc1 : P1 ∣ c) (hc2 : P2 ∣ c) (hn : 0 < n) :
    P1 * P2 ≤ Nat.gcd n c := by
  have hcop : Nat.Coprime P1 P2 := (Nat.coprime_primes h1 h2).2 hne
  exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hn)
    (Nat.dvd_gcd (hcop.mul_dvd_of_dvd_of_dvd hn1 hn2) (hcop.mul_dvd_of_dvd_of_dvd hc1 hc2))

/-- Main claim: for `0 < k` with `2 k ≤ n = p q r`, the gcd of `n` and `C(n, k)` is at least
`p q`, because at least two of the three primes divide `C(n, k)`. -/
theorem e700_key (p a b k : ℕ) (hp : p.Prime) (hq : (p + a).Prime) (hr : (p + b).Prime)
    (ha : 1 ≤ a) (hab : 2 * a < b) (hb : 2 * b ^ 2 < p) (hk0 : 0 < k)
    (hk2 : 2 * k ≤ p * (p + a) * (p + b)) :
    p * (p + a) ≤ Nat.gcd (p * (p + a) * (p + b)) ((p * (p + a) * (p + b)).choose k) := by
  have hp2 := hp.two_le
  have hn0 : 0 < p * (p + a) * (p + b) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have np : p * (p + a) * (p + b) = p * ((p + a) * (p + b)) := by ring
  have nq : p * (p + a) * (p + b) = (p + a) * (p * (p + b)) := by ring
  have nr : p * (p + a) * (p + b) = (p + b) * (p * (p + a)) := by ring
  have dp : p ∣ p * (p + a) * (p + b) := ⟨(p + a) * (p + b), np⟩
  have dq : (p + a) ∣ p * (p + a) * (p + b) := ⟨p * (p + b), nq⟩
  have dr : (p + b) ∣ p * (p + a) * (p + b) := ⟨p * (p + a), nr⟩
  have hpq : p ≠ p + a := by omega
  have hpr : p ≠ p + b := by omega
  have hqr : p + a ≠ p + b := by omega
  by_cases hpC : p ∣ (p * (p + a) * (p + b)).choose k
  · by_cases hqC : (p + a) ∣ (p * (p + a) * (p + b)).choose k
    · exact e700_pair hp hq hpq dp dq hpC hqC hn0
    · by_cases hrC : (p + b) ∣ (p * (p + a) * (p + b)).choose k
      · calc p * (p + a) ≤ p * (p + b) := Nat.mul_le_mul_left _ (by omega)
          _ ≤ _ := e700_pair hp hr hpr dp dr hpC hrC hn0
      · exfalso
        rw [nq] at hqC
        rw [nr] at hrC
        obtain ⟨hqk, hq'⟩ := e700_first hq hqC
        obtain ⟨hrk, hr'⟩ := e700_first hr hrC
        obtain ⟨j, rfl⟩ := ((Nat.coprime_primes hq hr).2 hqr).mul_dvd_of_dvd_of_dvd hqk hrk
        rw [mul_assoc, Nat.mul_div_cancel_left _ hq.pos] at hq'
        rw [mul_comm (p + a) (p + b), mul_assoc, Nat.mul_div_cancel_left _ hr.pos] at hr'
        have hj : 1 ≤ j := by
          rcases Nat.eq_zero_or_pos j with h0 | h0
          · rw [h0, Nat.mul_zero] at hk0; omega
          · exact h0
        have hj2 : 2 * j ≤ p := by
          have h' : (p + a) * (p + b) * (2 * j) ≤ (p + a) * (p + b) * p := by
            calc (p + a) * (p + b) * (2 * j) = 2 * ((p + a) * (p + b) * j) := by ring
              _ ≤ p * (p + a) * (p + b) := hk2
              _ = (p + a) * (p + b) * p := by ring
          exact Nat.le_of_mul_le_mul_left h' (Nat.mul_pos (by omega) (by omega))
        exact e700_caseC p a b j hp hq hr ha hab hb hj hj2 hq' hr'
  · by_cases hqC : (p + a) ∣ (p * (p + a) * (p + b)).choose k
    · by_cases hrC : (p + b) ∣ (p * (p + a) * (p + b)).choose k
      · calc p * (p + a) ≤ (p + a) * (p + b) := by
              rw [mul_comm p (p + a)]; exact Nat.mul_le_mul_left _ (by omega)
          _ ≤ _ := e700_pair hq hr hqr dq dr hqC hrC hn0
      · exfalso
        rw [np] at hpC
        rw [nr] at hrC
        obtain ⟨hpk, hp'⟩ := e700_first hp hpC
        obtain ⟨hrk, hr'⟩ := e700_first hr hrC
        obtain ⟨j, rfl⟩ := ((Nat.coprime_primes hp hr).2 hpr).mul_dvd_of_dvd_of_dvd hpk hrk
        rw [mul_assoc, Nat.mul_div_cancel_left _ hp.pos] at hp'
        rw [mul_comm p (p + b), mul_assoc, Nat.mul_div_cancel_left _ hr.pos] at hr'
        have hj : 1 ≤ j := by
          rcases Nat.eq_zero_or_pos j with h0 | h0
          · rw [h0, Nat.mul_zero] at hk0; omega
          · exact h0
        have hj2 : 2 * j ≤ p + a := by
          have h' : p * (p + b) * (2 * j) ≤ p * (p + b) * (p + a) := by
            calc p * (p + b) * (2 * j) = 2 * (p * (p + b) * j) := by ring
              _ ≤ p * (p + a) * (p + b) := hk2
              _ = p * (p + b) * (p + a) := by ring
          exact Nat.le_of_mul_le_mul_left h' (Nat.mul_pos (by omega) (by omega))
        exact e700_caseB p a b j hp hr ha hab hb hj hj2 hp' hr'
    · exfalso
      rw [np] at hpC
      rw [nq] at hqC
      obtain ⟨hpk, hp'⟩ := e700_first hp hpC
      obtain ⟨hqk, hq'⟩ := e700_first hq hqC
      obtain ⟨j, rfl⟩ := ((Nat.coprime_primes hp hq).2 hpq).mul_dvd_of_dvd_of_dvd hpk hqk
      rw [mul_assoc, Nat.mul_div_cancel_left _ hp.pos] at hp'
      rw [mul_comm p (p + a), mul_assoc, Nat.mul_div_cancel_left _ hq.pos] at hq'
      have hj : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · rw [h0, Nat.mul_zero] at hk0; omega
        · exact h0
      have hj2 : 2 * j ≤ p + b := by
        have h' : p * (p + a) * (2 * j) ≤ p * (p + a) * (p + b) := by
          calc p * (p + a) * (2 * j) = 2 * (p * (p + a) * j) := by ring
            _ ≤ p * (p + a) * (p + b) := hk2
        exact Nat.le_of_mul_le_mul_left h' (Nat.mul_pos (by omega) (by omega))
      exact e700_caseA p a b j hp hq ha hab hb hj hj2 hp' hq'

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos700_erdos_700_parts_ii_R1.H1 := by
  intro p q r hp hq hr hpq hqr hgap hsmall
  obtain ⟨a, rfl⟩ : ∃ a, q = p + a := ⟨q - p, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, r = p + b := ⟨r - p, by omega⟩
  have ha : 1 ≤ a := by omega
  have hab : 2 * a < b := by omega
  have hb : 2 * b ^ 2 < p := by rwa [Nat.add_sub_cancel_left] at hsmall
  have hp2 := hp.two_le
  have h4 : 2 * 2 * 1 ≤ p * (p + a) * (p + b) :=
    Nat.mul_le_mul (Nat.mul_le_mul hp2 (by omega)) (by omega)
  have hne : ({m | ∃ k, 1 < k ∧ k ≤ p * (p + a) * (p + b) / 2 ∧
      m = Nat.gcd (p * (p + a) * (p + b)) ((p * (p + a) * (p + b)).choose k)} : Set ℕ).Nonempty :=
    ⟨_, 2, by omega, by omega, rfl⟩
  obtain ⟨k, hk1, hk2, hkeq⟩ := Nat.sInf_mem hne
  unfold Erdos700.f
  rw [hkeq]
  have hkey := e700_key p a b k hp hq hr ha hab hb (by omega) (by omega)
  have hX : p + b < p * (p + a) := by nlinarith
  have hpos : 0 < p * (p + a) := Nat.mul_pos (by omega) (by omega)
  have e1 : p * (p + a) * (p + b) < p * (p + a) * (p * (p + a)) :=
    Nat.mul_lt_mul_of_pos_left hX hpos
  have e2 := Nat.mul_le_mul hkey hkey
  rw [sq]
  exact lt_of_lt_of_le e1 e2
