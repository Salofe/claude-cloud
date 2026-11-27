import OMAStatements.S_oeis_a189202
import Mathlib

-- Problem: A189202: least m > 0 with s_2(m(n-1)) and s_n(2m(n-1))/(n-1) both even.
-- Shevelev's conjecture a(n) > 0 holds: an admissible m exists for every n >= 2.
-- Odd n = 2c+1: put Q = (n^2-1)/2 and pick 2^k with Q < 2^k <= 2Q. For m = (2^k+1)(c+1),
--   m(n-1) = Q + 2^k Q has binary digit sum 2 s_2(Q), and 2m(n-1) = (2^k+1)(n^2-1)
--   = (n^2-1-2^k) + n^2 2^k has base-n digit sum 2(n-1) (complementary two-digit blocks).
-- Even n: for m = n^i + n^j with j >= i+2 and (n-1)n^i < 2^j, the base-n digit sum of
--   2m(n-1) is 2(n-1) and the binary digit sum of m(n-1) is s_2((n-1)n^i) + s_2((n-1)n^j).
--   Among the positions 0, n, n(n+1) two of these binary digit sums share a parity.
-- Written by Claude (Anthropic), working as the claude-code agent.

namespace OMA.Helpers

open OMA.S_oeis_a189202

theorem a189202_ds_zero (b : ℕ) : ds b 0 = 0 := by
  simp [ds]

theorem a189202_ds_step (b x : ℕ) (hb : 2 ≤ b) : ds b x = x % b + ds b (x / b) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [ds]
  · unfold ds
    rw [Nat.digits_def' (by omega) hx, List.sum_cons]

theorem a189202_ds_append (b : ℕ) (hb : 2 ≤ b) :
    ∀ k r q : ℕ, r < b ^ k → ds b (r + b ^ k * q) = ds b r + ds b q := by
  intro k
  induction k with
  | zero =>
    intro r q hr
    have : r = 0 := by simpa using hr
    subst this
    simp [a189202_ds_zero]
  | succ k ih =>
    intro r q hr
    have hb0 : 0 < b := by omega
    have e : r + b ^ (k + 1) * q = r + b * (b ^ k * q) := by ring
    rw [a189202_ds_step b (r + b ^ (k + 1) * q) hb, a189202_ds_step b r hb, e,
      Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hb0]
    have hr' : r / b < b ^ k := by
      rw [Nat.div_lt_iff_lt_mul hb0, ← pow_succ]
      exact hr
    rw [ih (r / b) q hr']
    ring

theorem a189202_ds_shift (b : ℕ) (hb : 2 ≤ b) (k q : ℕ) : ds b (b ^ k * q) = ds b q := by
  have h := a189202_ds_append b hb k 0 q (by positivity)
  simpa [a189202_ds_zero] using h

theorem a189202_ds_two_digits (n v : ℕ) (hn : 2 ≤ n) (hv : v < n * n) :
    ds n v = v % n + v / n := by
  have hn0 : 0 < n := by omega
  have h1 : v / n < n := by rw [Nat.div_lt_iff_lt_mul hn0]; exact hv
  rw [a189202_ds_step n v hn, a189202_ds_step n (v / n) hn, Nat.mod_eq_of_lt h1,
    Nat.div_eq_of_lt h1, a189202_ds_zero]
  ring

/-- Two complementary numbers below `n^2` have base-`n` digit sums adding to `2(n-1)`. -/
theorem a189202_complement (n a : ℕ) (hn : 2 ≤ n) (ha : a < n * n) :
    ds n (n * n - 1 - a) + ds n a = 2 * (n - 1) := by
  have hn0 : 0 < n := by omega
  set d0 := a % n with hd0
  set d1 := a / n with hd1
  have hd0lt : d0 < n := Nat.mod_lt _ hn0
  have hd1lt : d1 < n := by rw [hd1, Nat.div_lt_iff_lt_mul hn0]; exact ha
  have hadec : a = d0 + n * d1 := (Nat.mod_add_div a n).symm
  obtain ⟨e0, he0⟩ : ∃ e0, n = d0 + e0 + 1 := ⟨n - d0 - 1, by omega⟩
  obtain ⟨e1, he1⟩ : ∃ e1, n = d1 + e1 + 1 := ⟨n - d1 - 1, by omega⟩
  have key : n * n = n * d1 + n * e1 + n := by
    have : n * n = n * (d1 + e1 + 1) := by rw [← he1]
    rw [this]; ring
  have hr : n * n - 1 - a = e0 + n * e1 := by omega
  have he0lt : e0 < n := by omega
  have hr2 : n * n - 1 - a < n * n := by omega
  rw [a189202_ds_two_digits n _ hn hr2, a189202_ds_two_digits n a hn ha, hr,
    Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hn0, Nat.mod_eq_of_lt he0lt,
    Nat.div_eq_of_lt he0lt]
  omega

theorem a189202_odd (c : ℕ) (hc : 1 ≤ c) : ∃ m, admissible (2 * c + 1) m := by
  set n := 2 * c + 1 with hn
  set Q := 2 * c * (c + 1) with hQ
  have hQ0 : Q ≠ 0 := by positivity
  set k := Nat.log 2 Q + 1 with hk
  set a := 2 ^ k with ha
  have hQa : Q < a := Nat.lt_pow_succ_log_self (by norm_num) Q
  have haQ : a ≤ 2 * Q := by
    have := Nat.pow_log_le_self 2 hQ0
    rw [ha, hk, pow_succ]
    omega
  have hnn : n * n = 2 * Q + 1 := by rw [hn, hQ]; ring
  have hn1 : n - 1 = 2 * c := by omega
  refine ⟨(a + 1) * (c + 1), by positivity, ?_, ?_⟩
  · have e : (a + 1) * (c + 1) * (n - 1) = Q + 2 ^ k * Q := by
      rw [hn1, hQ, ← ha]; ring
    rw [e, a189202_ds_append 2 le_rfl k Q Q hQa]
    exact ⟨ds 2 Q, rfl⟩
  · have hn2 : 2 ≤ n := by omega
    have halt : a < n * n := by omega
    set r := n * n - 1 - a with hr
    have hr1 : r + a + 1 = n * n := by omega
    have e1 : 2 * ((a + 1) * (c + 1)) * (n - 1) + (a + 1) = (a + 1) * (n * n) := by
      rw [hn1, hnn, hQ]; ring
    have e2 : r + n ^ 2 * a + (a + 1) = (a + 1) * (n * n) := by
      have : r + n ^ 2 * a + (a + 1) = (r + a + 1) + n ^ 2 * a := by ring
      rw [this, hr1]; ring
    have e3 : 2 * ((a + 1) * (c + 1)) * (n - 1) = r + n ^ 2 * a := by omega
    have hrlt : r < n ^ 2 := by rw [sq]; omega
    rw [e3, a189202_ds_append n hn2 2 r a hrlt, hr, a189202_complement n a hn2 halt]
    have hpos : 0 < n - 1 := by omega
    rw [Nat.mul_div_cancel _ hpos]
    exact even_two

theorem a189202_ds_twice (n : ℕ) (hn : 2 ≤ n) : ds n (2 * (n - 1)) = n - 1 := by
  have hn0 : 0 < n := by omega
  have e : 2 * (n - 1) = (n - 2) + n * 1 := by omega
  rw [a189202_ds_step n _ hn, e, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hn0,
    Nat.mod_eq_of_lt (by omega : n - 2 < n), Nat.div_eq_of_lt (by omega : n - 2 < n),
    a189202_ds_step n 1 hn, Nat.mod_eq_of_lt (by omega : 1 < n),
    Nat.div_eq_of_lt (by omega : 1 < n), a189202_ds_zero]
  omega

theorem a189202_even_pair (c i j : ℕ) (hc : 1 ≤ c) (hij : i + 2 ≤ j)
    (hsep : (2 * c - 1) * (2 * c) ^ i < 2 ^ j)
    (hpar : Even (ds 2 ((2 * c - 1) * (2 * c) ^ i) + ds 2 ((2 * c - 1) * (2 * c) ^ j))) :
    admissible (2 * c) ((2 * c) ^ i + (2 * c) ^ j) := by
  set n := 2 * c with hn
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  refine ⟨by positivity, ?_, ?_⟩
  · have hpow : n ^ j = 2 ^ j * c ^ j := by rw [hn, mul_pow]
    have e : (n ^ i + n ^ j) * (n - 1) = (n - 1) * n ^ i + 2 ^ j * ((n - 1) * c ^ j) := by
      rw [hpow]; ring
    have ej : (n - 1) * n ^ j = 2 ^ j * ((n - 1) * c ^ j) := by rw [hpow]; ring
    rw [e, a189202_ds_append 2 le_rfl j _ _ hsep]
    rw [ej, a189202_ds_shift 2 le_rfl] at hpar
    exact hpar
  · have hlt : 2 * (n - 1) * n ^ i < n ^ j := by
      have h1 : 2 * (n - 1) < n ^ 2 := by
        have h3 : 2 * n ≤ n * n := Nat.mul_le_mul_right n hn2
        rw [sq]; omega
      calc 2 * (n - 1) * n ^ i < n ^ 2 * n ^ i := by
            exact Nat.mul_lt_mul_of_pos_right h1 (by positivity)
        _ = n ^ (i + 2) := by ring
        _ ≤ n ^ j := Nat.pow_le_pow_right hn0 hij
    have e : 2 * (n ^ i + n ^ j) * (n - 1) =
        2 * (n - 1) * n ^ i + n ^ j * (2 * (n - 1)) := by ring
    have ei : 2 * (n - 1) * n ^ i = n ^ i * (2 * (n - 1)) := by ring
    rw [e, a189202_ds_append n hn2 j _ _ hlt, ei, a189202_ds_shift n hn2,
      a189202_ds_twice n hn2]
    have hpos : 0 < n - 1 := by omega
    rw [show n - 1 + (n - 1) = 2 * (n - 1) by ring, Nat.mul_div_cancel _ hpos]
    exact even_two

theorem a189202_even (c : ℕ) (hc : 1 ≤ c) : ∃ m, admissible (2 * c) m := by
  set n := 2 * c with hn
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  set P := fun R : ℕ => ds 2 ((n - 1) * n ^ R) with hP
  have hn2n : n < 2 ^ n := Nat.lt_two_pow_self
  have s0B : (n - 1) * n ^ 0 < 2 ^ n := by simp; omega
  have s0C : (n - 1) * n ^ 0 < 2 ^ (n * (n + 1)) := by
    have : 2 ^ n ≤ 2 ^ (n * (n + 1)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    simp; omega
  have sBC : (n - 1) * n ^ n < 2 ^ (n * (n + 1)) := by
    have h1 : (n - 1) * n ^ n < n ^ (n + 1) := by
      rw [pow_succ, mul_comm (n ^ n) n]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
    have h2 : n ^ (n + 1) < (2 ^ n) ^ (n + 1) :=
      Nat.pow_lt_pow_left hn2n (by omega)
    rw [← pow_mul] at h2
    omega
  have dB : 0 + 2 ≤ n := by omega
  have dC : 0 + 2 ≤ n * (n + 1) := by nlinarith
  have dBC : n + 2 ≤ n * (n + 1) := by nlinarith
  by_cases h1 : (Even (P 0) ↔ Even (P n))
  · exact ⟨_, a189202_even_pair c 0 n hc dB s0B (Nat.even_add.mpr h1)⟩
  · by_cases h2 : (Even (P 0) ↔ Even (P (n * (n + 1))))
    · exact ⟨_, a189202_even_pair c 0 (n * (n + 1)) hc dC s0C (Nat.even_add.mpr h2)⟩
    · have h3 : (Even (P n) ↔ Even (P (n * (n + 1)))) := by tauto
      exact ⟨_, a189202_even_pair c n (n * (n + 1)) hc dBC sBC (Nat.even_add.mpr h3)⟩

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a189202.main := by
  classical
  intro n hn
  have hex : ∃ m, OMA.S_oeis_a189202.admissible n m := by
    rcases Nat.even_or_odd n with ⟨c, hc⟩ | ⟨c, hc⟩
    · have : n = 2 * c := by omega
      rw [this]
      exact OMA.Helpers.a189202_even c (by omega)
    · rw [hc]
      exact OMA.Helpers.a189202_odd c (by omega)
  unfold OMA.S_oeis_a189202.term
  rw [dif_pos hex]
  exact (Nat.find_spec hex).1
