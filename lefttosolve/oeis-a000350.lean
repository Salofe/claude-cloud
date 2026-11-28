import OMAStatements.S_oeis_a000350
import Mathlib

namespace OMA.Helpers

/-- `fib (2m)` in terms of `fib m` and `fib (m+1)`, over the integers. -/
theorem fib_two_mul_int (m : ℕ) :
    (Nat.fib (2 * m) : ℤ) = 2 * Nat.fib m * Nat.fib (m + 1) - (Nat.fib m) ^ 2 := by
  have h1 := Nat.fib_two_mul_add_two m
  have h2 := Nat.fib_two_mul_add_one m
  have h3 : Nat.fib (2 * m + 2) = Nat.fib (2 * m) + Nat.fib (2 * m + 1) := Nat.fib_add_two
  have h1' : (Nat.fib (2 * m + 2) : ℤ) = Nat.fib (m + 1) * (2 * Nat.fib m + Nat.fib (m + 1)) := by
    exact_mod_cast h1
  have h2' : (Nat.fib (2 * m + 1) : ℤ) = Nat.fib (m + 1) ^ 2 + Nat.fib m ^ 2 := by
    exact_mod_cast h2
  have h3' : (Nat.fib (2 * m + 2) : ℤ) = Nat.fib (2 * m) + Nat.fib (2 * m + 1) := by
    exact_mod_cast h3
  linear_combination h3'.symm.trans h1' - h2'

/-- The Pisano period of `2^(k+1)` divides `3 * 2^k`. -/
theorem pisano (k : ℕ) : (2 ^ (k + 1) : ℤ) ∣ (Nat.fib (3 * 2 ^ k) : ℤ) ∧
    (2 ^ (k + 1) : ℤ) ∣ (Nat.fib (3 * 2 ^ k + 1) : ℤ) - 1 := by
  induction k with
  | zero => exact ⟨⟨1, by norm_num [Nat.fib_add_two]⟩, ⟨1, by norm_num [Nat.fib_add_two]⟩⟩
  | succ k ih =>
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ih
    have hm : 3 * 2 ^ (k + 1) = 2 * (3 * 2 ^ k) := by ring
    have e1 := fib_two_mul_int (3 * 2 ^ k)
    have e2 : (Nat.fib (2 * (3 * 2 ^ k) + 1) : ℤ) =
        Nat.fib (3 * 2 ^ k + 1) ^ 2 + Nat.fib (3 * 2 ^ k) ^ 2 := by
      exact_mod_cast Nat.fib_two_mul_add_one (3 * 2 ^ k)
    have hb' : (Nat.fib (3 * 2 ^ k + 1) : ℤ) = 2 ^ (k + 1) * b + 1 := by linarith
    rw [hm]
    refine ⟨⟨a * (2 ^ (k + 1) * b + 1) - 2 ^ k * a ^ 2, ?_⟩, ⟨2 ^ k * b ^ 2 + b + 2 ^ k * a ^ 2, ?_⟩⟩
    · rw [e1, ha, hb']
      ring
    · rw [e2, ha, hb']
      ring

/-- Periodicity of Fibonacci numbers modulo `2^(k+1)` with period `3 * 2^k`. -/
theorem per (k n : ℕ) : (2 ^ (k + 1) : ℤ) ∣ (Nat.fib (n + 3 * 2 ^ k) : ℤ) - Nat.fib n := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := pisano k
  rcases n with _ | n
  · simp only [zero_add, Nat.fib_zero, Nat.cast_zero, sub_zero]
    exact ⟨a, ha⟩
  · have e := Nat.fib_add n (3 * 2 ^ k)
    have e' : (Nat.fib (n + 1 + 3 * 2 ^ k) : ℤ) =
        Nat.fib n * Nat.fib (3 * 2 ^ k) + Nat.fib (n + 1) * Nat.fib (3 * 2 ^ k + 1) := by
      rw [show n + 1 + 3 * 2 ^ k = n + 3 * 2 ^ k + 1 by ring]
      exact_mod_cast e
    have hb' : (Nat.fib (3 * 2 ^ k + 1) : ℤ) = 2 ^ (k + 1) * b + 1 := by linarith
    refine ⟨Nat.fib n * a + Nat.fib (n + 1) * b, ?_⟩
    rw [e', ha, hb']
    ring

theorem per_mul (k r t : ℕ) :
    (2 ^ (k + 1) : ℤ) ∣ (Nat.fib (r + 3 * 2 ^ k * t) : ℤ) - Nat.fib r := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h := per k (r + 3 * 2 ^ k * t)
    rw [show r + 3 * 2 ^ k * (t + 1) = r + 3 * 2 ^ k * t + 3 * 2 ^ k by ring]
    have := dvd_add h ih
    simpa using this

theorem fib_small (r : ℕ) (hr : r = 0 ∨ r = 1 ∨ r = 5) : (Nat.fib r : ℤ) = r := by
  rcases hr with rfl | rfl | rfl <;> norm_num [Nat.fib_add_two]

/-- Alekseyev's induction: if `fib n ≡ n (mod 2^(k+1))` then `n ≡ 0, 1, 5 (mod 3 * 2^(k+1))`. -/
theorem key (k n : ℕ) (h : (2 ^ (k + 1) : ℤ) ∣ (Nat.fib n : ℤ) - n) :
    n % (3 * 2 ^ (k + 1)) = 0 ∨ n % (3 * 2 ^ (k + 1)) = 1 ∨ n % (3 * 2 ^ (k + 1)) = 5 := by
  induction k with
  | zero =>
    have hn : n = n % 6 + 3 * 2 ^ 0 * (2 * (n / 6)) := by omega
    have hp := per_mul 0 (n % 6) (2 * (n / 6))
    rw [← hn] at hp
    have h6 : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
    have hc : (2 : ℤ) ∣ (Nat.fib (n % 6) : ℤ) - (n % 6 : ℕ) := by
      have hsub : (Nat.fib (n % 6) : ℤ) - (n % 6 : ℕ) =
          ((Nat.fib n : ℤ) - n) - ((Nat.fib n : ℤ) - Nat.fib (n % 6)) + ((n : ℤ) - (n % 6 : ℕ)) := by
        ring
      rw [hsub]
      refine dvd_add (dvd_sub (by simpa using h) (by simpa using hp)) ?_
      refine ⟨3 * (n / 6 : ℕ), ?_⟩
      have : (n : ℤ) = ((n % 6 : ℕ) : ℤ) + 6 * ((n / 6 : ℕ) : ℤ) := by
        exact_mod_cast (Nat.mod_add_div n 6).symm
      rw [this]
      ring
    show n % (3 * 2) = 0 ∨ n % (3 * 2) = 1 ∨ n % (3 * 2) = 5
    norm_num
    interval_cases hr : n % 6 <;> first | omega | (norm_num [Nat.fib_add_two] at hc)
  | succ k ih =>
    have h' : (2 ^ (k + 1) : ℤ) ∣ (Nat.fib n : ℤ) - n :=
      dvd_trans (pow_dvd_pow 2 (by omega)) h
    have hr := ih h'
    set P := 3 * 2 ^ (k + 1) with hP
    have hn : n = n % P + P * (n / P) := (Nat.mod_add_div n P).symm
    have hfr := fib_small (n % P) hr
    have hp := per_mul (k + 1) (n % P) (n / P)
    rw [← hP, ← hn] at hp
    have h2 : (2 ^ (k + 2) : ℤ) ∣ ((P * (n / P) : ℕ) : ℤ) := by
      have hsub : ((P * (n / P) : ℕ) : ℤ) =
          ((Nat.fib n : ℤ) - Nat.fib (n % P)) - ((Nat.fib n : ℤ) - n) := by
        rw [hfr]
        have : (n : ℤ) = ((n % P : ℕ) : ℤ) + ((P * (n / P) : ℕ) : ℤ) := by
          exact_mod_cast hn
        rw [this]
        ring
      rw [hsub]
      exact dvd_sub hp h
    have h2n : 2 ^ (k + 2) ∣ P * (n / P) := by exact_mod_cast h2
    have h3 : 2 ∣ 3 * (n / P) := by
      rw [hP, show 3 * 2 ^ (k + 1) * (n / P) = 2 ^ (k + 1) * (3 * (n / P)) by ring,
        show 2 ^ (k + 2) = 2 ^ (k + 1) * 2 by ring] at h2n
      exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h2n
    obtain ⟨s, hs⟩ : ∃ s, n / P = 2 * s := ⟨n / P / 2, by omega⟩
    have hPs : P * (n / P) = 3 * 2 ^ (k + 2) * s := by
      rw [hs, hP]
      ring
    have hn2 : n = n % P + 3 * 2 ^ (k + 2) * s := by
      omega
    have hlt : n % P < 3 * 2 ^ (k + 2) := by
      have : 12 ≤ 3 * 2 ^ (k + 2) := by
        have : 4 ≤ 2 ^ (k + 2) := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      omega
    have hmod : n % (3 * 2 ^ (k + 2)) = n % P := by
      conv_lhs => rw [hn2]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    rw [show k + 1 + 1 = k + 2 by ring, hmod]
    exact hr

end OMA.Helpers

open OMA.S_oeis_a000350 in
theorem OMA.solution : type_of% @OMA.S_oeis_a000350.main := by
  intro m hm
  constructor
  · rintro ⟨front, hfront⟩
    have hd : Nat.digits 2 (Nat.fib m) = Nat.digits 2 m ++ front.reverse := by
      have := congrArg List.reverse hfront
      simpa using this
    have hval : Nat.fib m = m + 2 ^ (Nat.digits 2 m).length * Nat.ofDigits 2 front.reverse := by
      have := congrArg (Nat.ofDigits 2) hd
      rw [Nat.ofDigits_digits, Nat.ofDigits_append, Nat.ofDigits_digits] at this
      exact this
    have hlt : m < 2 ^ (Nat.digits 2 m).length := Nat.lt_base_pow_length_digits (by norm_num)
    have hL : (Nat.digits 2 m).length ≠ 0 := by
      rw [Ne, List.length_eq_zero_iff]
      exact Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
    obtain ⟨k, hk⟩ : ∃ k, (Nat.digits 2 m).length = k + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero hL).symm⟩
    rw [hk] at hval hlt
    have hdiv : (2 ^ (k + 1) : ℤ) ∣ (Nat.fib m : ℤ) - m := by
      refine ⟨(Nat.ofDigits 2 front.reverse : ℕ), ?_⟩
      rw [hval]
      push_cast
      ring
    have hk3 : m % (3 * 2 ^ (k + 1)) = m := Nat.mod_eq_of_lt (by omega)
    rcases OMA.Helpers.key k m hdiv with h | h | h <;> rw [hk3] at h <;> omega
  · rintro (rfl | rfl)
    · exact ⟨[], by norm_num⟩
    · refine ⟨[], ?_⟩
      have : Nat.fib 5 = 5 := by norm_num [Nat.fib_add_two]
      rw [this]
      simp
