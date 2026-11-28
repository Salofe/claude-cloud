import OMAStatements.S_oeis_a085094
import Mathlib

/-!
Proof of the conjecture of OEIS A085094: for every n >= 1 there is k >= 1 such that n k - 1 is a
(base 10) palindrome.

Write n = 2^a 5^b m with m coprime to 10, let e = a + b and u = phi(m), so 10^u = 1 mod m.
Start from the digit 9 and wrap it c times in the blocks Y = 8 9...9 (u digits) on the low side
and its reverse on the high side. This gives a palindrome M_c of length 1 + 2uc whose value is
9 - 2c mod m. The number P with digits 9^e, M_c, 9^e is a palindrome (all its digits are 8 or 9),
and P + 1 = 10^e (1 + M_c + 10^(len M_c) (10^e - 1)) = 10^e (10^(e+1) - 2c) mod m. Choosing
c = 10^(e+1) (m+1)/2 (m is odd) makes the second factor divisible by m, and 2^a 5^b divides 10^e,
so n divides P + 1 and k = (P + 1)/n works.
-/

namespace OMA.Helpers

open OMA.S_oeis_a085094

/-- The repdigit `9...9` with `k` digits. -/
theorem rep9 (k : ℕ) : Nat.ofDigits 10 (List.replicate k 9) + 1 = 10 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, pow_succ, ← ih]
    ring

/-- The block `8 9 ... 9` (read from the least significant digit), of length `u`. -/
def Y (u : ℕ) : List ℕ := 8 :: List.replicate (u - 1) 9

/-- `Mc u c`: wrap the single digit `9` in `c` layers `Y`, `reverse Y`. -/
def Mc (u : ℕ) : ℕ → List ℕ
  | 0 => [9]
  | c + 1 => Y u ++ Mc u c ++ (Y u).reverse

theorem Y_length (u : ℕ) (hu : 1 ≤ u) : (Y u).length = u := by
  simp [Y]; omega

theorem Mc_length (u : ℕ) (hu : 1 ≤ u) (c : ℕ) : (Mc u c).length = 1 + 2 * u * c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    simp only [Mc, List.length_append, List.length_reverse, Y_length u hu, ih]
    ring

theorem Mc_rev (u c : ℕ) : (Mc u c).reverse = Mc u c := by
  induction c with
  | zero => rfl
  | succ c ih => simp [Mc, ih]

theorem Mc_digits (u c : ℕ) : ∀ d ∈ Mc u c, d = 8 ∨ d = 9 := by
  induction c with
  | zero => intro d hd; simp [Mc] at hd; right; exact hd
  | succ c ih =>
    intro d hd
    simp only [Mc, List.mem_append, List.mem_reverse, Y, List.mem_cons, List.mem_replicate] at hd
    rcases hd with ((h | ⟨_, h⟩) | h) | (h | ⟨_, h⟩)
    · left; exact h
    · right; exact h
    · exact ih d h
    · left; exact h
    · right; exact h

theorem Y_val (u : ℕ) (hu : 1 ≤ u) : Nat.ofDigits 10 (Y u) + 2 = 10 ^ u := by
  have h := rep9 (u - 1)
  rw [Y, Nat.ofDigits_cons]
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h ⊢
  rw [pow_succ, ← h]
  ring

theorem Yr_val (u : ℕ) : Nat.ofDigits 10 (Y u).reverse + 1 = 9 * 10 ^ (u - 1) := by
  have h := rep9 (u - 1)
  rw [Y, List.reverse_cons, List.reverse_replicate, Nat.ofDigits_append, List.length_replicate]
  simp only [Nat.ofDigits_cons, Nat.ofDigits_nil]
  rw [← h]
  ring

theorem Mc_val (m u : ℕ) (hu : 1 ≤ u) (ht : (10 : ZMod m) ^ u = 1) (c : ℕ) :
    ((Nat.ofDigits 10 (Mc u c) : ℕ) : ZMod m) = 9 - 2 * c := by
  induction c with
  | zero => simp [Mc]
  | succ c ih =>
    have hY : ((Nat.ofDigits 10 (Y u) : ℕ) : ZMod m) + 2 = 1 := by
      rw [← ht]; exact_mod_cast congrArg (fun x : ℕ => (x : ZMod m)) (Y_val u hu)
    have hYr : ((Nat.ofDigits 10 (Y u).reverse : ℕ) : ZMod m) + 1 = 9 * 10 ^ (u - 1) := by
      exact_mod_cast congrArg (fun x : ℕ => (x : ZMod m)) (Yr_val u)
    have h1 : (10 : ZMod m) * 10 ^ (u - 1) = 1 := by
      rw [← pow_succ', show u - 1 + 1 = u by omega, ht]
    have hp : (10 : ZMod m) ^ (Mc u c).length = 10 := by
      rw [Mc_length u hu, show 1 + 2 * u * c = 1 + u * (2 * c) by ring, pow_add, pow_one,
        pow_mul, ht, one_pow, mul_one]
    rw [Mc, Nat.ofDigits_append, Nat.ofDigits_append, List.length_append, Y_length u hu]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [ih, pow_add, hp, ht]
    linear_combination hY + 10 * hYr + 9 * h1

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a085094.main := by
  intro n hn
  obtain ⟨a, n1, h2, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) 2 (by norm_num)
  have hn1 : n1 ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨b, m, h5, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn1 5 (by norm_num)
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hn
    · exact h
  have h2' : ¬ 2 ∣ m := fun hd => h2 (dvd_mul_of_dvd_right hd _)
  have hcop : Nat.Coprime 10 m := by
    have c2 : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2'
    have c5 : Nat.Coprime 5 m := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5
    exact Nat.Coprime.mul_left c2 c5
  set u := Nat.totient m with hu_def
  have hu : 1 ≤ u := Nat.totient_pos.mpr hm
  have ht : (10 : ZMod m) ^ u = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.pow_totient hcop)
    push_cast at this
    exact this
  have hodd : m % 2 = 1 := by omega
  set h := (m + 1) / 2 with hh_def
  have hh : (2 : ZMod m) * h = 1 := by
    have e : 2 * h = m + 1 := by omega
    have := congrArg (fun x : ℕ => (x : ZMod m)) e
    push_cast at this
    rw [this, ZMod.natCast_self, zero_add]
  obtain ⟨e, he⟩ : ∃ e, e = a + b := ⟨_, rfl⟩
  set c := 10 ^ (e + 1) * h with hc_def
  set M := OMA.Helpers.Mc u c with hM
  set L := List.replicate e 9 ++ M ++ List.replicate e 9 with hL
  set P := Nat.ofDigits 10 L with hP
  set X := 1 + Nat.ofDigits 10 M + 10 ^ M.length * Nat.ofDigits 10 (List.replicate e 9) with hX
  have hPX : P + 1 = 10 ^ e * X := by
    have r := OMA.Helpers.rep9 e
    rw [hP, hL, Nat.ofDigits_append, Nat.ofDigits_append, List.length_append,
      List.length_replicate, hX, pow_add, ← r]
    ring
  have hmX : m ∣ X := by
    rw [← ZMod.natCast_eq_zero_iff]
    have r : ((Nat.ofDigits 10 (List.replicate e 9) : ℕ) : ZMod m) + 1 = 10 ^ e := by
      exact_mod_cast congrArg (fun x : ℕ => (x : ZMod m)) (OMA.Helpers.rep9 e)
    have hp : (10 : ZMod m) ^ M.length = 10 := by
      rw [hM, OMA.Helpers.Mc_length u hu, show 1 + 2 * u * c = 1 + u * (2 * c) by ring, pow_add,
        pow_one, pow_mul, ht, one_pow, mul_one]
    have hcz : ((c : ℕ) : ZMod m) = 10 ^ (e + 1) * h := by
      rw [hc_def]; push_cast; ring
    rw [hX]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    rw [hp, hM, OMA.Helpers.Mc_val m u hu ht c, hcz]
    linear_combination 10 * r - 10 ^ (e + 1) * hh
  have h10 : 2 ^ a * 5 ^ b ∣ 10 ^ e := by
    rw [he, pow_add, show (10 : ℕ) = 2 * 5 by norm_num, mul_pow, mul_pow]
    exact mul_dvd_mul (dvd_mul_right _ _) (dvd_mul_left _ _)
  have hdvd : 2 ^ a * (5 ^ b * m) ∣ P + 1 := by
    rw [hPX, ← mul_assoc]
    exact mul_dvd_mul h10 hmX
  obtain ⟨k, hk⟩ := hdvd
  have hdig : ∀ d ∈ L, d = 8 ∨ d = 9 := by
    intro d hd
    rw [hL] at hd
    simp only [List.mem_append, List.mem_replicate] at hd
    rcases hd with (⟨_, h⟩ | h) | ⟨_, h⟩
    · right; exact h
    · exact OMA.Helpers.Mc_digits u c d h
    · right; exact h
  refine ⟨k, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, mul_zero] at hk; omega
    · exact h0
  · have e1 : 2 ^ a * (5 ^ b * m) * k - 1 = P := by omega
    unfold OMA.S_oeis_a085094.IsPalindrome10
    rw [e1, hP, Nat.digits_ofDigits 10 (by norm_num) L
      (fun d hd => by rcases hdig d hd with h | h <;> omega)
      (fun hne => by
        have := hdig _ (List.getLast_mem hne)
        omega)]
    rw [hL]
    simp [hM, OMA.Helpers.Mc_rev]
