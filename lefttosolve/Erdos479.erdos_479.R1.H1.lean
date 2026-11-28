import OMAReductions.R_Erdos479_erdos_479_R1
import Mathlib

-- Step H1 of reduction Erdos479.erdos_479.R1: the four elementary families.
-- k = 0: n = 2^j. k = -1: n = 3^j, since 3^(j+1) divides (x+1)(x^2-x+1) with x = 2^(3^j).
-- k = -2: the chain n -> 2^n + 2 from n = 2, keeping n = 2 mod 4, n | 2^n + 2, n - 1 | 2^n + 1.
-- k = 2^i: n = i p for primes p > i with p = 1 mod phi(b), where b is the odd part of i
-- (Fermat modulo p, Euler modulo b, and both sides vanish modulo the 2-part of i).

namespace OMA.Helpers

/-- 3^j divides 2^(3^j) + 1. -/
theorem three_pow_dvd (j : ℕ) : (3 : ℤ) ^ j ∣ 2 ^ (3 ^ j) + 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    set x : ℤ := 2 ^ (3 ^ j) with hx
    have h3 : (3 : ℤ) ∣ x + 1 := by
      have hodd : Odd (3 ^ j) := Odd.pow (by decide)
      simpa using Odd.add_dvd_pow_add_pow (2 : ℤ) 1 hodd
    have hq : (3 : ℤ) ∣ x ^ 2 - x + 1 := by
      obtain ⟨c, hc⟩ := h3
      exact ⟨3 * c ^ 2 - x, by linear_combination (x + 1 + 3 * c) * hc⟩
    have heq : (2 : ℤ) ^ (3 ^ (j + 1)) + 1 = (x + 1) * (x ^ 2 - x + 1) := by
      rw [pow_succ, pow_mul, ← hx]; ring
    rw [heq, pow_succ]
    exact mul_dvd_mul ih hq

/-- The chain n ↦ 2^n + 2 starting at 2. -/
def chain : ℕ → ℕ
  | 0 => 2
  | j + 1 => 2 ^ chain j + 2

theorem chain_inv (j : ℕ) : 2 ≤ chain j ∧ chain j % 4 = 2 ∧ chain j ∣ 2 ^ chain j + 2 ∧
    chain j - 1 ∣ 2 ^ chain j + 1 := by
  induction j with
  | zero => decide
  | succ j ih =>
    obtain ⟨h2, h4, hd, hd1⟩ := ih
    set n := chain j with hn
    have hN : chain (j + 1) = 2 ^ n + 2 := rfl
    rw [hN]
    have hpow4 : 2 ^ n = 4 * 2 ^ (n - 2) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    have hpow2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']; congr 1; omega
    refine ⟨by omega, by omega, ?_, ?_⟩
    · -- N ∣ 2^N + 2
      obtain ⟨d, hdd⟩ := hd1
      have hdodd : Odd d := by
        rcases Nat.even_or_odd d with ⟨e, he⟩ | h
        · exfalso
          have : 2 ^ n + 1 = 2 * ((n - 1) * e) := by rw [hdd, he]; ring
          omega
        · exact h
      have key : 2 ^ (n - 1) + 1 ∣ 2 ^ (2 ^ n + 1) + 1 := by
        rw [hdd, pow_mul]
        simpa using Odd.nat_add_dvd_pow_add_pow (2 ^ (n - 1)) 1 hdodd
      have e1 : 2 ^ n + 2 = 2 * (2 ^ (n - 1) + 1) := by omega
      have e2 : 2 ^ (2 ^ n + 2) + 2 = 2 * (2 ^ (2 ^ n + 1) + 1) := by
        rw [pow_succ]; ring
      rw [e2, e1]
      exact mul_dvd_mul_left 2 key
    · -- N - 1 ∣ 2^N + 1
      obtain ⟨c, hc⟩ := hd
      have hcodd : Odd c := by
        rcases Nat.even_or_odd c with ⟨e, he⟩ | h
        · exfalso
          obtain ⟨m, hm⟩ : ∃ m, n = 4 * m + 2 := ⟨n / 4, by omega⟩
          have : 2 ^ n + 2 = 4 * ((2 * m + 1) * e) := by rw [hc, he, hm]; ring
          omega
        · exact h
      have hsub : 2 ^ n + 2 - 1 = 2 ^ n + 1 := by omega
      rw [hsub, hc, pow_mul]
      simpa using Odd.nat_add_dvd_pow_add_pow (2 ^ n) 1 hcodd

theorem chain_strictMono : StrictMono chain := by
  apply strictMono_nat_of_lt_succ
  intro j
  show chain j < 2 ^ chain j + 2
  have := Nat.lt_two_pow_self (n := chain j)
  omega

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos479_erdos_479_R1.H1 := by
  rintro k (rfl | rfl | rfl | ⟨i, hi, rfl⟩)
  · -- k = 0 : n = 2^j
    refine Set.infinite_of_injective_forall_mem (f := fun j : ℕ => 2 ^ j)
      (Nat.pow_right_injective (le_refl 2)) ?_
    intro j
    simp only [Set.mem_ofPred_eq]
    apply Int.modEq_zero_iff_dvd.2
    push_cast
    exact pow_dvd_pow 2 (Nat.lt_two_pow_self).le
  · -- k = -1 : n = 3^j
    refine Set.infinite_of_injective_forall_mem (f := fun j : ℕ => 3 ^ j)
      (Nat.pow_right_injective (by norm_num)) ?_
    intro j
    simp only [Set.mem_ofPred_eq]
    rw [Int.modEq_iff_dvd]
    have h := OMA.Helpers.three_pow_dvd j
    push_cast
    have : (-1 : ℤ) - 2 ^ 3 ^ j = -(2 ^ 3 ^ j + 1) := by ring
    rw [this, dvd_neg]
    exact h
  · -- k = -2 : the chain
    refine Set.infinite_of_injective_forall_mem (f := OMA.Helpers.chain)
      OMA.Helpers.chain_strictMono.injective ?_
    intro j
    simp only [Set.mem_ofPred_eq]
    rw [Int.modEq_iff_dvd]
    obtain ⟨-, -, hd, -⟩ := OMA.Helpers.chain_inv j
    have : (-2 : ℤ) - 2 ^ OMA.Helpers.chain j = -((2 ^ OMA.Helpers.chain j + 2 : ℕ) : ℤ) := by
      push_cast; ring
    rw [this, dvd_neg]
    exact_mod_cast hd
  · -- k = 2^i : n = i * p with p prime, p > i, p ≡ 1 mod φ(odd part of i)
    obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (show i ≠ 0 by omega)
    have hb0 : b ≠ 0 := by rintro rfl; simp at hb
    have htot : Nat.totient b ≠ 0 := (Nat.totient_pos.2 (Nat.pos_of_ne_zero hb0)).ne'
    apply Set.infinite_of_forall_exists_gt
    intro M
    obtain ⟨p, hp, hpM, hp1⟩ := Nat.exists_prime_gt_modEq_one (M + i) htot
    refine ⟨i * p, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq]
      have hcop : i.Coprime p :=
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2
          (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))
      have hmodp : 2 ^ (i * p) ≡ 2 ^ i [MOD p] := by
        have := Fact.mk hp
        rw [← ZMod.natCast_eq_natCast_iff]
        push_cast
        rw [mul_comm, pow_mul, ZMod.pow_card]
      have hmodi : 2 ^ (i * p) ≡ 2 ^ i [MOD i] := by
        have hcop2 : (2 ^ a).Coprime b := Nat.Coprime.pow_left a (Nat.coprime_two_left.2 hb)
        rw [hab]
        apply (Nat.modEq_and_modEq_iff_modEq_mul hcop2).1
        have ha : a ≤ i := by
          have := Nat.lt_two_pow_self (n := a)
          have : 2 ^ a ≤ i := by rw [hab]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hb0)
          omega
        constructor
        · have h1 : 2 ^ a ∣ 2 ^ (i * p) := pow_dvd_pow 2 (ha.trans (Nat.le_mul_of_pos_right _ hp.pos))
          have h2 : 2 ^ a ∣ 2 ^ i := pow_dvd_pow 2 ha
          rw [← hab]
          exact (Nat.modEq_zero_iff_dvd.2 h1).trans (Nat.modEq_zero_iff_dvd.2 h2).symm
        · rw [← hab]
          have hdvd : Nat.totient b ∣ p - 1 := (Nat.modEq_iff_dvd' hp.one_le).1 hp1.symm
          obtain ⟨t, ht⟩ := hdvd
          have hpt : i * p = i + Nat.totient b * (i * t) := by
            have : p = 1 + Nat.totient b * t := by have := hp.one_le; omega
            rw [this]; ring
          have hE : 2 ^ Nat.totient b ≡ 1 [MOD b] := Nat.ModEq.pow_totient (Nat.coprime_two_left.2 hb)
          rw [hpt, pow_add, pow_mul]
          calc 2 ^ i * (2 ^ Nat.totient b) ^ (i * t) ≡ 2 ^ i * 1 ^ (i * t) [MOD b] :=
                Nat.ModEq.mul_left _ (hE.pow _)
            _ = 2 ^ i := by simp
      have h := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨hmodi, hmodp⟩
      have h' := Int.natCast_modEq_iff.2 h
      push_cast at h'
      exact_mod_cast h'
    · have : M < p := by omega
      calc M < p := this
        _ ≤ i * p := Nat.le_mul_of_pos_left p (by omega)
