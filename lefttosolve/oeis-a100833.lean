import OMAStatements.S_oeis_a100833
import Mathlib

/-!
Proof of Israel's formula for A100833.

Write `fw n` for the formula. Letters at positions in different classes mod 3 differ, and
letters at positions in the same nonzero class mod 3 agree (`fw_ne`, `fw_eq`).

* `fw` has no palindromic suffix of length at least two: the middle two (or the two letters
  around the middle) of such a suffix are at distance one or two, hence differ.
* `fw` has no square suffix: if the half length `d` is not a multiple of 3, the last letter
  differs from the one `d` places before; if `d = 3e`, the positions `3m` of the second half give
  the letters `3 + v(m)` and `3 + v(m - e)` (with `v` the 2-adic valuation), and some `m` in any
  `e` consecutive integers has `v(m) ≠ v(m - e)` (`ruler`).
* Every smaller positive letter creates a forbidden suffix: a palindrome `11`, `22` or `121`,
  or, for the letter `3 + j` with `j < v(n / 3)`, a square of half length `3 * 2 ^ j` (`v_sub`).

So the greedy choice is `fw n` at each step (`main_eq`, by strong induction).
-/

namespace OMA.Helpers

open OMA.S_oeis_a100833

/-- Israel's formula. -/
def fw (n : ℕ) : ℕ := if n % 3 = 1 then 1 else if n % 3 = 2 then 2 else 3 + padicValNat 2 (n / 3)

theorem fw_ne (i i' : ℕ) (h : i % 3 ≠ i' % 3) : fw i ≠ fw i' := by
  unfold fw
  split_ifs <;> omega

theorem fw_eq (i i' : ℕ) (h : i % 3 = i' % 3) (h0 : i % 3 ≠ 0) : fw i = fw i' := by
  unfold fw
  split_ifs <;> omega

theorem fw_three (m : ℕ) : fw (3 * m) = 3 + padicValNat 2 m := by
  unfold fw
  rw [if_neg (by omega), if_neg (by omega), Nat.mul_div_cancel_left m (by norm_num)]

theorem fw_pos (n : ℕ) : 0 < fw n := by
  unfold fw
  split_ifs <;> omega

theorem v_odd (a b : ℕ) : padicValNat 2 (2 ^ a * (2 * b + 1)) = a := by
  rw [padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by omega)]
  rfl

/-- Subtracting from a multiple of `2 ^ (a + 1)` a number of valuation `a`. -/
theorem v_sub (a b y : ℕ) (hy : 2 ^ (a + 1) ∣ y) (hlt : 2 ^ a * (2 * b + 1) < y) :
    padicValNat 2 (y - 2 ^ a * (2 * b + 1)) = a := by
  obtain ⟨z, rfl⟩ := hy
  have hP : 0 < 2 ^ a := by positivity
  rw [pow_succ, mul_assoc] at hlt ⊢
  have h1 : 2 * b + 1 < 2 * z := lt_of_mul_lt_mul_left hlt (Nat.zero_le _)
  have h2 : 2 ^ a * (2 * z) - 2 ^ a * (2 * b + 1) = 2 ^ a * (2 * (z - b - 1) + 1) := by
    rw [← Nat.mul_sub]
    congr 1
    omega
  rw [h2, v_odd]

theorem ruler (e L : ℕ) (he : 0 < e) (hL : e + 1 ≤ L) :
    ∃ m, L ≤ m ∧ m + 1 ≤ L + e ∧ padicValNat 2 m ≠ padicValNat 2 (m - e) := by
  obtain ⟨k, o, ho, hek⟩ := Nat.exists_eq_two_pow_mul_odd he.ne'
  obtain ⟨o', rfl⟩ := ho
  set P := 2 ^ k with hPdef
  have hP : 0 < P := by positivity
  have hPe : P ≤ e := by rw [hek]; exact Nat.le_mul_of_pos_right P (by omega)
  set j := (L + P - 1) / P with hj
  have hdm := Nat.div_add_mod (L + P - 1) P
  have hmod := Nat.mod_lt (L + P - 1) hP
  rw [← hj] at hdm
  have hm1 : L ≤ P * j := by omega
  have hm2 : P * j + 1 ≤ L + e := by omega
  refine ⟨P * j, hm1, hm2, ?_⟩
  have hjo : 2 * o' + 1 < j := by
    by_contra hcon
    have : P * j ≤ P * (2 * o' + 1) := Nat.mul_le_mul_left P (by omega)
    omega
  have hsub : P * j - e = P * (j - (2 * o' + 1)) := by rw [hek, ← Nat.mul_sub]
  rw [hsub, padicValNat.mul hP.ne' (by omega), padicValNat.mul hP.ne' (by omega), hPdef,
    padicValNat.prime_pow]
  intro hcon
  have hc : padicValNat 2 j = padicValNat 2 (j - (2 * o' + 1)) := by omega
  rcases Nat.even_or_odd j with hje | hjo'
  · have h1 : 1 ≤ padicValNat 2 j := one_le_padicValNat_of_dvd (by omega) (even_iff_two_dvd.1 hje)
    have h2 : padicValNat 2 (j - (2 * o' + 1)) = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      obtain ⟨t, ht⟩ := hje
      omega
    omega
  · have h1 : padicValNat 2 j = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      obtain ⟨t, ht⟩ := hjo'
      omega
    have h2 : 1 ≤ padicValNat 2 (j - (2 * o' + 1)) := by
      apply one_le_padicValNat_of_dvd (by omega)
      obtain ⟨t, ht⟩ := hjo'
      exact ⟨t - o', by omega⟩
    omega

theorem allowed_congr (w w' : ℕ → ℕ) (n : ℕ) (h : ∀ i, 1 ≤ i → i ≤ n → w i = w' i) :
    AllowedEnd w n ↔ AllowedEnd w' n := by
  unfold AllowedEnd
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun s hs hsn => ?_, fun d hd hdn => ?_⟩
    · obtain ⟨i, hi1, hi2, hne⟩ := h1 s hs hsn
      refine ⟨i, hi1, hi2, ?_⟩
      rwa [← h i (by omega) hi2, ← h (s + n - i) (by omega) (by omega)]
    · obtain ⟨i, hi1, hi2, hne⟩ := h2 d hd hdn
      refine ⟨i, hi1, hi2, ?_⟩
      rwa [← h i (by omega) hi2, ← h (i - d) (by omega) (by omega)]
  · rintro ⟨h1, h2⟩
    refine ⟨fun s hs hsn => ?_, fun d hd hdn => ?_⟩
    · obtain ⟨i, hi1, hi2, hne⟩ := h1 s hs hsn
      refine ⟨i, hi1, hi2, ?_⟩
      rwa [h i (by omega) hi2, h (s + n - i) (by omega) (by omega)]
    · obtain ⟨i, hi1, hi2, hne⟩ := h2 d hd hdn
      refine ⟨i, hi1, hi2, ?_⟩
      rwa [h i (by omega) hi2, h (i - d) (by omega) (by omega)]

theorem good (n : ℕ) : AllowedEnd fw n := by
  refine ⟨fun s hs hsn => ?_, fun d hd hdn => ?_⟩
  · by_cases hp : (s + n) % 2 = 1
    · refine ⟨(s + n - 1) / 2, by omega, by omega, ?_⟩
      rw [show s + n - (s + n - 1) / 2 = (s + n - 1) / 2 + 1 by omega]
      exact fw_ne _ _ (by omega)
    · refine ⟨(s + n) / 2 - 1, by omega, by omega, ?_⟩
      rw [show s + n - ((s + n) / 2 - 1) = ((s + n) / 2 - 1) + 2 by omega]
      exact fw_ne _ _ (by omega)
  · by_cases hd3 : d % 3 = 0
    · obtain ⟨e, rfl⟩ : ∃ e, d = 3 * e := ⟨d / 3, by omega⟩
      obtain ⟨m, hm1, hm2, hv⟩ := ruler e (n / 3 - e + 1) (by omega) (by omega)
      refine ⟨3 * m, by omega, by omega, ?_⟩
      rw [show 3 * m - 3 * e = 3 * (m - e) by omega, fw_three, fw_three]
      omega
    · exact ⟨n, by omega, le_rfl, fw_ne _ _ (by omega)⟩

theorem bad (n c : ℕ) (hn : 1 ≤ n) (hc : 0 < c) (hcn : c < fw n) :
    ¬ AllowedEnd (fun i => if i = n then c else fw i) n := by
  rintro ⟨h1, h2⟩
  have hf : ∀ i, i ≠ n → (if i = n then c else fw i) = fw i := fun i hi => if_neg hi
  have hcn' := hcn
  unfold fw at hcn'
  by_cases h31 : n % 3 = 1
  · rw [if_pos h31] at hcn'
    omega
  by_cases h32 : n % 3 = 2
  · rw [if_neg h31, if_pos h32] at hcn'
    obtain ⟨i, hi1, hi2, hne⟩ := h1 (n - 1) (by omega) (by omega)
    beta_reduce at hne
    have hn1 : fw (n - 1) = 1 := by unfold fw; rw [if_pos (by omega)]
    rcases (show i = n - 1 ∨ i = n by omega) with h | h
    · rw [h, show n - 1 + n - (n - 1) = n by omega, if_neg (by omega : n - 1 ≠ n), if_pos rfl,
        hn1] at hne
      omega
    · rw [h, show n - 1 + n - n = n - 1 by omega, if_neg (by omega : n - 1 ≠ n), if_pos rfl,
        hn1] at hne
      omega
  rw [if_neg h31, if_neg h32] at hcn'
  obtain ⟨M, rfl⟩ : ∃ M, n = 3 * M := ⟨n / 3, by omega⟩
  rw [Nat.mul_div_cancel_left M (by norm_num)] at hcn'
  have hfa : fw (3 * M - 1) = 2 := by unfold fw; rw [if_neg (by omega), if_pos (by omega)]
  have hfb : fw (3 * M - 2) = 1 := by unfold fw; rw [if_pos (by omega)]
  by_cases hc1 : c = 1
  · subst hc1
    obtain ⟨i, hi1, hi2, hne⟩ := h1 (3 * M - 2) (by omega) (by omega)
    beta_reduce at hne
    rcases (show i = 3 * M - 2 ∨ i = 3 * M - 1 ∨ i = 3 * M by omega) with h | h | h
    · rw [h, show 3 * M - 2 + 3 * M - (3 * M - 2) = 3 * M by omega,
        if_neg (by omega : 3 * M - 2 ≠ 3 * M), if_pos rfl, hfb] at hne
      omega
    · rw [h, show 3 * M - 2 + 3 * M - (3 * M - 1) = 3 * M - 1 by omega] at hne
      exact hne rfl
    · rw [h, show 3 * M - 2 + 3 * M - 3 * M = 3 * M - 2 by omega,
        if_neg (by omega : 3 * M - 2 ≠ 3 * M), if_pos rfl, hfb] at hne
      omega
  by_cases hc2 : c = 2
  · subst hc2
    obtain ⟨i, hi1, hi2, hne⟩ := h1 (3 * M - 1) (by omega) (by omega)
    beta_reduce at hne
    rcases (show i = 3 * M - 1 ∨ i = 3 * M by omega) with h | h
    · rw [h, show 3 * M - 1 + 3 * M - (3 * M - 1) = 3 * M by omega,
        if_neg (by omega : 3 * M - 1 ≠ 3 * M), if_pos rfl, hfa] at hne
      omega
    · rw [h, show 3 * M - 1 + 3 * M - 3 * M = 3 * M - 1 by omega,
        if_neg (by omega : 3 * M - 1 ≠ 3 * M), if_pos rfl, hfa] at hne
      omega
  -- c = 3 + j with j < v(M): a square of half length 3 * 2 ^ j
  obtain ⟨j, rfl⟩ : ∃ j, c = 3 + j := ⟨c - 3, by omega⟩
  have hj : j + 1 ≤ padicValNat 2 M := by omega
  have hM0 : M ≠ 0 := by omega
  have hdvd : 2 ^ (j + 1) ∣ M :=
    (pow_dvd_pow 2 hj).trans pow_padicValNat_dvd
  obtain ⟨q, hq⟩ := hdvd
  have hP : 0 < 2 ^ j := by positivity
  have hq0 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h, mul_zero] at hq; omega
    · exact h
  have hMP : 2 * 2 ^ j ≤ M := by
    rw [hq, pow_succ]
    calc 2 * 2 ^ j = 2 ^ j * 2 * 1 := by ring
      _ ≤ 2 ^ j * 2 * q := Nat.mul_le_mul_left _ hq0
  obtain ⟨i, hi1, hi2, hne⟩ := h2 (3 * 2 ^ j) (by omega) (by omega)
  beta_reduce at hne
  by_cases hin : i = 3 * M
  · subst hin
    rw [if_pos rfl, hf _ (by omega), show 3 * M - 3 * 2 ^ j = 3 * (M - 2 ^ j) by omega,
      fw_three] at hne
    have : padicValNat 2 (M - 2 ^ j * (2 * 0 + 1)) = j :=
      v_sub j 0 M ⟨q, hq⟩ (by omega)
    rw [show 2 ^ j * (2 * 0 + 1) = 2 ^ j by ring] at this
    omega
  rw [hf _ hin, hf _ (by omega)] at hne
  by_cases hi3 : i % 3 = 0
  · obtain ⟨m, rfl⟩ : ∃ m, i = 3 * m := ⟨i / 3, by omega⟩
    rw [show 3 * m - 3 * 2 ^ j = 3 * (m - 2 ^ j) by omega, fw_three, fw_three] at hne
    -- m = M - t with 0 < t < 2 ^ j
    obtain ⟨a, b, hb, ht⟩ := Nat.exists_eq_two_pow_mul_odd (n := M - m) (by omega)
    obtain ⟨b', rfl⟩ := hb
    have hta : 2 ^ a < 2 ^ j := by
      have : 2 ^ a ≤ 2 ^ a * (2 * b' + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have haj : a < j := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hta
    have hdiv : 2 ^ (a + 1) ∣ M := (pow_dvd_pow 2 (by omega)).trans ⟨q, hq⟩
    have e1 : m = M - 2 ^ a * (2 * b' + 1) := by omega
    have v1 : padicValNat 2 m = a := by rw [e1]; exact v_sub a b' M hdiv (by omega)
    have hja : 2 ^ j = 2 ^ a * 2 ^ (j - a - 1) * 2 := by
      rw [← pow_add, ← pow_succ]
      congr 1
      omega
    have e2 : m - 2 ^ j = M - 2 ^ a * (2 * (2 ^ (j - a - 1) + b') + 1) := by
      have : 2 ^ a * (2 * (2 ^ (j - a - 1) + b') + 1) = 2 ^ j + 2 ^ a * (2 * b' + 1) := by
        rw [hja]; ring
      omega
    have v2 : padicValNat 2 (m - 2 ^ j) = a := by
      rw [e2]
      apply v_sub a _ M hdiv
      have : 2 ^ a * (2 * (2 ^ (j - a - 1) + b') + 1) = 2 ^ j + 2 ^ a * (2 * b' + 1) := by
        rw [hja]; ring
      omega
    omega
  · exact hne (fw_eq _ _ (by omega) hi3)

theorem main_eq (n : ℕ) (hn : 0 < n) : a n = fw n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [a, if_neg (by omega)]
    have hset : {c : ℕ | 0 < c ∧
        AllowedEnd (fun i => if _h : i < n ∧ 0 < i then a i else c) n} =
        {c : ℕ | 0 < c ∧ AllowedEnd (fun i => if i = n then c else fw i) n} := by
      ext c
      simp only [Set.mem_ofPred_eq]
      refine and_congr Iff.rfl (allowed_congr _ _ n fun i hi1 hi2 => ?_)
      by_cases hin : i = n
      · rw [dif_neg (by omega), if_pos hin]
      · rw [dif_pos (by omega), if_neg hin, ih i (by omega) (by omega)]
    rw [hset]
    have hmem : fw n ∈ {c : ℕ | 0 < c ∧ AllowedEnd (fun i => if i = n then c else fw i) n} := by
      refine ⟨fw_pos n, (allowed_congr _ _ n fun i _ _ => ?_).2 (good n)⟩
      by_cases hin : i = n
      · rw [if_pos hin, hin]
      · rw [if_neg hin]
    refine le_antisymm (Nat.sInf_le hmem) ?_
    by_contra hlt
    have hm := Nat.sInf_mem ⟨_, hmem⟩
    exact bad n _ hn hm.1 (not_le.1 hlt) hm.2

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a100833.main := by
  intro n hn
  rw [OMA.Helpers.main_eq n hn]
  rfl
