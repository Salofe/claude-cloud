import OMAStatements.S_oeis_a204988
import Mathlib

-- Problem: A204988: The index j < k such that n divides 2^k - 2^j, where k is the least index (A204987) for which such j exists.
-- Upstream: formal-conjectures statements/oeis-a204988.lean:0 (declaration OMA.S_oeis_a204988.main)
-- Credit: @Salofe (the owner of the agent is credited as the solver)
-- Proof: write n = 2^v * m with m odd and w = max v 1. Since 2^k - 2^j = 2^j * (2^(k-j) - 1)
-- with the second factor odd, n divides it iff v <= j and m divides 2^(k-j) - 1; the pair
-- (w, w + (k - j)) is then valid too, so minimality of k forces j = w (cf. A. Howroyd, OEIS A204988).

namespace OMA.Helpers

open OMA.S_oeis_a204988

/-- Splitting `2^k - 2^j = 2^j * (2^(k-j) - 1)` against `2^v * m` with `m` odd. -/
theorem a204988_key {v m j k : ℕ} (hm : Odd m) (hjk : j < k)
    (h : 2 ^ v * m ∣ 2 ^ k - 2 ^ j) : v ≤ j ∧ m ∣ 2 ^ (k - j) - 1 := by
  have e : 2 ^ k - 2 ^ j = 2 ^ j * (2 ^ (k - j) - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hjk.le]
  rw [e] at h
  have hpos : 1 ≤ 2 ^ (k - j) := Nat.one_le_two_pow
  have hev : Even (2 ^ (k - j)) := (Nat.even_pow' (by omega)).2 even_two
  have hodd : Odd (2 ^ (k - j) - 1) := Nat.Even.sub_odd hpos hev odd_one
  constructor
  · have h1 : 2 ^ v ∣ 2 ^ j * (2 ^ (k - j) - 1) := dvd_trans (dvd_mul_right _ _) h
    have hcop : Nat.Coprime (2 ^ v) (2 ^ (k - j) - 1) :=
      Nat.Coprime.pow_left _ ((Nat.coprime_two_left).2 hodd)
    have h2 := hcop.dvd_of_dvd_mul_right h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2
  · have h2 : m ∣ 2 ^ j * (2 ^ (k - j) - 1) := dvd_trans (dvd_mul_left _ _) h
    have hcop : Nat.Coprime m (2 ^ j) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_two_right).2 hm)
    exact hcop.dvd_of_dvd_mul_left h2

/-- The converse direction: a valid pair starting at `w`. -/
theorem a204988_back {v m w d : ℕ} (hvw : v ≤ w) (hd : m ∣ 2 ^ d - 1) :
    2 ^ v * m ∣ 2 ^ (w + d) - 2 ^ w := by
  have e : 2 ^ (w + d) - 2 ^ w = 2 ^ w * (2 ^ d - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_add]
  rw [e]
  exact mul_dvd_mul (pow_dvd_pow 2 hvw) hd

end OMA.Helpers

open OMA.S_oeis_a204988 in
theorem OMA.solution : type_of% @OMA.S_oeis_a204988.main := by
  intro n hn
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
  set w := max v 1 with hw
  have hvw : v ≤ w := le_max_left _ _
  have h1w : 1 ≤ w := le_max_right _ _
  have hm0 : 0 < m := hm.pos
  -- nonemptiness of the set defining kmin
  have hne : (w + Nat.totient m) ∈
      {k : ℕ | ∃ j, 1 ≤ j ∧ j < k ∧ 2 ^ v * m ∣ 2 ^ k - 2 ^ j} := by
    refine ⟨w, h1w, ?_, ?_⟩
    · have := Nat.totient_pos.2 hm0
      omega
    · apply OMA.Helpers.a204988_back hvw
      have hc : Nat.Coprime 2 m := (Nat.coprime_two_left).2 hm
      have h := (Nat.ModEq.pow_totient hc).symm
      exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).1 h
  have hK : kmin (2 ^ v * m) ∈
      {k : ℕ | ∃ j, 1 ≤ j ∧ j < k ∧ 2 ^ v * m ∣ 2 ^ k - 2 ^ j} := Nat.sInf_mem ⟨_, hne⟩
  -- any valid j for kmin must be w
  have claim : ∀ j, 1 ≤ j → j < kmin (2 ^ v * m) →
      2 ^ v * m ∣ 2 ^ kmin (2 ^ v * m) - 2 ^ j → j = w := by
    intro j hj1 hjK hdvd
    obtain ⟨hvj, hmd⟩ := OMA.Helpers.a204988_key hm hjK hdvd
    have hwj : w ≤ j := max_le hvj hj1
    by_contra hneq
    have hlt : w < j := lt_of_le_of_ne hwj (Ne.symm hneq)
    have hmem : (w + (kmin (2 ^ v * m) - j)) ∈
        {k : ℕ | ∃ j, 1 ≤ j ∧ j < k ∧ 2 ^ v * m ∣ 2 ^ k - 2 ^ j} := by
      refine ⟨w, h1w, by omega, OMA.Helpers.a204988_back hvw hmd⟩
    have hle : kmin (2 ^ v * m) ≤ w + (kmin (2 ^ v * m) - j) := Nat.sInf_le hmem
    omega
  obtain ⟨j0, hj01, hj0K, hj0d⟩ := hK
  have hj0 : j0 = w := claim j0 hj01 hj0K hj0d
  have hT : a (2 ^ v * m) ∈ {j : ℕ | 1 ≤ j ∧ j < kmin (2 ^ v * m) ∧
      2 ^ v * m ∣ 2 ^ kmin (2 ^ v * m) - 2 ^ j} := Nat.sInf_mem ⟨j0, hj01, hj0K, hj0d⟩
  obtain ⟨ha1, haK, had⟩ := hT
  rw [claim _ ha1 haK had]
  -- compute the right-hand side
  have hnd : ¬ 2 ∣ m := by
    rintro ⟨c, rfl⟩
    exact (Nat.not_even_iff_odd.2 hm) (even_two_mul c)
  have hval : padicValNat 2 (2 ^ v * m) = v := by
    rw [padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hnd, add_zero]
  rw [hval, hw]
  rcases Nat.eq_zero_or_pos v with h0 | hv
  · subst h0
    have : m % 2 = 1 := Nat.odd_iff.1 hm
    simp [this]
  · have h2 : 2 ^ v * m % 2 = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) m
    simp [h2]
    omega
