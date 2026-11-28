import OMAStatements.S_oeis_a068129
import Mathlib

namespace OMA.Helpers

theorem a068129_pow_ten (k : ℕ) (h : (Nat.digits 10 k).sum = 1) : ∃ j, k = 10 ^ j := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at h
    · rw [Nat.digits_def' (by norm_num) hk, List.sum_cons] at h
      have hlt : k / 10 < k := Nat.div_lt_self hk (by norm_num)
      have hdm := Nat.div_add_mod k 10
      rcases Nat.eq_zero_or_pos (k % 10) with h0 | h0
      · rw [h0, zero_add] at h
        obtain ⟨j, hj⟩ := ih _ hlt h
        refine ⟨j + 1, ?_⟩
        rw [h0, hj] at hdm
        rw [pow_succ]
        omega
      · have h2 : (Nat.digits 10 (k / 10)).sum = 0 := by omega
        have h3 : k / 10 = 0 := by
          by_contra hne
          have hl := Nat.getLast_digit_ne_zero 10 hne
          have hmem := List.getLast_mem (Nat.digits_ne_nil_iff_ne_zero.mpr hne : Nat.digits 10 (k / 10) ≠ [])
          have := List.le_sum_of_mem hmem
          omega
        exact ⟨0, by omega⟩

theorem a068129_core (m P Q : ℕ) (hP2 : 2 ≤ P) (hQ2 : 2 ≤ Q) (h : m * (m + 1) = P * Q)
    (hPQ : Nat.Coprime P Q) (hPd : P ∣ m ∨ P ∣ m + 1) (hQd : Q ∣ m ∨ Q ∣ m + 1) :
    (m = P ∧ m + 1 = Q) ∨ (m = Q ∧ m + 1 = P) ∨ P * Q ≤ 2 := by
  have hPQpos : 0 < P * Q := by positivity
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at h
    omega
  rcases hPd with hPm | hPm <;> rcases hQd with hQm | hQm
  · exfalso
    have hle : P * Q ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) (hPQ.mul_dvd_of_dvd_of_dvd hPm hQm)
    have : m * (m + 1) ≤ m * 1 := by nlinarith
    have : m + 1 ≤ 1 := Nat.le_of_mul_le_mul_left this (Nat.pos_of_ne_zero hm0)
    omega
  · obtain ⟨u, hu⟩ := hPm
    obtain ⟨v, hv⟩ := hQm
    have huv : P * Q * (u * v) = P * Q * 1 := by
      calc P * Q * (u * v) = (P * u) * (Q * v) := by ring
        _ = m * (m + 1) := by rw [← hu, ← hv]
        _ = P * Q * 1 := by rw [h, mul_one]
    have h1 : u * v = 1 := Nat.eq_of_mul_eq_mul_left hPQpos huv
    have hu1 : u = 1 := Nat.eq_one_of_mul_eq_one_right h1
    have hv1 : v = 1 := Nat.eq_one_of_mul_eq_one_left h1
    subst hu1 hv1
    left
    exact ⟨by rw [hu, mul_one], by rw [hv, mul_one]⟩
  · obtain ⟨u, hu⟩ := hPm
    obtain ⟨v, hv⟩ := hQm
    have huv : P * Q * (u * v) = P * Q * 1 := by
      calc P * Q * (u * v) = (Q * v) * (P * u) := by ring
        _ = m * (m + 1) := by rw [← hu, ← hv]
        _ = P * Q * 1 := by rw [h, mul_one]
    have h1 : u * v = 1 := Nat.eq_of_mul_eq_mul_left hPQpos huv
    have hu1 : u = 1 := Nat.eq_one_of_mul_eq_one_right h1
    have hv1 : v = 1 := Nat.eq_one_of_mul_eq_one_left h1
    subst hu1 hv1
    right; left
    exact ⟨by rw [hv, mul_one], by rw [hu, mul_one]⟩
  · right; right
    have hle : P * Q ≤ m + 1 := Nat.le_of_dvd (by omega) (hPQ.mul_dvd_of_dvd_of_dvd hPm hQm)
    have hm1 : m ≤ 1 := by
      by_contra hm1
      push Not at hm1
      have : 2 * (m + 1) ≤ m * (m + 1) := Nat.mul_le_mul_right _ hm1
      omega
    interval_cases m <;> omega

theorem a068129_j_le (j m : ℕ) (h : m * (m + 1) = 2 ^ (j + 1) * 5 ^ j) : j ≤ 1 := by
  have hcop : Nat.Coprime m (m + 1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right m)
  have hP : 2 ^ (j + 1) ∣ m ∨ 2 ^ (j + 1) ∣ m + 1 :=
    (hcop.isPrimePow_dvd_mul (Nat.prime_two.isPrimePow.pow (Nat.succ_ne_zero j))).mp
      (h ▸ dvd_mul_right _ _)
  have hQ : 5 ^ j ∣ m ∨ 5 ^ j ∣ m + 1 := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · left; simp
    · exact (hcop.isPrimePow_dvd_mul ((by norm_num : Nat.Prime 5).isPrimePow.pow hj.ne')).mp
        (h ▸ dvd_mul_left _ _)
  by_contra hj
  push Not at hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  have e1 : 2 ^ (i + 2 + 1) = 8 * 2 ^ i := by ring
  have e2 : 5 ^ (i + 2) = 25 * 5 ^ i := by ring
  have hi : 2 ^ i ≤ 5 ^ i := Nat.pow_le_pow_left (by norm_num) i
  have hi0 : 0 < 2 ^ i := by positivity
  have hPQ : Nat.Coprime (2 ^ (i + 2 + 1)) (5 ^ (i + 2)) := Nat.Coprime.pow _ _ (by norm_num)
  simp only [e1, e2] at h hP hQ hPQ
  generalize 2 ^ i = a at *
  generalize 5 ^ i = b at *
  rcases a068129_core m (8 * a) (25 * b) (by omega) (by omega) h hPQ hP hQ with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | h3
  · omega
  · omega
  · have : 8 * 25 ≤ 8 * a * (25 * b) := Nat.mul_le_mul (by omega) (by omega)
    omega

end OMA.Helpers

open OMA.S_oeis_a068129 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a068129.main) := by
  intro H
  have hinf := H 1 le_rfl ⟨1, by norm_num⟩
  apply hinf
  refine (Set.finite_le_nat 10).subset ?_
  rintro k ⟨⟨m, hm⟩, hs⟩
  obtain ⟨j, rfl⟩ := OMA.Helpers.a068129_pow_ten k hs
  have hev : 2 ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
  have h2 : m * (m + 1) = 2 ^ (j + 1) * 5 ^ j := by
    have := Nat.div_mul_cancel hev
    rw [← hm] at this
    rw [← this, pow_succ, show (10 : ℕ) = 2 * 5 by norm_num, mul_pow]
    ring
  have hj := OMA.Helpers.a068129_j_le j m h2
  show 10 ^ j ≤ 10
  calc 10 ^ j ≤ 10 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj
    _ = 10 := by norm_num
