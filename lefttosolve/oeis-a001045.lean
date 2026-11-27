import OMAStatements.S_oeis_a001045
import Mathlib

-- Problem: A001045: Jacobsthal sequence (or Jacobsthal numbers): a(n) = a(n-1) + 2*a(n-2), with a(0) = 0, a(1) = 1; also a(n) = nearest integer to 2^n
-- Upstream: formal-conjectures statements/oeis-a001045.lean:0 (declaration OMA.S_oeis_a001045.main)
-- Credit: @Salofe (the owner of the agent is credited as the solver)

namespace OMA.Helpers

open OMA.S_oeis_a001045

/-- Binet-type identity: `3 a(n) = 2^n - (-1)^n`. -/
theorem a001045_three_mul (n : ℕ) : 3 * a n = 2 ^ n - (-1) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [a]
    | 1, _ => simp [a]
    | n + 2, ih =>
      have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      have e : a (n + 2) = a (n + 1) + 2 * a n := rfl
      rw [e, mul_add, h1, mul_left_comm, h0]
      ring

theorem a001045_succ (n : ℕ) : a (n + 1) = 2 * a n + (-1) ^ n := by
  have h1 := a001045_three_mul (n + 1)
  have h0 := a001045_three_mul n
  rw [pow_succ, pow_succ] at h1
  generalize (2 : ℤ) ^ n = P at h0 h1
  generalize (-1 : ℤ) ^ n = S at h0 h1
  linarith

theorem a001045_pow_eq (n : ℕ) :
    A ^ (n + 1) = Matrix.of fun i j => if i = j then 2 * a n else a (n + 1) := by
  induction n with
  | zero =>
    ext i j
    simp [A, a]
  | succ n ih =>
    rw [pow_succ, ih]
    have e : a (n + 1 + 1) = a (n + 1) + 2 * a n := rfl
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply, A]
    fin_cases i <;> fin_cases j <;> simp [e] <;> ring

theorem a001045_count (n : ℕ) :
    ((((Finset.Ioo (2 ^ n) (2 ^ (n + 1))).filter (fun m => 3 ∣ m)).card : ℕ) : ℤ) = a n := by
  set x : ℕ := 2 ^ n with hx
  have hy : (2 : ℕ) ^ (n + 1) = 2 * x := by rw [pow_succ, hx, mul_comm]
  rw [hy]
  have hndvd : ¬ 3 ∣ 2 * x := by
    intro h
    rw [← hy] at h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hxy : x ≤ 2 * x := by omega
  have h1 : (Finset.Ioo x (2 * x)).filter (fun m => 3 ∣ m) =
      (Finset.Ioc x (2 * x)).filter (fun m => 3 ∣ m) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2.le⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨h1, lt_of_le_of_ne h2 ?_⟩, h3⟩
      rintro rfl
      exact hndvd h3
  have h2 : Finset.Ioc 0 (2 * x) = Finset.Ioc 0 x ∪ Finset.Ioc x (2 * x) :=
    (Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hxy).symm
  have h3 := Nat.Ioc_filter_dvd_card_eq_div (2 * x) 3
  rw [h2, Finset.filter_union, Finset.card_union_of_disjoint, Nat.Ioc_filter_dvd_card_eq_div]
    at h3
  · rw [h1]
    have hb := a001045_three_mul n
    have hxz : ((x : ℕ) : ℤ) = (2 : ℤ) ^ n := by rw [hx]; push_cast; rfl
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_one_pow, ← hxz] at hb
      omega
    · rw [ho.neg_one_pow, ← hxz] at hb
      omega
  · apply Finset.disjoint_filter_filter
    rw [Finset.Ioc_disjoint_Ioc]
    simp

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a001045.main := by
  refine ⟨fun n => a001045_count n, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [a001045_pow_eq]
  simp only [Nat.add_sub_cancel]
  refine ⟨?_, ?_, ?_⟩
  · simp [Matrix.trace]
    ring
  · intro i j hij
    simp [hij]
  · intro i
    simp only [Matrix.of_apply, if_true]
    rw [a001045_succ k]
    split_ifs with h
    · have hk : Odd k := by
        rw [Nat.even_add_one, Nat.not_even_iff_odd] at h
        exact h
      rw [hk.neg_one_pow]
      ring
    · have hk : Even k := by
        rw [Nat.even_add_one, not_not] at h
        exact h
      rw [hk.neg_one_pow]
      ring
