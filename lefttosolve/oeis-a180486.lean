import OMAStatements.S_oeis_a180486

/-!
Proof of Barker's three conjectures for A180486.

For every k, twice the sum of the integers strictly between k and 2k is 3k(k-1) (Gauss).
* If k = 2m + 1 is odd, the sum is k * 3m, so the remainder modulo k is 0 and k gives no term.
* A nonprime k = 2m with m = 0 or m = 1 is impossible (k >= 1, and 2 is prime); for
  k = 2r + 4 the sum is (2r + 4)(3r + 4) + (r + 2), so the remainder is r + 2 (nonzero) and the
  rounded-up quotient is 3r + 5.
Every 2r + 4 is a nonprime k >= 1, hence a term of A018252 (`Nat.nth_count`), and every term of
A018252 is a nonprime k >= 1 (`Nat.nth_mem_of_infinite`). So the set of values is exactly
{v | v % 3 = 2, v >= 5}, whose (n-1)-th element is 3n + 2: below 3n + 2 it has n - 1 elements
(`Nat.count`, by induction). The recurrence and the generating function follow from this
closed form by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a180486

/-- Twice the sum of the integers strictly between `k` and `2k` is `3k(k-1)`. -/
theorem two_mul_sumIoo (k : ℕ) :
    2 * ∑ i ∈ Finset.Ioo k (2 * k), i = 3 * k * (k - 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have h1 := Finset.sum_range_add_sum_Ico (fun i => i) (show k + 1 ≤ 2 * k by omega)
  rw [Finset.Ico_add_one_left_eq_Ioo] at h1
  have h2 := Finset.sum_range_id_mul_two (k + 1)
  have h3 := Finset.sum_range_id_mul_two (2 * k)
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := by omega
  have e2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  have e3 : m + 1 - 1 = m := by omega
  rw [e1] at h2
  rw [e2] at h3
  rw [e3]
  nlinarith [h1, h2, h3]

theorem sumIoo_odd (m : ℕ) :
    ∑ i ∈ Finset.Ioo (2 * m + 1) (2 * (2 * m + 1)), i = (2 * m + 1) * (3 * m) := by
  have h := two_mul_sumIoo (2 * m + 1)
  have e : 2 * m + 1 - 1 = 2 * m := by omega
  rw [e] at h
  nlinarith [h]

theorem sumIoo_even (r : ℕ) :
    ∑ i ∈ Finset.Ioo (2 * r + 4) (2 * (2 * r + 4)), i = (2 * r + 4) * (3 * r + 4) + (r + 2) := by
  have h := two_mul_sumIoo (2 * r + 4)
  have e : 2 * r + 4 - 1 = 2 * r + 3 := by omega
  rw [e] at h
  nlinarith [h]

/-- The remainder and the rounded-up quotient for `k = 2r + 4`. -/
theorem val_even (r : ℕ) :
    (∑ i ∈ Finset.Ioo (2 * r + 4) (2 * (2 * r + 4)), i) % (2 * r + 4) = r + 2 ∧
    ⌈((∑ i ∈ Finset.Ioo (2 * r + 4) (2 * (2 * r + 4)), i : ℕ) : ℚ) / ((2 * r + 4 : ℕ) : ℚ)⌉₊ =
      3 * r + 5 := by
  rw [sumIoo_even]
  constructor
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.ceil_eq_iff (by omega)]
    have hpos : (0 : ℚ) < ((2 * r + 4 : ℕ) : ℚ) := by positivity
    have e : 3 * r + 5 - 1 = 3 * r + 4 := by omega
    rw [e]
    constructor
    · rw [lt_div_iff₀ hpos]
      push_cast
      nlinarith
    · rw [div_le_iff₀ hpos]
      push_cast
      nlinarith

/-- The nonprime numbers `k ≥ 1` form an infinite set. -/
theorem np_infinite : (Set.ofPred (fun k : ℕ => 1 ≤ k ∧ ¬ k.Prime)).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  refine ⟨2 * N + 4, ⟨by omega, ?_⟩, by omega⟩
  intro hp
  have := hp.eq_one_or_self_of_dvd 2 ⟨N + 2, by ring⟩
  omega

theorem A018252_np (j : ℕ) : 1 ≤ A018252 j ∧ ¬ (A018252 j).Prime :=
  Nat.nth_mem_of_infinite np_infinite (j - 1)

theorem A018252_surj {k : ℕ} (hk : 1 ≤ k ∧ ¬ k.Prime) : ∃ j, 1 ≤ j ∧ A018252 j = k := by
  classical
  refine ⟨Nat.count (fun k => 1 ≤ k ∧ ¬ k.Prime) k + 1, by omega, ?_⟩
  unfold A018252
  rw [Nat.add_sub_cancel]
  exact Nat.nth_count hk

/-- A nonprime `k ≥ 1` for which the sum is not a multiple of `k` is of the form `2r + 4`. -/
theorem even_form {k : ℕ} (hk : 1 ≤ k ∧ ¬ k.Prime)
    (hmod : (∑ i ∈ Finset.Ioo k (2 * k), i) % k ≠ 0) : ∃ r, k = 2 * r + 4 := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' k
  · subst hm
    rcases (show m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with h | h | h
    · omega
    · subst h
      exact absurd Nat.prime_two hk.2
    · exact ⟨m - 2, by omega⟩
  · subst hm
    exfalso
    apply hmod
    rw [sumIoo_odd]
    exact Nat.mul_mod_right _ _

theorem mem_S_iff (v : ℕ) : v ∈ S ↔ v % 3 = 2 ∧ 5 ≤ v := by
  constructor
  · rintro ⟨j, -, hmod, rfl⟩
    unfold A179896 at hmod ⊢
    obtain ⟨r, hr⟩ := even_form (A018252_np j) hmod
    rw [hr, (val_even r).2]
    omega
  · rintro ⟨h3, h5⟩
    obtain ⟨r, rfl⟩ : ∃ r, v = 3 * r + 5 := ⟨(v - 5) / 3, by omega⟩
    have hnp : 1 ≤ 2 * r + 4 ∧ ¬ (2 * r + 4).Prime := by
      refine ⟨by omega, fun hp => ?_⟩
      have := hp.eq_one_or_self_of_dvd 2 ⟨r + 2, by ring⟩
      omega
    obtain ⟨j, hj, hjk⟩ := A018252_surj hnp
    refine ⟨j, hj, ?_, ?_⟩
    · unfold A179896
      rw [hjk, (val_even r).1]
      omega
    · unfold A179896
      rw [hjk, (val_even r).2]

theorem count_q (n : ℕ) : Nat.count (fun v => v % 3 = 2 ∧ 5 ≤ v) (3 * n + 2) = n - 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show 3 * (n + 1) + 2 = 3 * n + 2 + 1 + 1 + 1 by ring, Nat.count_succ, Nat.count_succ,
      Nat.count_succ, ih]
    split_ifs <;> omega

theorem a_closed (n : ℕ) (hn : 1 ≤ n) : a n = 2 + 3 * n := by
  have hS : (fun x => x ∈ S) = (fun v => v % 3 = 2 ∧ 5 ≤ v) :=
    funext fun v => propext (mem_S_iff v)
  have key : a n = Nat.nth (fun v => v % 3 = 2 ∧ 5 ≤ v) (n - 1) :=
    congrArg (fun p => Nat.nth p (n - 1)) hS
  rw [key, ← count_q n, Nat.nth_count (p := fun v => v % 3 = 2 ∧ 5 ≤ v) ⟨by omega, by omega⟩]
  ring

theorem a_rec (n : ℕ) (hn : 2 < n) : (a n : ℤ) = 2 * a (n - 1) - a (n - 2) := by
  rw [a_closed n (by omega), a_closed (n - 1) (by omega), a_closed (n - 2) (by omega)]
  push_cast
  omega

open PowerSeries in
theorem gen_fun : (1 - X) ^ 2 * series = X * (5 - 2 * X) := by
  have hc : ∀ n, coeff n series = if n = 0 then 0 else ((2 + 3 * n : ℕ) : ℚ) := by
    intro n
    unfold series
    rw [coeff_mk]
    split_ifs with h
    · rfl
    · rw [a_closed n (by omega)]
  have e : (1 - X : PowerSeries ℚ) ^ 2 * series =
      series - X * series - X * series + X * (X * series) := by ring
  have e2 : (X : PowerSeries ℚ) * (5 - 2 * X) = X * C 5 - X * (X * C 2) := by
    simp only [map_ofNat]
    ring
  have h0 : constantCoeff series = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hc, if_pos rfl]
  rw [e, e2]
  ext n
  rcases n with _ | _ | n
  · simp [h0]
  · simp [hc, coeff_succ_X_mul]
  · simp only [map_add, map_sub, coeff_succ_X_mul, hc, coeff_C]
    simp
    split_ifs with h
    · subst h
      norm_num
    · ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a180486.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.a_rec, OMA.Helpers.a_closed⟩
