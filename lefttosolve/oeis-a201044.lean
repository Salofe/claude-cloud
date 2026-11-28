import OMAStatements.S_oeis_a201044

/-!
Proof of Barker's conjectures for A201044 (arrays x(0..4) of 5 elements of -n..n whose adjacent
differences are also in -n..n).

Write `I = -n..n`. For an entry `y ∈ I`, the entries `d ∈ I` with `d - y ∈ I` form the window
`Icc (|y| - n) n` (for `y ≥ 0`) or `Icc (-n) (n - |y|)` (for `y < 0`). Splitting such a window at 0
(`sum_Icc_natAbs`) gives, for every `H : ℕ → ℚ` (`window`),
  Sum_{d ∈ I, d - y ∈ I} H(|d|) = Sum_{v ≤ n} H(v) + Sum_{v ≤ n - |y|} H(v) - H(0).
So the number `cnt n k y` of ways to extend an array ending at `y` by `k` more entries depends only
on `|y|`: it is `F n k |y|`, where `F n 0 = 1` and `F n (k + 1) u` is the right-hand side above for
`H = F n k` (`cnt_eq`). Listing an array as the 5-tuple of its entries (`a_eq_sum`), the count is
`a(n) = Sum_{x0 ∈ I} cnt n 4 x0 = cnt n 5 0 = F n 5 0` (`a_eq_F`).

Each layer `F n k u` (for `u ≤ n`) is an explicit polynomial `P k n u` of degree `k`, and so is its
partial sum `Q k n m = Sum_{v ≤ m} P k n v` (`sum1` .. `sum4`, by induction on `m`); one layer
gives the next (`F_step`, `F1` .. `F4`). The last step gives, for every `n`,
  a(n) = (169/15) n^5 + (169/6) n^4 + 32 n^3 + (119/6) n^2 + (101/15) n + 1
(`a_formula`). The recurrence and the generating function follow by comparing coefficients: the
sixth difference of a polynomial of degree 5 vanishes.
-/

namespace OMA.Helpers

open OMA.S_oeis_a201044 Finset

/-- The window `-n..n`. -/
noncomputable abbrev Iw (n : ℕ) : Finset ℤ := Icc (-(n : ℤ)) n

theorem sum_Icc_zero (H : ℕ → ℚ) (b : ℕ) :
    ∑ d ∈ Icc (0 : ℤ) b, H d.natAbs = ∑ v ∈ range (b + 1), H v := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hs : Icc (0 : ℤ) ((b + 1 : ℕ) : ℤ) = insert ((b + 1 : ℕ) : ℤ) (Icc (0 : ℤ) b) := by
      ext d
      simp only [mem_Icc, mem_insert]
      omega
    have hn : ((b + 1 : ℕ) : ℤ) ∉ Icc (0 : ℤ) b := by
      simp only [mem_Icc]
      omega
    rw [hs, sum_insert hn, ih, sum_range_succ _ (b + 1), Int.natAbs_natCast]
    ring

theorem sum_Icc_natAbs (H : ℕ → ℚ) (a b : ℕ) :
    ∑ d ∈ Icc (-(a : ℤ)) b, H d.natAbs =
      ∑ v ∈ range (b + 1), H v + ∑ v ∈ range (a + 1), H v - H 0 := by
  induction a with
  | zero => simp [sum_Icc_zero]
  | succ a ih =>
    have hs : Icc (-((a + 1 : ℕ) : ℤ)) b = insert (-((a + 1 : ℕ) : ℤ)) (Icc (-(a : ℤ)) b) := by
      ext d
      simp only [mem_Icc, mem_insert]
      omega
    have hn : -((a + 1 : ℕ) : ℤ) ∉ Icc (-(a : ℤ)) b := by
      simp only [mem_Icc]
      omega
    have habs : (-((a + 1 : ℕ) : ℤ)).natAbs = a + 1 := by omega
    rw [hs, sum_insert hn, ih, sum_range_succ _ (a + 1), habs]
    ring

theorem window (n : ℕ) (H : ℕ → ℚ) (c : ℤ) (hc : c ∈ Iw n) :
    ∑ d ∈ Iw n, (if d - c ∈ Iw n then H d.natAbs else 0) =
      ∑ v ∈ range (n + 1), H v + ∑ v ∈ range (n + 1 - c.natAbs), H v - H 0 := by
  rw [← sum_filter]
  simp only [Iw, mem_Icc] at hc
  rcases le_or_gt 0 c with h0 | h0
  · have hf : (Iw n).filter (fun d => d - c ∈ Iw n) =
        Icc (-((n - c.natAbs : ℕ) : ℤ)) (n : ℤ) := by
      ext d
      simp only [Iw, mem_filter, mem_Icc]
      omega
    rw [hf, sum_Icc_natAbs, show n - c.natAbs + 1 = n + 1 - c.natAbs by omega]
  · have hf : (Iw n).filter (fun d => d - c ∈ Iw n) =
        Icc (-(n : ℤ)) ((n - c.natAbs : ℕ) : ℤ) := by
      ext d
      simp only [Iw, mem_filter, mem_Icc]
      omega
    rw [hf, sum_Icc_natAbs, show n - c.natAbs + 1 = n + 1 - c.natAbs by omega]
    ring

/-- The number of ways to continue an array from the entry `y` by `k` more entries. -/
noncomputable def cnt (n : ℕ) : ℕ → ℤ → ℚ
  | 0, _ => 1
  | k + 1, y => ∑ d ∈ Iw n, if d - y ∈ Iw n then cnt n k d else 0

/-- The same count, as a function of `|y|`. -/
def F (n : ℕ) : ℕ → ℕ → ℚ
  | 0, _ => 1
  | k + 1, u => ∑ v ∈ range (n + 1), F n k v + ∑ v ∈ range (n + 1 - u), F n k v - F n k 0

theorem cnt_eq (n k : ℕ) : ∀ y ∈ Iw n, cnt n k y = F n k y.natAbs := by
  induction k with
  | zero => intro y _; rfl
  | succ k ih =>
    intro y hy
    have h1 : ∑ d ∈ Iw n, (if d - y ∈ Iw n then cnt n k d else 0) =
        ∑ d ∈ Iw n, (if d - y ∈ Iw n then F n k d.natAbs else 0) :=
      sum_congr rfl (fun d hd => by rw [ih d hd])
    show ∑ d ∈ Iw n, (if d - y ∈ Iw n then cnt n k d else 0) = F n (k + 1) y.natAbs
    rw [h1, window n (F n k) y hy]
    rfl


/-- Membership in the filter of the statement, written out for the four adjacent pairs. -/
theorem good_iff (n : ℕ) (x : Fin 5 → ℤ) :
    (∀ i : Fin 4, x i.succ - x i.castSucc ∈ Icc (-(n : ℤ)) n) ↔
      (x 1 - x 0 ∈ Iw n ∧ x 2 - x 1 ∈ Iw n ∧ x 3 - x 2 ∈ Iw n ∧ x 4 - x 3 ∈ Iw n) := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3

theorem a_eq_sum (n : ℕ) : (a n : ℚ) = ∑ x0 ∈ Iw n, cnt n 4 x0 := by
  unfold a
  rw [natCast_card_filter]
  have e : ∑ x ∈ Fintype.piFinset (fun _ : Fin 5 => Icc (-(n : ℤ)) n),
      (if (∀ i : Fin 4, x i.succ - x i.castSucc ∈ Icc (-(n : ℤ)) n) then (1 : ℚ) else 0) =
      ∑ p ∈ Iw n ×ˢ Iw n ×ˢ Iw n ×ˢ Iw n ×ˢ Iw n,
        (if p.2.1 - p.1 ∈ Iw n ∧ p.2.2.1 - p.2.1 ∈ Iw n ∧ p.2.2.2.1 - p.2.2.1 ∈ Iw n ∧
          p.2.2.2.2 - p.2.2.2.1 ∈ Iw n then (1 : ℚ) else 0) := by
    refine sum_nbij' (fun x => (x 0, x 1, x 2, x 3, x 4))
      (fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2]) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [Fintype.mem_piFinset] at hx
      simp only [mem_product]
      exact ⟨hx 0, hx 1, hx 2, hx 3, hx 4⟩
    · intro p hp
      simp only [mem_product] at hp
      rw [Fintype.mem_piFinset]
      intro i
      fin_cases i
      · exact hp.1
      · exact hp.2.1
      · exact hp.2.2.1
      · exact hp.2.2.2.1
      · exact hp.2.2.2.2
    · intro x _
      funext i
      fin_cases i <;> rfl
    · intro p _
      rfl
    · intro x _
      exact if_congr (good_iff n x) rfl rfl
  rw [e]
  simp only [sum_product, ite_and, sum_ite_irrel, sum_const_zero]
  rfl

theorem a_eq_F (n : ℕ) : (a n : ℚ) = F n 5 0 := by
  have h0 : (0 : ℤ) ∈ Iw n := by simp
  rw [a_eq_sum, show F n 5 0 = F n 5 (Int.natAbs 0) from rfl, ← cnt_eq n 5 0 h0]
  show ∑ x0 ∈ Iw n, cnt n 4 x0 = ∑ d ∈ Iw n, (if d - 0 ∈ Iw n then cnt n 4 d else 0)
  refine sum_congr rfl (fun d hd => ?_)
  rw [sub_zero, if_pos hd]


/-- One layer: if `F n k` agrees with `p` on `0..n` and `q m` is the sum of `p` over `0..m`,
then `F n (k + 1) u = q n + q (n - u) - p 0` for `u ≤ n`. -/
theorem F_step (n k : ℕ) (p q : ℕ → ℚ) (hp : ∀ v ≤ n, F n k v = p v)
    (hq : ∀ m, ∑ v ∈ range (m + 1), p v = q m) (u : ℕ) (hu : u ≤ n) :
    F n (k + 1) u = q n + q (n - u) - p 0 := by
  show ∑ v ∈ range (n + 1), F n k v + ∑ v ∈ range (n + 1 - u), F n k v - F n k 0 = _
  have h1 : ∑ v ∈ range (n + 1), F n k v = ∑ v ∈ range (n + 1), p v :=
    sum_congr rfl (fun v hv => hp v (by simp only [mem_range] at hv; omega))
  have h2 : ∑ v ∈ range (n + 1 - u), F n k v = ∑ v ∈ range (n - u + 1), p v := by
    rw [show n + 1 - u = n - u + 1 by omega]
    exact sum_congr rfl (fun v hv => hp v (by simp only [mem_range] at hv; omega))
  rw [h1, h2, hq, hq, hp 0 (Nat.zero_le n)]

/-! Explicit layers: `P k N U` is `F n k u` at `N = n`, `U = u`, and `Q k N M` is the sum of
`P k N v` over `v = 0..M`. -/

def P1 (N U : ℚ) : ℚ := 2 * N - U + 1

def Q1 (N M : ℚ) : ℚ := -M ^ 2 / 2 + 2 * M * N + M / 2 + 2 * N + 1

def P2 (N U : ℚ) : ℚ := 3 * N ^ 2 - N * U + 3 * N - U ^ 2 / 2 - U / 2 + 1

def Q2 (N M : ℚ) : ℚ :=
  -M ^ 3 / 6 - M ^ 2 * N / 2 - M ^ 2 / 2 + 3 * M * N ^ 2 + 5 * M * N / 2 + 2 * M / 3 +
    3 * N ^ 2 + 3 * N + 1

def P3 (N U : ℚ) : ℚ :=
  14 * N ^ 3 / 3 - 3 * N ^ 2 * U / 2 + 7 * N ^ 2 - N * U ^ 2 - 3 * N * U / 2 + 13 * N / 3 +
    U ^ 3 / 6 - U ^ 2 / 2 - 2 * U / 3 + 1

def Q3 (N M : ℚ) : ℚ :=
  M ^ 4 / 24 - M ^ 3 * N / 3 - M ^ 3 / 12 - 3 * M ^ 2 * N ^ 2 / 4 - 5 * M ^ 2 * N / 4 -
    13 * M ^ 2 / 24 + 14 * M * N ^ 3 / 3 + 25 * M * N ^ 2 / 4 + 41 * M * N / 12 + 7 * M / 12 +
    14 * N ^ 3 / 3 + 7 * N ^ 2 + 13 * N / 3 + 1

def P4 (N U : ℚ) : ℚ :=
  29 * N ^ 4 / 4 - 7 * N ^ 3 * U / 3 + 29 * N ^ 3 / 2 - 3 * N ^ 2 * U ^ 2 / 2 -
    7 * N ^ 2 * U / 2 + 51 * N ^ 2 / 4 + N * U ^ 3 / 6 - 3 * N * U ^ 2 / 2 - 7 * N * U / 3 +
    11 * N / 2 + U ^ 4 / 24 + U ^ 3 / 12 - 13 * U ^ 2 / 24 - 7 * U / 12 + 1

def Q4 (N M : ℚ) : ℚ :=
  M ^ 5 / 120 + M ^ 4 * N / 24 + M ^ 4 / 24 - M ^ 3 * N ^ 2 / 2 - 5 * M ^ 3 * N / 12 -
    M ^ 3 / 8 - 7 * M ^ 2 * N ^ 3 / 6 - 5 * M ^ 2 * N ^ 2 / 2 - 15 * M ^ 2 * N / 8 -
    13 * M ^ 2 / 24 + 29 * M * N ^ 4 / 4 + 40 * M * N ^ 3 / 3 + 43 * M * N ^ 2 / 4 +
    49 * M * N / 12 + 37 * M / 60 + 29 * N ^ 4 / 4 + 29 * N ^ 3 / 2 + 51 * N ^ 2 / 4 +
    11 * N / 2 + 1

theorem sum0 (m : ℕ) : ∑ _v ∈ range (m + 1), (1 : ℚ) = (m : ℚ) + 1 := by
  simp

theorem sum1 (N : ℚ) (m : ℕ) : ∑ v ∈ range (m + 1), P1 N v = Q1 N m := by
  induction m with
  | zero => simp only [zero_add, sum_range_one, P1, Q1, Nat.cast_zero]; ring
  | succ m ih => rw [sum_range_succ, ih]; simp only [P1, Q1]; push_cast; ring

theorem sum2 (N : ℚ) (m : ℕ) : ∑ v ∈ range (m + 1), P2 N v = Q2 N m := by
  induction m with
  | zero => simp only [zero_add, sum_range_one, P2, Q2, Nat.cast_zero]; ring
  | succ m ih => rw [sum_range_succ, ih]; simp only [P2, Q2]; push_cast; ring

theorem sum3 (N : ℚ) (m : ℕ) : ∑ v ∈ range (m + 1), P3 N v = Q3 N m := by
  induction m with
  | zero => simp only [zero_add, sum_range_one, P3, Q3, Nat.cast_zero]; ring
  | succ m ih => rw [sum_range_succ, ih]; simp only [P3, Q3]; push_cast; ring

theorem sum4 (N : ℚ) (m : ℕ) : ∑ v ∈ range (m + 1), P4 N v = Q4 N m := by
  induction m with
  | zero => simp only [zero_add, sum_range_one, P4, Q4, Nat.cast_zero]; ring
  | succ m ih => rw [sum_range_succ, ih]; simp only [P4, Q4]; push_cast; ring

theorem F1 (n : ℕ) : ∀ u ≤ n, F n 1 u = P1 n u := by
  intro u hu
  rw [F_step n 0 (fun _ => 1) (fun m => (m : ℚ) + 1) (fun v _ => rfl) sum0 u hu]
  simp only [P1]
  rw [Nat.cast_sub hu]
  ring

theorem F2 (n : ℕ) : ∀ u ≤ n, F n 2 u = P2 n u := by
  intro u hu
  rw [F_step n 1 (fun v => P1 n v) (fun m => Q1 n m) (F1 n) (sum1 n) u hu]
  simp only [P1, P2, Q1, Nat.cast_zero]
  rw [Nat.cast_sub hu]
  ring

theorem F3 (n : ℕ) : ∀ u ≤ n, F n 3 u = P3 n u := by
  intro u hu
  rw [F_step n 2 (fun v => P2 n v) (fun m => Q2 n m) (F2 n) (sum2 n) u hu]
  simp only [P2, P3, Q2, Nat.cast_zero]
  rw [Nat.cast_sub hu]
  ring

theorem F4 (n : ℕ) : ∀ u ≤ n, F n 4 u = P4 n u := by
  intro u hu
  rw [F_step n 3 (fun v => P3 n v) (fun m => Q3 n m) (F3 n) (sum3 n) u hu]
  simp only [P3, P4, Q3, Nat.cast_zero]
  rw [Nat.cast_sub hu]
  ring

theorem a_formula (n : ℕ) : (a n : ℚ) =
    169 / 15 * n ^ 5 + 169 / 6 * n ^ 4 + 32 * n ^ 3 + 119 / 6 * n ^ 2 + 101 / 15 * n + 1 := by
  rw [a_eq_F, F_step n 4 (fun v => P4 n v) (fun m => Q4 n m) (F4 n) (sum4 n) 0 (Nat.zero_le n)]
  simp only [P4, Q4, Nat.cast_zero, Nat.sub_zero]
  ring

theorem recurrence (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
      6 * a (n - 5) - a (n - 6) := by
  have hQ : (a n : ℚ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
      6 * a (n - 5) - a (n - 6) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
    rw [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega,
      show k + 7 - 3 = k + 4 by omega, show k + 7 - 4 = k + 3 by omega,
      show k + 7 - 5 = k + 2 by omega, show k + 7 - 6 = k + 1 by omega]
    rw [a_formula (k + 7), a_formula (k + 6), a_formula (k + 5), a_formula (k + 4),
      a_formula (k + 3), a_formula (k + 2), a_formula (k + 1)]
    push_cast
    ring
  exact_mod_cast hQ

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℚ)) =
      (X : PowerSeries ℚ) * (99 + 567 * X + 602 * X ^ 2 + 78 * X ^ 3 + 7 * X ^ 4 - X ^ 5) *
        ((1 - X) ^ 6 : PowerSeries ℚ)⁻¹ := by
  have h6 : constantCoeff ((1 - X) ^ 6 : PowerSeries ℚ) ≠ 0 := by simp
  rw [PowerSeries.eq_mul_inv_iff_mul_eq h6]
  set A : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℚ)) with hA
  have key : A * (1 - X) ^ 6 =
      A * X ^ 0 - C (6 : ℚ) * (A * X ^ 1) + C (15 : ℚ) * (A * X ^ 2) - C (20 : ℚ) * (A * X ^ 3) +
        C (15 : ℚ) * (A * X ^ 4) - C (6 : ℚ) * (A * X ^ 5) + A * X ^ 6 := by
    simp only [map_ofNat]
    ring
  have hrhs : (X : PowerSeries ℚ) * (99 + 567 * X + 602 * X ^ 2 + 78 * X ^ 3 + 7 * X ^ 4 - X ^ 5) =
      C (99 : ℚ) * X ^ 1 + C (567 : ℚ) * X ^ 2 + C (602 : ℚ) * X ^ 3 + C (78 : ℚ) * X ^ 4 +
        C (7 : ℚ) * X ^ 5 - C (1 : ℚ) * X ^ 6 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk]
  by_cases hk : k < 7
  · interval_cases k <;> norm_num [a_formula]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
    simp only [show 0 ≤ j + 7 by omega, show 1 ≤ j + 7 by omega, show 2 ≤ j + 7 by omega,
      show 3 ≤ j + 7 by omega, show 4 ≤ j + 7 by omega, show 5 ≤ j + 7 by omega,
      show 6 ≤ j + 7 by omega,
      show j + 7 - 0 = j + 7 by omega, show j + 7 - 1 = j + 6 by omega,
      show j + 7 - 2 = j + 5 by omega, show j + 7 - 3 = j + 4 by omega,
      show j + 7 - 4 = j + 3 by omega, show j + 7 - 5 = j + 2 by omega,
      show j + 7 - 6 = j + 1 by omega,
      show ¬ (j + 7 = 0) by omega, show ¬ (j + 6 = 0) by omega, show ¬ (j + 5 = 0) by omega,
      show ¬ (j + 4 = 0) by omega, show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega,
      show ¬ (j + 1 = 0) by omega,
      show ¬ (j + 7 = 1) by omega, show ¬ (j + 7 = 2) by omega, show ¬ (j + 7 = 3) by omega,
      show ¬ (j + 7 = 4) by omega, show ¬ (j + 7 = 5) by omega, show ¬ (j + 7 = 6) by omega,
      if_true, if_false]
    rw [a_formula (j + 7), a_formula (j + 6), a_formula (j + 5), a_formula (j + 4),
      a_formula (j + 3), a_formula (j + 2), a_formula (j + 1)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a201044.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
