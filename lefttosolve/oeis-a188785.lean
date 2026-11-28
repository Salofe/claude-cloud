import OMAStatements.S_oeis_a188785

/-!
Proof of Barker's conjectures for A188785 (2-step self-avoiding walks on an n X n X n X n 4-cube).

A walk is an ordered pair of distinct adjacent cells: its second cell `c` together with a
neighbour of `c`. So `a n = Σ_c d(c)`, where `d(c)` is the number of neighbours of `c`. For
`c = (i, j, k, l)`, `d(c) = h(i) + h(j) + h(k) + h(l)`, where `h(i)` is the number of neighbours
of `i` on a line of `n` cells, so `a n = 4 n^3 Σ_i h(i)`. For `n = m + 2` the two end cells of a
line have one neighbour and the `m` inner cells have two, so `Σ_i h(i) = 2 m + 2` and
`a (m + 2) = 8 m^4 + 56 m^3 + 144 m^2 + 160 m + 64`, i.e. `a n = 8 n^4 - 8 n^3` for `n ≥ 2`;
also `a 1 = 0`, which fits the same formula. The recurrence and the generating function follow
by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a188785 Finset

instance decAdj {n : ℕ} (p q : Fin n × Fin n × Fin n × Fin n) : Decidable (Adj p q) :=
  inferInstanceAs (Decidable (_ = 1))

/-- The neighbours of a cell. -/
def nbr {n : ℕ} (c : Fin n × Fin n × Fin n × Fin n) : Finset (Fin n × Fin n × Fin n × Fin n) :=
  univ.filter (fun p => Adj p c)

theorem adj_ne {n : ℕ} {p q : Fin n × Fin n × Fin n × Fin n} (h : Adj p q) : p ≠ q := by
  rintro rfl
  unfold Adj at h
  omega

theorem mem_nbr {n : ℕ} {p c : Fin n × Fin n × Fin n × Fin n} : p ∈ nbr c ↔ Adj p c := by
  simp [nbr]

/-- A walk is its second cell together with a neighbour of that cell (its first cell). -/
def walkEquiv (n : ℕ) :
    {w : Fin 2 → Fin n × Fin n × Fin n × Fin n // IsWalk w} ≃
      Σ c : Fin n × Fin n × Fin n × Fin n, ↥(nbr c) where
  toFun w := ⟨w.1 1, ⟨w.1 0, mem_nbr.2 w.2.2⟩⟩
  invFun x := ⟨![x.2.1, x.1], by
    obtain ⟨c, ⟨p, h⟩⟩ := x
    rw [mem_nbr] at h
    refine ⟨?_, h⟩
    have h1 := adj_ne h
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv x := by
    obtain ⟨c, ⟨p, h⟩⟩ := x
    rfl

theorem a_eq_sum (n : ℕ) :
    a n = ∑ c : Fin n × Fin n × Fin n × Fin n, (nbr c).card := by
  classical
  unfold a
  rw [Fintype.card_congr (walkEquiv n), Fintype.card_sigma]
  simp only [Fintype.card_coe]

/-- The neighbours of `i` on a line of `n` cells. -/
def lnbr {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  univ.filter (fun i' => ((i' : ℤ) - i).natAbs = 1)

theorem mem_lnbr {n : ℕ} {i i' : Fin n} : i' ∈ lnbr i ↔ ((i' : ℤ) - i).natAbs = 1 := by
  simp only [lnbr, mem_filter, mem_univ, true_and]

/-- The neighbours of a cell: move by one along one of the four axes. -/
theorem nbr_eq {n : ℕ} (i j k l : Fin n) :
    nbr (i, j, k, l) =
      lnbr i ×ˢ ({j} ×ˢ ({k} ×ˢ {l})) ∪
        ({i} ×ˢ (lnbr j ×ˢ ({k} ×ˢ {l})) ∪
          ({i} ×ˢ ({j} ×ˢ (lnbr k ×ˢ {l})) ∪ {i} ×ˢ ({j} ×ˢ ({k} ×ˢ lnbr l)))) := by
  ext ⟨i', j', k', l'⟩
  simp only [mem_nbr, mem_union, mem_product, mem_lnbr, mem_singleton]
  unfold Adj
  dsimp only
  omega

theorem card_nbr {n : ℕ} (i j k l : Fin n) :
    (nbr (i, j, k, l)).card =
      (lnbr i).card + (lnbr j).card + (lnbr k).card + (lnbr l).card := by
  rw [nbr_eq, card_union_of_disjoint, card_union_of_disjoint, card_union_of_disjoint]
  · simp only [card_product, card_singleton, mul_one, one_mul]
    omega
  all_goals
    rw [disjoint_left]
    rintro ⟨i', j', k', l'⟩ h1 h2
    simp only [mem_union, mem_product, mem_lnbr, mem_singleton] at h1 h2
    omega

theorem lnbr_first (m : ℕ) : (lnbr (0 : Fin (m + 2))).card = 1 := by
  rw [card_eq_one]
  refine ⟨⟨1, by omega⟩, ?_⟩
  ext i'
  rw [mem_lnbr, mem_singleton, Fin.ext_iff, Fin.val_zero]
  dsimp only
  omega

theorem lnbr_last (m : ℕ) : (lnbr (Fin.last m).succ).card = 1 := by
  rw [card_eq_one]
  refine ⟨⟨m, by omega⟩, ?_⟩
  ext i'
  rw [mem_lnbr, mem_singleton, Fin.ext_iff, Fin.val_succ, Fin.val_last]
  dsimp only
  omega

theorem lnbr_mid (m : ℕ) (k : Fin m) : (lnbr k.castSucc.succ).card = 2 := by
  rw [card_eq_two]
  refine ⟨⟨k, by omega⟩, ⟨k + 2, by omega⟩, ?_, ?_⟩
  · simp [Fin.ext_iff]
  ext i'
  rw [mem_lnbr, mem_insert, mem_singleton, Fin.ext_iff, Fin.ext_iff, Fin.val_succ,
    Fin.val_castSucc]
  dsimp only
  omega

/-- On a line of `m + 2` cells, the two end cells have one neighbour and the `m` inner cells
have two. -/
theorem line_sum (m : ℕ) : ∑ i : Fin (m + 2), (lnbr i).card = 2 * m + 2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [lnbr_first, lnbr_last, lnbr_mid, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- A line of one cell has no neighbours. -/
theorem line_sum_one : ∑ i : Fin 1, (lnbr i).card = 0 := by
  have h : ∀ i : Fin 1, (lnbr i).card = 0 := by
    intro i
    rw [card_eq_zero]
    ext i'
    rw [mem_lnbr]
    simp only [Finset.notMem_empty, iff_false]
    omega
  simp [h]

/-- Summing the degrees over the 4-cube: each of the four axes contributes `n ^ 3` times the
line sum. -/
theorem a_eq_line (n : ℕ) : a n = 4 * n ^ 3 * ∑ i : Fin n, (lnbr i).card := by
  rw [a_eq_sum, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, card_nbr]
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, ← mul_sum]
  ring

theorem a_closed (m : ℕ) : a (m + 2) = 8 * m ^ 4 + 56 * m ^ 3 + 144 * m ^ 2 + 160 * m + 64 := by
  rw [a_eq_line, line_sum]
  ring

theorem a_one : a 1 = 0 := by
  rw [a_eq_line, line_sum_one, mul_zero]

theorem a_closedQ (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = 8 * (n : ℚ) ^ 4 - 8 * (n : ℚ) ^ 3 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [a_one]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [a_closed]
    push_cast
    ring

theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  have key : ∀ k : ℕ, 1 ≤ k → (a k : ℤ) = 8 * (k : ℤ) ^ 4 - 8 * (k : ℤ) ^ 3 := by
    intro k hk
    have := a_closedQ k hk
    exact_mod_cast this
  rw [key n (by omega), key (n - 1) (by omega), key (n - 2) (by omega), key (n - 3) (by omega),
    key (n - 4) (by omega), key (n - 5) (by omega)]
  push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
    show 4 ≤ n by omega, show 5 ≤ n by omega]
  ring

open PowerSeries in
/-- The coefficient of `x^k` in `A * (c x^j)`. -/
theorem coeff_mul_CX (A : ℚ⟦X⟧) (c : ℚ) (j k : ℕ) :
    coeff k (A * (C c * X ^ j)) = if j ≤ k then c * coeff (k - j) A else 0 := by
  rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow', mul_ite, mul_zero]

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      16 * X ^ 2 * (4 + 7 * X + X ^ 2) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have hpow : A * ((1 : ℚ⟦X⟧) - X) ^ 5 =
      A * (C (1 : ℚ) * X ^ 0) - A * (C (5 : ℚ) * X ^ 1) + A * (C (10 : ℚ) * X ^ 2) -
        A * (C (10 : ℚ) * X ^ 3) + A * (C (5 : ℚ) * X ^ 4) - A * (C (1 : ℚ) * X ^ 5) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (16 : ℚ⟦X⟧) * X ^ 2 * (4 + 7 * X + X ^ 2) =
      C (64 : ℚ) * X ^ 2 + C (112 : ℚ) * X ^ 3 + C (16 : ℚ) * X ^ 4 := by
    simp only [map_ofNat]
    ring
  rw [hpow, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow, coeff_mul_CX, hA, coeff_mk, zero_le, if_true,
    Nat.sub_zero, one_mul]
  have h1 : (a 1 : ℚ) = 0 := by rw [a_one]; simp
  have h2 : (a 2 : ℚ) = 64 := by rw [a_closed 0]; norm_num
  have h3 : (a 3 : ℚ) = 432 := by rw [a_closed 1]; norm_num
  have h4 : (a 4 : ℚ) = 1536 := by rw [a_closed 2]; norm_num
  have h5 : (a 5 : ℚ) = 4000 := by rw [a_closed 3]; norm_num
  rcases k with _ | _ | _ | _ | _ | _ | j
  · simp
  · simp only [Nat.reduceAdd, Nat.reduceSub, h1]
    norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, h1, h2]
    norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, h1, h2, h3]
    norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, h1, h2, h3, h4]
    norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, h1, h2, h3, h4, h5]
    norm_num
  · simp only [show ¬ (j + 6 = 0) by omega, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega,
      show 3 ≤ j + 6 by omega, show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega,
      show j + 6 - 1 = j + 5 by omega, show j + 6 - 2 = j + 4 by omega,
      show j + 6 - 3 = j + 3 by omega, show j + 6 - 4 = j + 2 by omega,
      show j + 6 - 5 = j + 1 by omega, show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega,
      show ¬ (j + 6 = 2) by omega, show ¬ (j + 6 = 3) by omega, show ¬ (j + 6 = 4) by omega,
      if_true, if_false]
    rw [a_closedQ (j + 6) (by omega), a_closedQ (j + 5) (by omega), a_closedQ (j + 4) (by omega),
      a_closedQ (j + 3) (by omega), a_closedQ (j + 2) (by omega), a_closedQ (j + 1) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a188785.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
