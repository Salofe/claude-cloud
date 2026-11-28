import OMAStatements.S_oeis_a188148

/-!
Proof of Barker's conjectures for A188148 (3-step self-avoiding walks on an n X n board).

A walk is a middle cell `c` together with an ordered pair of distinct neighbours of `c`, so
`a n = Σ_c d(c) (d(c) - 1)`, where `d(c)` is the number of neighbours of `c`. For `c = (i, j)`,
`d(c) = h(i) + h(j)`, where `h(i)` is the number of neighbours of `i` on a line of `n` cells.
For `n = m + 2` the two end cells of a line have one neighbour and the `m` inner cells have two,
which gives `a (m + 2) = 12 m^2 + 24 m + 8`, i.e. `a n = 12 n^2 - 24 n + 8` for `n ≥ 2`, while
`a 1 = 0`. The recurrence and the generating function follow by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a188148 Finset

instance decAdj {n : ℕ} (p q : Fin n × Fin n) : Decidable (Adj p q) :=
  inferInstanceAs (Decidable (_ = 1))

/-- The neighbours of a cell. -/
def nbr {n : ℕ} (c : Fin n × Fin n) : Finset (Fin n × Fin n) :=
  univ.filter (fun p => Adj p c)

theorem adj_symm {n : ℕ} {p q : Fin n × Fin n} (h : Adj p q) : Adj q p := by
  unfold Adj at *
  omega

theorem adj_ne {n : ℕ} {p q : Fin n × Fin n} (h : Adj p q) : p ≠ q := by
  rintro rfl
  unfold Adj at h
  omega

theorem mem_nbr {n : ℕ} {p c : Fin n × Fin n} : p ∈ nbr c ↔ Adj p c := by
  simp [nbr]

/-- A walk is its middle cell together with an ordered pair of distinct neighbours of it. -/
def walkEquiv (n : ℕ) :
    {w : Fin 3 → Fin n × Fin n // IsWalk w} ≃ Σ c : Fin n × Fin n, ↥(nbr c).offDiag where
  toFun w := ⟨w.1 1, ⟨(w.1 0, w.1 2), by
    rw [mem_offDiag]
    refine ⟨mem_nbr.2 w.2.2.1, mem_nbr.2 (adj_symm w.2.2.2), fun h => ?_⟩
    exact absurd (w.2.1 h) (by decide)⟩⟩
  invFun x := ⟨![x.2.1.1, x.1, x.2.1.2], by
    obtain ⟨c, ⟨⟨p, q⟩, h⟩⟩ := x
    rw [mem_offDiag, mem_nbr, mem_nbr] at h
    obtain ⟨hp, hq, hpq⟩ := h
    refine ⟨?_, hp, adj_symm hq⟩
    have h1 := adj_ne hp
    have h2 := adj_ne hq
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv x := by
    obtain ⟨c, ⟨⟨p, q⟩, h⟩⟩ := x
    rfl

theorem a_eq_sum (n : ℕ) :
    a n = ∑ c : Fin n × Fin n, ((nbr c).card * (nbr c).card - (nbr c).card) := by
  classical
  unfold a
  rw [Fintype.card_congr (walkEquiv n), Fintype.card_sigma]
  simp only [Fintype.card_coe, offDiag_card]

/-- The neighbours of `i` on a line of `n` cells. -/
def lnbr {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  univ.filter (fun i' => ((i' : ℤ) - i).natAbs = 1)

theorem mem_lnbr {n : ℕ} {i i' : Fin n} : i' ∈ lnbr i ↔ ((i' : ℤ) - i).natAbs = 1 := by
  simp only [lnbr, mem_filter, mem_univ, true_and]

theorem nbr_eq {n : ℕ} (i j : Fin n) :
    nbr (i, j) = lnbr i ×ˢ {j} ∪ {i} ×ˢ lnbr j := by
  ext ⟨i', j'⟩
  rw [mem_nbr, mem_union, mem_product, mem_product, mem_lnbr, mem_lnbr, mem_singleton,
    mem_singleton]
  unfold Adj
  dsimp only
  omega

theorem card_nbr {n : ℕ} (i j : Fin n) :
    (nbr (i, j)).card = (lnbr i).card + (lnbr j).card := by
  rw [nbr_eq, card_union_of_disjoint, card_product, card_product, card_singleton,
    card_singleton, mul_one, one_mul]
  rw [disjoint_left]
  rintro ⟨i', j'⟩ h1 h2
  rw [mem_product, mem_lnbr, mem_singleton] at h1
  rw [mem_product, mem_lnbr, mem_singleton] at h2
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

/-- On a line of `m + 2` cells, two cells have one neighbour and `m` cells have two. -/
theorem peel (m : ℕ) (g : ℕ → ℕ) :
    ∑ i : Fin (m + 2), g (lnbr i).card = 2 * g 1 + m * g 2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [lnbr_first, lnbr_last, lnbr_mid, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  ring

theorem a_closed (m : ℕ) : a (m + 2) = 12 * m ^ 2 + 24 * m + 8 := by
  rw [a_eq_sum, Fintype.sum_prod_type]
  simp only [card_nbr]
  have inner : ∀ i : Fin (m + 2), ∑ j : Fin (m + 2),
      (((lnbr i).card + (lnbr j).card) * ((lnbr i).card + (lnbr j).card) -
        ((lnbr i).card + (lnbr j).card)) =
      2 * (((lnbr i).card + 1) * ((lnbr i).card + 1) - ((lnbr i).card + 1)) +
        m * (((lnbr i).card + 2) * ((lnbr i).card + 2) - ((lnbr i).card + 2)) :=
    fun i => peel m (fun y => ((lnbr i).card + y) * ((lnbr i).card + y) - ((lnbr i).card + y))
  simp only [inner]
  have outer : ∑ i : Fin (m + 2),
      (2 * (((lnbr i).card + 1) * ((lnbr i).card + 1) - ((lnbr i).card + 1)) +
        m * (((lnbr i).card + 2) * ((lnbr i).card + 2) - ((lnbr i).card + 2))) =
      2 * (2 * ((1 + 1) * (1 + 1) - (1 + 1)) + m * ((1 + 2) * (1 + 2) - (1 + 2))) +
        m * (2 * ((2 + 1) * (2 + 1) - (2 + 1)) + m * ((2 + 2) * (2 + 2) - (2 + 2))) :=
    peel m (fun x => 2 * ((x + 1) * (x + 1) - (x + 1)) + m * ((x + 2) * (x + 2) - (x + 2)))
  rw [outer]
  norm_num
  ring

theorem a_one : a 1 = 0 := by
  rw [a_eq_sum, Fintype.sum_prod_type]
  simp only [card_nbr]
  have h : ∀ i : Fin 1, (lnbr i).card = 0 := by
    intro i
    rw [card_eq_zero]
    ext i'
    rw [mem_lnbr]
    simp only [Finset.notMem_empty, iff_false]
    omega
  simp [h]

theorem a_closedQ (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = 12 * (n : ℚ) ^ 2 - 24 * n + 8 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [a_closed]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  have key : ∀ k : ℕ, 2 ≤ k → (a k : ℤ) = 12 * (k : ℤ) ^ 2 - 24 * k + 8 := by
    intro k hk
    have := a_closedQ k hk
    exact_mod_cast this
  rw [key n (by omega), key (n - 1) (by omega), key (n - 2) (by omega), key (n - 3) (by omega)]
  push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega]
  ring

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 3 =
      4 * X ^ 2 * (2 + 5 * X - X ^ 2) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have hcube : ((1 : ℚ⟦X⟧) - X) ^ 3 = 1 - X ^ 1 - X ^ 1 - X ^ 1 + X ^ 2 + X ^ 2 + X ^ 2 - X ^ 3 := by
    ring
  have hrhs : (4 : ℚ⟦X⟧) * X ^ 2 * (2 + 5 * X - X ^ 2) =
      C (8 : ℚ) * X ^ 2 + C (20 : ℚ) * X ^ 3 - C (4 : ℚ) * X ^ 4 := by
    simp only [map_ofNat]
    ring
  rw [hcube, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mul_X_pow', hA, coeff_mk]
  have h1 : (a 1 : ℚ) = 0 := by rw [a_one]; simp
  rcases k with _ | _ | _ | _ | _ | j
  · simp
  · simp [h1]
  · norm_num [h1, a_closedQ]
  · norm_num [h1, a_closedQ]
  · norm_num [h1, a_closedQ]
  · simp only [show ¬ (j + 5 = 0) by omega, show 1 ≤ j + 5 by omega, show 2 ≤ j + 5 by omega,
      show 3 ≤ j + 5 by omega, show j + 5 - 1 = j + 4 by omega, show j + 5 - 2 = j + 3 by omega,
      show j + 5 - 3 = j + 2 by omega, show ¬ (j + 4 = 0) by omega, show ¬ (j + 3 = 0) by omega,
      show ¬ (j + 2 = 0) by omega, show ¬ (j + 5 = 2) by omega, show ¬ (j + 5 = 3) by omega,
      show ¬ (j + 5 = 4) by omega, if_true, if_false]
    rw [a_closedQ (j + 5) (by omega), a_closedQ (j + 4) (by omega), a_closedQ (j + 3) (by omega),
      a_closedQ (j + 2) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a188148.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
