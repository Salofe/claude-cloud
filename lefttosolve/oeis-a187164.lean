import OMAStatements.S_oeis_a187164

/-!
Proof of Barker's conjectures for A187164 (3-step self-avoiding walks on an n X n X n cube).

A walk is a middle cell `c` together with an ordered pair of distinct neighbours of `c`, so
`a n = Σ_c d(c) (d(c) - 1)`, where `d(c)` is the number of neighbours of `c`. For
`c = (i, j, k)`, `d(c) = h(i) + h(j) + h(k)`, where `h(i)` is the number of neighbours of `i` on
a line of `n` cells. For `n = m + 2` the two end cells of a line have one neighbour and the `m`
inner cells have two, which gives `a (m + 2) = 30 m^3 + 120 m^2 + 144 m + 48`, i.e.
`a n = 30 n^3 - 60 n^2 + 24 n` for `n ≥ 2`, while `a 1 = 0`. The recurrence and the generating
function follow by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a187164 Finset

instance decAdj {n : ℕ} (p q : Fin n × Fin n × Fin n) : Decidable (Adj p q) :=
  inferInstanceAs (Decidable (_ = 1))

/-- The neighbours of a cell. -/
def nbr {n : ℕ} (c : Fin n × Fin n × Fin n) : Finset (Fin n × Fin n × Fin n) :=
  univ.filter (fun p => Adj p c)

theorem adj_symm {n : ℕ} {p q : Fin n × Fin n × Fin n} (h : Adj p q) : Adj q p := by
  unfold Adj at *
  omega

theorem adj_ne {n : ℕ} {p q : Fin n × Fin n × Fin n} (h : Adj p q) : p ≠ q := by
  rintro rfl
  unfold Adj at h
  omega

theorem mem_nbr {n : ℕ} {p c : Fin n × Fin n × Fin n} : p ∈ nbr c ↔ Adj p c := by
  simp [nbr]

/-- A walk is its middle cell together with an ordered pair of distinct neighbours of it. -/
def walkEquiv (n : ℕ) :
    {w : Fin 3 → Fin n × Fin n × Fin n // IsWalk w} ≃
      Σ c : Fin n × Fin n × Fin n, ↥(nbr c).offDiag where
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
    a n = ∑ c : Fin n × Fin n × Fin n, ((nbr c).card * (nbr c).card - (nbr c).card) := by
  classical
  unfold a
  rw [Fintype.card_congr (walkEquiv n), Fintype.card_sigma]
  simp only [Fintype.card_coe, offDiag_card]

/-- The neighbours of `i` on a line of `n` cells. -/
def lnbr {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  univ.filter (fun i' => ((i' : ℤ) - i).natAbs = 1)

theorem mem_lnbr {n : ℕ} {i i' : Fin n} : i' ∈ lnbr i ↔ ((i' : ℤ) - i).natAbs = 1 := by
  simp only [lnbr, mem_filter, mem_univ, true_and]

/-- The neighbours of a cell: move along one of the three axes. -/
theorem nbr_eq {n : ℕ} (i j k : Fin n) :
    nbr (i, j, k) =
      lnbr i ×ˢ ({j} ×ˢ {k}) ∪ ({i} ×ˢ (lnbr j ×ˢ {k}) ∪ {i} ×ˢ ({j} ×ˢ lnbr k)) := by
  ext ⟨i', j', k'⟩
  simp only [mem_nbr, mem_union, mem_product, mem_lnbr, mem_singleton]
  unfold Adj
  dsimp only
  omega

theorem card_nbr {n : ℕ} (i j k : Fin n) :
    (nbr (i, j, k)).card = (lnbr i).card + (lnbr j).card + (lnbr k).card := by
  rw [nbr_eq, card_union_of_disjoint, card_union_of_disjoint]
  · simp only [card_product, card_singleton, mul_one, one_mul]
    omega
  · rw [disjoint_left]
    rintro ⟨i', j', k'⟩ h1 h2
    simp only [mem_product, mem_lnbr, mem_singleton] at h1 h2
    omega
  · rw [disjoint_left]
    rintro ⟨i', j', k'⟩ h1 h2
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

/-- On a line of `m + 2` cells, two cells have one neighbour and `m` cells have two. -/
theorem peel (m : ℕ) (g : ℕ → ℕ) :
    ∑ i : Fin (m + 2), g (lnbr i).card = 2 * g 1 + m * g 2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [lnbr_first, lnbr_last, lnbr_mid, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- The triple sum over the cube, peeled one axis at a time. -/
theorem peel3 (m : ℕ) (f : ℕ → ℕ) :
    ∑ i : Fin (m + 2), ∑ j : Fin (m + 2), ∑ k : Fin (m + 2),
        f ((lnbr i).card + (lnbr j).card + (lnbr k).card) =
      8 * f 3 + 12 * m * f 4 + 6 * m ^ 2 * f 5 + m ^ 3 * f 6 := by
  have h1 : ∀ x y : ℕ, ∑ k : Fin (m + 2), f (x + y + (lnbr k).card) =
      2 * f (x + y + 1) + m * f (x + y + 2) :=
    fun x y => peel m (fun z => f (x + y + z))
  simp only [h1]
  have h2 : ∀ x : ℕ, ∑ j : Fin (m + 2),
      (2 * f (x + (lnbr j).card + 1) + m * f (x + (lnbr j).card + 2)) =
      2 * (2 * f (x + 1 + 1) + m * f (x + 1 + 2)) +
        m * (2 * f (x + 2 + 1) + m * f (x + 2 + 2)) :=
    fun x => peel m (fun y => 2 * f (x + y + 1) + m * f (x + y + 2))
  simp only [h2]
  rw [peel m (fun x => 2 * (2 * f (x + 1 + 1) + m * f (x + 1 + 2)) +
    m * (2 * f (x + 2 + 1) + m * f (x + 2 + 2)))]
  norm_num
  ring

theorem a_closed (m : ℕ) : a (m + 2) = 30 * m ^ 3 + 120 * m ^ 2 + 144 * m + 48 := by
  rw [a_eq_sum, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, card_nbr]
  rw [peel3 m (fun d => d * d - d)]
  norm_num
  ring

theorem a_one : a 1 = 0 := by
  rw [a_eq_sum, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, card_nbr]
  have h : ∀ i : Fin 1, (lnbr i).card = 0 := by
    intro i
    rw [card_eq_zero]
    ext i'
    rw [mem_lnbr]
    simp only [Finset.notMem_empty, iff_false]
    omega
  simp [h]

theorem a_closedQ (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℚ) = 30 * (n : ℚ) ^ 3 - 60 * (n : ℚ) ^ 2 + 24 * n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [a_closed]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  have key : ∀ k : ℕ, 2 ≤ k → (a k : ℤ) = 30 * (k : ℤ) ^ 3 - 60 * (k : ℤ) ^ 2 + 24 * k := by
    intro k hk
    have := a_closedQ k hk
    exact_mod_cast this
  rw [key n (by omega), key (n - 1) (by omega), key (n - 2) (by omega), key (n - 3) (by omega),
    key (n - 4) (by omega)]
  push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
    show 4 ≤ n by omega]
  ring

open PowerSeries in
/-- The coefficient of `x^k` in `A * (c x^j)`. -/
theorem coeff_mul_CX (A : ℚ⟦X⟧) (c : ℚ) (j k : ℕ) :
    coeff k (A * (C c * X ^ j)) = if j ≤ k then c * coeff (k - j) A else 0 := by
  rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow', mul_ite, mul_zero]

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 4 =
      6 * X ^ 2 * (8 + 25 * X - 4 * X ^ 2 + X ^ 3) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have hpow : A * ((1 : ℚ⟦X⟧) - X) ^ 4 =
      A * (C (1 : ℚ) * X ^ 0) - A * (C (4 : ℚ) * X ^ 1) + A * (C (6 : ℚ) * X ^ 2) -
        A * (C (4 : ℚ) * X ^ 3) + A * (C (1 : ℚ) * X ^ 4) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (6 : ℚ⟦X⟧) * X ^ 2 * (8 + 25 * X - 4 * X ^ 2 + X ^ 3) =
      C (48 : ℚ) * X ^ 2 + C (150 : ℚ) * X ^ 3 - C (24 : ℚ) * X ^ 4 + C (6 : ℚ) * X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [hpow, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow, coeff_mul_CX, hA, coeff_mk, zero_le, if_true,
    Nat.sub_zero, one_mul]
  have h1 : (a 1 : ℚ) = 0 := by rw [a_one]; simp
  have h2 : (a 2 : ℚ) = 48 := by rw [a_closed 0]; norm_num
  have h3 : (a 3 : ℚ) = 342 := by rw [a_closed 1]; norm_num
  have h4 : (a 4 : ℚ) = 1056 := by rw [a_closed 2]; norm_num
  have h5 : (a 5 : ℚ) = 2370 := by rw [a_closed 3]; norm_num
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
      show 3 ≤ j + 6 by omega, show 4 ≤ j + 6 by omega, show j + 6 - 1 = j + 5 by omega,
      show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega,
      show j + 6 - 4 = j + 2 by omega, show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega, show ¬ (j + 6 = 2) by omega,
      show ¬ (j + 6 = 3) by omega, show ¬ (j + 6 = 4) by omega, show ¬ (j + 6 = 5) by omega,
      if_true, if_false]
    rw [a_closedQ (j + 6) (by omega), a_closedQ (j + 5) (by omega), a_closedQ (j + 4) (by omega),
      a_closedQ (j + 3) (by omega), a_closedQ (j + 2) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a187164.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
