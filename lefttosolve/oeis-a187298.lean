import OMAStatements.S_oeis_a187298

/-!
Proof of Hardin's formula and Barker's conjectures for A187298 (3-step asymmetric rook's tours on an n X n board; the
rook moves one space leftwards or up, or two spaces rightwards or down).

No two moves cancel, so two consecutive moves never come back to the first square. Hence a tour
is just a middle square `c` together with a square from which a move reaches `c` and a square
that a move from `c` reaches (the three squares are then automatically distinct), and
`a n = Σ_c i(c) o(c)`, where `i(c)` and `o(c)` count the moves into and out of `c`. For
`c = (r, s)` both split along the two coordinates: `o(c) = ho(r) + ho(s)` with
`ho(x) = [x ≥ 1] + [x + 2 < n]`, and `i(c) = hi(r) + hi(s)` with `hi(x) = [x + 1 < n] + [x ≥ 2]`.
For `n = m + 4` the positions of a line have `(hi, ho) = (1, 1), (1, 2), (2, 2), ..., (2, 2),
(2, 1), (1, 1)` (with `m` pairs `(2, 2)`), which gives `a (m + 4) = 16 m^2 + 84 m + 98`, i.e.
`a n = 16 n^2 - 44 n + 18` for `n ≥ 4`, while `a 1 = 0`, `a 2 = 2` and `a 3 = 36`. The
recurrence and the generating function follow by comparing coefficients.
-/

namespace OMA.Helpers

open Finset

/-- A move of the asymmetric rook from `p` to `q`, written coordinatewise. -/
def Move {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  (q.1 = p.1 ∧ (q.2 : ℤ) = p.2 - 1) ∨
    ((q.1 : ℤ) = p.1 - 1 ∧ q.2 = p.2) ∨
    (q.1 = p.1 ∧ (q.2 : ℤ) = p.2 + 2) ∨
    ((q.1 : ℤ) = p.1 + 2 ∧ q.2 = p.2)

/-- A 3-step tour, written with the coordinatewise moves. -/
def IsTour {n : ℕ} (w : Fin 3 → Fin n × Fin n) : Prop :=
  Function.Injective w ∧ Move (w 0) (w 1) ∧ Move (w 1) (w 2)

/-- The count of 3-step tours with the coordinatewise moves. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {w : Fin 3 → Fin n × Fin n // IsTour w}

instance decMove {n : ℕ} (p q : Fin n × Fin n) : Decidable (Move p q) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _)))

/-- The squares from which a move reaches `c`. -/
def inN {n : ℕ} (c : Fin n × Fin n) : Finset (Fin n × Fin n) :=
  univ.filter (fun p => Move p c)

/-- The squares that a move from `c` reaches. -/
def outN {n : ℕ} (c : Fin n × Fin n) : Finset (Fin n × Fin n) :=
  univ.filter (fun q => Move c q)

theorem mem_inN {n : ℕ} {p c : Fin n × Fin n} : p ∈ inN c ↔ Move p c := by
  simp [inN]

theorem mem_outN {n : ℕ} {c q : Fin n × Fin n} : q ∈ outN c ↔ Move c q := by
  simp [outN]

theorem move_ne {n : ℕ} {p q : Fin n × Fin n} (h : Move p q) : p ≠ q := by
  rintro rfl
  unfold Move at h
  omega

/-- No two moves cancel: two consecutive moves never come back to the first square. -/
theorem move_move_ne {n : ℕ} {p q r : Fin n × Fin n} (h1 : Move p q) (h2 : Move q r) :
    p ≠ r := by
  rintro rfl
  unfold Move at h1 h2
  omega

/-- A tour is its middle square together with a square from which a move reaches it and a
square that a move from it reaches. -/
def tourEquiv (n : ℕ) :
    {w : Fin 3 → Fin n × Fin n // IsTour w} ≃ Σ c : Fin n × Fin n, ↥(inN c ×ˢ outN c) where
  toFun w := ⟨w.1 1, ⟨(w.1 0, w.1 2), mem_product.2 ⟨mem_inN.2 w.2.2.1, mem_outN.2 w.2.2.2⟩⟩⟩
  invFun x := ⟨![x.2.1.1, x.1, x.2.1.2], by
    obtain ⟨c, ⟨⟨p, q⟩, h⟩⟩ := x
    rw [mem_product, mem_inN, mem_outN] at h
    obtain ⟨hp, hq⟩ := h
    refine ⟨?_, hp, hq⟩
    have h1 := move_ne hp
    have h2 := move_ne hq
    have h3 := move_move_ne hp hq
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
    a n = ∑ c : Fin n × Fin n, (inN c).card * (outN c).card := by
  classical
  unfold a
  rw [Fintype.card_congr (tourEquiv n), Fintype.card_sigma]
  simp only [Fintype.card_coe, card_product]

/-- The positions of a line that a move along it reaches from `x`: one back or two forward. -/
def lout {n : ℕ} (x : Fin n) : Finset (Fin n) :=
  univ.filter (fun x' => (x' : ℤ) = x - 1 ∨ (x' : ℤ) = x + 2)

/-- The positions of a line from which a move along it reaches `x`. -/
def lin {n : ℕ} (x : Fin n) : Finset (Fin n) :=
  univ.filter (fun x' => (x' : ℤ) = x + 1 ∨ (x' : ℤ) = x - 2)

theorem mem_lout {n : ℕ} {x x' : Fin n} :
    x' ∈ lout x ↔ (x' : ℤ) = x - 1 ∨ (x' : ℤ) = x + 2 := by
  simp only [lout, mem_filter, mem_univ, true_and]

theorem mem_lin {n : ℕ} {x x' : Fin n} :
    x' ∈ lin x ↔ (x' : ℤ) = x + 1 ∨ (x' : ℤ) = x - 2 := by
  simp only [lin, mem_filter, mem_univ, true_and]

theorem outN_eq {n : ℕ} (i j : Fin n) : outN (i, j) = lout i ×ˢ {j} ∪ {i} ×ˢ lout j := by
  ext ⟨i', j'⟩
  rw [mem_outN, mem_union, mem_product, mem_product, mem_lout, mem_lout, mem_singleton,
    mem_singleton]
  unfold Move
  dsimp only
  omega

theorem inN_eq {n : ℕ} (i j : Fin n) : inN (i, j) = lin i ×ˢ {j} ∪ {i} ×ˢ lin j := by
  ext ⟨i', j'⟩
  rw [mem_inN, mem_union, mem_product, mem_product, mem_lin, mem_lin, mem_singleton,
    mem_singleton]
  unfold Move
  dsimp only
  omega

theorem card_outN {n : ℕ} (i j : Fin n) :
    (outN (i, j)).card = (lout i).card + (lout j).card := by
  rw [outN_eq, card_union_of_disjoint, card_product, card_product, card_singleton,
    card_singleton, mul_one, one_mul]
  rw [disjoint_left]
  rintro ⟨i', j'⟩ h1 h2
  rw [mem_product, mem_lout, mem_singleton] at h1
  rw [mem_product, mem_lout, mem_singleton] at h2
  omega

theorem card_inN {n : ℕ} (i j : Fin n) :
    (inN (i, j)).card = (lin i).card + (lin j).card := by
  rw [inN_eq, card_union_of_disjoint, card_product, card_product, card_singleton,
    card_singleton, mul_one, one_mul]
  rw [disjoint_left]
  rintro ⟨i', j'⟩ h1 h2
  rw [mem_product, mem_lin, mem_singleton] at h1
  rw [mem_product, mem_lin, mem_singleton] at h2
  omega

/-! Positions `0`, `1`, `k + 2` (for `k < m`), `m + 2` and `m + 3` of a line of `m + 4`. -/

theorem lout_p0 (m : ℕ) : (lout (0 : Fin (m + 4))).card = 1 := by
  rw [card_eq_one]
  refine ⟨⟨2, by omega⟩, ?_⟩
  ext x'
  rw [mem_lout, mem_singleton, Fin.ext_iff, Fin.val_zero]
  dsimp only
  omega

theorem lout_p1 (m : ℕ) : (lout (0 : Fin (m + 3)).succ).card = 2 := by
  rw [card_eq_two]
  refine ⟨⟨0, by omega⟩, ⟨3, by omega⟩, by simp [Fin.ext_iff], ?_⟩
  ext x'
  rw [mem_lout, mem_insert, mem_singleton, Fin.ext_iff, Fin.ext_iff, Fin.val_succ, Fin.val_zero]
  dsimp only
  omega

theorem lout_mid (m : ℕ) (k : Fin m) : (lout k.castSucc.castSucc.succ.succ).card = 2 := by
  rw [card_eq_two]
  refine ⟨⟨k + 1, by omega⟩, ⟨k + 4, by omega⟩, by simp [Fin.ext_iff], ?_⟩
  ext x'
  rw [mem_lout, mem_insert, mem_singleton, Fin.ext_iff, Fin.ext_iff, Fin.val_succ, Fin.val_succ,
    Fin.val_castSucc, Fin.val_castSucc]
  dsimp only
  omega

theorem lout_p2 (m : ℕ) : (lout (Fin.last m).castSucc.succ.succ).card = 1 := by
  rw [card_eq_one]
  refine ⟨⟨m + 1, by omega⟩, ?_⟩
  ext x'
  rw [mem_lout, mem_singleton, Fin.ext_iff, Fin.val_succ, Fin.val_succ, Fin.val_castSucc,
    Fin.val_last]
  dsimp only
  omega

theorem lout_p3 (m : ℕ) : (lout (Fin.last (m + 1)).succ.succ).card = 1 := by
  rw [card_eq_one]
  refine ⟨⟨m + 2, by omega⟩, ?_⟩
  ext x'
  rw [mem_lout, mem_singleton, Fin.ext_iff, Fin.val_succ, Fin.val_succ, Fin.val_last]
  dsimp only
  omega

theorem lin_p0 (m : ℕ) : (lin (0 : Fin (m + 4))).card = 1 := by
  rw [card_eq_one]
  refine ⟨⟨1, by omega⟩, ?_⟩
  ext x'
  rw [mem_lin, mem_singleton, Fin.ext_iff, Fin.val_zero]
  dsimp only
  omega

theorem lin_p1 (m : ℕ) : (lin (0 : Fin (m + 3)).succ).card = 1 := by
  rw [card_eq_one]
  refine ⟨⟨2, by omega⟩, ?_⟩
  ext x'
  rw [mem_lin, mem_singleton, Fin.ext_iff, Fin.val_succ, Fin.val_zero]
  dsimp only
  omega

theorem lin_mid (m : ℕ) (k : Fin m) : (lin k.castSucc.castSucc.succ.succ).card = 2 := by
  rw [card_eq_two]
  refine ⟨⟨k, by omega⟩, ⟨k + 3, by omega⟩, by simp [Fin.ext_iff], ?_⟩
  ext x'
  rw [mem_lin, mem_insert, mem_singleton, Fin.ext_iff, Fin.ext_iff, Fin.val_succ, Fin.val_succ,
    Fin.val_castSucc, Fin.val_castSucc]
  dsimp only
  omega

theorem lin_p2 (m : ℕ) : (lin (Fin.last m).castSucc.succ.succ).card = 2 := by
  rw [card_eq_two]
  refine ⟨⟨m, by omega⟩, ⟨m + 3, by omega⟩, by simp [Fin.ext_iff], ?_⟩
  ext x'
  rw [mem_lin, mem_insert, mem_singleton, Fin.ext_iff, Fin.ext_iff, Fin.val_succ, Fin.val_succ,
    Fin.val_castSucc, Fin.val_last]
  dsimp only
  omega

theorem lin_p3 (m : ℕ) : (lin (Fin.last (m + 1)).succ.succ).card = 1 := by
  rw [card_eq_one]
  refine ⟨⟨m + 1, by omega⟩, ?_⟩
  ext x'
  rw [mem_lin, mem_singleton, Fin.ext_iff, Fin.val_succ, Fin.val_succ, Fin.val_last]
  dsimp only
  omega

/-- On a line of `m + 4` positions, the pairs `(hi, ho)` are `(1, 1)` twice, `(1, 2)` once,
`(2, 1)` once and `(2, 2)` `m` times. -/
theorem peel (m : ℕ) (g : ℕ → ℕ → ℕ) :
    ∑ x : Fin (m + 4), g (lin x).card (lout x).card = 2 * g 1 1 + g 1 2 + g 2 1 + m * g 2 2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [lin_p0, lin_p1, lin_mid, lin_p2, lin_p3, lout_p0, lout_p1, lout_mid, lout_p2,
    lout_p3, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  ring

theorem a_closed (m : ℕ) : a (m + 4) = 16 * m ^ 2 + 84 * m + 98 := by
  rw [a_eq_sum, Fintype.sum_prod_type]
  simp only [card_inN, card_outN]
  have inner : ∀ i : Fin (m + 4), ∑ j : Fin (m + 4),
      ((lin i).card + (lin j).card) * ((lout i).card + (lout j).card) =
      2 * (((lin i).card + 1) * ((lout i).card + 1)) + ((lin i).card + 1) * ((lout i).card + 2) +
        ((lin i).card + 2) * ((lout i).card + 1) +
        m * (((lin i).card + 2) * ((lout i).card + 2)) :=
    fun i => peel m (fun y z => ((lin i).card + y) * ((lout i).card + z))
  simp only [inner]
  have outer : ∑ i : Fin (m + 4),
      (2 * (((lin i).card + 1) * ((lout i).card + 1)) + ((lin i).card + 1) * ((lout i).card + 2) +
        ((lin i).card + 2) * ((lout i).card + 1) +
        m * (((lin i).card + 2) * ((lout i).card + 2))) =
      2 * (2 * ((1 + 1) * (1 + 1)) + (1 + 1) * (1 + 2) + (1 + 2) * (1 + 1) +
          m * ((1 + 2) * (1 + 2))) +
        (2 * ((1 + 1) * (2 + 1)) + (1 + 1) * (2 + 2) + (1 + 2) * (2 + 1) +
          m * ((1 + 2) * (2 + 2))) +
        (2 * ((2 + 1) * (1 + 1)) + (2 + 1) * (1 + 2) + (2 + 2) * (1 + 1) +
          m * ((2 + 2) * (1 + 2))) +
        m * (2 * ((2 + 1) * (2 + 1)) + (2 + 1) * (2 + 2) + (2 + 2) * (2 + 1) +
          m * ((2 + 2) * (2 + 2))) :=
    peel m (fun x w => 2 * ((x + 1) * (w + 1)) + (x + 1) * (w + 2) + (x + 2) * (w + 1) +
      m * ((x + 2) * (w + 2)))
  rw [outer]
  ring

theorem a_one : a 1 = 0 := by
  rw [a_eq_sum, Fintype.sum_prod_type]
  simp only [card_inN, card_outN]
  have h1 : ∀ i : Fin 1, (lin i).card = 0 := by decide
  have h2 : ∀ i : Fin 1, (lout i).card = 0 := by decide
  simp [h1, h2]

theorem a_two : a 2 = 2 := by
  rw [a_eq_sum, Fintype.sum_prod_type]
  simp only [card_inN, card_outN]
  have h1 : (lin (0 : Fin 2)).card = 1 := by decide
  have h2 : (lin (1 : Fin 2)).card = 0 := by decide
  have h3 : (lout (0 : Fin 2)).card = 0 := by decide
  have h4 : (lout (1 : Fin 2)).card = 1 := by decide
  simp [Fin.sum_univ_two, h1, h2, h3, h4]

theorem a_three : a 3 = 36 := by
  rw [a_eq_sum, Fintype.sum_prod_type]
  simp only [card_inN, card_outN]
  have h1 : ∀ i : Fin 3, (lin i).card = 1 := by decide
  have h2 : ∀ i : Fin 3, (lout i).card = 1 := by decide
  simp [h1, h2]

theorem a_closedQ (n : ℕ) (hn : 4 ≤ n) : (a n : ℚ) = 16 * (n : ℚ) ^ 2 - 44 * n + 18 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [a_closed]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  have key : ∀ k : ℕ, 4 ≤ k → (a k : ℤ) = 16 * (k : ℤ) ^ 2 - 44 * k + 18 := by
    intro k hk
    have := a_closedQ k hk
    exact_mod_cast this
  rw [key n (by omega), key (n - 1) (by omega), key (n - 2) (by omega), key (n - 3) (by omega)]
  push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega]
  ring

theorem a_zero : a 0 = 0 := by
  rw [a_eq_sum]
  simp

theorem a_closedZ (n : ℕ) (hn : 4 ≤ n) : (a n : ℤ) = 16 * (n : ℤ) ^ 2 - 44 * n + 18 := by
  have := a_closedQ n hn
  exact_mod_cast this

open PowerSeries in
theorem gen_funZ :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - X) ^ 3 =
      2 * X ^ 2 * (1 + 15 * X - 2 * X ^ 2 + 5 * X ^ 3 - 3 * X ^ 4) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℤ)) with hA
  have hcube : ((1 : ℤ⟦X⟧) - X) ^ 3 =
      1 - X ^ 1 - X ^ 1 - X ^ 1 + X ^ 2 + X ^ 2 + X ^ 2 - X ^ 3 := by
    ring
  have hrhs : (2 : ℤ⟦X⟧) * X ^ 2 * (1 + 15 * X - 2 * X ^ 2 + 5 * X ^ 3 - 3 * X ^ 4) =
      C (2 : ℤ) * X ^ 2 + C (30 : ℤ) * X ^ 3 - C (4 : ℤ) * X ^ 4 + C (10 : ℤ) * X ^ 5 -
        C (6 : ℤ) * X ^ 6 := by
    simp only [map_ofNat]
    ring
  rw [hcube, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mul_X_pow', hA, coeff_mk]
  have h0 : (a 0 : ℤ) = 0 := by rw [a_zero]; simp
  have h1 : (a 1 : ℤ) = 0 := by rw [a_one]; simp
  have h2 : (a 2 : ℤ) = 2 := by rw [a_two]; simp
  have h3 : (a 3 : ℤ) = 36 := by rw [a_three]; simp
  rcases k with _ | _ | _ | _ | _ | _ | _ | j
  · simp [h0]
  · simp [h0, h1]
  · norm_num [h0, h1, h2]
  · norm_num [h0, h1, h2, h3]
  · norm_num [h0, h1, h2, h3, a_closedZ]
  · norm_num [h0, h1, h2, h3, a_closedZ]
  · norm_num [h0, h1, h2, h3, a_closedZ]
  · simp only [show 1 ≤ j + 7 by omega, show 2 ≤ j + 7 by omega,
      show 3 ≤ j + 7 by omega, show j + 7 - 1 = j + 6 by omega, show j + 7 - 2 = j + 5 by omega,
      show j + 7 - 3 = j + 4 by omega, show ¬ (j + 7 = 2) by omega, show ¬ (j + 7 = 3) by omega,
      show ¬ (j + 7 = 4) by omega, show ¬ (j + 7 = 5) by omega, show ¬ (j + 7 = 6) by omega,
      if_true, if_false]
    rw [a_closedZ (j + 7) (by omega), a_closedZ (j + 6) (by omega), a_closedZ (j + 5) (by omega),
      a_closedZ (j + 4) (by omega)]
    push_cast
    ring

/-! Bridge from the statement's definitions (moves as displacements in a list) to the
coordinatewise ones above. Both read a square as a pair of coordinates and allow the same four
displacements `(-1, 0)`, `(0, -1)`, `(2, 0)`, `(0, 2)`. -/

theorem move_iff {n : ℕ} (p q : Fin n × Fin n) :
    OMA.S_oeis_a187298.toZ q - OMA.S_oeis_a187298.toZ p ∈ OMA.S_oeis_a187298.moves ↔
      Move p q := by
  obtain ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩ := p
  obtain ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩⟩ := q
  simp only [OMA.S_oeis_a187298.toZ, OMA.S_oeis_a187298.moves, List.mem_cons,
    List.not_mem_nil, or_false, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Move, Fin.ext_iff]
  omega

theorem tour_iff {n : ℕ} (w : Fin 3 → Fin n × Fin n) :
    OMA.S_oeis_a187298.IsTour n 3 w ↔ IsTour w := by
  unfold OMA.S_oeis_a187298.IsTour IsTour
  refine and_congr_right fun _ => ⟨fun h => ⟨(move_iff _ _).1 (h 0 1 rfl),
    (move_iff _ _).1 (h 1 2 rfl)⟩, fun h i j hij => ?_⟩
  obtain ⟨h1, h2⟩ := h
  rw [move_iff]
  fin_cases i <;> fin_cases j <;> simp at hij <;> first | exact h1 | exact h2

theorem a_bridge (n : ℕ) : OMA.S_oeis_a187298.a n = a n := by
  classical
  unfold OMA.S_oeis_a187298.a a
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquivRight tour_iff)

theorem main_proof :
    (∀ n : ℕ, 3 < n → (OMA.S_oeis_a187298.a n : ℤ) = 16 * n ^ 2 - 44 * n + 18) ∧
    PowerSeries.mk (fun n => (OMA.S_oeis_a187298.a n : ℤ)) * (1 - PowerSeries.X) ^ 3 =
      2 * PowerSeries.X ^ 2 * (1 + 15 * PowerSeries.X - 2 * PowerSeries.X ^ 2 +
        5 * PowerSeries.X ^ 3 - 3 * PowerSeries.X ^ 4) ∧
    (∀ n : ℕ, 6 < n → (OMA.S_oeis_a187298.a n : ℤ) =
      3 * OMA.S_oeis_a187298.a (n - 1) - 3 * OMA.S_oeis_a187298.a (n - 2) +
        OMA.S_oeis_a187298.a (n - 3)) := by
  simp only [a_bridge]
  exact ⟨fun n hn => a_closedZ n hn, gen_funZ, recurrence⟩

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a187298.main :=
  OMA.Helpers.main_proof
