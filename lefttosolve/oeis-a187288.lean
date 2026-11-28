import OMAStatements.S_oeis_a187288

/-!
Proof of Hardin's formula and Barker's conjectures for A187288 (3-step one or two space at a time
rook's tours on an n X n board).

The tours of the statement are first identified with sequences `w 0, w 1, w 2` of distinct
squares, each a one or two space rook move from the previous one (`T`). A tour is then a middle
square `c` together with an ordered pair of distinct squares one move away from `c`, so
`a n = Σ_c d(c) (d(c) - 1)`, where `d(c)` is the number of squares one move away from `c`. For
`c = (i, j)`, `d(c) = h(i) + h(j)`, where `h(i)` is the number of positions at distance 1 or 2
from `i` on a line of `n` positions. For `n = m + 4` the positions of a line have
`h = 2, 3, 4, ..., 4, 3, 2` (with `m` fours), which gives `a (m + 4) = 56 m^2 + 288 m + 328`,
i.e. `a n = 56 n^2 - 160 n + 72` for `n ≥ 4`, while `a 0 = 0`, `a 1 = 0`, `a 2 = 8` and
`a 3 = 108`. The recurrence and the generating function follow by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a187288 Finset

/-- A one or two space at a time rook move on the `n × n` board. -/
def RookMove {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  (p.1 = q.1 ∧ (((p.2 : ℤ) - q.2).natAbs = 1 ∨ ((p.2 : ℤ) - q.2).natAbs = 2)) ∨
    (p.2 = q.2 ∧ (((p.1 : ℤ) - q.1).natAbs = 1 ∨ ((p.1 : ℤ) - q.1).natAbs = 2))

/-- Three distinct squares, each one rook move (of one or two spaces) from the previous one. -/
def T {n : ℕ} (w : Fin 3 → Fin n × Fin n) : Prop :=
  Function.Injective w ∧ RookMove (w 0) (w 1) ∧ RookMove (w 1) (w 2)

/-- The number of such sequences. -/
noncomputable def b (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {w : Fin 3 → Fin n × Fin n // T w}

theorem move_iff {n : ℕ} (p q : Fin n × Fin n) : toZ q - toZ p ∈ moves ↔ RookMove p q := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := p
  obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := q
  simp only [OMA.S_oeis_a187288.toZ, moves, List.mem_cons, List.not_mem_nil, Prod.mk_sub_mk,
    Prod.mk.injEq, RookMove, Fin.mk.injEq, or_false]
  omega

theorem tour_iff {n : ℕ} (w : Fin 3 → Fin n × Fin n) : IsTour n 3 w ↔ T w := by
  unfold IsTour T
  simp only [move_iff]
  constructor
  · rintro ⟨hi, h⟩
    exact ⟨hi, h 0 1 rfl, h 1 2 rfl⟩
  · rintro ⟨hi, h1, h2⟩
    refine ⟨hi, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;> simp at hij <;> assumption

theorem a_eq_b (n : ℕ) : a n = b n := by
  classical
  unfold a b
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquivRight tour_iff)

instance decRookMove {n : ℕ} (p q : Fin n × Fin n) : Decidable (RookMove p q) :=
  inferInstanceAs (Decidable ((_ ∧ (_ ∨ _)) ∨ (_ ∧ (_ ∨ _))))

/-- The squares one move away from a square. -/
def nbr {n : ℕ} (c : Fin n × Fin n) : Finset (Fin n × Fin n) :=
  univ.filter (fun p => RookMove p c)

theorem rookMove_symm {n : ℕ} {p q : Fin n × Fin n} (h : RookMove p q) : RookMove q p := by
  unfold RookMove at *
  omega

theorem rookMove_ne {n : ℕ} {p q : Fin n × Fin n} (h : RookMove p q) : p ≠ q := by
  rintro rfl
  unfold RookMove at h
  omega

theorem mem_nbr {n : ℕ} {p c : Fin n × Fin n} : p ∈ nbr c ↔ RookMove p c := by
  simp [nbr]

/-- A tour is its middle square together with an ordered pair of distinct squares one move
away from it. -/
def tourEquiv (n : ℕ) :
    {w : Fin 3 → Fin n × Fin n // T w} ≃ Σ c : Fin n × Fin n, ↥(nbr c).offDiag where
  toFun w := ⟨w.1 1, ⟨(w.1 0, w.1 2), by
    rw [mem_offDiag]
    refine ⟨mem_nbr.2 w.2.2.1, mem_nbr.2 (rookMove_symm w.2.2.2), fun h => ?_⟩
    exact absurd (w.2.1 h) (by decide)⟩⟩
  invFun x := ⟨![x.2.1.1, x.1, x.2.1.2], by
    obtain ⟨c, ⟨⟨p, q⟩, h⟩⟩ := x
    rw [mem_offDiag, mem_nbr, mem_nbr] at h
    obtain ⟨hp, hq, hpq⟩ := h
    refine ⟨?_, hp, rookMove_symm hq⟩
    have h1 := rookMove_ne hp
    have h2 := rookMove_ne hq
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv x := by
    obtain ⟨c, ⟨⟨p, q⟩, h⟩⟩ := x
    rfl

theorem b_eq_sum (n : ℕ) :
    b n = ∑ c : Fin n × Fin n, ((nbr c).card * (nbr c).card - (nbr c).card) := by
  classical
  unfold b
  rw [Fintype.card_congr (tourEquiv n), Fintype.card_sigma]
  simp only [Fintype.card_coe, offDiag_card]

/-- The positions at distance 1 or 2 from `i` on a line of `n` positions. -/
def lnbr {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  univ.filter (fun i' => ((i' : ℤ) - i).natAbs = 1 ∨ ((i' : ℤ) - i).natAbs = 2)

theorem mem_lnbr {n : ℕ} {i i' : Fin n} :
    i' ∈ lnbr i ↔ ((i' : ℤ) - i).natAbs = 1 ∨ ((i' : ℤ) - i).natAbs = 2 := by
  simp only [lnbr, mem_filter, mem_univ, true_and]

theorem nbr_eq {n : ℕ} (i j : Fin n) :
    nbr (i, j) = lnbr i ×ˢ {j} ∪ {i} ×ˢ lnbr j := by
  ext ⟨i', j'⟩
  rw [mem_nbr, mem_union, mem_product, mem_product, mem_lnbr, mem_lnbr, mem_singleton,
    mem_singleton]
  unfold RookMove
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

/-- Position `0` of a line of `m + 4` positions has two neighbours: `1, 2`. -/
theorem lnbr_p0 (m : ℕ) : (lnbr (0 : Fin (m + 4))).card = 2 := by
  have h : lnbr (0 : Fin (m + 4)) = {⟨1, by omega⟩, ⟨2, by omega⟩} := by
    ext i'
    simp only [mem_lnbr, mem_insert, mem_singleton, Fin.ext_iff, Fin.val_zero]
    omega
  rw [h, card_pair]
  simp [Fin.ext_iff]

/-- Position `1` has three neighbours: `0, 2, 3`. -/
theorem lnbr_p1 (m : ℕ) : (lnbr (0 : Fin (m + 3)).succ).card = 3 := by
  have h : lnbr (0 : Fin (m + 3)).succ = {⟨0, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩} := by
    ext i'
    simp only [mem_lnbr, mem_insert, mem_singleton, Fin.ext_iff, Fin.val_succ, Fin.val_zero]
    omega
  rw [h, card_insert_of_notMem, card_pair]
  · simp [Fin.ext_iff]
  · simp [Fin.ext_iff]

/-- A middle position `k + 2` has four neighbours: `k, k + 1, k + 3, k + 4`. -/
theorem lnbr_mid (m : ℕ) (k : Fin m) : (lnbr k.castSucc.castSucc.succ.succ).card = 4 := by
  have h : lnbr k.castSucc.castSucc.succ.succ =
      {⟨k, by omega⟩, ⟨k + 1, by omega⟩, ⟨k + 3, by omega⟩, ⟨k + 4, by omega⟩} := by
    ext i'
    simp only [mem_lnbr, mem_insert, mem_singleton, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
    omega
  rw [h, card_insert_of_notMem, card_insert_of_notMem, card_pair]
  · simp [Fin.ext_iff]
  · simp [Fin.ext_iff]
  · simp [Fin.ext_iff]

/-- Position `m + 2` has three neighbours: `m, m + 1, m + 3`. -/
theorem lnbr_p2 (m : ℕ) : (lnbr (Fin.last m).castSucc.succ.succ).card = 3 := by
  have h : lnbr (Fin.last m).castSucc.succ.succ =
      {⟨m, by omega⟩, ⟨m + 1, by omega⟩, ⟨m + 3, by omega⟩} := by
    ext i'
    simp only [mem_lnbr, mem_insert, mem_singleton, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc,
      Fin.val_last]
    omega
  rw [h, card_insert_of_notMem, card_pair]
  · simp [Fin.ext_iff]
  · simp [Fin.ext_iff]

/-- Position `m + 3` has two neighbours: `m + 1, m + 2`. -/
theorem lnbr_p3 (m : ℕ) : (lnbr (Fin.last (m + 1)).succ.succ).card = 2 := by
  have h : lnbr (Fin.last (m + 1)).succ.succ = {⟨m + 1, by omega⟩, ⟨m + 2, by omega⟩} := by
    ext i'
    simp only [mem_lnbr, mem_insert, mem_singleton, Fin.ext_iff, Fin.val_succ, Fin.val_last]
    omega
  rw [h, card_pair]
  simp [Fin.ext_iff]

/-- On a line of `m + 4` positions, two positions have two neighbours, two have three and `m`
have four. -/
theorem peel (m : ℕ) (g : ℕ → ℕ) :
    ∑ i : Fin (m + 4), g (lnbr i).card = 2 * g 2 + 2 * g 3 + m * g 4 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [lnbr_p0, lnbr_p1, lnbr_mid, lnbr_p2, lnbr_p3, sum_const, card_univ,
    Fintype.card_fin, smul_eq_mul]
  ring

theorem b_closed (m : ℕ) : b (m + 4) = 56 * m ^ 2 + 288 * m + 328 := by
  rw [b_eq_sum, Fintype.sum_prod_type]
  simp only [card_nbr]
  have inner : ∀ i : Fin (m + 4), ∑ j : Fin (m + 4),
      (((lnbr i).card + (lnbr j).card) * ((lnbr i).card + (lnbr j).card) -
        ((lnbr i).card + (lnbr j).card)) =
      2 * (((lnbr i).card + 2) * ((lnbr i).card + 2) - ((lnbr i).card + 2)) +
        2 * (((lnbr i).card + 3) * ((lnbr i).card + 3) - ((lnbr i).card + 3)) +
        m * (((lnbr i).card + 4) * ((lnbr i).card + 4) - ((lnbr i).card + 4)) :=
    fun i => peel m (fun y => ((lnbr i).card + y) * ((lnbr i).card + y) - ((lnbr i).card + y))
  simp only [inner]
  have outer : ∑ i : Fin (m + 4),
      (2 * (((lnbr i).card + 2) * ((lnbr i).card + 2) - ((lnbr i).card + 2)) +
        2 * (((lnbr i).card + 3) * ((lnbr i).card + 3) - ((lnbr i).card + 3)) +
        m * (((lnbr i).card + 4) * ((lnbr i).card + 4) - ((lnbr i).card + 4))) =
      2 * (2 * ((2 + 2) * (2 + 2) - (2 + 2)) + 2 * ((2 + 3) * (2 + 3) - (2 + 3)) +
          m * ((2 + 4) * (2 + 4) - (2 + 4))) +
        2 * (2 * ((3 + 2) * (3 + 2) - (3 + 2)) + 2 * ((3 + 3) * (3 + 3) - (3 + 3)) +
          m * ((3 + 4) * (3 + 4) - (3 + 4))) +
        m * (2 * ((4 + 2) * (4 + 2) - (4 + 2)) + 2 * ((4 + 3) * (4 + 3) - (4 + 3)) +
          m * ((4 + 4) * (4 + 4) - (4 + 4))) :=
    peel m (fun x => 2 * ((x + 2) * (x + 2) - (x + 2)) + 2 * ((x + 3) * (x + 3) - (x + 3)) +
      m * ((x + 4) * (x + 4) - (x + 4)))
  rw [outer]
  norm_num
  ring

theorem b_one : b 1 = 0 := by
  rw [b_eq_sum, Fintype.sum_prod_type]
  simp only [card_nbr]
  have h : ∀ i : Fin 1, (lnbr i).card = 0 := by decide
  simp [h]

theorem b_two : b 2 = 8 := by
  rw [b_eq_sum, Fintype.sum_prod_type]
  simp only [card_nbr]
  have h : ∀ i : Fin 2, (lnbr i).card = 1 := by decide
  simp [h]

theorem b_three : b 3 = 108 := by
  rw [b_eq_sum, Fintype.sum_prod_type]
  simp only [card_nbr]
  have h : ∀ i : Fin 3, (lnbr i).card = 2 := by decide
  simp [h]

theorem a_zero : a 0 = 0 := by
  unfold a
  simp

theorem a_closedZ (n : ℕ) (hn : 4 ≤ n) : (a n : ℤ) = 56 * (n : ℤ) ^ 2 - 160 * n + 72 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [a_eq_b, b_closed]
  push_cast
  ring

theorem formula (n : ℕ) (hn : 3 < n) : (a n : ℤ) = 56 * n ^ 2 - 160 * n + 72 :=
  a_closedZ n hn

theorem recurrence (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  rw [a_closedZ n (by omega), a_closedZ (n - 1) (by omega), a_closedZ (n - 2) (by omega),
    a_closedZ (n - 3) (by omega)]
  push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega]
  ring

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - X) ^ 3 =
      4 * X ^ 2 * (2 + 21 * X + 7 * X ^ 2 + X ^ 3 - 3 * X ^ 4) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℤ)) with hA
  have hcube : ((1 : ℤ⟦X⟧) - X) ^ 3 =
      1 - X ^ 1 - X ^ 1 - X ^ 1 + X ^ 2 + X ^ 2 + X ^ 2 - X ^ 3 := by
    ring
  have hrhs : (4 : ℤ⟦X⟧) * X ^ 2 * (2 + 21 * X + 7 * X ^ 2 + X ^ 3 - 3 * X ^ 4) =
      C (8 : ℤ) * X ^ 2 + C (84 : ℤ) * X ^ 3 + C (28 : ℤ) * X ^ 4 + C (4 : ℤ) * X ^ 5 -
        C (12 : ℤ) * X ^ 6 := by
    simp only [map_ofNat]
    ring
  rw [hcube, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mul_X_pow', hA, coeff_mk]
  have h0 : (a 0 : ℤ) = 0 := by rw [a_zero]; simp
  have h1 : (a 1 : ℤ) = 0 := by rw [a_eq_b, b_one]; simp
  have h2 : (a 2 : ℤ) = 8 := by rw [a_eq_b, b_two]; simp
  have h3 : (a 3 : ℤ) = 108 := by rw [a_eq_b, b_three]; simp
  have h4 : (a 4 : ℤ) = 328 := by rw [a_closedZ 4 le_rfl]; norm_num
  have h5 : (a 5 : ℤ) = 672 := by rw [a_closedZ 5 (by norm_num)]; norm_num
  have h6 : (a 6 : ℤ) = 1128 := by rw [a_closedZ 6 (by norm_num)]; norm_num
  rcases k with _ | _ | _ | _ | _ | _ | _ | j
  · simp [h0]
  · norm_num [h0, h1]
  · norm_num [h0, h1, h2]
  · norm_num [h0, h1, h2, h3]
  · norm_num [h1, h2, h3, h4]
  · norm_num [h2, h3, h4, h5]
  · norm_num [h3, h4, h5, h6]
  · simp only [show 1 ≤ j + 7 by omega, show 2 ≤ j + 7 by omega,
      show 3 ≤ j + 7 by omega, show j + 7 - 1 = j + 6 by omega, show j + 7 - 2 = j + 5 by omega,
      show j + 7 - 3 = j + 4 by omega, show ¬ (j + 7 = 2) by omega, show ¬ (j + 7 = 3) by omega,
      show ¬ (j + 7 = 4) by omega, show ¬ (j + 7 = 5) by omega, show ¬ (j + 7 = 6) by omega,
      if_true, if_false]
    rw [a_closedZ (j + 7) (by omega), a_closedZ (j + 6) (by omega), a_closedZ (j + 5) (by omega),
      a_closedZ (j + 4) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a187288.main :=
  ⟨OMA.Helpers.formula, OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
