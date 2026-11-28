import OMAStatements.S_oeis_a202331

/-!
Proof of Barker's conjectures for A202331: (n+1) X 5 binary arrays whose consecutive windows of two
bits, read as binary numbers (first bit most significant), are nondecreasing in every row and
every column.

On bits, `2x + y ≤ 2y + z` holds iff `x ≤ y` and `x ≤ z` (`bit_iff`). Hence a word `v` of length
`L` has nondecreasing windows iff `v i ≤ v (i + 1)` and `v i ≤ v (i + 2)` whenever `i + 2 < L`
(`wn_iff`). For a row of length 5 these are six inequalities (`RowOK`), satisfied by exactly seven
rows (`e`): 00000, 00001, 00010, 00011, 00111, 01111, 11111. For the columns the condition says
that every row is pointwise below the next two rows (`valid_iff`, `Good`).

Putting a row `p` on top of a good sequence of at least three rows keeps it good iff `p` satisfies
the row condition and `p` is pointwise below the old top row (`good_cons_long`: the old top row is
already below the next one). So the number `D m p` of good sequences of `m + 3` rows starting
with a good row `p` satisfies `D 0 p = up(p)^2`, where `up(p)` counts the good rows above `p`
(`D_zero`), and `D (m + 1) p = Sum_{q good, p ≤ q} D m q` (`D_succ`); `D m p = 0` if `p` is not
good. Under the pointwise order the seven good rows form a chain, except that 00001 and 00010 are
incomparable (`rle_e`); this gives the recursions `step0`, ..., `step6` and, by induction, the
closed forms (`closed`)
  D m 11111 = 1, D m 01111 = m + 4, D m 00111 = (m+3)(m+6)/2, D m 00011 = (m+3)(m+4)(m+8)/6,
  D m 00010 = D m 00001 = (m+3)(m+4)(m+5)(m+10)/24,
  D m 00000 = (2m^5 + 55m^4 + 560m^3 + 2705m^2 + 6278m + 5880)/120.
Summing over the seven rows gives 120 a(n) = 2n^5 + 45n^4 + 360n^3 + 1335n^2 + 2338n + 1800 for
n ≥ 2 (`a_closed`), and also for n = 1, where the column condition is empty and a(1) = 7^2 = 49
(`a_one`). The recurrence and the generating function follow by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a202331 Finset

/-- A row of the array. -/
abbrev Row := Fin 5 → Fin 2

/-- On bits, `2x + y ≤ 2y + z` iff `x ≤ y` and `x ≤ z`. -/
theorem bit_iff : ∀ x y z : Fin 2, 2 * x.val + y.val ≤ 2 * y.val + z.val ↔ x ≤ y ∧ x ≤ z := by
  decide

theorem wn_iff {L : ℕ} (v : Fin L → Fin 2) :
    WindowsNondecreasing v ↔ ∀ (i : ℕ) (hi : i + 2 < L),
      v ⟨i, by omega⟩ ≤ v ⟨i + 1, by omega⟩ ∧ v ⟨i, by omega⟩ ≤ v ⟨i + 2, hi⟩ := by
  unfold WindowsNondecreasing window
  exact forall_congr' fun i => forall_congr' fun hi => bit_iff _ _ _

/-- The row condition, as six inequalities between bits. -/
def RowOK (r : Row) : Prop :=
  r 0 ≤ r 1 ∧ r 0 ≤ r 2 ∧ r 1 ≤ r 2 ∧ r 1 ≤ r 3 ∧ r 2 ≤ r 3 ∧ r 2 ≤ r 4

instance decRowOK (r : Row) : Decidable (RowOK r) := by
  unfold RowOK
  infer_instance

theorem row_iff (r : Row) : WindowsNondecreasing r ↔ RowOK r := by
  rw [wn_iff]
  constructor
  · intro h
    exact ⟨(h 0 (by norm_num)).1, (h 0 (by norm_num)).2, (h 1 (by norm_num)).1,
      (h 1 (by norm_num)).2, (h 2 (by norm_num)).1, (h 2 (by norm_num)).2⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩ i hi
    have : i < 3 := by omega
    interval_cases i
    · exact ⟨h1, h2⟩
    · exact ⟨h3, h4⟩
    · exact ⟨h5, h6⟩

/-- The pointwise order on rows. -/
def rle (x y : Row) : Prop := ∀ c, x c ≤ y c

instance decRle (x y : Row) : Decidable (rle x y) := by
  unfold rle
  infer_instance

theorem rle_trans {x y z : Row} (h1 : rle x y) (h2 : rle y z) : rle x z :=
  fun c => le_trans (h1 c) (h2 c)

/-- The condition on a sequence of rows: every row satisfies the row condition, and every row is
pointwise below the next two rows. -/
def Good {m : ℕ} (g : Fin m → Row) : Prop :=
  (∀ i, RowOK (g i)) ∧
    ∀ (i : ℕ) (hi : i + 2 < m),
      rle (g ⟨i, by omega⟩) (g ⟨i + 1, by omega⟩) ∧ rle (g ⟨i, by omega⟩) (g ⟨i + 2, hi⟩)

theorem valid_iff {n : ℕ} (A : Fin (n + 1) → Fin 5 → Fin 2) : IsValid A ↔ Good A := by
  unfold IsValid Good
  refine and_congr (forall_congr' fun i => row_iff (A i)) ?_
  simp only [wn_iff, rle]
  constructor
  · intro h i hi
    exact ⟨fun j => (h j i hi).1, fun j => (h j i hi).2⟩
  · intro h j i hi
    exact ⟨(h i hi).1 j, (h i hi).2 j⟩

theorem good_cons_long {m : ℕ} (p : Row) (g : Fin (m + 3) → Row) :
    Good (Fin.cons p g : Fin (m + 4) → Row) ↔ RowOK p ∧ rle p (g 0) ∧ Good g := by
  constructor
  · rintro ⟨hr, hc⟩
    have h0 := hc 0 (by omega)
    refine ⟨hr 0, ?_, fun i => hr i.succ, fun i hi => hc (i + 1) (by omega)⟩
    exact h0.1
  · rintro ⟨hp, hpg, hr, hc⟩
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact hp
      · exact hr j
    · cases i with
      | zero => exact ⟨hpg, rle_trans hpg (hc 0 (by omega)).1⟩
      | succ i => exact hc i (by omega)

theorem good_three (h : Fin 3 → Row) :
    Good h ↔ RowOK (h 0) ∧ RowOK (h 1) ∧ RowOK (h 2) ∧ rle (h 0) (h 1) ∧ rle (h 0) (h 2) := by
  constructor
  · rintro ⟨hr, hc⟩
    exact ⟨hr 0, hr 1, hr 2, (hc 0 (by norm_num)).1, (hc 0 (by norm_num)).2⟩
  · rintro ⟨h0, h1, h2, h01, h02⟩
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · fin_cases i
      · exact h0
      · exact h1
      · exact h2
    · obtain rfl : i = 0 := by omega
      exact ⟨h01, h02⟩

theorem good_two (h : Fin 2 → Row) : Good h ↔ ∀ i, RowOK (h i) := by
  constructor
  · exact fun hh => hh.1
  · exact fun hh => ⟨hh, fun i hi => absurd hi (by omega)⟩

/-- The number of good sequences of `m + 3` rows whose first row is `p`. -/
noncomputable def D (m : ℕ) (p : Row) : ℕ := by
  classical
  exact ∑ g : Fin (m + 2) → Row, if Good (Fin.cons p g : Fin (m + 3) → Row) then 1 else 0

theorem D_invalid (m : ℕ) (p : Row) (hp : ¬ RowOK p) : D m p = 0 := by
  classical
  unfold D
  exact Finset.sum_eq_zero fun g _ => if_neg fun h => hp (h.1 0)

theorem D_succ (m : ℕ) (p : Row) :
    D (m + 1) p = if RowOK p then ∑ q : Row, (if rle p q then D m q else 0) else 0 := by
  classical
  unfold D
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun x => if Good (Fin.cons p (Fin.cons x.1 x.2) : Fin (m + 4) → Row) then 1 else 0)
    (fun g => by simp), Fintype.sum_prod_type]
  split_ifs with hp
  · refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs with hq
    · refine Finset.sum_congr rfl fun g _ => if_congr ?_ rfl rfl
      rw [good_cons_long]
      exact ⟨fun h => h.2.2, fun h => ⟨hp, hq, h⟩⟩
    · refine Finset.sum_eq_zero fun g _ => if_neg ?_
      rw [good_cons_long]
      exact fun h => hq h.2.1
  · refine Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun g _ => if_neg ?_
    rw [good_cons_long]
    exact fun h => hp h.1

theorem D_zero (p : Row) :
    D 0 p = if RowOK p then (∑ q : Row, if RowOK q ∧ rle p q then 1 else 0) ^ 2 else 0 := by
  classical
  unfold D
  rw [Fintype.sum_equiv (piFinTwoEquiv fun _ => Row) _
    (fun x => if RowOK p ∧ RowOK x.1 ∧ RowOK x.2 ∧ rle p x.1 ∧ rle p x.2 then 1 else 0)
    (fun g => if_congr (good_three _) rfl rfl), Fintype.sum_prod_type]
  split_ifs with hp
  · rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
    rw [ite_zero_mul_ite_zero, one_mul]
    exact if_congr (by tauto) rfl rfl
  · exact Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun r _ => if_neg fun h => hp h.1

theorem a_eq (m : ℕ) : a (m + 2) = ∑ p : Row, D m p := by
  classical
  have h1 : a (m + 2) = ∑ A : Fin (m + 3) → Row, if Good A then 1 else 0 := by
    unfold a
    rw [Fintype.card_subtype, Finset.card_filter]
    exact Finset.sum_congr rfl fun A _ => if_congr (valid_iff A) rfl rfl
  rw [h1, Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun x => if Good (Fin.cons x.1 x.2 : Fin (m + 3) → Row) then 1 else 0) (fun A => by simp),
    Fintype.sum_prod_type]
  rfl

theorem rowOK_count : (∑ q : Row, if RowOK q then 1 else 0) = 7 := by
  decide

theorem a_one : a 1 = 49 := by
  classical
  have h1 : a 1 = ∑ A : Fin 2 → Row, if RowOK (A 0) ∧ RowOK (A 1) then 1 else 0 := by
    unfold a
    rw [Fintype.card_subtype, Finset.card_filter]
    refine Finset.sum_congr rfl fun A _ => if_congr ?_ rfl rfl
    rw [valid_iff, good_two, Fin.forall_fin_two]
  rw [h1, Fintype.sum_equiv (piFinTwoEquiv fun _ => Row)
    (fun A : Fin 2 → Row => if RowOK (A 0) ∧ RowOK (A 1) then 1 else 0)
    (fun x => if RowOK x.1 ∧ RowOK x.2 then 1 else 0) (fun A => rfl), Fintype.sum_prod_type]
  have h2 : ∀ q r : Row, (if RowOK q ∧ RowOK r then 1 else 0) =
      (if RowOK q then 1 else 0) * (if RowOK r then 1 else 0) := by
    intro q r
    by_cases hq : RowOK q <;> by_cases hr : RowOK r <;> simp [hq, hr]
  simp only [h2, ← Finset.sum_mul_sum, rowOK_count]
  norm_num

/-- The seven rows satisfying the row condition. -/
def e : Fin 7 → Row :=
  ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 1], ![0, 0, 0, 1, 0], ![0, 0, 0, 1, 1], ![0, 0, 1, 1, 1],
    ![0, 1, 1, 1, 1], ![1, 1, 1, 1, 1]]

theorem e_injective : Function.Injective e := by
  decide

/-- `e` as an embedding. -/
def eEmb : Fin 7 ↪ Row := ⟨e, e_injective⟩

theorem filter_rowOK : Finset.univ.filter RowOK = Finset.univ.map eEmb := by
  decide

theorem sum_rows {M : Type*} [AddCommMonoid M] (f : Row → M) (hf : ∀ q, ¬ RowOK q → f q = 0) :
    ∑ q, f q = ∑ i, f (e i) := by
  rw [← Finset.sum_filter_of_ne (p := RowOK) (fun q _ hq => by_contra fun h => hq (hf q h)),
    filter_rowOK, Finset.sum_map]
  rfl

theorem rowOK_e : ∀ i, RowOK (e i) := by
  decide

theorem rle_e : ∀ i j : Fin 7, rle (e i) (e j) ↔ (i ≤ j ∧ ¬ (i = 1 ∧ j = 2)) := by
  decide

theorem D_succ_e (m : ℕ) (i : Fin 7) :
    D (m + 1) (e i) = ∑ j : Fin 7, if rle (e i) (e j) then D m (e j) else 0 := by
  rw [D_succ, if_pos (rowOK_e i)]
  exact sum_rows _ fun q hq => by rw [D_invalid m q hq]; simp

theorem D_zero_vals : D 0 (e 6) = 1 ∧ D 0 (e 5) = 4 ∧ D 0 (e 4) = 9 ∧ D 0 (e 3) = 16 ∧
    D 0 (e 2) = 25 ∧ D 0 (e 1) = 25 ∧ D 0 (e 0) = 49 := by
  simp only [D_zero, rowOK_e, if_true]
  decide

theorem step6 (m : ℕ) : D (m + 1) (e 6) = D m (e 6) := by
  rw [D_succ_e, Fin.sum_univ_seven]
  simp [rle_e]

theorem step5 (m : ℕ) : D (m + 1) (e 5) = D m (e 5) + D m (e 6) := by
  rw [D_succ_e, Fin.sum_univ_seven]
  simp [rle_e]

theorem step4 (m : ℕ) : D (m + 1) (e 4) = D m (e 4) + D m (e 5) + D m (e 6) := by
  rw [D_succ_e, Fin.sum_univ_seven]
  simp [rle_e]

theorem step3 (m : ℕ) : D (m + 1) (e 3) = D m (e 3) + D m (e 4) + D m (e 5) + D m (e 6) := by
  rw [D_succ_e, Fin.sum_univ_seven]
  simp [rle_e]

theorem step2 (m : ℕ) :
    D (m + 1) (e 2) = D m (e 2) + D m (e 3) + D m (e 4) + D m (e 5) + D m (e 6) := by
  rw [D_succ_e, Fin.sum_univ_seven]
  simp [rle_e]

theorem step1 (m : ℕ) :
    D (m + 1) (e 1) = D m (e 1) + D m (e 3) + D m (e 4) + D m (e 5) + D m (e 6) := by
  rw [D_succ_e, Fin.sum_univ_seven]
  simp [rle_e]

theorem step0 (m : ℕ) : D (m + 1) (e 0) = D m (e 0) + D m (e 1) + D m (e 2) + D m (e 3) +
    D m (e 4) + D m (e 5) + D m (e 6) := by
  rw [D_succ_e, Fin.sum_univ_seven]
  simp [rle_e]

theorem closed (m : ℕ) :
    (D m (e 6) : ℚ) = 1 ∧
    (D m (e 5) : ℚ) = m + 4 ∧
    (D m (e 4) : ℚ) = (m + 3) * (m + 6) / 2 ∧
    (D m (e 3) : ℚ) = (m + 3) * (m + 4) * (m + 8) / 6 ∧
    (D m (e 2) : ℚ) = (m + 3) * (m + 4) * (m + 5) * (m + 10) / 24 ∧
    (D m (e 1) : ℚ) = (m + 3) * (m + 4) * (m + 5) * (m + 10) / 24 ∧
    (D m (e 0) : ℚ) =
      (2 * m ^ 5 + 55 * m ^ 4 + 560 * m ^ 3 + 2705 * m ^ 2 + 6278 * m + 5880) / 120 := by
  induction m with
  | zero =>
    obtain ⟨h6, h5, h4, h3, h2, h1, h0⟩ := D_zero_vals
    rw [h6, h5, h4, h3, h2, h1, h0]
    norm_num
  | succ m ih =>
    obtain ⟨h6, h5, h4, h3, h2, h1, h0⟩ := ih
    rw [step6, step5, step4, step3, step2, step1, step0]
    push_cast
    refine ⟨h6, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination h5 + h6
    · linear_combination h4 + h5 + h6
    · linear_combination h3 + h4 + h5 + h6
    · linear_combination h2 + h3 + h4 + h5 + h6
    · linear_combination h1 + h3 + h4 + h5 + h6
    · linear_combination h0 + h1 + h2 + h3 + h4 + h5 + h6

theorem a_closed (m : ℕ) :
    (a (m + 2) : ℚ) = (2 * ((m : ℚ) + 2) ^ 5 + 45 * ((m : ℚ) + 2) ^ 4 +
      360 * ((m : ℚ) + 2) ^ 3 + 1335 * ((m : ℚ) + 2) ^ 2 + 2338 * ((m : ℚ) + 2) + 1800) / 120 := by
  rw [a_eq, sum_rows _ (D_invalid m), Fin.sum_univ_seven]
  push_cast
  obtain ⟨h6, h5, h4, h3, h2, h1, h0⟩ := closed m
  linear_combination h0 + h1 + h2 + h3 + h4 + h5 + h6

theorem closedQ (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (2 * (n : ℚ) ^ 5 + 45 * (n : ℚ) ^ 4 + 360 * (n : ℚ) ^ 3 + 1335 * (n : ℚ) ^ 2 +
      2338 * (n : ℚ) + 1800) / 120 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [a_one]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [a_closed m]
    push_cast
    ring

theorem recurrence (n : ℕ) (hn : n > 6) :
    (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
      6 * a (n - 5) - a (n - 6) := by
  have h : ((a n : ℤ) : ℚ) = ((6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
      15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) : ℤ) : ℚ) := by
    push_cast
    rw [closedQ n (by omega), closedQ (n - 1) (by omega), closedQ (n - 2) (by omega),
      closedQ (n - 3) (by omega), closedQ (n - 4) (by omega), closedQ (n - 5) (by omega),
      closedQ (n - 6) (by omega)]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega]
    ring
  exact_mod_cast h

theorem a_val (n : ℕ) (hn : 1 ≤ n) (v : ℕ)
    (hv : (2 * (n : ℚ) ^ 5 + 45 * (n : ℚ) ^ 4 + 360 * (n : ℚ) ^ 3 + 1335 * (n : ℚ) ^ 2 +
      2338 * (n : ℚ) + 1800) / 120 = v) : a n = v := by
  have h := closedQ n hn
  rw [hv] at h
  exact_mod_cast h

theorem a_vals : a 1 = 49 ∧ a 2 = 129 ∧ a 3 = 289 ∧ a 4 = 576 ∧ a 5 = 1052 ∧ a 6 = 1796 :=
  ⟨a_one, a_val 2 (by norm_num) 129 (by norm_num), a_val 3 (by norm_num) 289 (by norm_num),
    a_val 4 (by norm_num) 576 (by norm_num), a_val 5 (by norm_num) 1052 (by norm_num),
    a_val 6 (by norm_num) 1796 (by norm_num)⟩

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (1 - X) ^ 6 =
      X * (49 - 165 * X + 250 * X ^ 2 - 203 * X ^ 3 + 86 * X ^ 4 - 15 * X ^ 5) := by
  set F : ℕ → ℤ := fun n => if n = 0 then (0 : ℤ) else (a n : ℤ) with hF
  have key : PowerSeries.mk F * (1 - X) ^ 6 =
      PowerSeries.mk F * X ^ 0 - C 6 * (PowerSeries.mk F * X ^ 1) +
        C 15 * (PowerSeries.mk F * X ^ 2) - C 20 * (PowerSeries.mk F * X ^ 3) +
        C 15 * (PowerSeries.mk F * X ^ 4) - C 6 * (PowerSeries.mk F * X ^ 5) +
        PowerSeries.mk F * X ^ 6 := by
    simp only [map_ofNat]
    ring
  have hrhs : (X : ℤ⟦X⟧) * (49 - 165 * X + 250 * X ^ 2 - 203 * X ^ 3 + 86 * X ^ 4 - 15 * X ^ 5) =
      C 49 * X ^ 1 - C 165 * X ^ 2 + C 250 * X ^ 3 - C 203 * X ^ 4 + C 86 * X ^ 5 -
        C 15 * X ^ 6 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := a_vals
  by_cases hk : k < 7
  · interval_cases k <;> simp [hF, h1, h2, h3, h4, h5, h6]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
    have hr := recurrence (j + 7) (by omega)
    simp only [show j + 7 - 1 = j + 6 by omega, show j + 7 - 2 = j + 5 by omega,
      show j + 7 - 3 = j + 4 by omega, show j + 7 - 4 = j + 3 by omega,
      show j + 7 - 5 = j + 2 by omega, show j + 7 - 6 = j + 1 by omega] at hr
    simp only [show 1 ≤ j + 7 by omega, show 2 ≤ j + 7 by omega, show 3 ≤ j + 7 by omega,
      show 4 ≤ j + 7 by omega, show 5 ≤ j + 7 by omega, show 6 ≤ j + 7 by omega,
      show j + 7 - 0 = j + 7 by omega, show j + 7 - 1 = j + 6 by omega,
      show j + 7 - 2 = j + 5 by omega, show j + 7 - 3 = j + 4 by omega,
      show j + 7 - 4 = j + 3 by omega, show j + 7 - 5 = j + 2 by omega,
      show j + 7 - 6 = j + 1 by omega,
      show ¬ (j + 7 = 1) by omega, show ¬ (j + 7 = 2) by omega, show ¬ (j + 7 = 3) by omega,
      show ¬ (j + 7 = 4) by omega, show ¬ (j + 7 = 5) by omega, show ¬ (j + 7 = 6) by omega,
      show ¬ (j + 7 = 0) by omega, show ¬ (j + 6 = 0) by omega, show ¬ (j + 5 = 0) by omega,
      show ¬ (j + 4 = 0) by omega, show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega,
      show ¬ (j + 1 = 0) by omega, if_true, if_false, hF, zero_le]
    linear_combination hr

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a202331.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
