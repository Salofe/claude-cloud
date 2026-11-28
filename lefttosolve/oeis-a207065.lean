import OMAStatements.S_oeis_a207065
import Mathlib

/-!
Rows read left to right avoid 001 and 010: exactly fourteen rows of length 5 do. Columns read top
to bottom avoid 001 and 101, that is, a 0 with a row above it is followed by a 0: every row from
the second one on is pointwise below the previous row. So an array is a free valid top row
followed by a pointwise nonincreasing chain of valid rows, and the chains are counted state by
state.
-/

namespace OMA.Helpers

open OMA.S_oeis_a207065 Finset

/-- A row of the array. -/
abbrev Row := Fin 5 → Fin 2

/-- Entry of a row, with a natural index (`0` outside). -/
def rg (v : Row) (j : ℕ) : ℕ := if h : j < 5 then (v ⟨j, h⟩ : ℕ) else 0

/-- The horizontal condition on one row. -/
def HOK (v : Row) : Prop :=
  ∀ j < 3, (rg v j, rg v (j + 1), rg v (j + 2)) ≠ (0, 0, 1) ∧
    (rg v j, rg v (j + 1), rg v (j + 2)) ≠ (0, 1, 0)

instance decHOK (v : Row) : Decidable (HOK v) := by
  unfold HOK
  infer_instance

/-- The pointwise order on rows. -/
def rle (x y : Row) : Prop := ∀ c, x c ≤ y c

instance decRle (x y : Row) : Decidable (rle x y) := by
  unfold rle
  infer_instance

theorem rle_trans {x y z : Row} (h1 : rle x y) (h2 : rle y z) : rle x z :=
  fun c => le_trans (h1 c) (h2 c)

theorem get_eq {r : ℕ} (x : Fin r → Row) (i : ℕ) (hi : i < r) (j : ℕ) :
    OMA.S_oeis_a207065.get x i j = rg (x ⟨i, hi⟩) j := by
  unfold OMA.S_oeis_a207065.get rg
  by_cases hj : j < 5
  · simp [hi, hj]
  · simp [hj]

theorem rg_fin (v : Row) (c : Fin 5) : rg v c.val = (v c : ℕ) := by
  simp [rg, c.isLt]

theorem bit3 : ∀ a b c : Fin 2,
    (((a : ℕ), (b : ℕ), (c : ℕ)) ≠ (0, 0, 1) ∧ ((a : ℕ), (b : ℕ), (c : ℕ)) ≠ (1, 0, 1)) ↔ c ≤ b := by
  decide

theorem avoids_iff {r : ℕ} (x : Fin r → Row) :
    avoids x = true ↔ (∀ i : Fin r, HOK (x i)) ∧
      ∀ (i : ℕ) (h : i + 2 < r), rle (x ⟨i + 2, h⟩) (x ⟨i + 1, by omega⟩) := by
  unfold avoids
  rw [decide_eq_true_iff]
  apply and_congr
  · constructor
    · intro h i j hj
      have := h i.val i.isLt j (by omega)
      rwa [get_eq x i.val i.isLt, get_eq x i.val i.isLt, get_eq x i.val i.isLt] at this
    · intro h i hi j hj
      rw [get_eq x i hi, get_eq x i hi, get_eq x i hi]
      exact h ⟨i, hi⟩ j (by omega)
  · constructor
    · intro h i hi c
      have := h i (by omega) c.val c.isLt
      rw [get_eq x i (by omega), get_eq x (i + 1) (by omega), get_eq x (i + 2) hi, rg_fin,
        rg_fin, rg_fin] at this
      exact (bit3 _ _ _).1 this
    · intro h i hi j hj
      rw [get_eq x i (by omega), get_eq x (i + 1) (by omega), get_eq x (i + 2) (by omega)]
      have := (bit3 (x ⟨i, by omega⟩ ⟨j, hj⟩) (x ⟨i + 1, by omega⟩ ⟨j, hj⟩)
        (x ⟨i + 2, by omega⟩ ⟨j, hj⟩)).2 (h i (by omega) ⟨j, hj⟩)
      have e : ∀ v : Row, rg v j = (v ⟨j, hj⟩ : ℕ) := fun v => rg_fin v ⟨j, hj⟩
      rw [e, e, e]
      exact this

/-- A pointwise nonincreasing chain of valid rows. -/
def Chain {m : ℕ} (g : Fin m → Row) : Prop :=
  (∀ i, HOK (g i)) ∧ ∀ (i : ℕ) (h : i + 1 < m), rle (g ⟨i + 1, h⟩) (g ⟨i, by omega⟩)

noncomputable instance decChain {m : ℕ} (g : Fin m → Row) : Decidable (Chain g) :=
  Classical.dec _

theorem avoids_cons {m : ℕ} (p : Row) (g : Fin m → Row) :
    avoids (Fin.cons p g : Fin (m + 1) → Row) = true ↔ HOK p ∧ Chain g := by
  rw [avoids_iff, Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [and_assoc]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h i hi
    have := h i (by omega)
    exact this
  · intro h i hi
    exact h i (by omega)

theorem chain_cons {m : ℕ} (q : Row) (g : Fin (m + 1) → Row) :
    Chain (Fin.cons q g : Fin (m + 2) → Row) ↔ HOK q ∧ rle (g 0) q ∧ Chain g := by
  constructor
  · rintro ⟨hr, hc⟩
    have h0 := hc 0 (by omega)
    refine ⟨hr 0, h0, fun i => hr i.succ, fun i hi => hc (i + 1) (by omega)⟩
  · rintro ⟨hq, hgq, hr, hc⟩
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact hq
      · exact hr j
    · cases i with
      | zero => exact hgq
      | succ i => exact hc i (by omega)

theorem chain_one (g : Fin 1 → Row) : Chain g ↔ HOK (g 0) := by
  constructor
  · exact fun h => h.1 0
  · intro h
    refine ⟨fun i => ?_, fun i hi => absurd hi (by omega)⟩
    rw [Subsingleton.elim i 0]
    exact h

/-- Number of chains of `k + 1` rows starting with `q`. -/
noncomputable def E (k : ℕ) (q : Row) : ℕ :=
  ∑ g : Fin k → Row, if Chain (Fin.cons q g : Fin (k + 1) → Row) then 1 else 0

theorem E_invalid (k : ℕ) (q : Row) (hq : ¬ HOK q) : E k q = 0 := by
  unfold E
  exact Finset.sum_eq_zero fun g _ => if_neg fun h => hq (h.1 0)

theorem E_zero (q : Row) : E 0 q = if HOK q then 1 else 0 := by
  unfold E
  rw [Fintype.sum_unique]
  exact if_congr (chain_one _) rfl rfl

theorem E_succ (k : ℕ) (q : Row) :
    E (k + 1) q = if HOK q then ∑ q' : Row, (if rle q' q then E k q' else 0) else 0 := by
  unfold E
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun x => if Chain (Fin.cons q (Fin.cons x.1 x.2) : Fin (k + 2) → Row) then 1 else 0)
    (fun g => by simp), Fintype.sum_prod_type]
  split_ifs with hq
  · refine Finset.sum_congr rfl fun q' _ => ?_
    split_ifs with hq'
    · refine Finset.sum_congr rfl fun g _ => if_congr ?_ rfl rfl
      rw [chain_cons]
      simp only [Fin.cons_zero]
      exact ⟨fun h => h.2.2, fun h => ⟨hq, hq', h⟩⟩
    · refine Finset.sum_eq_zero fun g _ => if_neg ?_
      rw [chain_cons]
      simp only [Fin.cons_zero]
      exact fun h => hq' h.2.1
  · refine Finset.sum_eq_zero fun q' _ => Finset.sum_eq_zero fun g _ => if_neg ?_
    rw [chain_cons]
    exact fun h => hq h.1

theorem HOK_count : (∑ q : Row, if HOK q then 1 else 0) = 14 := by
  decide

theorem a_eq (m : ℕ) : a (m + 1) = 14 * ((∑ g : Fin m → Row, if Chain g then 1 else 0 : ℕ) : ℤ) := by
  unfold a
  rw [Finset.card_filter, Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun x => if avoids (Fin.cons x.1 x.2 : Fin (m + 1) → Row) = true then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  have h2 : ∀ (p : Row) (g : Fin m → Row),
      (if avoids (Fin.cons p g : Fin (m + 1) → Row) = true then 1 else 0) =
        (if HOK p then 1 else 0) * (if Chain g then 1 else 0) := by
    intro p g
    rw [ite_zero_mul_ite_zero, one_mul]
    exact if_congr (avoids_cons p g) rfl rfl
  simp only [h2, ← Finset.sum_mul_sum, HOK_count]
  push_cast
  rfl

theorem chain_zero : (∑ g : Fin 0 → Row, if Chain g then 1 else 0) = 1 := by
  rw [Fintype.sum_unique]
  rw [if_pos]
  exact ⟨fun i => i.elim0, fun i hi => absurd hi (by omega)⟩

theorem chain_succ (k : ℕ) : (∑ g : Fin (k + 1) → Row, if Chain g then 1 else 0) = ∑ q : Row, E k q := by
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun x => if Chain (Fin.cons x.1 x.2 : Fin (k + 1) → Row) then 1 else 0) (fun A => by simp),
    Fintype.sum_prod_type]
  rfl

/-- The fourteen valid rows. -/
def e : Fin 14 → Row :=
  ![![0, 0, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 0, 1], ![0, 1, 1, 1, 0], ![0, 1, 1, 1, 1],
    ![1, 0, 0, 0, 0], ![1, 0, 1, 1, 0], ![1, 0, 1, 1, 1], ![1, 1, 0, 0, 0], ![1, 1, 0, 1, 1],
    ![1, 1, 1, 0, 0], ![1, 1, 1, 0, 1], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 1]]

theorem e_injective : Function.Injective e := by
  decide

/-- `e` as an embedding. -/
def eEmb : Fin 14 ↪ Row := ⟨e, e_injective⟩

theorem filter_HOK : Finset.univ.filter HOK = Finset.univ.map eEmb := by
  decide

theorem sum_rows {M : Type*} [AddCommMonoid M] (f : Row → M) (hf : ∀ q, ¬ HOK q → f q = 0) :
    ∑ q, f q = ∑ i, f (e i) := by
  rw [← Finset.sum_filter_of_ne (p := HOK) (fun q _ hq => by_contra fun h => hq (hf q h)),
    filter_HOK, Finset.sum_map]
  rfl

theorem HOK_e : ∀ i, HOK (e i) := by
  decide

/-- Rows below each valid row. -/
def bl : Fin 14 → Finset (Fin 14) :=
  ![{0}, {0, 1}, {0, 1, 2}, {0, 1, 3}, {0, 1, 2, 3, 4}, {0, 5}, {0, 5, 6}, {0, 5, 6, 7},
    {0, 5, 8}, {0, 5, 8, 9}, {0, 1, 5, 8, 10}, {0, 1, 2, 5, 8, 10, 11},
    {0, 1, 3, 5, 6, 8, 10, 12}, Finset.univ]

theorem rle_e : ∀ i j : Fin 14, rle (e j) (e i) ↔ j ∈ bl i := by
  decide

theorem E_succ_e (k : ℕ) (i : Fin 14) : E (k + 1) (e i) = ∑ j ∈ bl i, E k (e j) := by
  rw [E_succ, if_pos (HOK_e i), sum_rows _ (fun q hq => by simp [E_invalid k q hq]),
    ← Finset.sum_filter]
  congr 1
  ext j
  simp [rle_e]

theorem E_zero_e (i : Fin 14) : E 0 (e i) = 1 := by
  rw [E_zero, if_pos (HOK_e i)]

/-- Closed forms of the chain counts. -/
def P (k : ℚ) : Fin 14 → ℚ :=
  ![1, k + 1, (k + 1) * (k + 2) / 2, (k + 1) * (k + 2) / 2, (k + 1) * (k + 2) * (2 * k + 3) / 6,
    k + 1, (k + 1) * (k + 2) / 2, (k + 1) * (k + 2) * (k + 3) / 6, (k + 1) * (k + 2) / 2,
    (k + 1) * (k + 2) * (k + 3) / 6, (k + 1) * (k ^ 2 + 8 * k + 6) / 6,
    (k + 1) * (k + 2) * (k ^ 2 + 15 * k + 12) / 24, (k + 1) * (k + 2) * (k ^ 2 + 19 * k + 12) / 24,
    (k + 1) * (k + 2) * (k ^ 3 + 32 * k ^ 2 + 77 * k + 30) / 60]

theorem closed (k : ℕ) : ∀ i, (E k (e i) : ℚ) = P k i := by
  induction k with
  | zero =>
    intro i
    rw [E_zero_e]
    fin_cases i <;> simp [P] <;> norm_num
  | succ k ih =>
    intro i
    rw [E_succ_e]
    push_cast
    fin_cases i <;> simp [bl, Fin.sum_univ_succ, ih, P] <;> ring

theorem a_one : a 1 = 14 := by
  rw [a_eq, chain_zero]
  norm_num

theorem a_closed (k : ℕ) :
    (a (k + 2) : ℚ) = 7 * ((k : ℚ) + 2) * ((k : ℚ) + 3) *
      (((k : ℚ) + 2) ^ 3 + 29 * ((k : ℚ) + 2) ^ 2 + 16 * ((k : ℚ) + 2) - 16) / 30 := by
  rw [a_eq, chain_succ, sum_rows _ (fun q hq => E_invalid k q hq)]
  push_cast
  simp only [closed k, Fin.sum_univ_succ, P]
  simp
  ring

theorem closedQ (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = 7 * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) ^ 3 + 29 * (n : ℚ) ^ 2 + 16 * (n : ℚ) - 16) / 30 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [a_one]
    norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [a_closed k]
    push_cast
    ring

theorem recurrence (n : ℕ) (hn : 7 ≤ n) :
    (a n : ℚ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
      6 * a (n - 5) - a (n - 6) := by
  rw [closedQ n (by omega), closedQ (n - 1) (by omega), closedQ (n - 2) (by omega),
    closedQ (n - 3) (by omega), closedQ (n - 4) (by omega), closedQ (n - 5) (by omega),
    closedQ (n - 6) (by omega)]
  push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
    show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega]
  ring

theorem a_val (n : ℕ) (hn : 1 ≤ n) (v : ℚ)
    (hv : 7 * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) ^ 3 + 29 * (n : ℚ) ^ 2 + 16 * (n : ℚ) - 16) / 30 = v) :
    (a n : ℚ) = v := by
  rw [closedQ n hn, hv]

theorem a_vals : (a 1 : ℚ) = 14 ∧ (a 2 : ℚ) = 196 ∧ (a 3 : ℚ) = 896 ∧ (a 4 : ℚ) = 2688 ∧
    (a 5 : ℚ) = 6398 ∧ (a 6 : ℚ) = 13132 :=
  ⟨a_val 1 (by norm_num) 14 (by norm_num), a_val 2 (by norm_num) 196 (by norm_num),
    a_val 3 (by norm_num) 896 (by norm_num), a_val 4 (by norm_num) 2688 (by norm_num),
    a_val 5 (by norm_num) 6398 (by norm_num), a_val 6 (by norm_num) 13132 (by norm_num)⟩

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 6 : PowerSeries ℚ) =
      14 * X * (1 + 8 * X - 5 * X ^ 2 - 2 * X ^ 3) := by
  set F : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - X) ^ 6 =
      PowerSeries.mk F * X ^ 0 - C 6 * (PowerSeries.mk F * X ^ 1) +
        C 15 * (PowerSeries.mk F * X ^ 2) - C 20 * (PowerSeries.mk F * X ^ 3) +
        C 15 * (PowerSeries.mk F * X ^ 4) - C 6 * (PowerSeries.mk F * X ^ 5) +
        PowerSeries.mk F * X ^ 6 := by
    simp only [map_ofNat]
    ring
  have hrhs : (14 : ℚ⟦X⟧) * X * (1 + 8 * X - 5 * X ^ 2 - 2 * X ^ 3) =
      C 14 * X ^ 1 + C 112 * X ^ 2 - C 70 * X ^ 3 - C 28 * X ^ 4 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := a_vals
  by_cases hk : k < 7
  · interval_cases k <;> simp [hF, h1, h2, h3, h4, h5, h6] <;> norm_num
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
      show ¬ (j + 7 = 4) by omega,
      show ¬ (j + 7 < 1) by omega, show ¬ (j + 6 < 1) by omega, show ¬ (j + 5 < 1) by omega,
      show ¬ (j + 4 < 1) by omega, show ¬ (j + 3 < 1) by omega, show ¬ (j + 2 < 1) by omega,
      show ¬ (j + 1 < 1) by omega, if_true, if_false, hF, zero_le]
    linear_combination hr
end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a207065.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
