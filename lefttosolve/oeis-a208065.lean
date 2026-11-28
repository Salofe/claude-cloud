import OMAStatements.S_oeis_a208065
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a208065 Finset

abbrev Row := Fin 4 → Fin 2

def getR (r : Row) (j : ℕ) : ℕ := if h : j < 4 then (r ⟨j, h⟩ : ℕ) else 0

theorem get_eq {n : ℕ} (x : Fin n → Fin 4 → Fin 2) (i j : ℕ) :
    S_oeis_a208065.get x i j = if h : i < n then getR (x ⟨i, h⟩) j else 0 := by
  unfold S_oeis_a208065.get getR
  by_cases hi : i < n <;> by_cases hj : j < 4 <;> simp [hi, hj]

def HOK (r : Row) : Prop :=
  ∀ j < 4 - 2, (getR r j, getR r (j + 1), getR r (j + 2)) ≠ (0, 0, 0) ∧
    (getR r j, getR r (j + 1), getR r (j + 2)) ≠ (1, 1, 1)

def VOK (r s t : Row) : Prop :=
  ∀ j < 4, (getR r j, getR s j, getR t j) ≠ (0, 0, 1) ∧ (getR r j, getR s j, getR t j) ≠ (0, 1, 1)

instance decHOK (r : Row) : Decidable (HOK r) := by
  unfold HOK
  infer_instance

instance decVOK (r s t : Row) : Decidable (VOK r s t) := by
  unfold VOK
  infer_instance

def Chain {m : ℕ} (A : Fin m → Row) : Prop :=
  (∀ (i : ℕ) (hi : i < m), HOK (A ⟨i, hi⟩)) ∧
  (∀ (i : ℕ) (hi : i + 2 < m), VOK (A ⟨i, by omega⟩) (A ⟨i + 1, by omega⟩) (A ⟨i + 2, hi⟩))

theorem avoids_iff {m : ℕ} (x : Fin m → Row) : avoids x = true ↔ Chain x := by
  unfold avoids Chain
  rw [decide_eq_true_iff]
  simp only [get_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_⟩
    · have := h1 i hi j hj
      simp only [dif_pos hi] at this
      exact this
    · have := h2 i (by omega) j hj
      simp only [dif_pos (show i < m by omega), dif_pos (show i + 1 < m by omega),
        dif_pos hi] at this
      exact this
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_⟩
    · simp only [dif_pos hi]
      exact h1 i hi j hj
    · simp only [dif_pos (show i < m by omega), dif_pos (show i + 1 < m by omega),
        dif_pos (show i + 2 < m by omega)]
      exact h2 i (by omega) j hj

theorem chain_cons3 {k : ℕ} (r : Row) (B : Fin (k + 2) → Row) :
    Chain (Fin.cons r B : Fin (k + 3) → Row) ↔
      HOK r ∧ VOK r (B ⟨0, by omega⟩) (B ⟨1, by omega⟩) ∧ Chain B := by
  constructor
  · rintro ⟨h1, h2⟩
    have a1 := h1 0 (by omega)
    have a2 := h2 0 (by omega)
    exact ⟨a1, a2, fun i hi => h1 (i + 1) (by omega), fun i hi => h2 (i + 1) (by omega)⟩
  · rintro ⟨hr, hv, hB1, hB2⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · cases i with
      | zero => exact hr
      | succ i => exact hB1 i (by omega)
    · cases i with
      | zero => exact hv
      | succ i => exact hB2 i (by omega)

theorem chain_two (r s : Row) (A : Fin 0 → Row) :
    Chain (Fin.cons r (Fin.cons s A) : Fin 2 → Row) ↔ HOK r ∧ HOK s := by
  constructor
  · rintro ⟨h1, _⟩
    have a1 := h1 0 (by omega)
    have a2 := h1 1 (by omega)
    exact ⟨a1, a2⟩
  · rintro ⟨hr, hs⟩
    refine ⟨fun i hi => ?_, fun i hi => absurd hi (by omega)⟩
    match i, hi with
    | 0, _ => exact hr
    | 1, _ => exact hs

/-- Ways to continue the first two rows `r`, `s` by `m` more rows into a `Chain`. -/
noncomputable def N (m : ℕ) (r s : Row) : ℕ := by
  classical
  exact ∑ A : Fin m → Row, if Chain (Fin.cons r (Fin.cons s A) : Fin (m + 2) → Row) then 1 else 0

theorem N_zero (r s : Row) : N 0 r s = if HOK r ∧ HOK s then 1 else 0 := by
  classical
  unfold N
  rw [Fintype.sum_unique]
  exact if_congr (chain_two r s _) rfl rfl

theorem N_succ (m : ℕ) (r s : Row) :
    N (m + 1) r s = ∑ t : Row, if HOK r ∧ VOK r s t then N m s t else 0 := by
  classical
  unfold N
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if Chain (Fin.cons r (Fin.cons s (Fin.cons p.1 p.2)) : Fin (m + 3) → Row)
      then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hc : HOK r ∧ VOK r s t
  · rw [if_pos hc]
    refine Finset.sum_congr rfl fun A _ => if_congr ?_ rfl rfl
    exact (chain_cons3 (k := m) r (Fin.cons s (Fin.cons t A))).trans
      ⟨fun h => h.2.2, fun h => ⟨hc.1, hc.2, h⟩⟩
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun A _ => if_neg ?_
    exact fun h => hc ⟨((chain_cons3 (k := m) r (Fin.cons s (Fin.cons t A))).1 h).1,
      ((chain_cons3 (k := m) r (Fin.cons s (Fin.cons t A))).1 h).2.1⟩

theorem a_succ2 (m : ℕ) : a (m + 2) = ∑ r : Row, ∑ s : Row, (N m r s : ℤ) := by
  classical
  have h1 : (Finset.univ.filter (fun x : Fin (m + 2) → Fin 4 → Fin 2 => avoids x)).card =
      ∑ A : Fin (m + 2) → Row, if Chain A then 1 else 0 := by
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun g _ => if_congr (avoids_iff g) rfl rfl
  have h2 : (∑ A : Fin (m + 2) → Row, if Chain A then 1 else 0) =
      ∑ r : Row, ∑ s : Row, N m r s := by
    rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
      (fun p => if Chain (Fin.cons p.1 p.2 : Fin (m + 2) → Row) then 1 else 0)
      (fun A => by simp), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
      (fun p => if Chain (Fin.cons r (Fin.cons p.1 p.2) : Fin (m + 2) → Row) then 1 else 0)
      (fun A => by simp), Fintype.sum_prod_type]
    rfl
  rw [a, h1, h2]
  push_cast
  rfl

/-- The row with code `u`: the entry of column `j` is bit `j` of `u`. -/
def row (u : Fin 16) : Row := fun j => if Nat.testBit u.val j.val then 1 else 0

theorem row_injective : Function.Injective row := by
  decide +kernel

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

def hok (u : Fin 16) : Bool := 2 ≤ u.val && u.val ≤ 13 && u.val != 7 && u.val != 8

def le (w u : Fin 16) : Bool := w.val &&& u.val == w.val

theorem hok_iff : ∀ u : Fin 16, HOK (row u) ↔ hok u = true := by
  decide +kernel

theorem vok_iff : ∀ u v w : Fin 16, VOK (row u) (row v) (row w) ↔ le w u = true := by
  decide +kernel

/-- The transfer recursion on codes: `G m u v` continues the rows `u`, `v` by `m` rows. -/
def G : ℕ → Fin 16 → Fin 16 → ℕ
  | 0, u, v => if hok u && hok v then 1 else 0
  | m + 1, u, v => ∑ w : Fin 16, if hok u && le w u then G m v w else 0

theorem N_eq_G (m : ℕ) : ∀ u v : Fin 16, N m (row u) (row v) = G m u v := by
  induction m with
  | zero =>
    intro u v
    rw [N_zero]
    simp only [G, hok_iff, Bool.and_eq_true]
  | succ m ih =>
    intro u v
    rw [N_succ, ← row_bijective.sum_comp]
    simp only [G]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ih v w]
    exact if_congr (by rw [hok_iff, vok_iff, Bool.and_eq_true]) rfl rfl

/-- Chains `u ⊇ t₁ ⊇ ... ⊇ t_k` of allowed rows below the code `u`. -/
def D : ℕ → Fin 16 → ℕ
  | 0, _ => 1
  | k + 1, u => ∑ w : Fin 16, if hok w && le w u then D k w else 0

theorem G_eq (m : ℕ) : ∀ u v : Fin 16,
    G m u v = (if hok u && hok v then 1 else 0) * D ((m + 1) / 2) u * D (m / 2) v := by
  induction m with
  | zero => intro u v; simp [G, D]
  | succ m ih =>
    intro u v
    rw [show (m + 1 + 1) / 2 = m / 2 + 1 by omega, show (m + 1) / 2 = (m + 1) / 2 from rfl]
    simp only [G, D, ih]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun w _ => ?_
    cases h1 : hok u <;> cases h2 : hok v <;> cases h3 : hok w <;> cases h4 : le w u <;>
      simp [mul_comm]

def e2 (u : Fin 16) : ℤ := if u.val = 11 ∨ u.val = 13 then 2 else 0

def e1 (u : Fin 16) : ℤ :=
  if u.val = 11 ∨ u.val = 13 then 6 else if u.val = 6 then 4
  else if u.val = 3 ∨ u.val = 5 ∨ u.val = 10 ∨ u.val = 12 then 2 else 0

theorem step_facts : ∀ u : Fin 16, hok u = true →
    (∑ w : Fin 16, if hok w && le w u then e2 w else 0) = e2 u ∧
    (∑ w : Fin 16, if hok w && le w u then e1 w else 0) = 2 * e2 u + e1 u ∧
    (∑ w : Fin 16, if hok w && le w u then (2 : ℤ) else 0) = e2 u + e1 u + 2 := by
  decide +kernel

theorem D_closed (k : ℕ) : ∀ u : Fin 16, hok u = true →
    2 * (D k u : ℤ) = e2 u * (k : ℤ) ^ 2 + e1 u * k + 2 := by
  induction k with
  | zero => intro u _; simp [D]
  | succ k ih =>
    intro u hu
    have hs : 2 * (D (k + 1) u : ℤ) =
        ∑ w : Fin 16, if hok w && le w u then e2 w * (k : ℤ) ^ 2 + e1 w * k + 2 else 0 := by
      rw [D]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      cases h : hok w <;> cases h' : le w u <;> simp [h, ih w]
    have hP : ∀ w : Fin 16, (if hok w && le w u then e2 w * (k : ℤ) ^ 2 + e1 w * k + 2 else 0) =
        (if hok w && le w u then e2 w else 0) * (k : ℤ) ^ 2 +
          (if hok w && le w u then e1 w else 0) * k + (if hok w && le w u then (2 : ℤ) else 0) := by
      intro w
      split_ifs <;> simp
    rw [hs]
    simp only [hP, Finset.sum_add_distrib, ← Finset.sum_mul]
    obtain ⟨h1, h2, h3⟩ := step_facts u hu
    rw [h1, h2, h3]
    push_cast
    ring

theorem sum_facts : (∑ u : Fin 16, if hok u then e2 u else 0) = 4 ∧
    (∑ u : Fin 16, if hok u then e1 u else 0) = 24 ∧
    (∑ u : Fin 16, if hok u then (2 : ℤ) else 0) = 20 := by
  decide +kernel

theorem S_closed (k : ℕ) :
    (∑ u : Fin 16, ((if hok u then 1 else 0) * D k u : ℤ)) = 2 * (k : ℤ) ^ 2 + 12 * k + 10 := by
  have h2 : 2 * (∑ u : Fin 16, ((if hok u then 1 else 0) * D k u : ℤ)) =
      ∑ u : Fin 16, ((if hok u then e2 u else 0) * (k : ℤ) ^ 2 +
        (if hok u then e1 u else 0) * k + (if hok u then (2 : ℤ) else 0)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    cases h : hok u
    · simp
    · simp only [if_true]
      linarith [D_closed k u h]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul] at h2
  obtain ⟨s1, s2, s3⟩ := sum_facts
  rw [s1, s2, s3] at h2
  linarith

theorem a_closed (m : ℕ) : a (m + 2) =
    (2 * (((m + 1) / 2 : ℕ) : ℤ) ^ 2 + 12 * ((m + 1) / 2 : ℕ) + 10) *
      (2 * ((m / 2 : ℕ) : ℤ) ^ 2 + 12 * (m / 2 : ℕ) + 10) := by
  rw [a_succ2, ← S_closed, ← S_closed, Finset.sum_mul_sum]
  rw [← row_bijective.sum_comp]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← row_bijective.sum_comp]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [N_eq_G, G_eq]
  cases h1 : hok u <;> cases h2 : hok v <;> simp [mul_comm]

theorem a_one : a 1 = 10 := by
  decide +kernel

theorem aq (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) =
    ((n : ℚ) ^ 2 * ((n : ℚ) + 8) ^ 2 -
      (1 - (-1) ^ n) / 2 * ((n : ℚ) ^ 2 + ((n : ℚ) + 8) ^ 2 - 1)) / 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [a_closed]
  rcases Nat.even_or_odd m with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [show (t + t + 1) / 2 = t by omega, show (t + t) / 2 = t by omega]
    have : ((-1 : ℚ)) ^ (t + t + 2) = 1 := by
      rw [show t + t + 2 = 2 * (t + 1) by ring, pow_mul]; norm_num
    rw [this]
    push_cast
    ring
  · rw [show (2 * t + 1 + 1) / 2 = t + 1 by omega, show (2 * t + 1) / 2 = t by omega]
    have : ((-1 : ℚ)) ^ (2 * t + 1 + 2) = -1 := by
      rw [show 2 * t + 1 + 2 = 2 * (t + 1) + 1 by ring, pow_succ, pow_mul]; norm_num
    rw [this]
    push_cast
    ring

open PowerSeries in
theorem gen_fun : PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) *
    ((1 - X) ^ 5 * (1 + X) ^ 3 : PowerSeries ℚ) = 2 * X * (5 + 40 * X + 10 * X ^ 2 - 22 * X ^ 3 -
      12 * X ^ 4 - 12 * X ^ 5 + 10 * X ^ 6 + 10 * X ^ 7 - 5 * X ^ 8) := by
  set f := PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) with hf
  have key : f * ((1 - X) ^ 5 * (1 + X) ^ 3 : PowerSeries ℚ) =
      C 1 * (f * X ^ 0) - C 2 * (f * X ^ 1) - C 2 * (f * X ^ 2) + C 6 * (f * X ^ 3) -
        C 6 * (f * X ^ 5) + C 2 * (f * X ^ 6) + C 2 * (f * X ^ 7) - C 1 * (f * X ^ 8) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (2 * X * (5 + 40 * X + 10 * X ^ 2 - 22 * X ^ 3 - 12 * X ^ 4 - 12 * X ^ 5 +
      10 * X ^ 6 + 10 * X ^ 7 - 5 * X ^ 8) : PowerSeries ℚ) =
      C 10 * X ^ 1 + C 80 * X ^ 2 + C 20 * X ^ 3 - C 44 * X ^ 4 - C 24 * X ^ 5 -
        C 24 * X ^ 6 + C 20 * X ^ 7 + C 20 * X ^ 8 - C 10 * X ^ 9 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', hf, coeff_mk]
  by_cases hk : k < 10
  · have v1 := a_one
    have q : ∀ n, 2 ≤ n → n < 10 → (a n : ℚ) = ((n : ℚ) ^ 2 * ((n : ℚ) + 8) ^ 2 -
        (1 - (-1) ^ n) / 2 * ((n : ℚ) ^ 2 + ((n : ℚ) + 8) ^ 2 - 1)) / 4 :=
      fun n hn _ => aq n hn
    interval_cases k <;> norm_num [v1, q]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 10 := ⟨k - 10, by omega⟩
    simp only [coeff_C]
    simp only [show j + 10 - 0 = j + 10 by omega, show j + 10 - 1 = j + 9 by omega, show j + 10 - 2 = j + 8 by omega, show j + 10 - 3 = j + 7 by omega, show j + 10 - 4 = j + 6 by omega, show j + 10 - 5 = j + 5 by omega, show j + 10 - 6 = j + 4 by omega, show j + 10 - 7 = j + 3 by omega, show j + 10 - 8 = j + 2 by omega, show j + 10 - 9 = j + 1 by omega]
    simp (disch := omega) only [if_pos, if_neg]
    rw [aq (j + 10) (by omega), aq (j + 9) (by omega), aq (j + 8) (by omega), aq (j + 7) (by omega),
      aq (j + 5) (by omega), aq (j + 4) (by omega), aq (j + 3) (by omega), aq (j + 2) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a208065.main := by
  refine ⟨OMA.Helpers.gen_fun, fun n hn he => ?_, fun n hn ho => ?_⟩
  · rw [OMA.Helpers.aq n hn, he.neg_one_pow]
    ring
  · rw [OMA.Helpers.aq n hn, ho.neg_one_pow]
    ring
