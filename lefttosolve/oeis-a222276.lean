import OMAStatements.S_oeis_a222276

/-!
Proof of Barker's conjectures for OEIS A222276 (n X 3 arrays, entries 0..5, no entry increasing
mod 6 by 5 rightwards or downwards, upper left entry 0).

Cutting off the first row gives a(m + 1) = sum over first rows r with r.1 = 0 of G m r, where
G m r counts the ways to continue the row r by m further rows (a transfer recursion). A finite
check shows that for every admissible row r the two-step count satisfies
G 2 r = 92 G 1 r - 335 G 0 r, and by induction G (m + 2) = 92 G (m + 1) - 335 G m pointwise.
Hence a(m + 3) = 92 a(m + 2) - 335 a(m + 1) with a(1) = 25, a(2) = 2205, which gives both the
generating function and, since 46 +- sqrt 1781 are the roots of t^2 = 92 t - 335, the closed form.
-/

namespace OMA.Helpers

open OMA.S_oeis_a222276 Finset

/-- The chain conditions of an array given by its rows. -/
def chainA222276 {m : ℕ} (f : Fin m → Fin 6 × Fin 6 × Fin 6) : Prop :=
  (∀ i, hrow (f i)) ∧ (∀ i j : Fin m, j.val = i.val + 1 → ok (f i) (f j))

instance a222276_decChain {m : ℕ} : DecidablePred (@chainA222276 m) := fun f => by
  unfold chainA222276; infer_instance

theorem a222276_chain_cons {m : ℕ} (x : Fin 6 × Fin 6 × Fin 6)
    (B : Fin (m + 1) → Fin 6 × Fin 6 × Fin 6) :
    chainA222276 (Fin.cons x B : Fin (m + 2) → Fin 6 × Fin 6 × Fin 6) ↔
      hrow x ∧ ok x (B 0) ∧ chainA222276 B := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1 0, h2 0 1 rfl, fun i => by simpa using h1 i.succ, fun i j hij => ?_⟩
    have := h2 i.succ j.succ (by simp [hij])
    simpa using this
  · rintro ⟨hx, hxb, hB1, hB2⟩
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · cases i using Fin.cases with
      | zero => simpa using hx
      | succ i => simpa using hB1 i
    · cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => simp at hij
        | succ j =>
          have hj : j = 0 := by
            ext
            simp only [Fin.val_succ, Fin.val_zero] at hij
            simp only [Fin.val_zero]
            omega
          subst hj
          simpa using hxb
      | succ i =>
        cases j using Fin.cases with
        | zero => simp at hij
        | succ j =>
          simp only [Fin.cons_succ]
          exact hB2 i j (by simp only [Fin.val_succ] at hij; omega)

/-- The number of ways to extend a first row by `m` further rows. -/
def gA222276 : ℕ → Fin 6 × Fin 6 × Fin 6 → ℕ
  | 0, r => if hrow r then 1 else 0
  | m + 1, r => if hrow r then ∑ s, if ok r s then gA222276 m s else 0 else 0

theorem a222276_count (m : ℕ) (r : Fin 6 × Fin 6 × Fin 6) :
    (∑ B : Fin m → Fin 6 × Fin 6 × Fin 6,
      if chainA222276 (Fin.cons r B : Fin (m + 1) → Fin 6 × Fin 6 × Fin 6) then 1 else 0) = gA222276 m r := by
  induction m generalizing r with
  | zero =>
    rw [Fintype.sum_unique]
    rw [show gA222276 0 r = if hrow r then 1 else 0 from rfl]
    refine if_congr ⟨fun h => by simpa using h.1 0, fun h => ⟨fun i => ?_, fun i j hij => ?_⟩⟩
      rfl rfl
    · have hi : i = 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_zero]; omega)
      subst hi
      simpa using h
    · have := j.isLt
      have := i.isLt
      omega
  | succ k ih =>
    rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 6 × Fin 6 × Fin 6).symm _
      (fun p => if chainA222276 (Fin.cons r (Fin.cons p.1 p.2) : Fin (k + 2) → Fin 6 × Fin 6 × Fin 6)
        then 1 else 0) (fun B => by simp), Fintype.sum_prod_type]
    show _ = if hrow r then ∑ s, if ok r s then gA222276 k s else 0 else 0
    by_cases hr : hrow r
    · rw [if_pos hr]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases hs : ok r s
      · rw [if_pos hs, ← ih s]
        refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
        rw [a222276_chain_cons, Fin.cons_zero]
        exact ⟨fun h => h.2.2, fun h => ⟨hr, hs, h⟩⟩
      · rw [if_neg hs]
        refine Finset.sum_eq_zero fun B _ => if_neg ?_
        rw [a222276_chain_cons, Fin.cons_zero]
        exact fun h => hs h.2.1
    · rw [if_neg hr]
      refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun B _ => if_neg ?_
      rw [a222276_chain_cons]
      exact fun h => hr h.1

theorem a222276_a_eq (m : ℕ) : a (m + 1) = ∑ r, if r.1 = 0 then gA222276 m r else 0 := by
  unfold a
  rw [Finset.card_filter, Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 6 × Fin 6 × Fin 6).symm _
    (fun p => if chainA222276 (Fin.cons p.1 p.2 : Fin (m + 1) → Fin 6 × Fin 6 × Fin 6) ∧ p.1.1 = 0
      then 1 else 0) ?_, Fintype.sum_prod_type]
  · refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h0 : r.1 = 0
    · rw [if_pos h0, ← a222276_count]
      exact Finset.sum_congr rfl fun B _ => if_congr (and_iff_left h0) rfl rfl
    · rw [if_neg h0]
      exact Finset.sum_eq_zero fun B _ => if_neg fun h => h0 h.2
  · intro f
    simp only [Fin.consEquiv_symm_apply, Fin.cons_self_tail]
    refine if_congr ?_ rfl rfl
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3 0 rfl⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, h2, fun i hi => ?_⟩
      have : i = 0 := Fin.ext hi
      subst this
      exact h3

/-- The one-step counts, by the differences of consecutive entries of the row. -/
def tblA222276 : List ℕ :=
  [88, 88, 88, 88, 89, 0, 88, 88, 88, 89, 88, 0, 88, 88, 89, 88, 88, 0, 88, 89, 88, 88, 88, 0,
    89, 88, 88, 88, 88, 0, 0, 0, 0, 0, 0, 0]

def g1A222276 (s : Fin 6 × Fin 6 × Fin 6) : ℕ :=
  tblA222276.getD (6 * ((s.2.1.val + 6 - s.1.val) % 6) + (s.2.2.val + 6 - s.2.1.val) % 6) 0

theorem a222276_G1_0 : ∀ y z : Fin 6, gA222276 1 (0, y, z) = g1A222276 (0, y, z) := by
  decide +kernel

theorem a222276_G1_1 : ∀ y z : Fin 6, gA222276 1 (1, y, z) = g1A222276 (1, y, z) := by
  decide +kernel

theorem a222276_G1_2 : ∀ y z : Fin 6, gA222276 1 (2, y, z) = g1A222276 (2, y, z) := by
  decide +kernel

theorem a222276_G1_3 : ∀ y z : Fin 6, gA222276 1 (3, y, z) = g1A222276 (3, y, z) := by
  decide +kernel

theorem a222276_G1_4 : ∀ y z : Fin 6, gA222276 1 (4, y, z) = g1A222276 (4, y, z) := by
  decide +kernel

theorem a222276_G1_5 : ∀ y z : Fin 6, gA222276 1 (5, y, z) = g1A222276 (5, y, z) := by
  decide +kernel

theorem a222276_G1 (s : Fin 6 × Fin 6 × Fin 6) : gA222276 1 s = g1A222276 s := by
  obtain ⟨c, y, z⟩ := s
  fin_cases c
  · exact a222276_G1_0 y z
  · exact a222276_G1_1 y z
  · exact a222276_G1_2 y z
  · exact a222276_G1_3 y z
  · exact a222276_G1_4 y z
  · exact a222276_G1_5 y z

theorem a222276_base_0 : ∀ y z : Fin 6, hrow (0, y, z) →
    (∑ s, if ok (0, y, z) s then g1A222276 s else 0) = 92 * g1A222276 (0, y, z) - 335 := by
  decide +kernel

theorem a222276_base_1 : ∀ y z : Fin 6, hrow (1, y, z) →
    (∑ s, if ok (1, y, z) s then g1A222276 s else 0) = 92 * g1A222276 (1, y, z) - 335 := by
  decide +kernel

theorem a222276_base_2 : ∀ y z : Fin 6, hrow (2, y, z) →
    (∑ s, if ok (2, y, z) s then g1A222276 s else 0) = 92 * g1A222276 (2, y, z) - 335 := by
  decide +kernel

theorem a222276_base_3 : ∀ y z : Fin 6, hrow (3, y, z) →
    (∑ s, if ok (3, y, z) s then g1A222276 s else 0) = 92 * g1A222276 (3, y, z) - 335 := by
  decide +kernel

theorem a222276_base_4 : ∀ y z : Fin 6, hrow (4, y, z) →
    (∑ s, if ok (4, y, z) s then g1A222276 s else 0) = 92 * g1A222276 (4, y, z) - 335 := by
  decide +kernel

theorem a222276_base_5 : ∀ y z : Fin 6, hrow (5, y, z) →
    (∑ s, if ok (5, y, z) s then g1A222276 s else 0) = 92 * g1A222276 (5, y, z) - 335 := by
  decide +kernel

theorem a222276_base_chk (r : Fin 6 × Fin 6 × Fin 6) (hr : hrow r) :
    (∑ s, if ok r s then g1A222276 s else 0) = 92 * g1A222276 r - 335 := by
  obtain ⟨c, y, z⟩ := r
  fin_cases c
  · exact a222276_base_0 y z hr
  · exact a222276_base_1 y z hr
  · exact a222276_base_2 y z hr
  · exact a222276_base_3 y z hr
  · exact a222276_base_4 y z hr
  · exact a222276_base_5 y z hr

theorem a222276_g1_ge : ∀ r, hrow r → 88 ≤ g1A222276 r := by decide +kernel

theorem a222276_G_invalid (m : ℕ) (r : Fin 6 × Fin 6 × Fin 6) (hr : ¬ hrow r) : gA222276 m r = 0 := by
  cases m with
  | zero => exact if_neg hr
  | succ k => exact if_neg hr

theorem a222276_G_rec (m : ℕ) (r : Fin 6 × Fin 6 × Fin 6) :
    (gA222276 (m + 2) r : ℤ) = 92 * gA222276 (m + 1) r - 335 * gA222276 m r := by
  induction m generalizing r with
  | zero =>
    by_cases hr : hrow r
    · have h2 : gA222276 2 r = ∑ s, if ok r s then g1A222276 s else 0 := by
        show (if hrow r then ∑ s, if ok r s then gA222276 1 s else 0 else 0) = _
        rw [if_pos hr]
        exact Finset.sum_congr rfl fun s _ => by rw [a222276_G1]
      have hc := a222276_base_chk r hr
      have h1 : gA222276 1 r = g1A222276 r := a222276_G1 r
      have h0 : gA222276 0 r = 1 := if_pos hr
      have hge : 335 ≤ 92 * g1A222276 r := by
        have := a222276_g1_ge r hr
        omega
      rw [h2, hc, h1, h0]
      push_cast [hge]
      ring
    · rw [a222276_G_invalid _ r hr, a222276_G_invalid _ r hr, a222276_G_invalid _ r hr]
      simp
  | succ k ih =>
    by_cases hr : hrow r
    · have e : ∀ n, (gA222276 (n + 1) r : ℤ) = ∑ s, if ok r s then (gA222276 n s : ℤ) else 0 := by
        intro n
        show ((if hrow r then ∑ s, if ok r s then gA222276 n s else 0 else 0 : ℕ) : ℤ) = _
        rw [if_pos hr]
        push_cast
        refine Finset.sum_congr rfl fun s _ => ?_
        split_ifs <;> simp
      rw [e (k + 2), e (k + 1), e k, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      split_ifs
      · exact ih s
      · ring
    · rw [a222276_G_invalid _ r hr, a222276_G_invalid _ r hr, a222276_G_invalid _ r hr]
      simp

theorem a222276_a_rec (m : ℕ) :
    (a (m + 3) : ℤ) = 92 * a (m + 2) - 335 * a (m + 1) := by
  rw [show m + 3 = (m + 2) + 1 by ring, show m + 2 = (m + 1) + 1 by ring,
    a222276_a_eq, a222276_a_eq, a222276_a_eq]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs
  · exact a222276_G_rec m r
  · ring

theorem a222276_a_one : a 1 = 25 := by
  rw [a222276_a_eq]
  decide +kernel

theorem a222276_a_two : a 2 = 2205 := by
  rw [a222276_a_eq]
  have : ∀ r, gA222276 1 r = g1A222276 r := a222276_G1
  simp only [this]
  decide +kernel

/-- The closed form. -/
noncomputable def fA222276 (n : ℕ) : ℝ :=
  ((46 - Real.sqrt 1781) ^ n * (-801 + 19 * Real.sqrt 1781) +
    (46 + Real.sqrt 1781) ^ n * (801 + 19 * Real.sqrt 1781)) / (134 * Real.sqrt 1781)

theorem a222276_F_rec (n : ℕ) : fA222276 (n + 2) = 92 * fA222276 (n + 1) - 335 * fA222276 n := by
  have hs : Real.sqrt 1781 ^ 2 = 1781 := Real.sq_sqrt (by norm_num)
  unfold fA222276
  have hn : ((46 - Real.sqrt 1781) ^ (n + 2) * (-801 + 19 * Real.sqrt 1781) +
      (46 + Real.sqrt 1781) ^ (n + 2) * (801 + 19 * Real.sqrt 1781)) =
      92 * ((46 - Real.sqrt 1781) ^ (n + 1) * (-801 + 19 * Real.sqrt 1781) +
      (46 + Real.sqrt 1781) ^ (n + 1) * (801 + 19 * Real.sqrt 1781)) -
      335 * ((46 - Real.sqrt 1781) ^ n * (-801 + 19 * Real.sqrt 1781) +
      (46 + Real.sqrt 1781) ^ n * (801 + 19 * Real.sqrt 1781)) := by
    simp only [pow_succ]
    linear_combination ((46 - Real.sqrt 1781) ^ n * (-801 + 19 * Real.sqrt 1781) +
      (46 + Real.sqrt 1781) ^ n * (801 + 19 * Real.sqrt 1781)) * hs
  rw [hn]
  ring

theorem a222276_F_one : fA222276 1 = 25 := by
  have hs : Real.sqrt 1781 ^ 2 = 1781 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 1781 := Real.sqrt_pos.mpr (by norm_num)
  unfold fA222276
  rw [div_eq_iff (by positivity)]
  ring_nf

theorem a222276_F_two : fA222276 2 = 2205 := by
  have hs : Real.sqrt 1781 ^ 2 = 1781 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 1781 := Real.sqrt_pos.mpr (by norm_num)
  unfold fA222276
  rw [div_eq_iff (by positivity)]
  linear_combination (38 * Real.sqrt 1781) * hs

theorem a222276_closed (m : ℕ) : (a (m + 1) : ℝ) = fA222276 (m + 1) ∧ (a (m + 2) : ℝ) = fA222276 (m + 2) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [a222276_a_one, a222276_F_one]; norm_num
    · rw [a222276_a_two, a222276_F_two]; norm_num
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have hr := a222276_a_rec k
    have hr' : (a (k + 3) : ℝ) = 92 * a (k + 2) - 335 * a (k + 1) := by exact_mod_cast hr
    show (a (k + 3) : ℝ) = fA222276 (k + 1 + 2)
    rw [hr', ih.1, ih.2, a222276_F_rec (k + 1)]

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a222276.main := by
  refine ⟨?_, ?_⟩
  · set f : PowerSeries ℚ := PowerSeries.mk
      (fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a222276.a n : ℚ)) with hf
    have e1 : f * (1 - 92 * PowerSeries.X + 335 * PowerSeries.X ^ 2)
        = f - PowerSeries.C (92 : ℚ) * (f * PowerSeries.X ^ 1)
          + PowerSeries.C (335 : ℚ) * (f * PowerSeries.X ^ 2) := by
      simp only [map_ofNat]; ring
    have e2 : (5 * PowerSeries.X * (5 - 19 * PowerSeries.X) : PowerSeries ℚ)
        = PowerSeries.C (25 : ℚ) * PowerSeries.X ^ 1
          - PowerSeries.C (95 : ℚ) * PowerSeries.X ^ 2 := by
      simp only [map_ofNat]; ring
    rw [e1, e2]
    ext k
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', hf,
      PowerSeries.coeff_mk, PowerSeries.coeff_C]
    rcases k with _ | _ | _ | k
    · simp
    · simp [OMA.Helpers.a222276_a_one]
    · simp [OMA.Helpers.a222276_a_one, OMA.Helpers.a222276_a_two]; norm_num
    · have h := OMA.Helpers.a222276_a_rec k
      have hq : (OMA.S_oeis_a222276.a (k + 3) : ℚ) =
          92 * OMA.S_oeis_a222276.a (k + 2) - 335 * OMA.S_oeis_a222276.a (k + 1) := by
        exact_mod_cast h
      simp only [show k + 1 + 1 + 1 = k + 3 by ring, show 1 ≤ k + 3 by omega,
        show 2 ≤ k + 3 by omega, if_true, show k + 3 - 1 = k + 2 by omega,
        show k + 3 - 2 = k + 1 by omega, show k + 3 ≠ 0 by omega, show k + 2 ≠ 0 by omega,
        show k + 1 ≠ 0 by omega, if_false, hq]
      ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact (OMA.Helpers.a222276_closed m).1
