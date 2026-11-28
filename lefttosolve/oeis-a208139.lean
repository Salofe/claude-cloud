import OMAStatements.S_oeis_a208139

/-!
Proof of Hardin's formula, Barker's g.f. and recurrence, and Eldar's two sums for A208139
(n X 5 0..1 arrays avoiding 0 0 1 and 0 1 1 horizontally and 0 0 1 and 1 0 1 vertically).

Counting. A row avoids `0 0 1` and `0 1 1` iff `c j = 0 → c (j + 2) = 0`, so (c1, c3, c5) and
(c2, c4) are both of the form 1..10..0: 4 * 3 = 12 valid rows. A column avoids `0 0 1` and
`1 0 1` iff no `0` is directly above a `1` from the second row on. Hence an array with `n + 1`
rows is a valid first row followed by a chain of `n` valid rows, each entrywise below the
previous one. Counting chains below a valid row `r` by recursion on the first row gives
`e n r = C(p + n, n) * C(q + n, n)`, where `p` and `q` are the numbers of ones of `r` in the odd
and even columns (hockey-stick identity). So `a (n + 1) = 12 * C(n + 3, 3) * C(n + 2, 2)
= (n + 1)^2 (n + 2)^2 (n + 3)`, which is Hardin's polynomial; the recurrence and the g.f. follow
by comparing coefficients.

Sums. `1 / (m^2 (m + 1)^2 (m + 2)) = 1/2 / m^2 + 1 / (m + 1)^2 - 5/4 / m + 1 / (m + 1)
+ 1/4 / (m + 2)`. The square terms use `ζ(2) = π^2/6` (and `η(2) = π^2/12`, from the even and
odd terms of `ζ(2)`), the remaining terms telescope, and in the alternating case they reduce to
the alternating harmonic series, whose partial sums `H(2m) - H(m)` tend to `log 2` because
`H(n) - log n` converges.
-/

namespace OMA.Helpers

open OMA.S_oeis_a208139 Finset

abbrev R := Fin 5 → Fin 2

/-- A row avoids `0 ? 1`, i.e. `0 0 1` and `0 1 1`. -/
def RowOK (r : R) : Prop := (r 0 = 0 → r 2 = 0) ∧ (r 1 = 0 → r 3 = 0) ∧ (r 2 = 0 → r 4 = 0)

instance (r : R) : Decidable (RowOK r) := by unfold RowOK; infer_instance

/-- `s ≤ r` entrywise. -/
def Below (s r : R) : Prop := ∀ j, r j = 0 → s j = 0

instance (s r : R) : Decidable (Below s r) := by unfold Below; infer_instance

theorem fin2 (x : Fin 2) : x = 0 ∨ x = 1 := by fin_cases x <;> simp

theorem hasFactor_five (r : R) (x y z : Fin 2) :
    HasFactor r x y z ↔ (r 0 = x ∧ r 1 = y ∧ r 2 = z) ∨ (r 1 = x ∧ r 2 = y ∧ r 3 = z) ∨
      (r 2 = x ∧ r 3 = y ∧ r 4 = z) := by
  constructor
  · rintro ⟨k, hk, h⟩
    have : k < 3 := by omega
    interval_cases k
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact ⟨0, by norm_num, h⟩
    · exact ⟨1, by norm_num, h⟩
    · exact ⟨2, by norm_num, h⟩

theorem rowOK_iff (r : R) : (¬ HasFactor r 0 0 1 ∧ ¬ HasFactor r 0 1 1) ↔ RowOK r := by
  rw [hasFactor_five, hasFactor_five]
  revert r
  decide

theorem col_iff {m : ℕ} (c : Fin m → Fin 2) :
    (¬ HasFactor c 0 0 1 ∧ ¬ HasFactor c 1 0 1) ↔
      ∀ (k : ℕ) (h : k + 2 < m), c ⟨k + 1, by omega⟩ = 0 → c ⟨k + 2, h⟩ = 0 := by
  constructor
  · rintro ⟨h1, h2⟩ k hk hk1
    rcases fin2 (c ⟨k + 2, hk⟩) with h | h
    · exact h
    · rcases fin2 (c ⟨k, by omega⟩) with h' | h'
      · exact absurd ⟨k, hk, h', hk1, h⟩ h1
      · exact absurd ⟨k, hk, h', hk1, h⟩ h2
  · intro H
    constructor
    · rintro ⟨k, hk, _, h1, h2⟩
      have := H k hk h1
      rw [h2] at this
      exact absurd this (by decide)
    · rintro ⟨k, hk, _, h1, h2⟩
      have := H k hk h1
      rw [h2] at this
      exact absurd this (by decide)

/-- `B` lists `n` valid rows, each entrywise below the previous one, the first one below `r`. -/
def Chain (n : ℕ) (r : R) (B : Fin n → R) : Prop :=
  (∀ i, RowOK (B i)) ∧ (∀ i : Fin n, ∀ h : i.val + 1 < n, Below (B ⟨i.val + 1, h⟩) (B i)) ∧
    (∀ h : 0 < n, Below (B ⟨0, h⟩) r)

instance (n : ℕ) (r : R) (B : Fin n → R) : Decidable (Chain n r B) := by
  unfold Chain; infer_instance

theorem chain_cons {n : ℕ} (r s : R) (B : Fin n → R) :
    Chain (n + 1) r (Fin.cons s B) ↔ RowOK s ∧ Below s r ∧ Chain n s B := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1 0, h3 (Nat.succ_pos n), fun i => h1 i.succ, fun i hi => ?_, fun hn => ?_⟩
    · exact h2 i.succ (by simp; omega)
    · exact h2 0 (by simp; omega)
  · rintro ⟨hs, hsr, h1, h2, h3⟩
    refine ⟨fun i => ?_, fun i hi => ?_, fun _ => hsr⟩
    · cases i using Fin.cases with
      | zero => exact hs
      | succ i => exact h1 i
    · cases i using Fin.cases with
      | zero => exact h3 (by simp at hi; omega)
      | succ i => exact h2 i (by simp at hi; omega)


/-- The number of such chains of length `n` below `r`. -/
def e (n : ℕ) (r : R) : ℕ := ∑ B : Fin n → R, if Chain n r B then 1 else 0

theorem e_zero (r : R) : e 0 r = 1 := by
  simp [e, Chain]

theorem e_succ (n : ℕ) (r : R) :
    e (n + 1) r = ∑ s : R, if RowOK s ∧ Below s r then e n s else 0 := by
  unfold e
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => R).symm _
    (fun x => if Chain (n + 1) r (Fin.cons x.1 x.2) then 1 else 0) (fun B => by simp),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : RowOK s ∧ Below s r
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun B _ => ?_
    simp only [chain_cons, h, true_and]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun B _ => ?_
    rw [if_neg]
    rw [chain_cons]
    tauto

/-- Number of ones among the odd-numbered columns 1, 3, 5. -/
def p (s : R) : ℕ := (s 0 : ℕ) + (s 2 : ℕ) + (s 4 : ℕ)

/-- Number of ones among the even-numbered columns 2, 4. -/
def q (s : R) : ℕ := (s 1 : ℕ) + (s 3 : ℕ)

/-- The valid row with `i` ones in columns 1, 3, 5 and `j` ones in columns 2, 4. -/
def rowOf (i j : ℕ) : R :=
  ![if 0 < i then 1 else 0, if 0 < j then 1 else 0, if 1 < i then 1 else 0,
    if 1 < j then 1 else 0, if 2 < i then 1 else 0]

theorem L1 : ∀ s r : R, Below s r → p s ≤ p r ∧ q s ≤ q r := by decide

theorem L2 : ∀ r : R, RowOK r → ∀ i : Fin 4, ∀ j : Fin 3, (i : ℕ) ≤ p r → (j : ℕ) ≤ q r →
    RowOK (rowOf i j) ∧ Below (rowOf i j) r := by decide

theorem L3 : ∀ s : R, RowOK s → rowOf (p s) (q s) = s := by decide

theorem L4 : ∀ i : Fin 4, ∀ j : Fin 3, p (rowOf i j) = i ∧ q (rowOf i j) = j := by decide

theorem L5 : ∀ r : R, p r ≤ 3 ∧ q r ≤ 2 := by decide


theorem reindex (r : R) (hr : RowOK r) (G : ℕ → ℕ → ℕ) :
    ∑ s : R, (if RowOK s ∧ Below s r then G (p s) (q s) else 0) =
      ∑ i ∈ range (p r + 1), ∑ j ∈ range (q r + 1), G i j := by
  rw [← Finset.sum_filter, ← Finset.sum_product']
  apply Finset.sum_nbij' (fun s => (p s, q s)) (fun x => rowOf x.1 x.2)
  · intro s hs
    rw [Finset.mem_filter] at hs
    have := L1 s r hs.2.2
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  · rintro ⟨i, j⟩ hij
    simp only [Finset.mem_product, Finset.mem_range] at hij
    have h5 := L5 r
    have := L2 r hr ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp; omega) (by simp; omega)
    simpa using this
  · intro s hs
    rw [Finset.mem_filter] at hs
    exact L3 s hs.2.1
  · rintro ⟨i, j⟩ hij
    simp only [Finset.mem_product, Finset.mem_range] at hij
    have h5 := L5 r
    have := L4 ⟨i, by omega⟩ ⟨j, by omega⟩
    simp only at this ⊢
    rw [this.1, this.2]
  · intro s _
    rfl

/-- `F n k` counts the weakly decreasing sequences of length `n` with values in `{0, ..., k}`. -/
def F (n k : ℕ) : ℕ := (k + n).choose n

theorem F_sum (n k : ℕ) : ∑ i ∈ range (k + 1), F n i = F (n + 1) k := by
  unfold F
  rw [Nat.sum_range_add_choose, Nat.add_assoc]

theorem e_formula (n : ℕ) : ∀ s : R, RowOK s → e n s = F n (p s) * F n (q s) := by
  induction n with
  | zero => intro s _; simp [e_zero, F]
  | succ n ih =>
    intro r hr
    rw [e_succ]
    have : ∀ s : R, (if RowOK s ∧ Below s r then e n s else 0) =
        (if RowOK s ∧ Below s r then F n (p s) * F n (q s) else 0) := by
      intro s
      split_ifs with h
      · exact ih s h.1
      · rfl
    rw [Finset.sum_congr rfl (fun s _ => this s), reindex r hr (fun i j => F n i * F n j),
      ← Finset.sum_mul_sum, F_sum, F_sum]

/-- The row of ones. -/
def top : R := fun _ => 1

theorem valid_iff {n : ℕ} (A : Fin (n + 1) → R) :
    Valid A ↔ RowOK (A 0) ∧ Chain n top (Fin.tail A) := by
  unfold Valid Chain
  simp only [rowOK_iff, col_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1 0, fun i => h1 i.succ, fun i hi j hj => ?_, fun _ j hj => ?_⟩
    · exact h2 j i.val (by omega) hj
    · exact absurd hj (by simp [top])
  · rintro ⟨h0, h1, h2, -⟩
    refine ⟨fun i => ?_, fun j k hk hk1 => ?_⟩
    · cases i using Fin.cases with
      | zero => exact h0
      | succ i => exact h1 i
    · exact h2 ⟨k, by omega⟩ (by simp; omega) j hk1

theorem a_succ (n : ℕ) : a (n + 1) = 12 * e n top := by
  classical
  have h1 : a (n + 1) = ∑ A : Fin (n + 1) → R, if Valid A then 1 else 0 := by
    unfold a
    rw [Fintype.card_subtype, Finset.card_filter]
  rw [h1, Fintype.sum_equiv (Fin.consEquiv fun _ => R).symm _
    (fun x => if RowOK x.1 ∧ Chain n top x.2 then 1 else 0)
    (fun A => by simp only [Fin.consEquiv_symm_apply]; exact if_congr (valid_iff A) rfl rfl),
    Fintype.sum_prod_type]
  have h12 : ∑ s : R, (if RowOK s then 1 else 0) = 12 := by decide
  unfold e
  rw [← h12, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun B _ => ?_
  by_cases hs : RowOK s <;> by_cases hB : Chain n top B <;> simp [hs, hB]

theorem top_ok : RowOK top := by decide
theorem p_top : p top = 3 := by decide
theorem q_top : q top = 2 := by decide

theorem a_closed (n : ℕ) : a (n + 1) = (n + 1) ^ 2 * (n + 2) ^ 2 * (n + 3) := by
  rw [a_succ, e_formula n top top_ok, p_top, q_top]
  unfold F
  have h3 : 6 * (3 + n).choose n = (n + 1) * (n + 2) * (n + 3) := by
    rw [← Nat.choose_symm_add]
    have := Nat.descFactorial_eq_factorial_mul_choose (3 + n) 3
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial] at this
    rw [show 3 + n - 2 = n + 1 by omega, show 3 + n - 1 = n + 2 by omega,
      show 3 + n - 0 = n + 3 by omega] at this
    nlinarith [this]
  have h2 : 2 * (2 + n).choose n = (n + 1) * (n + 2) := by
    rw [← Nat.choose_symm_add]
    have := Nat.descFactorial_eq_factorial_mul_choose (2 + n) 2
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial] at this
    rw [show 2 + n - 1 = n + 1 by omega, show 2 + n - 0 = n + 2 by omega] at this
    nlinarith [this]
  calc 12 * ((3 + n).choose n * (2 + n).choose n)
      = (6 * (3 + n).choose n) * (2 * (2 + n).choose n) := by ring
    _ = (n + 1) ^ 2 * (n + 2) ^ 2 * (n + 3) := by rw [h3, h2]; ring

theorem hardin (n : ℕ) (hn : 1 ≤ n) : a n = n ^ 5 + 4 * n ^ 4 + 5 * n ^ 3 + 2 * n ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_closed]
  ring


theorem a_closedZ (k : ℕ) :
    (a (k + 1) : ℤ) = ((k : ℤ) + 1) ^ 2 * ((k : ℤ) + 2) ^ 2 * ((k : ℤ) + 3) := by
  rw [a_closed]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3)
        - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  rw [show m + 7 - 1 = m + 5 + 1 by omega, show m + 7 - 2 = m + 4 + 1 by omega,
    show m + 7 - 3 = m + 3 + 1 by omega, show m + 7 - 4 = m + 2 + 1 by omega,
    show m + 7 - 5 = m + 1 + 1 by omega, show m + 7 - 6 = m + 1 by omega,
    show m + 7 = m + 6 + 1 by omega]
  simp only [a_closedZ]
  push_cast
  ring

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
      12 * X * (1 + 6 * X + 3 * X ^ 2) := by
  have hser : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      PowerSeries.mk (fun n => ((n : ℚ) ^ 5 + 4 * n ^ 4 + 5 * n ^ 3 + 2 * n ^ 2)) := by
    ext n
    simp only [coeff_mk]
    split_ifs with h
    · subst h
      simp
    · rw [hardin n (by omega)]
      push_cast
      ring
  rw [hser]
  set P : ℕ → ℚ := fun n => (n : ℚ) ^ 5 + 4 * n ^ 4 + 5 * n ^ 3 + 2 * n ^ 2 with hP
  have key : PowerSeries.mk P * (1 - X) ^ 6 =
      C 1 * (PowerSeries.mk P * X ^ 0) - C 6 * (PowerSeries.mk P * X ^ 1) +
        C 15 * (PowerSeries.mk P * X ^ 2) - C 20 * (PowerSeries.mk P * X ^ 3) +
        C 15 * (PowerSeries.mk P * X ^ 4) - C 6 * (PowerSeries.mk P * X ^ 5) +
        C 1 * (PowerSeries.mk P * X ^ 6) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (12 : ℚ⟦X⟧) * X * (1 + 6 * X + 3 * X ^ 2) =
      C 12 * X ^ 1 + C 72 * X ^ 2 + C 36 * X ^ 3 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 6
  · interval_cases k <;> norm_num [hP]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    simp only [show 0 ≤ j + 6 by omega, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega,
      show 3 ≤ j + 6 by omega, show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega,
      show 6 ≤ j + 6 by omega, show j + 6 - 0 = j + 6 by omega, show j + 6 - 1 = j + 5 by omega,
      show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega,
      show j + 6 - 4 = j + 2 by omega, show j + 6 - 5 = j + 1 by omega,
      show j + 6 - 6 = j by omega, show ¬ (j + 6 = 1) by omega, show ¬ (j + 6 = 2) by omega,
      show ¬ (j + 6 = 3) by omega, if_true, if_false, hP]
    push_cast
    ring

section Analysis

open Real Filter Topology

theorem hasSum_z : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa using this

theorem hasSum_z1 : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) (π ^ 2 / 6 - 1) := by
  have := (hasSum_nat_add_iff' 1).mpr hasSum_z
  rw [show π ^ 2 / 6 - 1 = π ^ 2 / 6 - ∑ i ∈ range 1, 1 / ((i : ℝ) + 1) ^ 2 by simp]
  exact this.congr_fun (fun n => by push_cast; ring)

theorem hasSum_t : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have h : ∀ N : ℕ, ∑ i ∈ range N, (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) =
        1 - 1 / ((N : ℝ) + 1) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih => rw [sum_range_succ, ih]; push_cast; ring
    simp_rw [h]
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  · intro i
    have h1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    rw [sub_nonneg]
    apply one_div_le_one_div_of_le h1
    linarith

theorem hasSum_t1 : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) - 1 / ((n : ℝ) + 3)) (1 / 2) := by
  have := (hasSum_nat_add_iff' 1).mpr hasSum_t
  rw [show (1 / 2 : ℝ) = 1 - ∑ i ∈ range 1, (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) by
    simp]
  exact this.congr_fun (fun n => by push_cast; ring)

theorem sum1 : HasSum (fun n : ℕ => 1 / (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 3)))
    (π ^ 2 / 4 - 19 / 8) := by
  have H := ((hasSum_z.mul_left (1 / 2)).add hasSum_z1).add
    ((hasSum_t.mul_left (-5 / 4)).add (hasSum_t1.mul_left (-1 / 4)))
  rw [show π ^ 2 / 4 - 19 / 8 = 1 / 2 * (π ^ 2 / 6) + (π ^ 2 / 6 - 1) +
    (-5 / 4 * 1 + -1 / 4 * (1 / 2)) by ring]
  refine H.congr_fun (fun n => ?_)
  have h1 : (0 : ℝ) < n + 1 := by positivity
  have h2 : (0 : ℝ) < n + 2 := by positivity
  have h3 : (0 : ℝ) < n + 3 := by positivity
  field_simp
  ring

theorem hasSum_eta : HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 12) := by
  have hz := hasSum_z
  have hodd : HasSum (fun k : ℕ => 1 / (((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2) (π ^ 2 / 24) := by
    have := hz.mul_left (1 / 4)
    rw [show π ^ 2 / 24 = 1 / 4 * (π ^ 2 / 6) by ring]
    refine this.congr_fun (fun k => ?_)
    have : (0 : ℝ) < k + 1 := by positivity
    push_cast
    field_simp
    ring
  have hevS : Summable (fun k : ℕ => 1 / (((2 * k : ℕ) : ℝ) + 1) ^ 2) :=
    hz.summable.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))
  have hev : HasSum (fun k : ℕ => 1 / (((2 * k : ℕ) : ℝ) + 1) ^ 2) (π ^ 2 / 8) := by
    have h := HasSum.even_add_odd (f := fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) hevS.hasSum hodd
    have := h.unique hz
    rw [show π ^ 2 / 8 = ∑' k : ℕ, 1 / (((2 * k : ℕ) : ℝ) + 1) ^ 2 by linarith]
    exact hevS.hasSum
  have := HasSum.even_add_odd (f := fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2)
    (hev.congr_fun (fun k => by simp [pow_mul])) (hodd.neg.congr_fun (fun k => by
      rw [pow_succ, pow_mul]; simp only [neg_one_sq, one_pow, one_mul]; ring))
  rw [show π ^ 2 / 12 = π ^ 2 / 8 + -(π ^ 2 / 24) by ring]
  exact this

/-- Partial sums of the alternating harmonic series. -/
noncomputable def A (N : ℕ) : ℝ := ∑ i ∈ range N, (-1 : ℝ) ^ i / ((i : ℝ) + 1)

theorem A_even (m : ℕ) : A (2 * m) = (harmonic (2 * m) : ℝ) - harmonic m := by
  induction m with
  | zero => simp [A]
  | succ m ih =>
    have e1 : (-1 : ℝ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
    unfold A at *
    rw [sum_range_succ, sum_range_succ, ih, pow_succ, e1]
    simp only [harmonic_succ]
    push_cast
    have : (0 : ℝ) < m + 1 := by positivity
    field_simp
    ring

theorem tendsto_two_mul : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
  tendsto_atTop_mono (fun m => by show m ≤ 2 * m; omega) tendsto_id

theorem tendsto_A_even : Tendsto (fun m : ℕ => A (2 * m)) atTop (𝓝 (log 2)) := by
  have h1 := tendsto_harmonic_sub_log
  have h2 := h1.comp tendsto_two_mul
  have h3 := (h2.sub h1).add (tendsto_const_nhds (x := log 2))
  rw [sub_self, zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [Function.comp_apply, A_even]
  push_cast
  rw [log_mul (by norm_num) hm']
  ring

theorem tendsto_A_odd : Tendsto (fun m : ℕ => A (2 * m + 1)) atTop (𝓝 (log 2)) := by
  have h : ∀ m : ℕ, A (2 * m + 1) = A (2 * m) + 1 / (((2 * m : ℕ) : ℝ) + 1) := by
    intro m
    unfold A
    rw [sum_range_succ, pow_mul]
    norm_num
  simp_rw [h]
  have h0 : Tendsto (fun m : ℕ => 1 / (((2 * m : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp tendsto_two_mul
  simpa using tendsto_A_even.add h0

theorem tendsto_A_even2 : Tendsto (fun m : ℕ => A (2 * m + 2)) atTop (𝓝 (log 2)) := by
  have := tendsto_A_even.comp (tendsto_add_atTop_nat 1)
  refine this.congr (fun m => ?_)
  simp only [Function.comp_apply]
  ring_nf

theorem Sh (N : ℕ) : ∑ n ∈ range N, (-1 : ℝ) ^ n * (-5 / 4 * (1 / ((n : ℝ) + 1)) +
      1 / ((n : ℝ) + 2) + 1 / 4 * (1 / ((n : ℝ) + 3))) =
    -5 / 4 * A N - (A (N + 1) - 1) + 1 / 4 * (A (N + 2) - 1 / 2) := by
  induction N with
  | zero => simp [A, sum_range_succ]; norm_num
  | succ N ih =>
    rw [sum_range_succ, ih]
    simp only [A, sum_range_succ]
    push_cast
    ring

theorem hasSum_h : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * (-5 / 4 * (1 / ((n : ℝ) + 1)) +
      1 / ((n : ℝ) + 2) + 1 / 4 * (1 / ((n : ℝ) + 3)))) (7 / 8 - 2 * log 2) := by
  have hg : HasSum (fun n : ℕ => -5 / 4 * (1 / ((n : ℝ) + 1)) + 1 / ((n : ℝ) + 2) +
      1 / 4 * (1 / ((n : ℝ) + 3))) (-11 / 8) := by
    have := (hasSum_t.mul_left (-5 / 4)).add (hasSum_t1.mul_left (-1 / 4))
    rw [show (-11 / 8 : ℝ) = -5 / 4 * 1 + -1 / 4 * (1 / 2) by norm_num]
    exact this.congr_fun (fun n => by ring)
  have hs := hg.summable.alternating
  have h1 := hs.hasSum.tendsto_sum_nat.comp tendsto_two_mul
  have h2 : Tendsto (fun m : ℕ => ∑ n ∈ range (2 * m), (-1 : ℝ) ^ n *
      (-5 / 4 * (1 / ((n : ℝ) + 1)) + 1 / ((n : ℝ) + 2) + 1 / 4 * (1 / ((n : ℝ) + 3))))
      atTop (𝓝 (7 / 8 - 2 * log 2)) := by
    simp_rw [Sh]
    have := ((tendsto_A_even.const_mul (-5 / 4)).sub (tendsto_A_odd.sub_const 1)).add
      ((tendsto_A_even2.sub_const (1 / 2)).const_mul (1 / 4))
    rw [show (7 / 8 - 2 * log 2 : ℝ) = -5 / 4 * log 2 - (log 2 - 1) + 1 / 4 * (log 2 - 1 / 2) by
      ring]
    exact this
  have := tendsto_nhds_unique h1 h2
  rw [← this]
  exact hs.hasSum

theorem sum2 : HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1 + 1) /
      (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 3)))
    (15 / 8 - π ^ 2 / 24 - 2 * log 2) := by
  have he1 := (hasSum_nat_add_iff' 1).mpr hasSum_eta
  have H := ((hasSum_eta.mul_left (1 / 2)).sub he1).add hasSum_h
  rw [show 15 / 8 - π ^ 2 / 24 - 2 * log 2 = 1 / 2 * (π ^ 2 / 12) -
    (π ^ 2 / 12 - ∑ i ∈ range 1, (-1 : ℝ) ^ i / ((i : ℝ) + 1) ^ 2) + (7 / 8 - 2 * log 2) by
      simp; ring]
  refine H.congr_fun (fun n => ?_)
  have h1 : (0 : ℝ) < n + 1 := by positivity
  have h2 : (0 : ℝ) < n + 2 := by positivity
  have h3 : (0 : ℝ) < n + 3 := by positivity
  push_cast
  field_simp
  ring

theorem a_closedR (m : ℕ) :
    (a (m + 1) : ℝ) = ((m : ℝ) + 1) ^ 2 * ((m : ℝ) + 2) ^ 2 * ((m : ℝ) + 3) := by
  rw [a_closed]
  push_cast
  ring

theorem eldar1 : HasSum (fun m : ℕ => 1 / (a (m + 1) : ℝ)) (Real.pi ^ 2 / 4 - 19 / 8) :=
  sum1.congr_fun (fun m => by rw [a_closedR])

theorem eldar2 : HasSum (fun m : ℕ => (-1 : ℝ) ^ (m + 1 + 1) / (a (m + 1) : ℝ))
    (15 / 8 - Real.pi ^ 2 / 24 - 2 * Real.log 2) :=
  sum2.congr_fun (fun m => by rw [a_closedR])

end Analysis

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a208139.main :=
  ⟨OMA.Helpers.hardin, OMA.Helpers.gen_fun, OMA.Helpers.recurrence, OMA.Helpers.eldar1,
    OMA.Helpers.eldar2⟩
