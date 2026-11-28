import OMAStatements.S_oeis_a229423
import Mathlib

/-!
Proof of the three conjectures of A229423 (n X 3 arrays over 0..2).

The array is a list of rows. Putting a row on top of a list, the conditions split into a
condition on the new top row and the same kind of condition on the rest, where the column
comparisons that are already decided are dropped (`good_cons`): we keep, for each of the two
column pairs, a flag saying whether the two columns agree so far. This gives a transfer recursion
for the number `G n r f` of admissible continuations of length `n` below a row `r` with flags
`f` (`G_succ`). For the 27 reachable states, `G n r f` is a fixed combination of binomial
coefficients `n.choose k` (k < 8), whose coefficients form a table checked by the kernel
(`cert0`, `cert1`), and the induction uses Pascal's rule (`shift`). Summing over the top row
gives a(m + 1) = 8 + 19 C(m,1) + 37 C(m,2) + 46 C(m,3) + 34 C(m,4) + 13 C(m,5) + 2 C(m,6), which
is the stated degree 6 polynomial; the generating function and the recurrence follow.
-/

namespace OMA.Helpers

open OMA.S_oeis_a229423 Finset

/-- A row of the array. -/
abbrev Row := Fin 3 → Fin 3

/-- The base 3 code of a row (leftmost entry most significant). -/
def code (r : Row) : ℕ := 9 * (r 0 : ℕ) + 3 * (r 1 : ℕ) + (r 2 : ℕ)

theorem lex_le_code (r s : Row) : toLex r ≤ toLex s ↔ code r ≤ code s := by
  have key : ∀ r s : Row,
      ((∃ i, (∀ j, j < i → r j = s j) ∧ r i < s i) ∨ r = s) ↔ code r ≤ code s := by
    decide +kernel
  rw [← key r s, le_iff_lt_or_eq, toLex_inj]
  exact Iff.rfl

theorem lcons_le (a b : Fin 3) (l₁ l₂ : List (Fin 3)) :
    (a :: l₁ ≤ b :: l₂) ↔ a < b ∨ (a = b ∧ l₁ ≤ l₂) := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
  have hlt : (a :: l₁ < b :: l₂) ↔ a < b ∨ (a = b ∧ l₁ < l₂) := by
    show List.Lex (· < ·) (a :: l₁) (b :: l₂) ↔ _
    constructor
    · intro h
      cases h with
      | cons h => exact Or.inr ⟨rfl, h⟩
      | rel h => exact Or.inl h
    · rintro (h | ⟨rfl, h⟩)
      · exact List.Lex.rel h
      · exact List.Lex.cons h
  rw [hlt, List.cons_eq_cons]
  constructor
  · rintro ((h | ⟨h1, h2⟩) | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, Or.inl h2⟩
    · exact Or.inr ⟨h1, Or.inr h2⟩
  · rintro (h | ⟨h1, h2 | h2⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · exact Or.inr ⟨h1, h2⟩

/-- The horizontal condition on a row. -/
def Hp (r : Row) : Prop := ∀ j : Fin 2, ((r j.succ : ℤ) - r j.castSucc) % 3 ≠ 1

instance (r : Row) : Decidable (Hp r) := by
  unfold Hp
  infer_instance

/-- The vertical condition between consecutive rows, as in the statement. -/
def Vr (r s : Row) : Prop := (∀ j, ((s j : ℤ) - r j) % 3 ≠ 2) ∧ toLex r ≤ toLex s

/-- The conditions on the rows below a row `r`, where `f j` says that column comparison `j`
is still undecided. -/
def Good (r : Row) (f : Fin 2 → Bool) (l : List Row) : Prop :=
  (∀ t ∈ l, Hp t) ∧ (r :: l).IsChain Vr ∧
    ∀ j : Fin 2, f j = true → l.map (fun t => t j.succ) ≤ l.map (fun t => t j.castSucc)

/-- The admissible next rows. -/
def Tb (r : Row) (f : Fin 2 → Bool) (s : Row) : Bool :=
  decide (Hp s ∧ (∀ j, ((s j : ℤ) - r j) % 3 ≠ 2) ∧ code r ≤ code s ∧
    ∀ j : Fin 2, f j = true → s j.succ ≤ s j.castSucc)

/-- The new flags. -/
def fp (f : Fin 2 → Bool) (s : Row) : Fin 2 → Bool :=
  fun j => f j && decide (s j.succ = s j.castSucc)

/-- The admissible top rows. -/
def Sb (s : Row) : Bool := decide (Hp s ∧ ∀ j : Fin 2, s j.succ ≤ s j.castSucc)

/-- The flags after the top row. -/
def fl (s : Row) : Fin 2 → Bool := fun j => decide (s j.succ = s j.castSucc)

theorem col_step (a b : Fin 3) (X : Prop) : (a < b ∨ a = b ∧ X) ↔ a ≤ b ∧ (a = b → X) := by
  constructor
  · rintro (h | ⟨h, hx⟩)
    · exact ⟨h.le, fun he => absurd he h.ne⟩
    · exact ⟨h.le, fun _ => hx⟩
  · rintro ⟨h, hx⟩
    rcases h.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hx h⟩

theorem good_cons (r : Row) (f : Fin 2 → Bool) (s : Row) (l : List Row) :
    Good r f (s :: l) ↔ Tb r f s = true ∧ Good s (fp f s) l := by
  simp only [Good, Tb, fp, Vr, List.forall_mem_cons, List.isChain_cons_cons, List.map_cons,
    lcons_le, col_step, decide_eq_true_eq, Bool.and_eq_true, lex_le_code]
  constructor
  · rintro ⟨⟨hs, hl⟩, ⟨hv, hc⟩, hcol⟩
    exact ⟨⟨hs, hv.1, hv.2, fun j hj => (hcol j hj).1⟩, hl, hc,
      fun j hj => (hcol j hj.1).2 hj.2⟩
  · rintro ⟨⟨hs, hv1, hv2, hcol1⟩, hl, hc, hcol2⟩
    exact ⟨⟨hs, hl⟩, ⟨⟨hv1, hv2⟩, hc⟩, fun j hj => ⟨hcol1 j hj, fun he => hcol2 j ⟨hj, he⟩⟩⟩

theorem sol_cons (s : Row) (l : List Row) :
    IsSolution (s :: l) ↔ Sb s = true ∧ Good s (fl s) l := by
  simp only [IsSolution, Good, Sb, fl, List.forall_mem_cons, List.map_cons,
    lcons_le, col_step, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hs, hl⟩, hc, hcol⟩
    exact ⟨⟨hs, fun j => (hcol j).1⟩, hl, hc, fun j hj => (hcol j).2 hj⟩
  · rintro ⟨⟨hs, hcol1⟩, hl, hc, hcol2⟩
    exact ⟨⟨hs, hl⟩, hc, fun j => ⟨hcol1 j, hcol2 j⟩⟩

theorem good_nil (r : Row) (f : Fin 2 → Bool) : Good r f [] :=
  ⟨fun _ ht => absurd ht List.not_mem_nil, List.IsChain.singleton r,
    fun _ _ => le_of_eq rfl⟩

open Classical in
/-- The number of admissible continuations of length `n` below `r` with flags `f`. -/
noncomputable def G (n : ℕ) (r : Row) (f : Fin 2 → Bool) : ℕ :=
  ∑ v : Fin n → Row, if Good r f (List.ofFn v) then 1 else 0

theorem G_zero (r : Row) (f : Fin 2 → Bool) : G 0 r f = 1 := by
  classical
  unfold G
  rw [Fintype.sum_unique]
  simp only [List.ofFn_zero]
  exact if_pos (good_nil r f)

theorem G_succ (n : ℕ) (r : Row) (f : Fin 2 → Bool) :
    G (n + 1) r f = ∑ s : Row, if Tb r f s = true then G n s (fp f s) else 0 := by
  classical
  unfold G
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun x => if Good r f (List.ofFn (Fin.cons x.1 x.2 : Fin (n + 1) → Row)) then 1 else 0)
    (fun g => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with hs
  · refine Finset.sum_congr rfl fun v _ => if_congr ?_ rfl rfl
    rw [List.ofFn_succ, good_cons]
    simp only [Fin.cons_zero, Fin.cons_succ]
    exact ⟨fun h => h.2, fun h => ⟨hs, h⟩⟩
  · refine Finset.sum_eq_zero fun v _ => if_neg ?_
    rw [List.ofFn_succ, good_cons]
    simp only [Fin.cons_zero]
    exact fun h => hs h.1

open Classical in
theorem card_eq (n : ℕ) (P : List Row → Prop) :
    Nat.card {l : List Row // l.length = n ∧ P l} =
      ∑ v : Fin n → Row, if P (List.ofFn v) then 1 else 0 := by
  have e : {l : List Row // l.length = n ∧ P l} ≃ {v : Fin n → Row // P (List.ofFn v)} :=
    { toFun := fun x => ⟨fun i => x.1[i.1]'(by rw [x.2.1]; exact i.2), by
        have h : List.ofFn (fun i : Fin n => x.1[i.1]'(by rw [x.2.1]; exact i.2)) = x.1 := by
          apply List.ext_getElem
          · rw [List.length_ofFn, x.2.1]
          · intro i h1 h2
            rw [List.getElem_ofFn]
        rw [h]
        exact x.2.2⟩
      invFun := fun v => ⟨List.ofFn v.1, List.length_ofFn, v.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply List.ext_getElem
        · rw [List.length_ofFn, x.2.1]
        · intro i h1 h2
          rw [List.getElem_ofFn]
      right_inv := by
        intro v
        apply Subtype.ext
        funext i
        simp only [List.getElem_ofFn] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

theorem a_eq (m : ℕ) : a (m + 1) = ∑ s : Row, if Sb s = true then G m s (fl s) else 0 := by
  classical
  unfold a
  rw [card_eq, Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun x => if IsSolution (List.ofFn (Fin.cons x.1 x.2 : Fin (m + 1) → Row)) then 1 else 0)
    (fun g => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold G
  split_ifs with hs
  · refine Finset.sum_congr rfl fun v _ => if_congr ?_ rfl rfl
    rw [List.ofFn_succ, sol_cons]
    simp only [Fin.cons_zero, Fin.cons_succ]
    exact ⟨fun h => h.2, fun h => ⟨hs, h⟩⟩
  · refine Finset.sum_eq_zero fun v _ => if_neg ?_
    rw [List.ofFn_succ, sol_cons]
    simp only [Fin.cons_zero]
    exact fun h => hs h.1

/-- The reachable states. -/
def Valid (r : Row) (f : Fin 2 → Bool) : Prop :=
  Hp r ∧ ∀ j : Fin 2, f j = true → r j.succ = r j.castSucc

theorem valid_step (r : Row) (f : Fin 2 → Bool) (s : Row) (h : Tb r f s = true) :
    Valid s (fp f s) := by
  simp only [Tb, decide_eq_true_eq] at h
  refine ⟨h.1, fun j hj => ?_⟩
  simp only [fp, Bool.and_eq_true, decide_eq_true_eq] at hj
  exact hj.2

theorem valid_top (s : Row) (h : Sb s = true) : Valid s (fl s) := by
  simp only [Sb, decide_eq_true_eq] at h
  refine ⟨h.1, fun j hj => ?_⟩
  simp only [fl, decide_eq_true_eq] at hj
  exact hj

/-- The coefficient table. -/
def tbl : List (List ℕ) := [[1, 3, 11, 22, 23, 11, 2, 0], [1, 3, 11, 22, 23, 11, 2, 0], [1, 3, 11, 22, 23, 11, 2, 0], [1, 3, 11, 22, 23, 11, 2, 0], [], [], [], [], [1, 3, 10, 25, 33, 19, 4, 0], [], [1, 3, 10, 25, 33, 19, 4, 0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [1, 2, 4, 12, 28, 34, 19, 4], [], [], [], [1, 2, 6, 17, 26, 17, 4, 0], [1, 1, 4, 11, 15, 9, 2, 0], [], [], [1, 4, 11, 15, 9, 2, 0, 0], [1, 4, 11, 15, 9, 2, 0, 0], [], [], [], [], [], [], [1, 2, 6, 11, 8, 2, 0, 0], [], [], [], [1, 4, 8, 7, 2, 0, 0, 0], [], [1, 4, 8, 7, 2, 0, 0, 0], [], [1, 3, 3, 1, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [1, 2, 3, 1, 0, 0, 0, 0], [], [], [], [1, 2, 1, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [], [], [], [], [], [], [], [], [], [], [1, 1, 0, 0, 0, 0, 0, 0], [], [1, 1, 0, 0, 0, 0, 0, 0], [], [1, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]

/-- The index of a state. -/
def idx (r : Row) (f : Fin 2 → Bool) : ℕ := code r * 4 + 2 * (f 0).toNat + (f 1).toNat

/-- The binomial coefficients of `G n r f`. -/
def cf (r : Row) (f : Fin 2 → Bool) (k : ℕ) : ℕ :=
  if k < 8 then (tbl.getD (idx r f) []).getD k 0 else 0

instance (r : Row) (f : Fin 2 → Bool) : Decidable (Valid r f) := by
  unfold Valid
  infer_instance

theorem cert0 : ∀ r f, Valid r f → cf r f 0 = 1 := by
  decide +kernel

theorem cert1 : ∀ r f, Valid r f → ∀ k < 8,
    (∑ s : Row, if Tb r f s = true then cf s (fp f s) k else 0) = cf r f k + cf r f (k + 1) := by
  decide +kernel

theorem shift (c : ℕ → ℕ) (hc : c 8 = 0) (n : ℕ) :
    ∑ k ∈ range 8, c k * (n + 1).choose k = ∑ k ∈ range 8, (c k + c (k + 1)) * n.choose k := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_succ_succ,
    Nat.choose_zero_right, hc]
  ring

theorem G_closed (n : ℕ) : ∀ r f, Valid r f → G n r f = ∑ k ∈ range 8, cf r f k * n.choose k := by
  induction n with
  | zero =>
    intro r f hv
    rw [G_zero]
    simp [Finset.sum_range_succ, cert0 r f hv]
  | succ n ih =>
    intro r f hv
    rw [G_succ, shift _ (by simp [cf]) n]
    have h1 : ∀ s : Row, (if Tb r f s = true then G n s (fp f s) else 0) =
        ∑ k ∈ range 8, (if Tb r f s = true then cf s (fp f s) k else 0) * n.choose k := by
      intro s
      split_ifs with hs
      · exact ih s (fp f s) (valid_step r f s hs)
      · simp
    rw [Finset.sum_congr rfl fun s _ => h1 s, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← Finset.sum_mul, cert1 r f hv k (Finset.mem_range.1 hk)]

/-- The coefficients of a(m + 1). -/
def dcf (k : ℕ) : ℕ := ∑ s : Row, if Sb s = true then cf s (fl s) k else 0

theorem dcf_vals : dcf 0 = 8 ∧ dcf 1 = 19 ∧ dcf 2 = 37 ∧ dcf 3 = 46 ∧ dcf 4 = 34 ∧
    dcf 5 = 13 ∧ dcf 6 = 2 ∧ dcf 7 = 0 := by
  decide +kernel

theorem a_binom (m : ℕ) : a (m + 1) = ∑ k ∈ range 8, dcf k * m.choose k := by
  rw [a_eq]
  have h1 : ∀ s : Row, (if Sb s = true then G m s (fl s) else 0) =
      ∑ k ∈ range 8, (if Sb s = true then cf s (fl s) k else 0) * m.choose k := by
    intro s
    split_ifs with hs
    · exact G_closed m s (fl s) (valid_top s hs)
    · simp
  rw [Finset.sum_congr rfl fun s _ => h1 s, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_mul]
  rfl

theorem ch3 (m : ℕ) : (m.choose 3 : ℚ) = m * (m - 1) * (m - 2) / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ m 2, Nat.cast_add, ih, Nat.cast_choose_two]
    push_cast
    ring

theorem ch4 (m : ℕ) : (m.choose 4 : ℚ) = m * (m - 1) * (m - 2) * (m - 3) / 24 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ m 3, Nat.cast_add, ih, ch3]
    push_cast
    ring

theorem ch5 (m : ℕ) : (m.choose 5 : ℚ) = m * (m - 1) * (m - 2) * (m - 3) * (m - 4) / 120 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ m 4, Nat.cast_add, ih, ch4]
    push_cast
    ring

theorem ch6 (m : ℕ) :
    (m.choose 6 : ℚ) = m * (m - 1) * (m - 2) * (m - 3) * (m - 4) * (m - 5) / 720 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ m 5, Nat.cast_add, ih, ch5]
    push_cast
    ring

theorem closedQ (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (1 / 360) * n ^ 6 + (1 / 20) * n ^ 5 + (5 / 18) * n ^ 4 + (2 / 3) * n ^ 3 +
      (799 / 360) * n ^ 2 + (107 / 60) * n + 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := dcf_vals
  rw [a_binom]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3, h4, h5, h6, h7]
  push_cast
  rw [Nat.cast_choose_two, ch3, ch4, ch5, ch6, Nat.choose_one_right, Nat.choose_zero_right]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : n > 7) :
    (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) +
      21 * a (n - 5) - 7 * a (n - 6) + 1 * a (n - 7) := by
  have h : ((a n : ℤ) : ℚ) = ((7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) -
      35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + 1 * a (n - 7) : ℤ) : ℚ) := by
    push_cast
    rw [closedQ n (by omega), closedQ (n - 1) (by omega), closedQ (n - 2) (by omega),
      closedQ (n - 3) (by omega), closedQ (n - 4) (by omega), closedQ (n - 5) (by omega),
      closedQ (n - 6) (by omega), closedQ (n - 7) (by omega)]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega]
    ring
  exact_mod_cast h

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 7 =
      8 - 29 * X + 62 * X ^ 2 - 72 * X ^ 3 + 48 * X ^ 4 - 18 * X ^ 5 + 3 * X ^ 6 := by
  set F : ℕ → ℚ := fun n => (a (n + 1) : ℚ) with hF
  have key : PowerSeries.mk F * (1 - X) ^ 7 =
      PowerSeries.mk F * X ^ 0 - C 7 * (PowerSeries.mk F * X ^ 1) +
        C 21 * (PowerSeries.mk F * X ^ 2) - C 35 * (PowerSeries.mk F * X ^ 3) +
        C 35 * (PowerSeries.mk F * X ^ 4) - C 21 * (PowerSeries.mk F * X ^ 5) +
        C 7 * (PowerSeries.mk F * X ^ 6) - PowerSeries.mk F * X ^ 7 := by
    simp only [map_ofNat]
    ring
  have hrhs : (8 - 29 * X + 62 * X ^ 2 - 72 * X ^ 3 + 48 * X ^ 4 - 18 * X ^ 5 + 3 * X ^ 6 :
      ℚ⟦X⟧) = C 8 * X ^ 0 - C 29 * X ^ 1 + C 62 * X ^ 2 - C 72 * X ^ 3 + C 48 * X ^ 4 -
        C 18 * X ^ 5 + C 3 * X ^ 6 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  have hc : ∀ i : ℕ, F i = (1 / 360) * ((i : ℚ) + 1) ^ 6 + (1 / 20) * ((i : ℚ) + 1) ^ 5 +
      (5 / 18) * ((i : ℚ) + 1) ^ 4 + (2 / 3) * ((i : ℚ) + 1) ^ 3 +
      (799 / 360) * ((i : ℚ) + 1) ^ 2 + (107 / 60) * ((i : ℚ) + 1) + 3 := by
    intro i
    rw [hF]
    simp only
    rw [closedQ (i + 1) (by omega)]
    push_cast
    ring
  by_cases hk : k < 7
  · interval_cases k <;> simp [hc] <;> norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
    simp only [show 1 ≤ j + 7 by omega, show 2 ≤ j + 7 by omega, show 3 ≤ j + 7 by omega,
      show 4 ≤ j + 7 by omega, show 5 ≤ j + 7 by omega, show 6 ≤ j + 7 by omega,
      show 7 ≤ j + 7 by omega, show 0 ≤ j + 7 by omega,
      show j + 7 - 0 = j + 7 by omega, show j + 7 - 1 = j + 6 by omega,
      show j + 7 - 2 = j + 5 by omega, show j + 7 - 3 = j + 4 by omega,
      show j + 7 - 4 = j + 3 by omega, show j + 7 - 5 = j + 2 by omega,
      show j + 7 - 6 = j + 1 by omega, show j + 7 - 7 = j by omega, if_true,
      show ¬ (j + 7 = 0) by omega, show ¬ (j + 7 = 1) by omega, show ¬ (j + 7 = 2) by omega,
      show ¬ (j + 7 = 3) by omega, show ¬ (j + 7 = 4) by omega, show ¬ (j + 7 = 5) by omega,
      show ¬ (j + 7 = 6) by omega, if_false, hc]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a229423.main :=
  ⟨fun n hn => OMA.Helpers.closedQ n hn, OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
