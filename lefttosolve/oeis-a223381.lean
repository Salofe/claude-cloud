import OMAStatements.S_oeis_a223381

/-!
Proof of Barker's conjectures for A223381 (n X 2 arrays with entries 0..2, all horizontally or
vertically connected equal values in a straight line, new values introduced in row major order).

Write `Row` for a row (a function `Fin 2 → Fin 3`).
* Straight lines. Call two consecutive rows `r` (above) and `s` (below) compatible (`PairOK`)
  when a row with two equal entries has no equal entry directly above or below it. If some pair
  of consecutive rows is not compatible, a cell has an equal horizontal neighbor and an equal
  vertical neighbor, and these two neighbors are connected through it but share neither a row
  nor a column. Conversely, if all pairs are compatible, a chain of equal neighbors starting at a
  cell `p` never turns: by induction along the chain, every cell `q` reached is `p`, or lies in
  the row of `p` and has an equal horizontal neighbor, or lies in the column of `p` and has an
  equal vertical neighbor (`Inv`, `inv_step`). So `Cond x ↔ Pw x` (`cond_iff`).
* Row major order. Generalize `RowMajorNew` to `RMNk k` (values below `k` count as already
  introduced). Removing the first row `r` (`rmn_cons`): `RMNk k (r :: B)` iff `r` respects
  `k` (`RowOKk`) and `RMNk (nk k r) B`, where `nk k r = max k (max r + 1)`; the values below
  `nk k r` are those below `k` and the entries of `r` (`cover`).
* Transfer. If `T m r k` counts the arrays with `m + 1` rows, first row `r`, all pairs
  compatible and `RMNk k`, then `T 0 r k = [RowOKk k r]`,
  `T (m + 1) r k = Sum_s [RowOKk k r ∧ PairOK r s] T m s (nk k r)`, and
  `a (m + 1) = Sum_r T m r 0`. On codes (9 rows, `k ≤ 3`) this is the recursion `G`.
* The recursion is linear, so `G (m + 4) + 10 G (m + 2) = 8 G (m + 3)` (entrywise), checked
  for `m = 0` by a finite computation, holds for every `m`. Hence
  `a n = 8 a (n - 1) - 10 a (n - 2)` for `n ≥ 5`, and for `n = 4` from `a 1, ..., a 4 =
  2, 9, 57, 366`. The generating function follows by comparing coefficients. The closed form
  satisfies the same recurrence (`4 ± √6` are the roots of `x^2 - 8x + 10`) and takes the
  values `9, 57` at `n = 2, 3`.
-/

namespace OMA.Helpers

open OMA.S_oeis_a223381 Finset

/-- A row of the array. -/
abbrev Row := Fin 2 → Fin 3

/-- Two consecutive rows `r` (above) and `s` (below) are compatible: a row with two equal
entries has no equal entry directly above or below it. -/
def PairOK (r s : Row) : Prop :=
  ¬ (r 0 = r 1 ∧ (s 0 = r 0 ∨ s 1 = r 1)) ∧ ¬ (s 0 = s 1 ∧ (r 0 = s 0 ∨ r 1 = s 1))

instance decPairOK (r s : Row) : Decidable (PairOK r s) := by
  unfold PairOK
  infer_instance

/-- All pairs of consecutive rows are compatible. -/
def Pw {R : ℕ} (x : Fin R → Row) : Prop :=
  ∀ (i : ℕ) (h : i + 1 < R), PairOK (x ⟨i, by omega⟩) (x ⟨i + 1, h⟩)

theorem eqNbr_symm {R : ℕ} (x : Fin R → Row) (p q : Fin R × Fin 2) (h : eqNbr x p q) :
    eqNbr x q p := by
  obtain ⟨h | h, hv⟩ := h
  · exact ⟨Or.inl ⟨h.1.symm, h.2.symm⟩, hv.symm⟩
  · exact ⟨Or.inr ⟨h.1.symm, h.2.symm⟩, hv.symm⟩

theorem two_step {R : ℕ} (x : Fin R → Row) (h : Cond x) (p q r : Fin R × Fin 2)
    (h1 : eqNbr x p q) (h2 : eqNbr x q r) : p.1 = r.1 ∨ p.2 = r.2 :=
  h p r (Relation.ReflTransGen.tail (Relation.ReflTransGen.single h1) h2)

theorem pw_of_cond {R : ℕ} (x : Fin R → Row) (h : Cond x) : Pw x := by
  intro i hi
  have hne : ¬ ((⟨i, by omega⟩ : Fin R) = ⟨i + 1, hi⟩) := by
    intro he
    rw [Fin.mk.injEq] at he
    omega
  have h10 : ¬ ((1 : Fin 2) = 0) := by decide
  have h01 : ¬ ((0 : Fin 2) = 1) := by decide
  refine ⟨?_, ?_⟩
  · rintro ⟨hr, hs | hs⟩
    · have := two_step x h (⟨i, by omega⟩, 1) (⟨i, by omega⟩, 0) (⟨i + 1, hi⟩, 0)
        ⟨Or.inl ⟨rfl, Or.inr rfl⟩, hr.symm⟩ ⟨Or.inr ⟨rfl, Or.inl rfl⟩, hs.symm⟩
      rcases this with h' | h'
      · exact hne h'
      · exact h10 h'
    · have := two_step x h (⟨i, by omega⟩, 0) (⟨i, by omega⟩, 1) (⟨i + 1, hi⟩, 1)
        ⟨Or.inl ⟨rfl, Or.inl rfl⟩, hr⟩ ⟨Or.inr ⟨rfl, Or.inl rfl⟩, hs.symm⟩
      rcases this with h' | h'
      · exact hne h'
      · exact h01 h'
  · rintro ⟨hs, hr | hr⟩
    · have := two_step x h (⟨i + 1, hi⟩, 1) (⟨i + 1, hi⟩, 0) (⟨i, by omega⟩, 0)
        ⟨Or.inl ⟨rfl, Or.inr rfl⟩, hs.symm⟩ ⟨Or.inr ⟨rfl, Or.inr rfl⟩, hr.symm⟩
      rcases this with h' | h'
      · exact hne h'.symm
      · exact h10 h'
    · have := two_step x h (⟨i + 1, hi⟩, 0) (⟨i + 1, hi⟩, 1) (⟨i, by omega⟩, 1)
        ⟨Or.inl ⟨rfl, Or.inl rfl⟩, hs⟩ ⟨Or.inr ⟨rfl, Or.inr rfl⟩, hr.symm⟩
      rcases this with h' | h'
      · exact hne h'.symm
      · exact h01 h'

/-- Two horizontal neighbors with equal values: the row has two equal entries. -/
theorem row_eq_of_horiz {R : ℕ} (x : Fin R → Row) (i : Fin R) (j j' : Fin 2)
    (hadj : j.val + 1 = j'.val ∨ j'.val + 1 = j.val) (he : x i j = x i j') : x i 0 = x i 1 := by
  fin_cases j <;> fin_cases j' <;> simp_all

/-- A row with two equal entries has no equal entry directly above or below it. -/
theorem no_bend {R : ℕ} (x : Fin R → Row) (h : Pw x) (c d : Fin R × Fin 2)
    (hrow : x c.1 0 = x c.1 1) (hcol : c.2 = d.2)
    (hadj : c.1.val + 1 = d.1.val ∨ d.1.val + 1 = c.1.val) (he : x c.1 c.2 = x d.1 d.2) :
    False := by
  obtain ⟨c1, c2⟩ := c
  obtain ⟨d1, d2⟩ := d
  simp only at hrow hcol hadj he
  subst hcol
  rcases hadj with hadj | hadj
  · have hp := h c1.val (by omega)
    have e1 : (⟨c1.val, by omega⟩ : Fin R) = c1 := rfl
    have e2 : (⟨c1.val + 1, by omega⟩ : Fin R) = d1 := Fin.ext hadj
    rw [e1, e2] at hp
    apply hp.1
    refine ⟨hrow, ?_⟩
    fin_cases c2
    · exact Or.inl he.symm
    · exact Or.inr he.symm
  · have hp := h d1.val (by omega)
    have e1 : (⟨d1.val, by omega⟩ : Fin R) = d1 := rfl
    have e2 : (⟨d1.val + 1, by omega⟩ : Fin R) = c1 := Fin.ext hadj
    rw [e1, e2] at hp
    apply hp.2
    refine ⟨hrow, ?_⟩
    fin_cases c2
    · exact Or.inl he.symm
    · exact Or.inr he.symm

/-- The invariant along a chain of equal neighbors starting at `p`. -/
def Inv {R : ℕ} (x : Fin R → Row) (p q : Fin R × Fin 2) : Prop :=
  q = p ∨ (q.1 = p.1 ∧ x q.1 0 = x q.1 1) ∨
    (q.2 = p.2 ∧ ∃ d : Fin R × Fin 2, q.2 = d.2 ∧
      (q.1.val + 1 = d.1.val ∨ d.1.val + 1 = q.1.val) ∧ x q.1 q.2 = x d.1 d.2)

theorem inv_step {R : ℕ} (x : Fin R → Row) (h : Pw x) (p b c : Fin R × Fin 2)
    (hb : Inv x p b) (hbc : eqNbr x b c) : Inv x p c := by
  obtain ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, he⟩ := hbc
  · -- horizontal step
    have hrowb : x b.1 0 = x b.1 1 := by
      have he' : x b.1 b.2 = x b.1 c.2 := by rw [he, h1]
      exact row_eq_of_horiz x b.1 b.2 c.2 h2 he'
    have hrow : x c.1 0 = x c.1 1 := h1 ▸ hrowb
    rcases hb with rfl | ⟨hb1, _⟩ | ⟨_, d, hd2, hdadj, hde⟩
    · exact Or.inr (Or.inl ⟨h1.symm, hrow⟩)
    · exact Or.inr (Or.inl ⟨h1.symm.trans hb1, hrow⟩)
    · exact (no_bend x h b d hrowb hd2 hdadj hde).elim
  · -- vertical step
    have hv : Inv x p c → Inv x p c := id
    apply hv
    rcases hb with rfl | ⟨_, hrow⟩ | ⟨hb2, _⟩
    · exact Or.inr (Or.inr ⟨h1.symm, b, h1.symm, h2.symm, he.symm⟩)
    · exact (no_bend x h b c hrow h1 h2 he).elim
    · exact Or.inr (Or.inr ⟨h1.symm.trans hb2, b, h1.symm, h2.symm, he.symm⟩)

theorem cond_of_pw {R : ℕ} (x : Fin R → Row) (h : Pw x) : Cond x := by
  intro p q hpq
  have hinv : Inv x p q := by
    induction hpq with
    | refl => exact Or.inl rfl
    | tail _ hbc ih => exact inv_step x h p _ _ ih hbc
  rcases hinv with rfl | ⟨h1, _⟩ | ⟨h2, _⟩
  · exact Or.inl rfl
  · exact Or.inl h1.symm
  · exact Or.inr h2.symm

theorem cond_iff {R : ℕ} (x : Fin R → Row) : Cond x ↔ Pw x :=
  ⟨pw_of_cond x, cond_of_pw x⟩

/-- Row major order, where the values below `k` count as already introduced. -/
def RMNk (k : ℕ) {R : ℕ} (x : Fin R → Row) : Prop :=
  ∀ i j, ∀ u : Fin 3, u < x i j → u.val < k ∨
    ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

theorem rmn_zero {R : ℕ} (x : Fin R → Row) : RowMajorNew x ↔ RMNk 0 x := by
  constructor
  · intro h i j u hu
    exact Or.inr (h i j u hu)
  · intro h i j u hu
    rcases h i j u hu with h' | h'
    · exact absurd h' (Nat.not_lt_zero _)
    · exact h'

/-- The first row `r` respects the values below `k`. -/
def RowOKk (k : ℕ) (r : Row) : Prop :=
  (∀ u : Fin 3, u < r 0 → u.val < k) ∧ (∀ u : Fin 3, u < r 1 → u.val < k ∨ r 0 = u)

instance decRowOKk (k : ℕ) (r : Row) : Decidable (RowOKk k r) := by
  unfold RowOKk
  infer_instance

/-- The values introduced after the row `r`. -/
def nk (k : ℕ) (r : Row) : ℕ := max k (max (r 0).val (r 1).val + 1)

theorem lt_nk (k : ℕ) (r : Row) (j : Fin 2) : (r j).val < nk k r := by
  unfold nk
  fin_cases j <;> simp

theorem cover (k : ℕ) (r : Row) (hr : RowOKk k r) (u : Fin 3) (hu : u.val < nk k r) :
    u.val < k ∨ r 0 = u ∨ r 1 = u := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨hk, h0, h1⟩ := hc
  have hu0 : ¬ u < r 0 := fun h' => by have := hr.1 u h'; omega
  have hu1 : ¬ u < r 1 := fun h' => by
    rcases hr.2 u h' with h'' | h''
    · omega
    · exact h0 h''
  rw [Fin.lt_def] at hu0 hu1
  have h0' : (r 0).val ≠ u.val := fun e => h0 (Fin.ext e)
  have h1' : (r 1).val ≠ u.val := fun e => h1 (Fin.ext e)
  unfold nk at hu
  omega

theorem rmn_cons (k : ℕ) {m : ℕ} (r : Row) (B : Fin m → Row) :
    RMNk k (Fin.cons r B : Fin (m + 1) → Row) ↔ RowOKk k r ∧ RMNk (nk k r) B := by
  constructor
  · intro h
    refine ⟨⟨fun u hu => ?_, fun u hu => ?_⟩, fun i j u hu => ?_⟩
    · rcases h 0 0 u (by simpa using hu) with h' | ⟨i', j', hlt, _⟩
      · exact h'
      · exfalso
        rcases hlt with hlt | ⟨_, hlt⟩
        · exact absurd hlt (Fin.not_lt_zero _)
        · exact absurd hlt (Fin.not_lt_zero _)
    · rcases h 0 1 u (by simpa using hu) with h' | ⟨i', j', hlt, hv⟩
      · exact Or.inl h'
      · right
        rcases hlt with hlt | ⟨rfl, hlt⟩
        · exact absurd hlt (Fin.not_lt_zero _)
        · have hj : j' = 0 := by
            rw [Fin.lt_def] at hlt
            exact Fin.ext (by simp at hlt ⊢; omega)
          subst hj
          simpa using hv
    · rcases h i.succ j u (by simpa using hu) with h' | ⟨i', j', hlt, hv⟩
      · exact Or.inl (lt_of_lt_of_le h' (le_max_left _ _))
      · induction i' using Fin.cases with
        | zero =>
          left
          have hv' : r j' = u := by simpa using hv
          rw [← hv']
          exact lt_nk k r j'
        | succ i' =>
          right
          refine ⟨i', j', ?_, by simpa using hv⟩
          rcases hlt with hlt | ⟨he, hlt⟩
          · exact Or.inl (Fin.succ_lt_succ_iff.1 hlt)
          · exact Or.inr ⟨Fin.succ_inj.1 he, hlt⟩
  · rintro ⟨hr, hB⟩ i j u hu
    induction i using Fin.cases with
    | zero =>
      have hu' : u < r j := by simpa using hu
      fin_cases j
      · exact Or.inl (hr.1 u hu')
      · rcases hr.2 u hu' with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨0, 0, Or.inr ⟨rfl, by decide⟩, by simpa using h'⟩
    | succ i =>
      have hu' : u < B i j := by simpa using hu
      rcases hB i j u hu' with h' | ⟨i', j', hlt, hv⟩
      · rcases cover k r hr u h' with h'' | h'' | h''
        · exact Or.inl h''
        · exact Or.inr ⟨0, 0, Or.inl (Fin.succ_pos _), by simpa using h''⟩
        · exact Or.inr ⟨0, 1, Or.inl (Fin.succ_pos _), by simpa using h''⟩
      · right
        refine ⟨i'.succ, j', ?_, by simpa using hv⟩
        rcases hlt with hlt | ⟨he, hlt⟩
        · exact Or.inl (Fin.succ_lt_succ_iff.2 hlt)
        · exact Or.inr ⟨by rw [he], hlt⟩

theorem rmn_nil (k : ℕ) (B : Fin 0 → Row) : RMNk k B := fun i => i.elim0

theorem pw_one (A : Fin 1 → Row) : Pw A := fun i hi => absurd hi (by omega)

theorem pw_cons {m : ℕ} (r : Row) (B : Fin (m + 1) → Row) :
    Pw (Fin.cons r B : Fin (m + 2) → Row) ↔ PairOK r (B 0) ∧ Pw B := by
  constructor
  · intro h
    have h0 := h 0 (by omega)
    exact ⟨h0, fun i hi => h (i + 1) (by omega)⟩
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => exact h0
    | succ i => exact h i (by omega)

/-- The conditions of the statement, with the values below `k` already introduced. -/
def Good (k : ℕ) {R : ℕ} (x : Fin R → Row) : Prop := Pw x ∧ RMNk k x

theorem good_one (k : ℕ) (r : Row) (B : Fin 0 → Row) :
    Good k (Fin.cons r B : Fin 1 → Row) ↔ RowOKk k r := by
  unfold Good
  rw [rmn_cons]
  exact ⟨fun h => h.2.1, fun h => ⟨pw_one _, h, rmn_nil _ _⟩⟩

theorem good_cons (k : ℕ) {m : ℕ} (r s : Row) (B : Fin m → Row) :
    Good k (Fin.cons r (Fin.cons s B) : Fin (m + 2) → Row) ↔
      (RowOKk k r ∧ PairOK r s) ∧ Good (nk k r) (Fin.cons s B : Fin (m + 1) → Row) := by
  unfold Good
  rw [rmn_cons, pw_cons]
  simp only [Fin.cons_zero]
  tauto

/-- The number of arrays with `m + 1` rows and first row `r` satisfying `Good k`. -/
noncomputable def T (m : ℕ) (r : Row) (k : ℕ) : ℕ := by
  classical
  exact ∑ B : Fin m → Row, if Good k (Fin.cons r B : Fin (m + 1) → Row) then 1 else 0

theorem T_zero (r : Row) (k : ℕ) : T 0 r k = if RowOKk k r then 1 else 0 := by
  classical
  unfold T
  rw [Fintype.sum_unique]
  exact if_congr (good_one k r _) rfl rfl

theorem T_succ (m : ℕ) (r : Row) (k : ℕ) :
    T (m + 1) r k = ∑ s : Row, if RowOKk k r ∧ PairOK r s then T m s (nk k r) else 0 := by
  classical
  unfold T
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if Good k (Fin.cons r (Fin.cons p.1 p.2) : Fin (m + 2) → Row) then 1 else 0)
    (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hv : RowOKk k r ∧ PairOK r s
  · rw [if_pos hv]
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    rw [good_cons]
    exact ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [good_cons]
    exact fun h => hv h.1

theorem a_eq (m : ℕ) : a (m + 1) = ∑ r : Row, T m r 0 := by
  classical
  have h1 : a (m + 1) = ∑ x : Fin (m + 1) → Row, if Good 0 x then 1 else 0 := by
    unfold a
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun x _ => if_congr ?_ rfl rfl
    rw [cond_iff, rmn_zero]
    rfl
  rw [h1, Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if Good 0 (Fin.cons p.1 p.2 : Fin (m + 1) → Row) then 1 else 0)
    (fun x => by simp), Fintype.sum_prod_type]
  rfl

/-- The row with code `u`: entries `u % 3` and `u / 3 % 3`. -/
def row (u : Fin 9) : Row := fun j => ⟨u.val / 3 ^ j.val % 3, Nat.mod_lt _ (by norm_num)⟩

theorem row_injective : Function.Injective row := by
  decide +kernel

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

/-- `RowOKk` on codes. -/
def okc (k : Fin 4) (u : Fin 9) : Bool :=
  Nat.ble (u.val % 3) k.val && Nat.ble (u.val / 3) (max k.val (u.val % 3 + 1))

/-- `PairOK` on codes. -/
def pc (u v : Fin 9) : Bool :=
  !(u.val % 3 == u.val / 3 && (v.val % 3 == u.val % 3 || v.val / 3 == u.val / 3)) &&
    !(v.val % 3 == v.val / 3 && (u.val % 3 == v.val % 3 || u.val / 3 == v.val / 3))

/-- `nk` on codes. -/
def nkc (k : Fin 4) (u : Fin 9) : Fin 4 :=
  ⟨max k.val (max (u.val % 3) (u.val / 3) + 1), by have := u.isLt; have := k.isLt; omega⟩

theorem okc_iff : ∀ (k : Fin 4) (u : Fin 9), RowOKk k.val (row u) ↔ okc k u = true := by
  decide +kernel

theorem step_iff : ∀ (k : Fin 4) (u v : Fin 9), (RowOKk k.val (row u) ∧ PairOK (row u) (row v)) ↔
    (okc k u && pc u v) = true := by
  decide +kernel

theorem nkc_eq : ∀ (k : Fin 4) (u : Fin 9), nk k.val (row u) = (nkc k u).val := by
  decide +kernel

/-- The transfer recursion on codes. -/
def G : ℕ → Fin 9 → Fin 4 → ℕ
  | 0, u, k => if okc k u then 1 else 0
  | m + 1, u, k => ∑ v : Fin 9, if okc k u && pc u v then G m v (nkc k u) else 0

theorem T_eq_G (m : ℕ) : ∀ (u : Fin 9) (k : Fin 4), T m (row u) k.val = G m u k := by
  induction m with
  | zero =>
    intro u k
    rw [T_zero]
    exact if_congr (okc_iff k u) rfl rfl
  | succ m ih =>
    intro u k
    rw [T_succ, ← row_bijective.sum_comp]
    simp only [G]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [nkc_eq, ih v]
    exact if_congr (step_iff k u v) rfl rfl

theorem a_eq_G (m : ℕ) : a (m + 1) = ∑ u : Fin 9, G m u 0 := by
  rw [a_eq, ← row_bijective.sum_comp]
  exact Finset.sum_congr rfl fun u _ => T_eq_G m u 0

theorem G_succ (m : ℕ) (u : Fin 9) (k : Fin 4) :
    G (m + 1) u k = ∑ v : Fin 9, if okc k u && pc u v then G m v (nkc k u) else 0 := rfl

theorem G_base : ∀ (u : Fin 9) (k : Fin 4), G 4 u k + 10 * G 2 u k = 8 * G 3 u k := by
  decide +kernel

theorem G_rec (m : ℕ) : ∀ (u : Fin 9) (k : Fin 4),
    G (m + 4) u k + 10 * G (m + 2) u k = 8 * G (m + 3) u k := by
  induction m with
  | zero => exact G_base
  | succ m ih =>
    intro u k
    show G ((m + 4) + 1) u k + 10 * G ((m + 2) + 1) u k = 8 * G ((m + 3) + 1) u k
    rw [G_succ (m + 4), G_succ (m + 2), G_succ (m + 3), Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs
    · exact ih v _
    · rfl

theorem a_rec (m : ℕ) : a (m + 5) + 10 * a (m + 3) = 8 * a (m + 4) := by
  rw [show m + 5 = (m + 4) + 1 by omega, show m + 4 = (m + 3) + 1 by omega,
    show m + 3 = (m + 2) + 1 by omega, a_eq_G, a_eq_G, a_eq_G, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ => G_rec m u 0

theorem a_vals : a 1 = 2 ∧ a 2 = 9 ∧ a 3 = 57 ∧ a 4 = 366 := by
  rw [a_eq_G 0, a_eq_G 1, a_eq_G 2, a_eq_G 3]
  decide +kernel

theorem a_rec' (n : ℕ) (hn : 4 ≤ n) : a n + 10 * a (n - 2) = 8 * a (n - 1) := by
  obtain ⟨v1, v2, v3, v4⟩ := a_vals
  rcases Nat.eq_or_lt_of_le hn with rfl | hn
  · simp [v2, v3, v4]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [show m + 5 - 2 = m + 3 by omega, show m + 5 - 1 = m + 4 by omega]
    exact a_rec m

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - 8 * X + 10 * X ^ 2) = X * (1 - X) * (2 - 5 * X) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  obtain ⟨v1, v2, v3, v4⟩ := a_vals
  have key : PowerSeries.mk F * (1 - 8 * X + 10 * X ^ 2) =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 8 * (PowerSeries.mk F * X ^ 1) +
        C 10 * (PowerSeries.mk F * X ^ 2) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (1 - X) * (2 - 5 * X) = C 2 * X ^ 1 - C 7 * X ^ 2 + C 5 * X ^ 3 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 4
  · interval_cases k <;> norm_num [hF, v1, v2, v3]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
    have hr : ((a (j + 4) + 10 * a (j + 4 - 2) : ℕ) : ℚ) = ((8 * a (j + 4 - 1) : ℕ) : ℚ) := by
      rw [a_rec' (j + 4) (by omega)]
    rw [show j + 4 - 2 = j + 2 by omega, show j + 4 - 1 = j + 3 by omega] at hr
    push_cast at hr
    simp only [show 0 ≤ j + 4 by omega, show 1 ≤ j + 4 by omega, show 2 ≤ j + 4 by omega,
      show j + 4 - 0 = j + 4 by omega, show j + 4 - 1 = j + 3 by omega,
      show j + 4 - 2 = j + 2 by omega,
      show ¬ (j + 4 = 1) by omega, show ¬ (j + 4 = 2) by omega, show ¬ (j + 4 = 3) by omega,
      show ¬ (j + 4 = 0) by omega, show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega,
      if_true, if_false, hF]
    linarith

/-- The closed form of the statement. -/
noncomputable def f (n : ℕ) : ℝ :=
  (-(4 - Real.sqrt 6) ^ n * (-6 + Real.sqrt 6) + (4 + Real.sqrt 6) ^ n * (6 + Real.sqrt 6)) / 40

theorem sqrt_six_sq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)

theorem f_rec (n : ℕ) : f (n + 2) = 8 * f (n + 1) - 10 * f n := by
  unfold f
  have hs := sqrt_six_sq
  set s := Real.sqrt 6
  linear_combination ((-(4 - s) ^ n * (-6 + s) + (4 + s) ^ n * (6 + s)) / 40) * hs

theorem f_zero : f 0 = 3 / 10 := by
  unfold f
  ring

theorem f_one : f 1 = 3 / 2 := by
  unfold f
  have hs := sqrt_six_sq
  set s := Real.sqrt 6
  linear_combination (1 / 20) * hs

theorem f_two : f 2 = 9 := by
  rw [f_rec 0, f_one, f_zero]
  norm_num

theorem f_three : f 3 = 57 := by
  rw [f_rec 1, f_two, f_one]
  norm_num

theorem closed_aux (m : ℕ) : (a (m + 2) : ℝ) = f (m + 2) ∧ (a (m + 3) : ℝ) = f (m + 3) := by
  obtain ⟨_, v2, v3, _⟩ := a_vals
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [v2, f_two]
      norm_num
    · rw [v3, f_three]
      norm_num
  | succ m ih =>
    obtain ⟨h2, h3⟩ := ih
    refine ⟨h3, ?_⟩
    have hr : ((a (m + 4) + 10 * a (m + 4 - 2) : ℕ) : ℝ) = ((8 * a (m + 4 - 1) : ℕ) : ℝ) := by
      rw [a_rec' (m + 4) (by omega)]
    rw [show m + 4 - 2 = m + 2 by omega, show m + 4 - 1 = m + 3 by omega] at hr
    push_cast at hr
    have hf := f_rec (m + 2)
    rw [show m + 1 + 3 = m + 4 by omega, show m + 2 + 2 = m + 4 by omega,
      show m + 2 + 1 = m + 3 by omega] at *
    linarith

theorem closed (n : ℕ) (hn : 1 < n) : (a n : ℝ) =
    (-(4 - Real.sqrt 6) ^ n * (-6 + Real.sqrt 6) + (4 + Real.sqrt 6) ^ n * (6 + Real.sqrt 6)) /
      40 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact (closed_aux m).1

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a223381.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.closed⟩
