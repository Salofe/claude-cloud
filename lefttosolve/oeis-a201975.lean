import OMAStatements.S_oeis_a201975
import Mathlib

/-!
Proof of Barker's g.f. and recurrence for A201975 (n X 2 arrays over 0..3 whose rows and columns
are lexicographically nondecreasing read forwards and nonincreasing read backwards).

Consecutive rows must satisfy `RowPLe` (at most the next row read forwards, at least it read
backwards); on the code `4 r0 + r1` this is `c <= e` and `rcRev e <= rcRev c`. The two columns
`u, v` have a state `cst u v` in 0..3 (0: equal; 3: u read backwards is smaller; else 1 if u is
smaller read forwards, else 2), the column conditions say the state is at most 1, and putting a
row on top changes the state by `cstep`. Counting arrays by their first row and column state gives
a transfer recursion `gt (n + 1) = Mop4 (gt n)`, `a (n + 1) = Aop4 (gt n)`. A finite table `K4`
with `Mop4 (K4 j) = K4 j + K4 (j + 1)`, `K4 4 = 0`, `gt 1 = K4 0` (checked by `decide +kernel`)
gives `gt (n + 1) = Sum_{j < 4} C(n, j) K4 j`, hence `a (m + 2) = 30 + 42 m + 17 C(m, 2) + C(m, 3)`
and `a 1 = 4`, a cubic in n for n >= 1. The recurrence and the g.f. follow.
-/

namespace OMA.Helpers

open OMA.S_oeis_a201975 Finset

/-- A row of the array: two entries in {0, 1, 2, 3}. -/
abbrev Row4 := Fin 2 → Fin 4

theorem w4_lt {m : ℕ} (x y : Fin m → Fin 4) :
    toLex x < toLex y ↔ ∃ i, (∀ j, j < i → x j = y j) ∧ x i < y i := Iff.rfl

theorem w4_le {m : ℕ} (x y : Fin m → Fin 4) :
    toLex x ≤ toLex y ↔ toLex x < toLex y ∨ x = y := by
  rw [← toLex_inj]
  exact le_iff_lt_or_eq

theorem w4_lexLE {m : ℕ} (x y : Fin m → Fin 4) : lexLE x y ↔ toLex x ≤ toLex y := by
  rw [w4_le, w4_lt]
  unfold lexLE
  exact or_comm

theorem w4_cons_lt {m : ℕ} (a b : Fin 4) (u v : Fin m → Fin 4) :
    toLex (Fin.cons a u : Fin (m + 1) → Fin 4) < toLex (Fin.cons b v : Fin (m + 1) → Fin 4) ↔
      a < b ∨ (a = b ∧ toLex u < toLex v) := by
  rw [w4_lt, w4_lt]
  constructor
  · rintro ⟨i, hi, hlt⟩
    cases i using Fin.cases with
    | zero => exact Or.inl (by simpa using hlt)
    | succ k =>
      refine Or.inr ⟨by simpa using hi 0 (Fin.succ_pos k), k, fun j hj => ?_, by simpa using hlt⟩
      simpa using hi j.succ (Fin.succ_lt_succ_iff.mpr hj)
  · rintro (h | ⟨rfl, k, hk, hlt⟩)
    · exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by simpa using h⟩
    · refine ⟨k.succ, fun j hj => ?_, by simpa using hlt⟩
      cases j using Fin.cases with
      | zero => simp
      | succ j => simpa using hk j (Fin.succ_lt_succ_iff.mp hj)

theorem w4_snoc_lt {m : ℕ} (a b : Fin 4) (u v : Fin m → Fin 4) :
    toLex (Fin.snoc u a : Fin (m + 1) → Fin 4) < toLex (Fin.snoc v b : Fin (m + 1) → Fin 4) ↔
      toLex u < toLex v ∨ (u = v ∧ a < b) := by
  rw [w4_lt, w4_lt]
  constructor
  · rintro ⟨i, hi, hlt⟩
    cases i using Fin.lastCases with
    | last =>
      refine Or.inr ⟨funext fun k => ?_, by simpa using hlt⟩
      simpa using hi k.castSucc (Fin.castSucc_lt_last k)
    | cast k =>
      refine Or.inl ⟨k, fun j hj => ?_, by simpa using hlt⟩
      simpa using hi j.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hj)
  · rintro (⟨k, hk, hlt⟩ | ⟨rfl, h⟩)
    · refine ⟨k.castSucc, fun j hj => ?_, by simpa using hlt⟩
      cases j using Fin.lastCases with
      | last => exact absurd hj (not_lt.mpr (Fin.le_last _))
      | cast j => simpa using hk j (Fin.castSucc_lt_castSucc_iff.mp hj)
    · refine ⟨Fin.last m, fun j hj => ?_, by simpa using h⟩
      cases j using Fin.lastCases with
      | last => exact absurd hj (lt_irrefl _)
      | cast j => simp

theorem bwd4_bwd {m : ℕ} (u : Fin m → Fin 4) : bwd (bwd u) = u := by
  funext i
  simp [bwd]

theorem bwd4_inj {m : ℕ} {u v : Fin m → Fin 4} : bwd u = bwd v ↔ u = v := by
  constructor
  · intro h
    rw [← bwd4_bwd u, h, bwd4_bwd]
  · rintro rfl
    rfl

theorem bwd4_cons {m : ℕ} (a : Fin 4) (u : Fin m → Fin 4) :
    bwd (Fin.cons a u : Fin (m + 1) → Fin 4) = Fin.snoc (bwd u) a := by
  funext i
  exact Fin.cons_rev a u i

/-- The state of the two columns `u, v`: 0 if they are equal; otherwise 3 if `u` read backwards
is lexicographically smaller than `v` read backwards, else 1 if `u < v` read forwards, else 2. -/
noncomputable def cst {m : ℕ} (u v : Fin m → Fin 4) : ℕ := by
  classical
  exact if u = v then 0 else if toLex (bwd u) < toLex (bwd v) then 3
    else if toLex u < toLex v then 1 else 2

/-- The new state of the two columns when the entries `x, y` are put on top. -/
def cstep (x y s : ℕ) : ℕ :=
  if x = y then s else if x < y then (if s = 1 ∨ s = 2 then 1 else 3) else (if s = 3 then 3 else 2)

theorem cst_le {m : ℕ} (u v : Fin m → Fin 4) : cst u v ≤ 3 := by
  unfold cst
  split_ifs <;> omega

theorem cst_cons {m : ℕ} (x y : Fin 4) (u v : Fin m → Fin 4) :
    cst (Fin.cons x u : Fin (m + 1) → Fin 4) (Fin.cons y v) = cstep x.val y.val (cst u v) := by
  classical
  unfold cst cstep
  simp only [bwd4_cons, w4_snoc_lt, w4_cons_lt, Fin.cons_inj, bwd4_inj]
  have hlt : x < y ↔ x.val < y.val := Fin.lt_def
  by_cases huv : u = v
  · subst huv
    have hirr : ¬ toLex (bwd u) < toLex (bwd u) := lt_irrefl _
    have hirr2 : ¬ toLex u < toLex u := lt_irrefl _
    simp only [and_true, true_and, if_true, hirr, hirr2, false_or, and_false, or_false]
    rcases lt_trichotomy x y with h | h | h
    · have h1 : x ≠ y := ne_of_lt h
      have h2 : x.val ≠ y.val := fun e => h1 (Fin.ext e)
      simp [h, h1, h2, hlt.mp h]
    · subst h
      simp
    · have h1 : x ≠ y := ne_of_gt h
      have h2 : x.val ≠ y.val := fun e => h1 (Fin.ext e)
      have h3 : ¬ x < y := not_lt.mpr (le_of_lt h)
      have h4 : ¬ x.val < y.val := fun e => h3 (hlt.mpr e)
      simp [h1, h2, h3, h4]
  · simp only [huv, and_false, false_and, or_false, if_false]
    by_cases hr : toLex (bwd u) < toLex (bwd v)
    · simp only [hr, if_true]
      split_ifs <;> omega
    · simp only [hr, if_false]
      rcases lt_trichotomy x y with h | h | h
      · have h1 : x ≠ y := ne_of_lt h
        have h2 : x.val ≠ y.val := fun e => h1 (Fin.ext e)
        simp only [h, true_or, if_true, h2, if_false, hlt.mp h]
        split_ifs <;> omega
      · subst h
        simp
      · have h1 : x ≠ y := ne_of_gt h
        have h2 : x.val ≠ y.val := fun e => h1 (Fin.ext e)
        have h3 : ¬ x < y := not_lt.mpr (le_of_lt h)
        have h4 : ¬ x.val < y.val := fun e => h3 (hlt.mpr e)
        simp only [h1, h3, false_and, or_false, if_false, h2, h4]
        split_ifs <;> omega

theorem cst_nil (u v : Fin 0 → Fin 4) : cst u v = 0 := by
  have : u = v := funext fun i => Fin.elim0 i
  unfold cst
  rw [if_pos this]

theorem cst_good {m : ℕ} (u v : Fin m → Fin 4) :
    (toLex u ≤ toLex v ∧ toLex (bwd v) ≤ toLex (bwd u)) ↔ cst u v ≤ 1 := by
  classical
  unfold cst
  by_cases huv : u = v
  · subst huv
    simp
  · rw [if_neg huv]
    have e1 : toLex u ≤ toLex v ↔ toLex u < toLex v := by
      rw [w4_le]
      exact ⟨fun h => h.resolve_right huv, Or.inl⟩
    have e2 : toLex (bwd v) ≤ toLex (bwd u) ↔ ¬ toLex (bwd u) < toLex (bwd v) := not_lt.symm
    rw [e1, e2]
    split_ifs with h1 h2
    · simp [h1]
    · simp [h1, h2]
    · simp [h1, h2]

/-- Row `r` is at most row `s` read forwards and at least `s` read backwards. -/
def RowPLe (r s : Row4) : Prop := toLex r ≤ toLex s ∧ toLex (bwd s) ≤ toLex (bwd r)

/-- Consecutive rows are related by `RowPLe`. -/
def ChainOK {n : ℕ} (B : Fin n → Row4) : Prop :=
  ∀ i i' : Fin n, i.val + 1 = i'.val → RowPLe (B i) (B i')

theorem ChainOK_nil (B : Fin 0 → Row4) : ChainOK B := fun i => Fin.elim0 i

theorem ChainOK_cons {n : ℕ} (r : Row4) (B : Fin n → Row4) :
    ChainOK (Fin.cons r B : Fin (n + 1) → Row4) ↔
      (∀ i : Fin n, i.val = 0 → RowPLe r (B i)) ∧ ChainOK B := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i i' hii => ?_⟩
    · have := h 0 i.succ (by simp [hi])
      simpa using this
    · have := h i.succ i'.succ (by simp [hii])
      simpa using this
  · rintro ⟨h1, h2⟩ i i' hii
    cases i using Fin.cases with
    | zero =>
      cases i' using Fin.cases with
      | zero => simp at hii
      | succ j => simpa using h1 j (by simp at hii; omega)
    | succ k =>
      cases i' using Fin.cases with
      | zero => simp at hii
      | succ j => simpa using h2 k j (by simp at hii; omega)

/-- Column `j` of `B`, read top to bottom. -/
def col4 {n : ℕ} (B : Fin n → Row4) (j : Fin 2) : Fin n → Fin 4 := fun i => B i j

theorem col4_cons {n : ℕ} (r : Row4) (B : Fin n → Row4) (j : Fin 2) :
    col4 (Fin.cons r B : Fin (n + 1) → Row4) j = Fin.cons (r j) (col4 B j) := by
  funext i
  cases i using Fin.cases <;> rfl

theorem good_iff4 {n : ℕ} (x : Fin n → Row4) :
    good x ↔ ChainOK x ∧ cst (col4 x 0) (col4 x 1) ≤ 1 := by
  unfold good ChainOK RowPLe
  simp only [w4_lexLE]
  rw [← cst_good]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2 0 1 rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro j j' hjj
    fin_cases j <;> fin_cases j' <;> simp at hjj
    exact h2

end OMA.Helpers

namespace OMA.Helpers

open OMA.S_oeis_a201975 Finset

/-- The row read as a number in base 4, left entry first. -/
def rc (r : Row4) : ℕ := 4 * (r 0 : ℕ) + (r 1 : ℕ)

def e0 (c : ℕ) : ℕ := c / 4
def e1 (c : ℕ) : ℕ := c % 4

/-- The code of the reversed row. -/
def rcRev (c : ℕ) : ℕ := 4 * e1 c + e0 c

/-- `RowPLe` on codes. -/
def cple (c e : ℕ) : Prop := c ≤ e ∧ rcRev e ≤ rcRev c

instance (c e : ℕ) : Decidable (cple c e) := by unfold cple; infer_instance

theorem rc_lt (r : Row4) : rc r < 16 := by
  unfold rc
  have := (r 0).isLt
  have := (r 1).isLt
  omega

theorem e0_rc (r : Row4) : e0 (rc r) = (r 0 : ℕ) := by
  unfold e0 rc
  have := (r 1).isLt
  omega

theorem e1_rc (r : Row4) : e1 (rc r) = (r 1 : ℕ) := by
  unfold e1 rc
  have := (r 1).isLt
  omega

theorem rcRev_rc (r : Row4) : rcRev (rc r) = rc (bwd r) := by
  unfold rcRev
  rw [e0_rc, e1_rc]
  rfl

theorem rc_inj {r s : Row4} (h : rc r = rc s) : r = s := by
  have h0 := e0_rc r
  have h1 := e1_rc r
  rw [h, e0_rc] at h0
  rw [h, e1_rc] at h1
  funext j
  fin_cases j
  · exact Fin.ext h0.symm
  · exact Fin.ext h1.symm

theorem row4_lex_lt (r s : Row4) : toLex r < toLex s ↔ r 0 < s 0 ∨ (r 0 = s 0 ∧ r 1 < s 1) := by
  have e : ∀ u : Row4, u = Fin.cons (u 0) (Fin.cons (u 1) Fin.elim0) := by
    intro u
    funext j
    fin_cases j <;> rfl
  conv_lhs => rw [e r, e s]
  simp only [w4_cons_lt]
  have hz : ¬ toLex (Fin.elim0 : Fin 0 → Fin 4) < toLex (Fin.elim0 : Fin 0 → Fin 4) :=
    lt_irrefl _
  simp only [hz, and_false, or_false]

theorem row4_lt_iff (r s : Row4) : toLex r < toLex s ↔ rc r < rc s := by
  rw [row4_lex_lt]
  simp only [Fin.lt_def, Fin.ext_iff]
  unfold rc
  have := (r 0).isLt
  have := (r 1).isLt
  have := (s 0).isLt
  have := (s 1).isLt
  omega

theorem row4_le_iff (r s : Row4) : toLex r ≤ toLex s ↔ rc r ≤ rc s := by
  rw [w4_le, row4_lt_iff, Nat.le_iff_lt_or_eq]
  constructor
  · rintro (h | rfl)
    · exact Or.inl h
    · exact Or.inr rfl
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (rc_inj h)

theorem RowPLe_iff (r s : Row4) : RowPLe r s ↔ cple (rc r) (rc s) := by
  unfold RowPLe cple
  rw [row4_le_iff, row4_le_iff, rcRev_rc, rcRev_rc]

instance (r s : Row4) : Decidable (RowPLe r s) := decidable_of_iff _ (RowPLe_iff r s).symm

theorem image_rc : (Finset.univ : Finset Row4).image rc = range 16 := by
  apply Finset.eq_of_subset_of_card_le
  · intro c hc
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_range.mpr (rc_lt r)
  · rw [Finset.card_image_of_injective _ (fun r s h => rc_inj h), Finset.card_univ]
    simp

theorem sum_Row4 {M : Type*} [AddCommMonoid M] (φ : ℕ → M) :
    ∑ r : Row4, φ (rc r) = ∑ c ∈ range 16, φ c := by
  rw [← image_rc, Finset.sum_image (fun r _ s _ h => rc_inj h)]

theorem cstep_three (x y : ℕ) : cstep x y 3 = 3 := by
  unfold cstep
  split_ifs <;> omega

/-- Split a count according to the value (at most 3) of `p`, when `Q` excludes the value 3. -/
theorem split1 {X : Type*} [Fintype X] (P : X → Prop) [DecidablePred P] (p : X → ℕ)
    (hp : ∀ x, p x ≤ 3) (Q : ℕ → Prop) [DecidablePred Q] (hQ : ¬ Q 3) :
    (∑ x, if P x ∧ Q (p x) then 1 else 0) =
      ∑ t ∈ range 3, if Q t then (∑ x, if P x ∧ p x = t then 1 else 0) else 0 := by
  have key : ∀ x, (if P x ∧ Q (p x) then 1 else 0) =
      ∑ t ∈ range 3, if Q t then (if P x ∧ p x = t then 1 else 0) else 0 := by
    intro x
    rcases (show p x < 3 ∨ p x = 3 by have := hp x; omega) with c | c
    · rw [Finset.sum_eq_single (p x)]
      · by_cases hP : P x <;> by_cases q : Q (p x) <;> simp [hP, q]
      · intro t _ ht
        simp [Ne.symm ht]
      · intro h
        exact absurd (Finset.mem_range.mpr c) h
    · rw [if_neg (by rw [c]; tauto)]
      symm
      apply Finset.sum_eq_zero
      intro t ht
      have : p x ≠ t := by
        rw [c]
        have := Finset.mem_range.mp ht
        omega
      simp [this]
  rw [Finset.sum_congr rfl (fun x _ => key x), Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases q : Q t
  · simp only [q, if_true]
  · simp [q]

/-- The arrays `B` with `n` rows forming a chain whose first row is above `r`, with column state
`s`. -/
noncomputable def Gc (n : ℕ) (r : Row4) (s : ℕ) : ℕ := by
  classical
  exact ∑ B : Fin n → Row4, if ChainOK B ∧ (∀ i : Fin n, i.val = 0 → RowPLe r (B i)) ∧
    cst (col4 B 0) (col4 B 1) = s then 1 else 0

theorem Gc_zero (r : Row4) (s : ℕ) : Gc 0 r s = if s = 0 then 1 else 0 := by
  classical
  unfold Gc
  rw [Fintype.sum_unique]
  refine if_congr ?_ rfl rfl
  simp only [cst_nil, ChainOK_nil, true_and, IsEmpty.forall_iff]
  exact eq_comm

theorem Gc_succ (n : ℕ) (r : Row4) (s : ℕ) (hs : s < 3) :
    Gc (n + 1) r s = ∑ r' : Row4, if RowPLe r r' then
      ∑ t ∈ range 3, if cstep (r' 0) (r' 1) t = s then Gc n r' t else 0
    else 0 := by
  classical
  unfold Gc
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row4).symm _
    (fun x => if ChainOK (Fin.cons x.1 x.2 : Fin (n + 1) → Row4) ∧
      (∀ i : Fin (n + 1), i.val = 0 → RowPLe r ((Fin.cons x.1 x.2 : Fin (n + 1) → Row4) i)) ∧
      cst (col4 (Fin.cons x.1 x.2 : Fin (n + 1) → Row4) 0)
        (col4 (Fin.cons x.1 x.2 : Fin (n + 1) → Row4) 1) = s then 1 else 0)
    (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r' _ => ?_
  by_cases h : RowPLe r r'
  · rw [if_pos h]
    have e : ∀ B : Fin n → Row4, (if ChainOK (Fin.cons r' B : Fin (n + 1) → Row4) ∧
        (∀ i : Fin (n + 1), i.val = 0 → RowPLe r ((Fin.cons r' B : Fin (n + 1) → Row4) i)) ∧
        cst (col4 (Fin.cons r' B : Fin (n + 1) → Row4) 0)
          (col4 (Fin.cons r' B : Fin (n + 1) → Row4) 1) = s then 1 else 0) =
        if (ChainOK B ∧ ∀ i : Fin n, i.val = 0 → RowPLe r' (B i)) ∧
          cstep (r' 0) (r' 1) (cst (col4 B 0) (col4 B 1)) = s then 1 else 0 := by
      intro B
      refine if_congr ?_ rfl rfl
      rw [ChainOK_cons, col4_cons, col4_cons, cst_cons]
      constructor
      · rintro ⟨⟨h1, h2⟩, -, h3⟩
        exact ⟨⟨h2, h1⟩, h3⟩
      · rintro ⟨⟨h2, h1⟩, h3⟩
        refine ⟨⟨h1, h2⟩, fun i hi => ?_, h3⟩
        cases i using Fin.cases with
        | zero => simpa using h
        | succ k => simp at hi
    rw [Finset.sum_congr rfl (fun B _ => e B)]
    rw [split1 (fun B => ChainOK B ∧ ∀ i : Fin n, i.val = 0 → RowPLe r' (B i))
      (fun B => cst (col4 B 0) (col4 B 1)) (fun B => cst_le _ _)
      (fun t => cstep (r' 0) (r' 1) t = s) (by simp only [cstep_three]; omega)]
    refine Finset.sum_congr rfl fun t _ => if_congr Iff.rfl ?_ rfl
    exact Finset.sum_congr rfl fun B _ => if_congr and_assoc rfl rfl
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rintro ⟨-, h2, -⟩
    exact h (by simpa using h2 0 rfl)

/-- One step of the transfer recursion, on codes of rows. -/
def Mop4 (f : ℕ → ℕ → ℕ) (c s : ℕ) : ℕ :=
  ∑ e ∈ range 16, if cple c e then
    ∑ t ∈ range 3, if cstep (e0 e) (e1 e) t = s then f e t else 0
  else 0

/-- The transfer counts on codes. -/
def gt : ℕ → ℕ → ℕ → ℕ
  | 0, _, s => if s = 0 then 1 else 0
  | n + 1, c, s => Mop4 (gt n) c s

theorem Gc_eq_gt (n : ℕ) : ∀ (r : Row4) (s : ℕ), s < 3 → Gc n r s = gt n (rc r) s := by
  induction n with
  | zero =>
    intro r s _
    rw [Gc_zero]
    rfl
  | succ n ih =>
    intro r s hs
    rw [Gc_succ n r s hs]
    show _ = Mop4 (gt n) (rc r) s
    unfold Mop4
    rw [← sum_Row4]
    refine Finset.sum_congr rfl fun r' _ => ?_
    simp only [e0_rc, e1_rc]
    refine if_congr (RowPLe_iff r r') ?_ rfl
    refine Finset.sum_congr rfl fun t ht => if_congr Iff.rfl ?_ rfl
    exact ih r' t (Finset.mem_range.mp ht)

/-- The count of arrays with `n + 1` rows from the transfer counts of their last `n` rows. -/
def Aop4 (f : ℕ → ℕ → ℕ) : ℕ :=
  ∑ e ∈ range 16, ∑ t ∈ range 3, if cstep (e0 e) (e1 e) t ≤ 1 then f e t else 0

theorem a_succ4 (n : ℕ) : a (n + 1) = Aop4 (gt n) := by
  classical
  have h1 : a (n + 1) = ∑ A : Fin (n + 1) → Row4,
      if ChainOK A ∧ cst (col4 A 0) (col4 A 1) ≤ 1 then 1 else 0 := by
    unfold a
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun A _ => if_congr (good_iff4 A) rfl rfl
  rw [h1, Fintype.sum_equiv (Fin.consEquiv fun _ => Row4).symm _
    (fun x => if ChainOK (Fin.cons x.1 x.2 : Fin (n + 1) → Row4) ∧
      cst (col4 (Fin.cons x.1 x.2 : Fin (n + 1) → Row4) 0)
        (col4 (Fin.cons x.1 x.2 : Fin (n + 1) → Row4) 1) ≤ 1 then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  unfold Aop4
  rw [← sum_Row4]
  refine Finset.sum_congr rfl fun r' _ => ?_
  simp only [e0_rc, e1_rc]
  have e : ∀ B : Fin n → Row4, (if ChainOK (Fin.cons r' B : Fin (n + 1) → Row4) ∧
      cst (col4 (Fin.cons r' B : Fin (n + 1) → Row4) 0)
        (col4 (Fin.cons r' B : Fin (n + 1) → Row4) 1) ≤ 1 then 1 else 0) =
      if (ChainOK B ∧ ∀ i : Fin n, i.val = 0 → RowPLe r' (B i)) ∧
        cstep (r' 0) (r' 1) (cst (col4 B 0) (col4 B 1)) ≤ 1 then 1 else 0 := by
    intro B
    refine if_congr ?_ rfl rfl
    rw [ChainOK_cons, col4_cons, col4_cons, cst_cons]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h2, h1⟩, h3⟩
    · rintro ⟨⟨h2, h1⟩, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  rw [Finset.sum_congr rfl (fun B _ => e B)]
  rw [split1 (fun B => ChainOK B ∧ ∀ i : Fin n, i.val = 0 → RowPLe r' (B i))
    (fun B => cst (col4 B 0) (col4 B 1)) (fun B => cst_le _ _)
    (fun t => cstep (r' 0) (r' 1) t ≤ 1) (by simp only [cstep_three]; omega)]
  refine Finset.sum_congr rfl fun t ht => if_congr Iff.rfl ?_ rfl
  rw [← Gc_eq_gt n r' t (Finset.mem_range.mp ht)]
  unfold Gc
  exact Finset.sum_congr rfl fun B _ => if_congr and_assoc rfl rfl

/-- The coefficients `K j c s` of the transfer counts in the basis of binomial coefficients:
`gt (n + 1) c s = Sum_{j < 4} C(n, j) K j c s`. -/
def KT4 : List (List (List ℕ)) := [
  [[1, 0, 0], [0, 0, 3], [1, 0, 5], [2, 0, 6], [0, 0, 1], [1, 0, 2], [0, 0, 4], [1, 0, 5], [0, 0, 1], [0, 0, 2], [1, 0, 2], [0, 0, 3], [0, 0, 1], [0, 0, 1], [0, 0, 1], [1, 0, 0]],
  [[0, 0, 0], [0, 3, 0], [0, 5, 3], [0, 10, 5], [0, 0, 0], [0, 0, 2], [0, 4, 1], [0, 5, 3], [0, 0, 0], [0, 0, 1], [0, 0, 2], [0, 3, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]],
  [[0, 0, 0], [0, 0, 0], [0, 3, 0], [0, 10, 0], [0, 0, 0], [0, 0, 0], [0, 1, 0], [0, 3, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]],
  [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 1, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0]]]

/-- The entry of the table `KT4`. -/
def K4 (j c s : ℕ) : ℕ := ((KT4.getD j []).getD c []).getD s 0

theorem K4_step : ∀ j < 4, ∀ c < 16, ∀ s < 3, Mop4 (K4 j) c s = K4 j c s + K4 (j + 1) c s := by
  decide +kernel

theorem K4_four : ∀ c < 16, ∀ s < 3, K4 4 c s = 0 := by
  decide +kernel

theorem gt_one : ∀ c < 16, ∀ s < 3, gt 1 c s = K4 0 c s := by
  decide +kernel

theorem Mop4_congr {f f' : ℕ → ℕ → ℕ} (h : ∀ e < 16, ∀ t < 3, f e t = f' e t) (c s : ℕ) :
    Mop4 f c s = Mop4 f' c s := by
  unfold Mop4
  refine Finset.sum_congr rfl fun e he => if_congr Iff.rfl ?_ rfl
  refine Finset.sum_congr rfl fun t ht => if_congr Iff.rfl ?_ rfl
  exact h e (Finset.mem_range.mp he) t (Finset.mem_range.mp ht)

theorem Mop4_add (f f' : ℕ → ℕ → ℕ) (c s : ℕ) :
    Mop4 (fun e t => f e t + f' e t) c s = Mop4 f c s + Mop4 f' c s := by
  unfold Mop4
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> simp
  · simp

theorem Mop4_smul (w : ℕ) (f : ℕ → ℕ → ℕ) (c s : ℕ) :
    Mop4 (fun e t => w * f e t) c s = w * Mop4 f c s := by
  simp only [Mop4, Finset.mul_sum, mul_ite, mul_zero]

theorem Mop4_lin (S : Finset ℕ) (w : ℕ → ℕ) (F : ℕ → ℕ → ℕ → ℕ) (c s : ℕ) :
    Mop4 (fun e t => ∑ j ∈ S, w j * F j e t) c s = ∑ j ∈ S, w j * Mop4 (F j) c s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Mop4]
  | insert j S hj ih =>
    simp only [Finset.sum_insert hj]
    rw [Mop4_add, Mop4_smul, ih]

theorem Aop4_congr {f f' : ℕ → ℕ → ℕ} (h : ∀ e < 16, ∀ t < 3, f e t = f' e t) :
    Aop4 f = Aop4 f' := by
  unfold Aop4
  refine Finset.sum_congr rfl fun e he => ?_
  refine Finset.sum_congr rfl fun t ht => if_congr Iff.rfl ?_ rfl
  exact h e (Finset.mem_range.mp he) t (Finset.mem_range.mp ht)

theorem Aop4_add (f f' : ℕ → ℕ → ℕ) : Aop4 (fun e t => f e t + f' e t) = Aop4 f + Aop4 f' := by
  unfold Aop4
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

theorem Aop4_smul (w : ℕ) (f : ℕ → ℕ → ℕ) : Aop4 (fun e t => w * f e t) = w * Aop4 f := by
  simp only [Aop4, Finset.mul_sum, mul_ite, mul_zero]

theorem Aop4_lin (S : Finset ℕ) (w : ℕ → ℕ) (F : ℕ → ℕ → ℕ → ℕ) :
    Aop4 (fun e t => ∑ j ∈ S, w j * F j e t) = ∑ j ∈ S, w j * Aop4 (F j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Aop4]
  | insert j S hj ih =>
    simp only [Finset.sum_insert hj]
    rw [Aop4_add, Aop4_smul, ih]

theorem gt_closed (n : ℕ) : ∀ c < 16, ∀ s < 3,
    gt (n + 1) c s = ∑ j ∈ range 4, n.choose j * K4 j c s := by
  induction n with
  | zero =>
    intro c hc s hs
    rw [gt_one c hc s hs]
    simp [Finset.sum_range_succ]
  | succ n ih =>
    intro c hc s hs
    show Mop4 (gt (n + 1)) c s = _
    rw [Mop4_congr (f' := fun e t => ∑ j ∈ range 4, n.choose j * K4 j e t)
      (fun e he t ht => ih e he t ht), Mop4_lin]
    rw [Finset.sum_congr rfl (fun j hj => by rw [K4_step j (Finset.mem_range.mp hj) c hc s hs])]
    have h4 := K4_four c hc s hs
    have p1 : (n + 1).choose 1 = n.choose 0 + n.choose 1 := Nat.choose_succ_succ n 0
    have p2 : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ n 1
    have p3 : (n + 1).choose 3 = n.choose 2 + n.choose 3 := Nat.choose_succ_succ n 2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, p1, p2, p3,
      Nat.choose_zero_right, h4]
    ring

theorem cK4 : Aop4 (K4 0) = 30 ∧ Aop4 (K4 1) = 42 ∧ Aop4 (K4 2) = 17 ∧ Aop4 (K4 3) = 1 := by
  decide +kernel

theorem a_one4 : a 1 = 4 := by
  rw [a_succ4]
  decide +kernel

theorem a_two4 (m : ℕ) : a (m + 2) = 30 + 42 * m + 17 * m.choose 2 + m.choose 3 := by
  rw [a_succ4, Aop4_congr (f' := fun e t => ∑ j ∈ range 4, m.choose j * K4 j e t)
    (fun e he t ht => gt_closed m e he t ht), Aop4_lin]
  obtain ⟨c0, c1, c2, c3⟩ := cK4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3,
    Nat.choose_zero_right, Nat.choose_one_right]
  ring

theorem choose2Q (m : ℕ) : (m.choose 2 : ℚ) = m * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, Nat.choose_one_right]
    push_cast
    ring

theorem choose3Q (m : ℕ) : (m.choose 3 : ℚ) = m * (m - 1) * (m - 2) / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose2Q]
    push_cast
    ring

theorem closed4 (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = 4 + 26 * ((n : ℚ) - 1) + 8 * ((n : ℚ) - 1) * ((n : ℚ) - 2) +
      ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) / 6 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [a_one4]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [a_two4]
    push_cast
    rw [choose2Q, choose3Q]
    ring

theorem recurrence4 (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  have h : ((a n : ℤ) : ℚ) = ((4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) : ℤ) : ℚ) := by
    push_cast
    rw [closed4 n (by omega), closed4 (n - 1) (by omega), closed4 (n - 2) (by omega),
      closed4 (n - 3) (by omega), closed4 (n - 4) (by omega)]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega]
    ring
  exact_mod_cast h

open PowerSeries in
theorem gen_fun4 :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 4 =
      X * (4 + 14 * X - 24 * X ^ 2 + 7 * X ^ 3) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - X) ^ 4 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 4 * (PowerSeries.mk F * X ^ 1) +
        C 6 * (PowerSeries.mk F * X ^ 2) - C 4 * (PowerSeries.mk F * X ^ 3) +
        C 1 * (PowerSeries.mk F * X ^ 4) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (4 + 14 * X - 24 * X ^ 2 + 7 * X ^ 3) =
      C 4 * X ^ 1 + C 14 * X ^ 2 - C 24 * X ^ 3 + C 7 * X ^ 4 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 5
  · interval_cases k <;> norm_num [hF, closed4]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
    simp only [show 0 ≤ j + 5 by omega, show 1 ≤ j + 5 by omega, show 2 ≤ j + 5 by omega,
      show 3 ≤ j + 5 by omega, show 4 ≤ j + 5 by omega,
      show j + 5 - 0 = j + 5 by omega, show j + 5 - 1 = j + 4 by omega,
      show j + 5 - 2 = j + 3 by omega, show j + 5 - 3 = j + 2 by omega,
      show j + 5 - 4 = j + 1 by omega,
      show ¬ (j + 5 = 1) by omega, show ¬ (j + 5 = 2) by omega, show ¬ (j + 5 = 3) by omega,
      show ¬ (j + 5 = 4) by omega, show ¬ (j + 5 = 0) by omega,
      show ¬ (j + 4 = 0) by omega, show ¬ (j + 3 = 0) by omega,
      show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega, if_true, if_false, hF]
    rw [closed4 (j + 5) (by omega), closed4 (j + 4) (by omega), closed4 (j + 3) (by omega),
      closed4 (j + 2) (by omega), closed4 (j + 1) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a201975.main :=
  ⟨OMA.Helpers.gen_fun4, OMA.Helpers.recurrence4⟩
