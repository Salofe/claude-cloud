import OMAStatements.S_oeis_a201371
import Mathlib

/-!
Proof of Barker's g.f. and recurrence for A201371 (n X 4 binary arrays whose rows and columns
are lexicographically nondecreasing read forwards and nonincreasing read backwards).

Rows: the row conditions relate consecutive rows (`PLe201371`), read on the codes of rows as
`c ≤ e` and `cRev e ≤ cRev c`. Columns: each pair of adjacent columns `u, v` has a state
`pst201371 u v` (0 if equal; 3 if `u` read backwards is smaller; else 1 if `u < v`; else 2), and
the column conditions hold iff the state is at most 1. Putting a row on top changes the states by
`stp201371`. Removing the first row gives a transfer recursion `g (n + 1) = Mop (g n)` over the
16 row codes and the 27 live state triples, and `a (n + 1) = Aop (g n)`. A table `K j` (j < 5)
satisfies `Mop (K j) = K j + K (j + 1)`, `K 5 = 0`, `g 1 = K 0` (kernel checks), so
`g (n + 1) = Sum_j C(n, j) K j` and `a (m + 2) = 5 + 9 m + 13 C(m,2) + 9 C(m,3) + 2 C(m,4)`,
with `a 1 = 2`. The recurrence and the g.f. follow from this quartic.
-/

namespace OMA.Helpers

open OMA.S_oeis_a201371 Finset

/-- A row of the array: four entries in {0, 1}. -/
abbrev Row201371 := Fin 4 → Fin 2

theorem lt_iff201371 {m : ℕ} (x y : Fin m → Fin 2) :
    toLex x < toLex y ↔ ∃ i, (∀ j, j < i → x j = y j) ∧ x i < y i := Iff.rfl

theorem le_iff201371 {m : ℕ} (x y : Fin m → Fin 2) :
    toLex x ≤ toLex y ↔ toLex x < toLex y ∨ x = y := by
  rw [← toLex_inj]
  exact le_iff_lt_or_eq

theorem lexLE_iff201371 {m : ℕ} (x y : Fin m → Fin 2) : lexLE x y ↔ toLex x ≤ toLex y := by
  rw [le_iff201371, lt_iff201371]
  unfold lexLE
  exact Or.comm

theorem cons_lt201371 {m : ℕ} (x y : Fin 2) (u v : Fin m → Fin 2) :
    toLex (Fin.cons x u : Fin (m + 1) → Fin 2) < toLex (Fin.cons y v : Fin (m + 1) → Fin 2) ↔
      x < y ∨ (x = y ∧ toLex u < toLex v) := by
  rw [lt_iff201371, lt_iff201371]
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

theorem snoc_lt201371 {m : ℕ} (x y : Fin 2) (u v : Fin m → Fin 2) :
    toLex (Fin.snoc u x : Fin (m + 1) → Fin 2) < toLex (Fin.snoc v y : Fin (m + 1) → Fin 2) ↔
      toLex u < toLex v ∨ (u = v ∧ x < y) := by
  rw [lt_iff201371, lt_iff201371]
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

theorem bwd_bwd201371 {m : ℕ} (u : Fin m → Fin 2) : bwd (bwd u) = u := by
  funext i
  simp [bwd]

theorem bwd_inj201371 {m : ℕ} {u v : Fin m → Fin 2} : bwd u = bwd v ↔ u = v := by
  constructor
  · intro h
    rw [← bwd_bwd201371 u, h, bwd_bwd201371]
  · rintro rfl
    rfl

theorem bwd_cons201371 {m : ℕ} (x : Fin 2) (u : Fin m → Fin 2) :
    bwd (Fin.cons x u : Fin (m + 1) → Fin 2) = Fin.snoc (bwd u) x := by
  funext i
  exact Fin.cons_rev x u i

/-- The state of the pair of columns `u, v`: 0 if `u = v`; otherwise 3 if `u` read backwards is
lexicographically smaller than `v` read backwards, else 1 if `u < v`, else 2. -/
noncomputable def pst201371 {m : ℕ} (u v : Fin m → Fin 2) : ℕ := by
  classical
  exact if u = v then 0 else if toLex (bwd u) < toLex (bwd v) then 3
    else if toLex u < toLex v then 1 else 2

/-- How the state of a pair of columns changes when the entries `x, y` are put on top. -/
def stp201371 (x y s : ℕ) : ℕ :=
  if x = y then s else if x < y then (if s = 1 ∨ s = 2 then 1 else 3) else (if s = 3 then 3 else 2)

theorem pst201371_le {m : ℕ} (u v : Fin m → Fin 2) : pst201371 u v ≤ 3 := by
  unfold pst201371
  split_ifs <;> omega

theorem pst201371_cons {m : ℕ} (x y : Fin 2) (u v : Fin m → Fin 2) :
    pst201371 (Fin.cons x u : Fin (m + 1) → Fin 2) (Fin.cons y v) =
      stp201371 x.val y.val (pst201371 u v) := by
  classical
  unfold pst201371 stp201371
  simp only [bwd_cons201371, snoc_lt201371, cons_lt201371, Fin.cons_inj, bwd_inj201371]
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

theorem pst201371_zero (u v : Fin 0 → Fin 2) : pst201371 u v = 0 := by
  have : u = v := funext fun i => Fin.elim0 i
  unfold pst201371
  rw [if_pos this]

/-- The column condition on a pair of columns `u, v`. -/
theorem colpair201371 {m : ℕ} (u v : Fin m → Fin 2) :
    (lexLE u v ∧ lexLE (bwd v) (bwd u)) ↔ pst201371 u v ≤ 1 := by
  classical
  rw [lexLE_iff201371, lexLE_iff201371]
  unfold pst201371
  by_cases huv : u = v
  · subst huv
    simp
  · rw [if_neg huv]
    have e1 : toLex u ≤ toLex v ↔ toLex u < toLex v := by
      rw [le_iff201371]
      exact ⟨fun h => h.resolve_right huv, Or.inl⟩
    have e2 : toLex (bwd v) ≤ toLex (bwd u) ↔ ¬ toLex (bwd u) < toLex (bwd v) := not_lt.symm
    rw [e1, e2]
    split_ifs with h1 h2
    · simp [h1]
    · simp [h1, h2]
    · simp [h1, h2]

/-- The row conditions between a row `r` and the next row `s`. -/
def PLe201371 (r s : Row201371) : Prop := lexLE r s ∧ lexLE (bwd s) (bwd r)

/-- The row conditions between consecutive rows of `B`. -/
def RowsOK201371 {n : ℕ} (B : Fin n → Row201371) : Prop :=
  ∀ i i' : Fin n, i.val + 1 = i'.val → PLe201371 (B i) (B i')

theorem rowsOK201371_cons {n : ℕ} (r : Row201371) (B : Fin n → Row201371) :
    RowsOK201371 (Fin.cons r B : Fin (n + 1) → Row201371) ↔
      (∀ i : Fin n, i.val = 0 → PLe201371 r (B i)) ∧ RowsOK201371 B := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i i' hii => ?_⟩
    · have := h 0 i.succ (by simp [hi])
      simpa using this
    · have := h i.succ i'.succ (by simp; omega)
      simpa using this
  · rintro ⟨h1, h2⟩ i i' hii
    cases i using Fin.cases with
    | zero =>
      cases i' using Fin.cases with
      | zero => simp at hii
      | succ j =>
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact h1 j (by simp at hii; omega)
    | succ k =>
      cases i' using Fin.cases with
      | zero => simp at hii
      | succ k' =>
        simp only [Fin.cons_succ]
        exact h2 k k' (by simp at hii; omega)

/-- Column `j` of `B`, read top to bottom. -/
def col201371 {n : ℕ} (B : Fin n → Row201371) (j : Fin 4) : Fin n → Fin 2 := fun i => B i j

theorem col201371_cons {n : ℕ} (r : Row201371) (B : Fin n → Row201371) (j : Fin 4) :
    col201371 (Fin.cons r B : Fin (n + 1) → Row201371) j = Fin.cons (r j) (col201371 B j) := by
  funext i
  cases i using Fin.cases <;> rfl

theorem good_iff201371 {n : ℕ} (A : Fin n → Row201371) :
    good A ↔ RowsOK201371 A ∧ pst201371 (col201371 A 0) (col201371 A 1) ≤ 1 ∧
      pst201371 (col201371 A 1) (col201371 A 2) ≤ 1 ∧
      pst201371 (col201371 A 2) (col201371 A 3) ≤ 1 := by
  unfold good
  rw [← colpair201371, ← colpair201371, ← colpair201371]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2 0 1 rfl, h2 1 2 rfl, h2 2 3 rfl⟩
  · rintro ⟨h1, c1, c2, c3⟩
    refine ⟨h1, fun j j' hj => ?_⟩
    fin_cases j <;> fin_cases j' <;> simp at hj
    · exact c1
    · exact c2
    · exact c3

/-- The row read as a number in base 2, left entry most significant. -/
def code201371 (r : Row201371) : ℕ := 8 * (r 0 : ℕ) + 4 * (r 1 : ℕ) + 2 * (r 2 : ℕ) + (r 3 : ℕ)

def e0_201371 (c : ℕ) : ℕ := c / 8
def e1_201371 (c : ℕ) : ℕ := c / 4 % 2
def e2_201371 (c : ℕ) : ℕ := c / 2 % 2
def e3_201371 (c : ℕ) : ℕ := c % 2

/-- The code of the reversed row. -/
def cRev201371 (c : ℕ) : ℕ :=
  8 * e3_201371 c + 4 * e2_201371 c + 2 * e1_201371 c + e0_201371 c

/-- The row conditions, on codes. -/
def ple201371 (c e : ℕ) : Prop := c ≤ e ∧ cRev201371 e ≤ cRev201371 c

instance (c e : ℕ) : Decidable (ple201371 c e) := by unfold ple201371; infer_instance

theorem code201371_lt (r : Row201371) : code201371 r < 16 := by
  unfold code201371
  have := (r 0).isLt
  have := (r 1).isLt
  have := (r 2).isLt
  have := (r 3).isLt
  omega

theorem e0_code201371 (r : Row201371) : e0_201371 (code201371 r) = (r 0 : ℕ) := by
  unfold e0_201371 code201371
  have := (r 1).isLt
  have := (r 2).isLt
  have := (r 3).isLt
  omega

theorem e1_code201371 (r : Row201371) : e1_201371 (code201371 r) = (r 1 : ℕ) := by
  unfold e1_201371 code201371
  have := (r 1).isLt
  have := (r 2).isLt
  have := (r 3).isLt
  omega

theorem e2_code201371 (r : Row201371) : e2_201371 (code201371 r) = (r 2 : ℕ) := by
  unfold e2_201371 code201371
  have := (r 2).isLt
  have := (r 3).isLt
  omega

theorem e3_code201371 (r : Row201371) : e3_201371 (code201371 r) = (r 3 : ℕ) := by
  unfold e3_201371 code201371
  have := (r 3).isLt
  omega

theorem cRev_code201371 (r : Row201371) : cRev201371 (code201371 r) = code201371 (bwd r) := by
  unfold cRev201371
  rw [e0_code201371, e1_code201371, e2_code201371, e3_code201371]
  rfl

theorem code201371_inj {r s : Row201371} (h : code201371 r = code201371 s) : r = s := by
  have f0 := e0_code201371 r
  have f1 := e1_code201371 r
  have f2 := e2_code201371 r
  have f3 := e3_code201371 r
  rw [h, e0_code201371] at f0
  rw [h, e1_code201371] at f1
  rw [h, e2_code201371] at f2
  rw [h, e3_code201371] at f3
  funext j
  fin_cases j
  · exact Fin.ext f0.symm
  · exact Fin.ext f1.symm
  · exact Fin.ext f2.symm
  · exact Fin.ext f3.symm

theorem lex4_lt201371 (r s : Row201371) :
    toLex r < toLex s ↔ r 0 < s 0 ∨ (r 0 = s 0 ∧ (r 1 < s 1 ∨ (r 1 = s 1 ∧
      (r 2 < s 2 ∨ (r 2 = s 2 ∧ r 3 < s 3))))) := by
  have e : ∀ u : Row201371,
      u = Fin.cons (u 0) (Fin.cons (u 1) (Fin.cons (u 2) (Fin.cons (u 3) Fin.elim0))) := by
    intro u
    funext j
    fin_cases j <;> rfl
  conv_lhs => rw [e r, e s]
  simp only [cons_lt201371]
  have hz : ¬ toLex (Fin.elim0 : Fin 0 → Fin 2) < toLex (Fin.elim0 : Fin 0 → Fin 2) :=
    lt_irrefl _
  simp only [hz, and_false, or_false]

theorem row_lt_iff201371 (r s : Row201371) : toLex r < toLex s ↔ code201371 r < code201371 s := by
  rw [lex4_lt201371]
  simp only [Fin.lt_def, Fin.ext_iff]
  unfold code201371
  have := (r 0).isLt
  have := (r 1).isLt
  have := (r 2).isLt
  have := (r 3).isLt
  have := (s 0).isLt
  have := (s 1).isLt
  have := (s 2).isLt
  have := (s 3).isLt
  omega

theorem row_le_iff201371 (r s : Row201371) :
    toLex r ≤ toLex s ↔ code201371 r ≤ code201371 s := by
  rw [le_iff201371, row_lt_iff201371, Nat.le_iff_lt_or_eq]
  constructor
  · rintro (h | rfl)
    · exact Or.inl h
    · exact Or.inr rfl
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (code201371_inj h)

theorem PLe_iff201371 (r s : Row201371) :
    PLe201371 r s ↔ ple201371 (code201371 r) (code201371 s) := by
  unfold PLe201371 ple201371
  rw [lexLE_iff201371, lexLE_iff201371, row_le_iff201371, row_le_iff201371, cRev_code201371,
    cRev_code201371]

instance (r s : Row201371) : Decidable (PLe201371 r s) :=
  decidable_of_iff _ (PLe_iff201371 r s).symm

theorem image_code201371 : (Finset.univ : Finset Row201371).image code201371 = range 16 := by
  apply Finset.eq_of_subset_of_card_le
  · intro c hc
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_range.mpr (code201371_lt r)
  · rw [Finset.card_image_of_injective _ (fun r s h => code201371_inj h), Finset.card_univ]
    simp

theorem sum_rows201371 {M : Type*} [AddCommMonoid M] (φ : ℕ → M) :
    ∑ r : Row201371, φ (code201371 r) = ∑ c ∈ range 16, φ c := by
  rw [← image_code201371, Finset.sum_image (fun r _ s _ h => code201371_inj h)]

theorem stp201371_three (x y : ℕ) : stp201371 x y 3 = 3 := by
  unfold stp201371
  split_ifs <;> omega

/-- Split a count according to the value (at most 3) of a function `p`, when the condition `Q`
on this value excludes the value 3. -/
theorem split1_201371 {X : Type*} [Fintype X] (P : X → Prop) [DecidablePred P] (p : X → ℕ)
    (h : ∀ x, p x ≤ 3) (Q : ℕ → Prop) [DecidablePred Q] (hQ : ¬ Q 3) :
    (∑ x, if P x ∧ Q (p x) then 1 else 0) =
      ∑ t ∈ range 3, if Q t then (∑ x, if P x ∧ p x = t then 1 else 0) else 0 := by
  have key : ∀ x, (if P x ∧ Q (p x) then 1 else 0) =
      ∑ t ∈ range 3, if Q t then (if P x ∧ p x = t then 1 else 0) else 0 := by
    intro x
    rcases (show p x < 3 ∨ p x = 3 by have := h x; omega) with c | c
    · rw [Finset.sum_eq_single (p x)]
      · by_cases hP : P x <;> by_cases q : Q (p x) <;> simp [hP, q]
      · intro t _ ht
        have : p x ≠ t := Ne.symm ht
        simp [this]
      · intro hn
        exact absurd (Finset.mem_range.mpr c) hn
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

/-- Split a count according to the values of three functions. -/
theorem split3_201371 {X : Type*} [Fintype X] (P : X → Prop) [DecidablePred P]
    (p1 p2 p3 : X → ℕ) (h1 : ∀ x, p1 x ≤ 3) (h2 : ∀ x, p2 x ≤ 3) (h3 : ∀ x, p3 x ≤ 3)
    (Q1 Q2 Q3 : ℕ → Prop) [DecidablePred Q1] [DecidablePred Q2] [DecidablePred Q3]
    (hQ1 : ¬ Q1 3) (hQ2 : ¬ Q2 3) (hQ3 : ¬ Q3 3) :
    (∑ x, if P x ∧ Q1 (p1 x) ∧ Q2 (p2 x) ∧ Q3 (p3 x) then 1 else 0) =
      ∑ t1 ∈ range 3, if Q1 t1 then ∑ t2 ∈ range 3, if Q2 t2 then
        ∑ t3 ∈ range 3, if Q3 t3 then
          (∑ x, if P x ∧ p1 x = t1 ∧ p2 x = t2 ∧ p3 x = t3 then 1 else 0) else 0
        else 0 else 0 := by
  have s1 : (∑ x, if P x ∧ Q1 (p1 x) ∧ Q2 (p2 x) ∧ Q3 (p3 x) then 1 else 0) =
      ∑ x, if (P x ∧ Q2 (p2 x) ∧ Q3 (p3 x)) ∧ Q1 (p1 x) then 1 else 0 :=
    Finset.sum_congr rfl fun x _ => if_congr (by tauto) rfl rfl
  rw [s1, split1_201371 _ p1 h1 Q1 hQ1]
  refine Finset.sum_congr rfl fun t1 _ => if_congr Iff.rfl ?_ rfl
  have s2 : (∑ x, if (P x ∧ Q2 (p2 x) ∧ Q3 (p3 x)) ∧ p1 x = t1 then 1 else 0) =
      ∑ x, if (P x ∧ p1 x = t1 ∧ Q3 (p3 x)) ∧ Q2 (p2 x) then 1 else 0 :=
    Finset.sum_congr rfl fun x _ => if_congr (by tauto) rfl rfl
  rw [s2, split1_201371 _ p2 h2 Q2 hQ2]
  refine Finset.sum_congr rfl fun t2 _ => if_congr Iff.rfl ?_ rfl
  have s3 : (∑ x, if (P x ∧ p1 x = t1 ∧ Q3 (p3 x)) ∧ p2 x = t2 then 1 else 0) =
      ∑ x, if (P x ∧ p1 x = t1 ∧ p2 x = t2) ∧ Q3 (p3 x) then 1 else 0 :=
    Finset.sum_congr rfl fun x _ => if_congr (by tauto) rfl rfl
  rw [s3, split1_201371 _ p3 h3 Q3 hQ3]
  refine Finset.sum_congr rfl fun t3 _ => if_congr Iff.rfl ?_ rfl
  exact Finset.sum_congr rfl fun x _ => if_congr (by tauto) rfl rfl

/-- The arrays `B` with `n` rows satisfying the row conditions, whose first row (if any) may
follow the row `r`, and whose three pairs of adjacent columns have the states `s1, s2, s3`. -/
noncomputable def G201371 (n : ℕ) (r : Row201371) (s1 s2 s3 : ℕ) : ℕ := by
  classical
  exact ∑ B : Fin n → Row201371, if RowsOK201371 B ∧ (∀ i : Fin n, i.val = 0 → PLe201371 r (B i)) ∧
    pst201371 (col201371 B 0) (col201371 B 1) = s1 ∧
    pst201371 (col201371 B 1) (col201371 B 2) = s2 ∧
    pst201371 (col201371 B 2) (col201371 B 3) = s3 then 1 else 0

theorem rowsOK201371_zero (B : Fin 0 → Row201371) : RowsOK201371 B := fun i => Fin.elim0 i

theorem G201371_zero (r : Row201371) (s1 s2 s3 : ℕ) :
    G201371 0 r s1 s2 s3 = if s1 = 0 ∧ s2 = 0 ∧ s3 = 0 then 1 else 0 := by
  classical
  unfold G201371
  rw [Fintype.sum_unique]
  refine if_congr ?_ rfl rfl
  simp only [pst201371_zero, rowsOK201371_zero, true_and, IsEmpty.forall_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.symm, h2.symm, h3.symm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.symm, h2.symm, h3.symm⟩

theorem first201371_cons {n : ℕ} (r r' : Row201371) (B : Fin n → Row201371) :
    (∀ i : Fin (n + 1), i.val = 0 → PLe201371 r ((Fin.cons r' B : Fin (n + 1) → Row201371) i))
      ↔ PLe201371 r r' := by
  constructor
  · intro h
    simpa using h 0 rfl
  · intro h i hi
    obtain rfl : i = 0 := Fin.ext hi
    simpa using h

theorem G201371_succ (n : ℕ) (r : Row201371) (s1 s2 s3 : ℕ) (hs1 : s1 < 3) (hs2 : s2 < 3)
    (hs3 : s3 < 3) :
    G201371 (n + 1) r s1 s2 s3 = ∑ r' : Row201371, if PLe201371 r r' then
      ∑ t1 ∈ range 3, if stp201371 (r' 0) (r' 1) t1 = s1 then
        ∑ t2 ∈ range 3, if stp201371 (r' 1) (r' 2) t2 = s2 then
          ∑ t3 ∈ range 3, if stp201371 (r' 2) (r' 3) t3 = s3 then G201371 n r' t1 t2 t3
          else 0
        else 0
      else 0
    else 0 := by
  classical
  unfold G201371
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row201371).symm _
    (fun x => if RowsOK201371 (Fin.cons x.1 x.2 : Fin (n + 1) → Row201371) ∧
      (∀ i : Fin (n + 1), i.val = 0 →
        PLe201371 r ((Fin.cons x.1 x.2 : Fin (n + 1) → Row201371) i)) ∧
      pst201371 (col201371 (Fin.cons x.1 x.2 : Fin (n + 1) → Row201371) 0)
        (col201371 (Fin.cons x.1 x.2 : Fin (n + 1) → Row201371) 1) = s1 ∧
      pst201371 (col201371 (Fin.cons x.1 x.2 : Fin (n + 1) → Row201371) 1)
        (col201371 (Fin.cons x.1 x.2 : Fin (n + 1) → Row201371) 2) = s2 ∧
      pst201371 (col201371 (Fin.cons x.1 x.2 : Fin (n + 1) → Row201371) 2)
        (col201371 (Fin.cons x.1 x.2 : Fin (n + 1) → Row201371) 3) = s3 then 1 else 0)
    (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r' _ => ?_
  simp only [first201371_cons, rowsOK201371_cons, col201371_cons, pst201371_cons]
  by_cases h : PLe201371 r r'
  · rw [if_pos h]
    have e : ∀ B : Fin n → Row201371,
        (if ((∀ i : Fin n, i.val = 0 → PLe201371 r' (B i)) ∧ RowsOK201371 B) ∧ PLe201371 r r' ∧
          stp201371 (r' 0) (r' 1) (pst201371 (col201371 B 0) (col201371 B 1)) = s1 ∧
          stp201371 (r' 1) (r' 2) (pst201371 (col201371 B 1) (col201371 B 2)) = s2 ∧
          stp201371 (r' 2) (r' 3) (pst201371 (col201371 B 2) (col201371 B 3)) = s3
          then 1 else 0) =
        if (RowsOK201371 B ∧ ∀ i : Fin n, i.val = 0 → PLe201371 r' (B i)) ∧
          stp201371 (r' 0) (r' 1) (pst201371 (col201371 B 0) (col201371 B 1)) = s1 ∧
          stp201371 (r' 1) (r' 2) (pst201371 (col201371 B 1) (col201371 B 2)) = s2 ∧
          stp201371 (r' 2) (r' 3) (pst201371 (col201371 B 2) (col201371 B 3)) = s3
          then 1 else 0 := by
      intro B
      refine if_congr ?_ rfl rfl
      tauto
    rw [Finset.sum_congr rfl (fun B _ => e B)]
    rw [split3_201371 (fun B => RowsOK201371 B ∧ ∀ i : Fin n, i.val = 0 → PLe201371 r' (B i))
      (fun B => pst201371 (col201371 B 0) (col201371 B 1))
      (fun B => pst201371 (col201371 B 1) (col201371 B 2))
      (fun B => pst201371 (col201371 B 2) (col201371 B 3))
      (fun B => pst201371_le _ _) (fun B => pst201371_le _ _) (fun B => pst201371_le _ _)
      (fun t => stp201371 (r' 0) (r' 1) t = s1) (fun t => stp201371 (r' 1) (r' 2) t = s2)
      (fun t => stp201371 (r' 2) (r' 3) t = s3)
      (by simp only [stp201371_three]; omega) (by simp only [stp201371_three]; omega)
      (by simp only [stp201371_three]; omega)]
    refine Finset.sum_congr rfl fun t1 _ => if_congr Iff.rfl ?_ rfl
    refine Finset.sum_congr rfl fun t2 _ => if_congr Iff.rfl ?_ rfl
    refine Finset.sum_congr rfl fun t3 _ => if_congr Iff.rfl ?_ rfl
    exact Finset.sum_congr rfl fun B _ => if_congr (by tauto) rfl rfl
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    tauto

/-- One step of the transfer recursion, on codes of rows. -/
def Mop201371 (f : ℕ → ℕ → ℕ → ℕ → ℕ) (c s1 s2 s3 : ℕ) : ℕ :=
  ∑ e ∈ range 16, if ple201371 c e then
    ∑ t1 ∈ range 3, if stp201371 (e0_201371 e) (e1_201371 e) t1 = s1 then
      ∑ t2 ∈ range 3, if stp201371 (e1_201371 e) (e2_201371 e) t2 = s2 then
        ∑ t3 ∈ range 3, if stp201371 (e2_201371 e) (e3_201371 e) t3 = s3 then f e t1 t2 t3
        else 0
      else 0
    else 0
  else 0

/-- The transfer counts on codes. -/
def g201371 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, s1, s2, s3 => if s1 = 0 ∧ s2 = 0 ∧ s3 = 0 then 1 else 0
  | n + 1, c, s1, s2, s3 => Mop201371 (g201371 n) c s1 s2 s3

theorem G_eq_g201371 (n : ℕ) : ∀ (r : Row201371) (s1 s2 s3 : ℕ), s1 < 3 → s2 < 3 → s3 < 3 →
    G201371 n r s1 s2 s3 = g201371 n (code201371 r) s1 s2 s3 := by
  induction n with
  | zero =>
    intro r s1 s2 s3 _ _ _
    rw [G201371_zero]
    rfl
  | succ n ih =>
    intro r s1 s2 s3 hs1 hs2 hs3
    rw [G201371_succ n r s1 s2 s3 hs1 hs2 hs3]
    show _ = Mop201371 (g201371 n) (code201371 r) s1 s2 s3
    unfold Mop201371
    rw [← sum_rows201371]
    refine Finset.sum_congr rfl fun r' _ => ?_
    simp only [e0_code201371, e1_code201371, e2_code201371, e3_code201371]
    refine if_congr (PLe_iff201371 r r') ?_ rfl
    refine Finset.sum_congr rfl fun t1 ht1 => if_congr Iff.rfl ?_ rfl
    refine Finset.sum_congr rfl fun t2 ht2 => if_congr Iff.rfl ?_ rfl
    refine Finset.sum_congr rfl fun t3 ht3 => if_congr Iff.rfl ?_ rfl
    exact ih r' t1 t2 t3 (Finset.mem_range.mp ht1) (Finset.mem_range.mp ht2)
      (Finset.mem_range.mp ht3)

/-- The count of the arrays with `n + 1` rows from the transfer counts of their last `n` rows. -/
def Aop201371 (f : ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=
  ∑ e ∈ range 16, ∑ t1 ∈ range 3, if stp201371 (e0_201371 e) (e1_201371 e) t1 ≤ 1 then
    ∑ t2 ∈ range 3, if stp201371 (e1_201371 e) (e2_201371 e) t2 ≤ 1 then
      ∑ t3 ∈ range 3, if stp201371 (e2_201371 e) (e3_201371 e) t3 ≤ 1 then f e t1 t2 t3 else 0
    else 0
  else 0

theorem a_succ201371 (n : ℕ) : a (n + 1) = Aop201371 (g201371 n) := by
  classical
  have h1 : a (n + 1) = ∑ A : Fin (n + 1) → Row201371, if RowsOK201371 A ∧
      pst201371 (col201371 A 0) (col201371 A 1) ≤ 1 ∧
      pst201371 (col201371 A 1) (col201371 A 2) ≤ 1 ∧
      pst201371 (col201371 A 2) (col201371 A 3) ≤ 1 then 1 else 0 := by
    unfold a
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun A _ => if_congr (good_iff201371 A) rfl rfl
  rw [h1, Fintype.sum_equiv (Fin.consEquiv fun _ => Row201371).symm _
    (fun x => if RowsOK201371 (Fin.cons x.1 x.2 : Fin (n + 1) → Row201371) ∧
      pst201371 (col201371 (Fin.cons x.1 x.2 : Fin (n + 1) → Row201371) 0)
        (col201371 (Fin.cons x.1 x.2 : Fin (n + 1) → Row201371) 1) ≤ 1 ∧
      pst201371 (col201371 (Fin.cons x.1 x.2 : Fin (n + 1) → Row201371) 1)
        (col201371 (Fin.cons x.1 x.2 : Fin (n + 1) → Row201371) 2) ≤ 1 ∧
      pst201371 (col201371 (Fin.cons x.1 x.2 : Fin (n + 1) → Row201371) 2)
        (col201371 (Fin.cons x.1 x.2 : Fin (n + 1) → Row201371) 3) ≤ 1 then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  unfold Aop201371
  rw [← sum_rows201371]
  refine Finset.sum_congr rfl fun r' _ => ?_
  simp only [e0_code201371, e1_code201371, e2_code201371, e3_code201371]
  simp only [rowsOK201371_cons, col201371_cons, pst201371_cons]
  have e : ∀ B : Fin n → Row201371,
      (if ((∀ i : Fin n, i.val = 0 → PLe201371 r' (B i)) ∧ RowsOK201371 B) ∧
        stp201371 (r' 0) (r' 1) (pst201371 (col201371 B 0) (col201371 B 1)) ≤ 1 ∧
        stp201371 (r' 1) (r' 2) (pst201371 (col201371 B 1) (col201371 B 2)) ≤ 1 ∧
        stp201371 (r' 2) (r' 3) (pst201371 (col201371 B 2) (col201371 B 3)) ≤ 1
        then 1 else 0) =
      if (RowsOK201371 B ∧ ∀ i : Fin n, i.val = 0 → PLe201371 r' (B i)) ∧
        stp201371 (r' 0) (r' 1) (pst201371 (col201371 B 0) (col201371 B 1)) ≤ 1 ∧
        stp201371 (r' 1) (r' 2) (pst201371 (col201371 B 1) (col201371 B 2)) ≤ 1 ∧
        stp201371 (r' 2) (r' 3) (pst201371 (col201371 B 2) (col201371 B 3)) ≤ 1
        then 1 else 0 := by
    intro B
    refine if_congr ?_ rfl rfl
    tauto
  rw [Finset.sum_congr rfl (fun B _ => e B)]
  rw [split3_201371 (fun B => RowsOK201371 B ∧ ∀ i : Fin n, i.val = 0 → PLe201371 r' (B i))
    (fun B => pst201371 (col201371 B 0) (col201371 B 1))
    (fun B => pst201371 (col201371 B 1) (col201371 B 2))
    (fun B => pst201371 (col201371 B 2) (col201371 B 3))
    (fun B => pst201371_le _ _) (fun B => pst201371_le _ _) (fun B => pst201371_le _ _)
    (fun t => stp201371 (r' 0) (r' 1) t ≤ 1) (fun t => stp201371 (r' 1) (r' 2) t ≤ 1)
    (fun t => stp201371 (r' 2) (r' 3) t ≤ 1)
    (by simp only [stp201371_three]; omega) (by simp only [stp201371_three]; omega)
    (by simp only [stp201371_three]; omega)]
  refine Finset.sum_congr rfl fun t1 ht1 => if_congr Iff.rfl ?_ rfl
  refine Finset.sum_congr rfl fun t2 ht2 => if_congr Iff.rfl ?_ rfl
  refine Finset.sum_congr rfl fun t3 ht3 => if_congr Iff.rfl ?_ rfl
  rw [← G_eq_g201371 n r' t1 t2 t3 (Finset.mem_range.mp ht1) (Finset.mem_range.mp ht2)
    (Finset.mem_range.mp ht3)]
  unfold G201371
  exact Finset.sum_congr rfl fun B _ => if_congr (by tauto) rfl rfl

/-- The coefficients `K j c (9 t1 + 3 t2 + t3)` of the transfer counts in the basis of binomial
coefficients: `g (n + 1) c t1 t2 t3 = Sum_{j < 5} C(n, j) K j c t1 t2 t3`. -/
def KT201371 : List (List (List ℕ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]

/-- The entry of the table. -/
def K201371 (j c t1 t2 t3 : ℕ) : ℕ := ((KT201371.getD j []).getD c []).getD (9 * t1 + 3 * t2 + t3) 0

theorem K201371_step0 : ∀ c < 16, ∀ s1 < 3, ∀ s2 < 3, ∀ s3 < 3,
    Mop201371 (K201371 0) c s1 s2 s3 = K201371 0 c s1 s2 s3 + K201371 1 c s1 s2 s3 := by
  decide +kernel

theorem K201371_step1 : ∀ c < 16, ∀ s1 < 3, ∀ s2 < 3, ∀ s3 < 3,
    Mop201371 (K201371 1) c s1 s2 s3 = K201371 1 c s1 s2 s3 + K201371 2 c s1 s2 s3 := by
  decide +kernel

theorem K201371_step2 : ∀ c < 16, ∀ s1 < 3, ∀ s2 < 3, ∀ s3 < 3,
    Mop201371 (K201371 2) c s1 s2 s3 = K201371 2 c s1 s2 s3 + K201371 3 c s1 s2 s3 := by
  decide +kernel

theorem K201371_step3 : ∀ c < 16, ∀ s1 < 3, ∀ s2 < 3, ∀ s3 < 3,
    Mop201371 (K201371 3) c s1 s2 s3 = K201371 3 c s1 s2 s3 + K201371 4 c s1 s2 s3 := by
  decide +kernel

theorem K201371_step4 : ∀ c < 16, ∀ s1 < 3, ∀ s2 < 3, ∀ s3 < 3,
    Mop201371 (K201371 4) c s1 s2 s3 = K201371 4 c s1 s2 s3 + K201371 5 c s1 s2 s3 := by
  decide +kernel

theorem K201371_step (j : ℕ) (hj : j < 5) : ∀ c < 16, ∀ s1 < 3, ∀ s2 < 3, ∀ s3 < 3,
    Mop201371 (K201371 j) c s1 s2 s3 = K201371 j c s1 s2 s3 + K201371 (j + 1) c s1 s2 s3 := by
  interval_cases j
  · exact K201371_step0
  · exact K201371_step1
  · exact K201371_step2
  · exact K201371_step3
  · exact K201371_step4

theorem K201371_five (c s1 s2 s3 : ℕ) : K201371 5 c s1 s2 s3 = 0 := rfl

theorem g201371_one : ∀ c < 16, ∀ s1 < 3, ∀ s2 < 3, ∀ s3 < 3,
    g201371 1 c s1 s2 s3 = K201371 0 c s1 s2 s3 := by
  decide +kernel

theorem Mop201371_congr {f f' : ℕ → ℕ → ℕ → ℕ → ℕ}
    (h : ∀ e < 16, ∀ t1 < 3, ∀ t2 < 3, ∀ t3 < 3, f e t1 t2 t3 = f' e t1 t2 t3)
    (c s1 s2 s3 : ℕ) : Mop201371 f c s1 s2 s3 = Mop201371 f' c s1 s2 s3 := by
  unfold Mop201371
  refine Finset.sum_congr rfl fun e he => if_congr Iff.rfl ?_ rfl
  refine Finset.sum_congr rfl fun t1 ht1 => if_congr Iff.rfl ?_ rfl
  refine Finset.sum_congr rfl fun t2 ht2 => if_congr Iff.rfl ?_ rfl
  refine Finset.sum_congr rfl fun t3 ht3 => if_congr Iff.rfl ?_ rfl
  exact h e (Finset.mem_range.mp he) t1 (Finset.mem_range.mp ht1) t2 (Finset.mem_range.mp ht2)
    t3 (Finset.mem_range.mp ht3)

theorem Mop201371_add (f f' : ℕ → ℕ → ℕ → ℕ → ℕ) (c s1 s2 s3 : ℕ) :
    Mop201371 (fun e t1 t2 t3 => f e t1 t2 t3 + f' e t1 t2 t3) c s1 s2 s3 =
      Mop201371 f c s1 s2 s3 + Mop201371 f' c s1 s2 s3 := by
  unfold Mop201371
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t1 _ => ?_
    split_ifs
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t2 _ => ?_
      split_ifs
      · rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun t3 _ => ?_
        split_ifs <;> simp
      · simp
    · simp
  · simp

theorem Mop201371_smul (w : ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℕ) (c s1 s2 s3 : ℕ) :
    Mop201371 (fun e t1 t2 t3 => w * f e t1 t2 t3) c s1 s2 s3 = w * Mop201371 f c s1 s2 s3 := by
  simp only [Mop201371, Finset.mul_sum, mul_ite, mul_zero]

theorem Mop201371_lin (S : Finset ℕ) (w : ℕ → ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
    (c s1 s2 s3 : ℕ) :
    Mop201371 (fun e t1 t2 t3 => ∑ j ∈ S, w j * F j e t1 t2 t3) c s1 s2 s3 =
      ∑ j ∈ S, w j * Mop201371 (F j) c s1 s2 s3 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Mop201371]
  | insert j S hj ih =>
    simp only [Finset.sum_insert hj]
    rw [Mop201371_add, Mop201371_smul, ih]

theorem Aop201371_congr {f f' : ℕ → ℕ → ℕ → ℕ → ℕ}
    (h : ∀ e < 16, ∀ t1 < 3, ∀ t2 < 3, ∀ t3 < 3, f e t1 t2 t3 = f' e t1 t2 t3) :
    Aop201371 f = Aop201371 f' := by
  unfold Aop201371
  refine Finset.sum_congr rfl fun e he => ?_
  refine Finset.sum_congr rfl fun t1 ht1 => if_congr Iff.rfl ?_ rfl
  refine Finset.sum_congr rfl fun t2 ht2 => if_congr Iff.rfl ?_ rfl
  refine Finset.sum_congr rfl fun t3 ht3 => if_congr Iff.rfl ?_ rfl
  exact h e (Finset.mem_range.mp he) t1 (Finset.mem_range.mp ht1) t2 (Finset.mem_range.mp ht2)
    t3 (Finset.mem_range.mp ht3)

theorem Aop201371_add (f f' : ℕ → ℕ → ℕ → ℕ → ℕ) :
    Aop201371 (fun e t1 t2 t3 => f e t1 t2 t3 + f' e t1 t2 t3) =
      Aop201371 f + Aop201371 f' := by
  unfold Aop201371
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t1 _ => ?_
  split_ifs
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t2 _ => ?_
    split_ifs
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t3 _ => ?_
      split_ifs <;> simp
    · simp
  · simp

theorem Aop201371_smul (w : ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℕ) :
    Aop201371 (fun e t1 t2 t3 => w * f e t1 t2 t3) = w * Aop201371 f := by
  simp only [Aop201371, Finset.mul_sum, mul_ite, mul_zero]

theorem Aop201371_lin (S : Finset ℕ) (w : ℕ → ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) :
    Aop201371 (fun e t1 t2 t3 => ∑ j ∈ S, w j * F j e t1 t2 t3) =
      ∑ j ∈ S, w j * Aop201371 (F j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Aop201371]
  | insert j S hj ih =>
    simp only [Finset.sum_insert hj]
    rw [Aop201371_add, Aop201371_smul, ih]

theorem g201371_closed (n : ℕ) : ∀ c < 16, ∀ s1 < 3, ∀ s2 < 3, ∀ s3 < 3,
    g201371 (n + 1) c s1 s2 s3 = ∑ j ∈ range 5, n.choose j * K201371 j c s1 s2 s3 := by
  induction n with
  | zero =>
    intro c hc s1 hs1 s2 hs2 s3 hs3
    rw [g201371_one c hc s1 hs1 s2 hs2 s3 hs3]
    simp [Finset.sum_range_succ]
  | succ n ih =>
    intro c hc s1 hs1 s2 hs2 s3 hs3
    show Mop201371 (g201371 (n + 1)) c s1 s2 s3 = _
    rw [Mop201371_congr (f' := fun e t1 t2 t3 => ∑ j ∈ range 5, n.choose j * K201371 j e t1 t2 t3)
      (fun e he t1 ht1 t2 ht2 t3 ht3 => ih e he t1 ht1 t2 ht2 t3 ht3), Mop201371_lin]
    rw [Finset.sum_congr rfl
      (fun j hj => by rw [K201371_step j (Finset.mem_range.mp hj) c hc s1 hs1 s2 hs2 s3 hs3])]
    have h5 := K201371_five c s1 s2 s3
    have p1 : (n + 1).choose 1 = n.choose 0 + n.choose 1 := Nat.choose_succ_succ n 0
    have p2 : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ n 1
    have p3 : (n + 1).choose 3 = n.choose 2 + n.choose 3 := Nat.choose_succ_succ n 2
    have p4 : (n + 1).choose 4 = n.choose 3 + n.choose 4 := Nat.choose_succ_succ n 3
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, p1, p2, p3, p4,
      Nat.choose_zero_right, h5]
    ring

theorem cK201371 : Aop201371 (K201371 0) = 5 ∧ Aop201371 (K201371 1) = 9 ∧
    Aop201371 (K201371 2) = 13 ∧ Aop201371 (K201371 3) = 9 ∧ Aop201371 (K201371 4) = 2 := by
  decide +kernel

theorem a201371_one : a 1 = 2 := by
  rw [a_succ201371]
  decide +kernel

theorem a201371_two (m : ℕ) :
    a (m + 2) = 5 + 9 * m + 13 * m.choose 2 + 9 * m.choose 3 + 2 * m.choose 4 := by
  rw [a_succ201371, Aop201371_congr
    (f' := fun e t1 t2 t3 => ∑ j ∈ range 5, m.choose j * K201371 j e t1 t2 t3)
    (fun e he t1 ht1 t2 ht2 t3 ht3 => g201371_closed m e he t1 ht1 t2 ht2 t3 ht3),
    Aop201371_lin]
  obtain ⟨c0, c1, c2, c3, c4⟩ := cK201371
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3, c4,
    Nat.choose_zero_right, Nat.choose_one_right]
  ring

theorem choose2_201371 (m : ℕ) : (m.choose 2 : ℚ) = m * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, Nat.choose_one_right]
    push_cast
    ring

theorem choose3_201371 (m : ℕ) : (m.choose 3 : ℚ) = m * (m - 1) * (m - 2) / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose2_201371]
    push_cast
    ring

theorem choose4_201371 (m : ℕ) :
    (m.choose 4 : ℚ) = m * (m - 1) * (m - 2) * (m - 3) / 24 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose3_201371]
    push_cast
    ring

/-- The polynomial giving `a n` for `n ≥ 1`. -/
def P201371 (x : ℚ) : ℚ :=
  5 + 9 * (x - 2) + 13 * (x - 2) * (x - 3) / 2 + 3 * (x - 2) * (x - 3) * (x - 4) / 2 +
    (x - 2) * (x - 3) * (x - 4) * (x - 5) / 12

theorem closedQ201371 (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = P201371 n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [a201371_one]
    unfold P201371
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [a201371_two]
    push_cast
    rw [choose2_201371, choose3_201371, choose4_201371]
    unfold P201371
    ring

theorem rec201371 (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  have h : ((a n : ℤ) : ℚ) = ((5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
      5 * a (n - 4) + a (n - 5) : ℤ) : ℚ) := by
    push_cast
    rw [closedQ201371 n (by omega), closedQ201371 (n - 1) (by omega),
      closedQ201371 (n - 2) (by omega), closedQ201371 (n - 3) (by omega),
      closedQ201371 (n - 4) (by omega), closedQ201371 (n - 5) (by omega)]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show 5 ≤ n by omega]
    unfold P201371
    ring
  exact_mod_cast h

open PowerSeries in
theorem gf_generic201371 (f : ℕ → ℚ) (h0 : f 0 = 0) (hf : ∀ n, 1 ≤ n → f n = P201371 n) :
    PowerSeries.mk f * (1 - X) ^ 5 = X * (2 - 5 * X + 9 * X ^ 2 - 4 * X ^ 3) := by
  have key : PowerSeries.mk f * (1 - X) ^ 5 =
      C 1 * (PowerSeries.mk f * X ^ 0) - C 5 * (PowerSeries.mk f * X ^ 1) +
        C 10 * (PowerSeries.mk f * X ^ 2) - C 10 * (PowerSeries.mk f * X ^ 3) +
        C 5 * (PowerSeries.mk f * X ^ 4) - C 1 * (PowerSeries.mk f * X ^ 5) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (2 - 5 * X + 9 * X ^ 2 - 4 * X ^ 3) =
      C 2 * X ^ 1 - C 5 * X ^ 2 + C 9 * X ^ 3 - C 4 * X ^ 4 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 6
  · interval_cases k <;> norm_num [h0, hf, P201371]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    simp only [show 0 ≤ j + 6 by omega, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega,
      show 3 ≤ j + 6 by omega, show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega,
      show j + 6 - 0 = j + 6 by omega, show j + 6 - 1 = j + 5 by omega,
      show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega,
      show j + 6 - 4 = j + 2 by omega, show j + 6 - 5 = j + 1 by omega,
      show ¬ (j + 6 = 1) by omega, show ¬ (j + 6 = 2) by omega, show ¬ (j + 6 = 3) by omega,
      show ¬ (j + 6 = 4) by omega, if_true, if_false]
    rw [hf (j + 6) (by omega), hf (j + 5) (by omega), hf (j + 4) (by omega),
      hf (j + 3) (by omega), hf (j + 2) (by omega), hf (j + 1) (by omega)]
    unfold P201371
    push_cast
    ring

open PowerSeries in
theorem gf201371 :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (2 - 5 * X + 9 * X ^ 2 - 4 * X ^ 3) := by
  apply gf_generic201371
  · simp
  · intro n hn
    rw [if_neg (by omega)]
    exact closedQ201371 n hn

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a201371.main :=
  ⟨OMA.Helpers.gf201371, OMA.Helpers.rec201371⟩
