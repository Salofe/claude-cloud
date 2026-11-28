import OMAStatements.S_oeis_a201695

/-!
Proof of Barker's g.f. and recurrence, and of Hardin's empirical formula, for A201695 (n X 3 0..2
arrays whose rows and columns are lexicographically nondecreasing read forwards and nonincreasing
read backwards).

Rows. Write `PLe r s` when the row `r` is lexicographically at most `s` read forwards and at
least `s` read backwards. This is a partial order on the 27 rows, and the two row conditions say
that the rows of the array form a chain for it (`RowsOK`). On the code `9 r0 + 3 r1 + r2` of a
row it reads `c ≤ e` and `cRev e ≤ cRev c`, where `cRev c` is the code of the reversed row
(`PLe_iff`).

Columns. The column conditions on two adjacent columns `u, v` say that `u ≤ v` read forwards and
`u ≥ v` read backwards. The state `pst u v` of the pair is 0 if `u = v`; otherwise it is 3 if
`u` read backwards is smaller than `v` read backwards, else 1 if `u < v` read forwards, else 2.
The conditions hold iff the state is 0 or 1 (`colpair_iff`). Putting the entries `x, y` on top of
`u, v` changes the state by `stpN x y` (`pst_cons`): it is unchanged if `x = y`; if `x < y`, the
states 1, 2 become 1 and the states 0, 3 become 3; if `x > y`, the states 0, 1, 2 become 2 and the
state 3 stays 3.

Transfer. Let `G n r s1 s2` count the arrays with `n` rows whose rows form a chain, all above the
row `r`, and whose column pairs have the states `s1, s2`. Removing the first row `r'` of an array
gives, for `s1, s2 < 3` (`G_succ`),
  `G (n + 1) r s1 s2 = Sum_{PLe r r'} Sum_{t1, t2 < 3, stpN t1 = s1, stpN t2 = s2} G n r' t1 t2`,
and `a (n + 1)` is the sum of `G n r' t1 t2` over the rows `r'` and the states `t1, t2 < 3` that
`r'` turns into accepted states (`a_succ`). On codes this is the recursion `g (n + 1) = Mop (g n)`
and `a (n + 1) = Aop (g n)`.

Closed form. A table `K j` (`j < 5`) of natural numbers satisfies `Mop (K j) = K j + K (j + 1)`,
with `K 5 = 0` and `g 1 = K 0` (finite checks by `decide +kernel`). By induction with Pascal's
rule, `g (n + 1) = Sum_{j < 5} C(n, j) K j`, hence
`a (n + 2) = 18 + 98 n + 181 C(n, 2) + 134 C(n, 3) + 36 C(n, 4)`, and `a 1 = 3`. This is Hardin's
polynomial for every `n ≥ 1`; the recurrence follows by substituting it, and the g.f. by comparing
coefficients (a polynomial of degree 4 has vanishing fifth difference).
-/

namespace OMA.Helpers

open OMA.S_oeis_a201695 Finset

/-- A row of the array: three entries in {0, 1, 2}. -/
abbrev R := Fin 3 → Fin 3

theorem lex_lt_iff {m : ℕ} (x y : Fin m → Fin 3) :
    toLex x < toLex y ↔ ∃ i, (∀ j, j < i → x j = y j) ∧ x i < y i := Iff.rfl

theorem lex_le_iff {m : ℕ} (x y : Fin m → Fin 3) :
    toLex x ≤ toLex y ↔ toLex x < toLex y ∨ x = y := by
  rw [← toLex_inj]
  exact le_iff_lt_or_eq

theorem lex_cons_lt {m : ℕ} (x y : Fin 3) (u v : Fin m → Fin 3) :
    toLex (Fin.cons x u : Fin (m + 1) → Fin 3) < toLex (Fin.cons y v : Fin (m + 1) → Fin 3) ↔
      x < y ∨ (x = y ∧ toLex u < toLex v) := by
  rw [lex_lt_iff, lex_lt_iff]
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

theorem lex_snoc_lt {m : ℕ} (x y : Fin 3) (u v : Fin m → Fin 3) :
    toLex (Fin.snoc u x : Fin (m + 1) → Fin 3) < toLex (Fin.snoc v y : Fin (m + 1) → Fin 3) ↔
      toLex u < toLex v ∨ (u = v ∧ x < y) := by
  rw [lex_lt_iff, lex_lt_iff]
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

theorem mono_cons {β : Type*} [Preorder β] {n : ℕ} (x : β) (f : Fin n → β) :
    Monotone (Fin.cons x f : Fin (n + 1) → β) ↔ (∀ i, x ≤ f i) ∧ Monotone f := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · simpa using h (Fin.zero_le i.succ)
    · simpa using h (Fin.succ_le_succ_iff.mpr hij)
  · rintro ⟨h1, h2⟩ i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact le_rfl
      | succ j => simpa using h1 j
    | succ i =>
      cases j using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ j => simpa using h2 (Fin.succ_le_succ_iff.mp hij)

theorem anti_cons {β : Type*} [Preorder β] {n : ℕ} (x : β) (f : Fin n → β) :
    Antitone (Fin.cons x f : Fin (n + 1) → β) ↔ (∀ i, f i ≤ x) ∧ Antitone f := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · simpa using h (Fin.zero_le i.succ)
    · simpa using h (Fin.succ_le_succ_iff.mpr hij)
  · rintro ⟨h1, h2⟩ i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact le_rfl
      | succ j => simpa using h1 j
    | succ i =>
      cases j using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ j => simpa using h2 (Fin.succ_le_succ_iff.mp hij)

/-- A word read backwards. -/
def rv {m : ℕ} (u : Fin m → Fin 3) : Fin m → Fin 3 := fun i => u (Fin.rev i)

theorem rv_rv {m : ℕ} (u : Fin m → Fin 3) : rv (rv u) = u := by
  funext i
  simp [rv]

theorem rv_inj {m : ℕ} {u v : Fin m → Fin 3} : rv u = rv v ↔ u = v := by
  constructor
  · intro h
    rw [← rv_rv u, h, rv_rv]
  · rintro rfl
    rfl

theorem rv_cons {m : ℕ} (x : Fin 3) (u : Fin m → Fin 3) :
    rv (Fin.cons x u : Fin (m + 1) → Fin 3) = Fin.snoc (rv u) x := by
  funext i
  exact Fin.cons_rev x u i

/-- The state of the pair of words `u, v` (two columns): 0 if `u = v`; otherwise 3 if `u` read
backwards is lexicographically smaller than `v` read backwards, else 1 if `u` is
lexicographically smaller than `v`, else 2. -/
noncomputable def pst {m : ℕ} (u v : Fin m → Fin 3) : ℕ := by
  classical
  exact if u = v then 0 else if toLex (rv u) < toLex (rv v) then 3
    else if toLex u < toLex v then 1 else 2

/-- How the state of a pair of columns changes when the entries `x, y` are put on top. -/
def stpN (x y s : ℕ) : ℕ :=
  if x = y then s else if x < y then (if s = 1 ∨ s = 2 then 1 else 3) else (if s = 3 then 3 else 2)

theorem pst_le {m : ℕ} (u v : Fin m → Fin 3) : pst u v ≤ 3 := by
  unfold pst
  split_ifs <;> omega

theorem pst_cons {m : ℕ} (x y : Fin 3) (u v : Fin m → Fin 3) :
    pst (Fin.cons x u : Fin (m + 1) → Fin 3) (Fin.cons y v) = stpN x.val y.val (pst u v) := by
  classical
  unfold pst stpN
  simp only [rv_cons, lex_snoc_lt, lex_cons_lt, Fin.cons_inj, rv_inj]
  have hxy : x = y ↔ x.val = y.val := Fin.val_inj.symm
  have hlt : x < y ↔ x.val < y.val := Fin.lt_def
  by_cases huv : u = v
  · subst huv
    have hirr : ¬ toLex (rv u) < toLex (rv u) := lt_irrefl _
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
    by_cases hr : toLex (rv u) < toLex (rv v)
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

theorem pst_zero (u v : Fin 0 → Fin 3) : pst u v = 0 := by
  have : u = v := funext fun i => Fin.elim0 i
  unfold pst
  rw [if_pos this]

/-- The column condition on a pair of columns `u, v`. -/
theorem colpair_iff {m : ℕ} (u v : Fin m → Fin 3) :
    (toLex u ≤ toLex v ∧ toLex (rv v) ≤ toLex (rv u)) ↔ pst u v ≤ 1 := by
  classical
  unfold pst
  by_cases huv : u = v
  · subst huv
    simp
  · have hne : rv u ≠ rv v := fun h => huv (rv_inj.mp h)
    rw [if_neg huv]
    have e1 : toLex u ≤ toLex v ↔ toLex u < toLex v := by
      rw [lex_le_iff]
      exact ⟨fun h => h.resolve_right huv, Or.inl⟩
    have e2 : toLex (rv v) ≤ toLex (rv u) ↔ ¬ toLex (rv u) < toLex (rv v) := not_lt.symm
    rw [e1, e2]
    split_ifs with h1 h2
    · simp [h1]
    · simp [h1, h2]
    · simp [h1, h2]


/-- The rows of `B`, read forwards, are lexicographically nondecreasing, and read backwards,
lexicographically nonincreasing. -/
def RowsOK {n : ℕ} (B : Fin n → R) : Prop :=
  Monotone (fun i => toLex (B i)) ∧ Antitone (fun i => toLex (rv (B i)))

/-- The order of the poset of rows: `r` is below `s` read forwards and above `s` read backwards. -/
def PLe (r s : R) : Prop := toLex r ≤ toLex s ∧ toLex (rv s) ≤ toLex (rv r)

theorem PLe_trans {r s t : R} (h1 : PLe r s) (h2 : PLe s t) : PLe r t :=
  ⟨le_trans h1.1 h2.1, le_trans h2.2 h1.2⟩

theorem RowsOK_cons {n : ℕ} (r : R) (B : Fin n → R) :
    RowsOK (Fin.cons r B : Fin (n + 1) → R) ↔ (∀ i, PLe r (B i)) ∧ RowsOK B := by
  unfold RowsOK PLe
  have h1 : (fun i => toLex ((Fin.cons r B : Fin (n + 1) → R) i)) =
      (Fin.cons (toLex r) (fun i => toLex (B i)) : Fin (n + 1) → Lex R) := by
    funext i
    cases i using Fin.cases <;> simp
  have h2 : (fun i => toLex (rv ((Fin.cons r B : Fin (n + 1) → R) i))) =
      (Fin.cons (toLex (rv r)) (fun i => toLex (rv (B i))) : Fin (n + 1) → Lex R) := by
    funext i
    cases i using Fin.cases <;> simp
  rw [h1, h2, mono_cons, anti_cons]
  constructor
  · rintro ⟨⟨a, b⟩, c, d⟩
    exact ⟨fun i => ⟨a i, c i⟩, b, d⟩
  · rintro ⟨h, b, d⟩
    exact ⟨⟨fun i => (h i).1, b⟩, fun i => (h i).2, d⟩

/-- Column `j` of `B`, read top to bottom. -/
def col {n : ℕ} (B : Fin n → R) (j : Fin 3) : Fin n → Fin 3 := fun i => B i j

theorem col_cons {n : ℕ} (r : R) (B : Fin n → R) (j : Fin 3) :
    col (Fin.cons r B : Fin (n + 1) → R) j = Fin.cons (r j) (col B j) := by
  funext i
  cases i using Fin.cases <;> rfl

theorem good_iff {n : ℕ} (A : Fin n → R) :
    Good A ↔ RowsOK A ∧ pst (col A 0) (col A 1) ≤ 1 ∧ pst (col A 1) (col A 2) ≤ 1 := by
  unfold Good RowsOK
  rw [← colpair_iff, ← colpair_iff, Fin.monotone_iff_le_succ (f := fun j => toLex (fun i => A i j)),
    Fin.antitone_iff_succ_le (f := fun j => toLex (fun i => A (Fin.rev i) j))]
  simp only [Fin.forall_fin_two]
  constructor
  · rintro ⟨a, b, ⟨c1, c2⟩, ⟨d1, d2⟩⟩
    exact ⟨⟨a, b⟩, ⟨c1, d1⟩, ⟨c2, d2⟩⟩
  · rintro ⟨⟨a, b⟩, ⟨c1, d1⟩, ⟨c2, d2⟩⟩
    exact ⟨a, b, ⟨c1, c2⟩, ⟨d1, d2⟩⟩

/-- The row read as a number in base 3, left entry most significant. -/
def code (r : R) : ℕ := 9 * (r 0 : ℕ) + 3 * (r 1 : ℕ) + (r 2 : ℕ)

def d0 (c : ℕ) : ℕ := c / 9
def d1 (c : ℕ) : ℕ := c / 3 % 3
def d2 (c : ℕ) : ℕ := c % 3

/-- The code of the reversed row. -/
def cRev (c : ℕ) : ℕ := 9 * d2 c + 3 * d1 c + d0 c

/-- The order of the poset of rows, on codes. -/
def ple (c e : ℕ) : Prop := c ≤ e ∧ cRev e ≤ cRev c

instance (c e : ℕ) : Decidable (ple c e) := by unfold ple; infer_instance

theorem code_lt (r : R) : code r < 27 := by
  unfold code
  have := (r 0).isLt
  have := (r 1).isLt
  have := (r 2).isLt
  omega

theorem d0_code (r : R) : d0 (code r) = (r 0 : ℕ) := by
  unfold d0 code
  have := (r 1).isLt
  have := (r 2).isLt
  omega

theorem d1_code (r : R) : d1 (code r) = (r 1 : ℕ) := by
  unfold d1 code
  have := (r 1).isLt
  have := (r 2).isLt
  omega

theorem d2_code (r : R) : d2 (code r) = (r 2 : ℕ) := by
  unfold d2 code
  have := (r 2).isLt
  omega

theorem cRev_code (r : R) : cRev (code r) = code (rv r) := by
  unfold cRev
  rw [d0_code, d1_code, d2_code]
  rfl

theorem code_inj {r s : R} (h : code r = code s) : r = s := by
  have e0 := d0_code r
  have e1 := d1_code r
  have e2 := d2_code r
  rw [h, d0_code] at e0
  rw [h, d1_code] at e1
  rw [h, d2_code] at e2
  funext j
  fin_cases j
  · exact Fin.ext e0.symm
  · exact Fin.ext e1.symm
  · exact Fin.ext e2.symm

theorem lex3_lt (r s : R) :
    toLex r < toLex s ↔ r 0 < s 0 ∨ (r 0 = s 0 ∧ (r 1 < s 1 ∨ (r 1 = s 1 ∧ r 2 < s 2))) := by
  have e : ∀ u : R, u = Fin.cons (u 0) (Fin.cons (u 1) (Fin.cons (u 2) Fin.elim0)) := by
    intro u
    funext j
    fin_cases j <;> rfl
  conv_lhs => rw [e r, e s]
  simp only [lex_cons_lt]
  have hz : ¬ toLex (Fin.elim0 : Fin 0 → Fin 3) < toLex (Fin.elim0 : Fin 0 → Fin 3) :=
    lt_irrefl _
  simp only [hz, and_false, or_false]

theorem row_lt_iff (r s : R) : toLex r < toLex s ↔ code r < code s := by
  rw [lex3_lt]
  simp only [Fin.lt_def, Fin.ext_iff]
  unfold code
  have := (r 0).isLt
  have := (r 1).isLt
  have := (r 2).isLt
  have := (s 0).isLt
  have := (s 1).isLt
  have := (s 2).isLt
  omega

theorem row_le_iff (r s : R) : toLex r ≤ toLex s ↔ code r ≤ code s := by
  rw [lex_le_iff, row_lt_iff, Nat.le_iff_lt_or_eq]
  constructor
  · rintro (h | rfl)
    · exact Or.inl h
    · exact Or.inr rfl
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (code_inj h)

theorem PLe_iff (r s : R) : PLe r s ↔ ple (code r) (code s) := by
  unfold PLe ple
  rw [row_le_iff, row_le_iff, cRev_code, cRev_code]

instance (r s : R) : Decidable (PLe r s) := decidable_of_iff _ (PLe_iff r s).symm

theorem image_code : (Finset.univ : Finset R).image code = range 27 := by
  apply Finset.eq_of_subset_of_card_le
  · intro c hc
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_range.mpr (code_lt r)
  · rw [Finset.card_image_of_injective _ (fun r s h => code_inj h), Finset.card_univ]
    simp

theorem sum_R {M : Type*} [AddCommMonoid M] (φ : ℕ → M) :
    ∑ r : R, φ (code r) = ∑ c ∈ range 27, φ c := by
  rw [← image_code, Finset.sum_image (fun r _ s _ h => code_inj h)]

theorem stpN_three (x y : ℕ) : stpN x y 3 = 3 := by
  unfold stpN
  split_ifs <;> omega

/-- Split a count according to the values (at most 3) of two functions `p1, p2`, when the
conditions `Q1, Q2` on these values exclude the value 3. -/
theorem split_sum {X : Type*} [Fintype X] (P : X → Prop) [DecidablePred P] (p1 p2 : X → ℕ)
    (h1 : ∀ x, p1 x ≤ 3) (h2 : ∀ x, p2 x ≤ 3) (Q1 Q2 : ℕ → Prop) [DecidablePred Q1]
    [DecidablePred Q2] (hQ1 : ¬ Q1 3) (hQ2 : ¬ Q2 3) :
    (∑ x, if P x ∧ Q1 (p1 x) ∧ Q2 (p2 x) then 1 else 0) =
      ∑ t1 ∈ range 3, if Q1 t1 then ∑ t2 ∈ range 3, if Q2 t2 then
        (∑ x, if P x ∧ p1 x = t1 ∧ p2 x = t2 then 1 else 0) else 0 else 0 := by
  have key : ∀ x, (if P x ∧ Q1 (p1 x) ∧ Q2 (p2 x) then 1 else 0) =
      ∑ t1 ∈ range 3, ∑ t2 ∈ range 3,
        if Q1 t1 ∧ Q2 t2 then (if P x ∧ p1 x = t1 ∧ p2 x = t2 then 1 else 0) else 0 := by
    intro x
    rcases (show p1 x < 3 ∨ p1 x = 3 by have := h1 x; omega) with c1 | c1
    · rcases (show p2 x < 3 ∨ p2 x = 3 by have := h2 x; omega) with c2 | c2
      · rw [Finset.sum_eq_single (p1 x), Finset.sum_eq_single (p2 x)]
        · by_cases hP : P x <;> by_cases q1 : Q1 (p1 x) <;> by_cases q2 : Q2 (p2 x) <;>
            simp [hP, q1, q2]
        · intro t2 _ ht2
          simp [Ne.symm ht2]
        · intro h
          exact absurd (Finset.mem_range.mpr c2) h
        · intro t1 _ ht1
          apply Finset.sum_eq_zero
          intro t2 _
          simp [Ne.symm ht1]
        · intro h
          exact absurd (Finset.mem_range.mpr c1) h
      · rw [if_neg (by rw [c2]; tauto)]
        symm
        apply Finset.sum_eq_zero
        intro t1 _
        apply Finset.sum_eq_zero
        intro t2 ht2
        have : p2 x ≠ t2 := by
          rw [c2]
          have := Finset.mem_range.mp ht2
          omega
        simp [this]
    · rw [if_neg (by rw [c1]; tauto)]
      symm
      apply Finset.sum_eq_zero
      intro t1 ht1
      apply Finset.sum_eq_zero
      intro t2 _
      have : p1 x ≠ t1 := by
        rw [c1]
        have := Finset.mem_range.mp ht1
        omega
      simp [this]
  rw [Finset.sum_congr rfl (fun x _ => key x), Finset.sum_comm]
  refine Finset.sum_congr rfl fun t1 _ => ?_
  rw [Finset.sum_comm]
  by_cases q1 : Q1 t1
  · rw [if_pos q1]
    refine Finset.sum_congr rfl fun t2 _ => ?_
    by_cases q2 : Q2 t2
    · simp only [q1, q2, and_self, if_true]
    · simp [q2]
  · simp [q1]


/-- The arrays `B` with `n` rows whose rows satisfy the row conditions and are all above `r` in
the poset of rows, and whose two pairs of adjacent columns have the states `s1` and `s2`. -/
noncomputable def G (n : ℕ) (r : R) (s1 s2 : ℕ) : ℕ := by
  classical
  exact ∑ B : Fin n → R, if RowsOK B ∧ (∀ i, PLe r (B i)) ∧
    pst (col B 0) (col B 1) = s1 ∧ pst (col B 1) (col B 2) = s2 then 1 else 0

theorem RowsOK_zero (B : Fin 0 → R) : RowsOK B :=
  ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

theorem G_zero (r : R) (s1 s2 : ℕ) : G 0 r s1 s2 = if s1 = 0 ∧ s2 = 0 then 1 else 0 := by
  classical
  unfold G
  rw [Fintype.sum_unique]
  refine if_congr ?_ rfl rfl
  simp only [pst_zero, RowsOK_zero, true_and, IsEmpty.forall_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩

theorem G_succ (n : ℕ) (r : R) (s1 s2 : ℕ) (hs1 : s1 < 3) (hs2 : s2 < 3) :
    G (n + 1) r s1 s2 = ∑ r' : R, if PLe r r' then
      ∑ t1 ∈ range 3, if stpN (r' 0) (r' 1) t1 = s1 then
        ∑ t2 ∈ range 3, if stpN (r' 1) (r' 2) t2 = s2 then G n r' t1 t2 else 0
      else 0
    else 0 := by
  classical
  unfold G
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => R).symm _
    (fun x => if RowsOK (Fin.cons x.1 x.2 : Fin (n + 1) → R) ∧
      (∀ i, PLe r ((Fin.cons x.1 x.2 : Fin (n + 1) → R) i)) ∧
      pst (col (Fin.cons x.1 x.2 : Fin (n + 1) → R) 0)
        (col (Fin.cons x.1 x.2 : Fin (n + 1) → R) 1) = s1 ∧
      pst (col (Fin.cons x.1 x.2 : Fin (n + 1) → R) 1)
        (col (Fin.cons x.1 x.2 : Fin (n + 1) → R) 2) = s2 then 1 else 0)
    (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r' _ => ?_
  by_cases h : PLe r r'
  · rw [if_pos h]
    have e : ∀ B : Fin n → R, (if RowsOK (Fin.cons r' B : Fin (n + 1) → R) ∧
        (∀ i, PLe r ((Fin.cons r' B : Fin (n + 1) → R) i)) ∧
        pst (col (Fin.cons r' B : Fin (n + 1) → R) 0) (col (Fin.cons r' B : Fin (n + 1) → R) 1)
          = s1 ∧
        pst (col (Fin.cons r' B : Fin (n + 1) → R) 1) (col (Fin.cons r' B : Fin (n + 1) → R) 2)
          = s2 then 1 else 0) =
        if (RowsOK B ∧ ∀ i, PLe r' (B i)) ∧
          stpN (r' 0) (r' 1) (pst (col B 0) (col B 1)) = s1 ∧
          stpN (r' 1) (r' 2) (pst (col B 1) (col B 2)) = s2 then 1 else 0 := by
      intro B
      refine if_congr ?_ rfl rfl
      rw [RowsOK_cons, Fin.forall_fin_succ, col_cons, col_cons, col_cons, pst_cons, pst_cons]
      simp only [Fin.cons_zero, Fin.cons_succ]
      constructor
      · rintro ⟨⟨h1, h2⟩, -, h3, h4⟩
        exact ⟨⟨h2, h1⟩, h3, h4⟩
      · rintro ⟨⟨h2, h1⟩, h3, h4⟩
        exact ⟨⟨h1, h2⟩, ⟨h, fun i => PLe_trans h (h1 i)⟩, h3, h4⟩
    rw [Finset.sum_congr rfl (fun B _ => e B)]
    rw [split_sum (fun B => RowsOK B ∧ ∀ i, PLe r' (B i)) (fun B => pst (col B 0) (col B 1))
      (fun B => pst (col B 1) (col B 2)) (fun B => pst_le _ _) (fun B => pst_le _ _)
      (fun t => stpN (r' 0) (r' 1) t = s1) (fun t => stpN (r' 1) (r' 2) t = s2)
      (by simp only [stpN_three]; omega) (by simp only [stpN_three]; omega)]
    refine Finset.sum_congr rfl fun t1 _ => if_congr Iff.rfl ?_ rfl
    refine Finset.sum_congr rfl fun t2 _ => if_congr Iff.rfl ?_ rfl
    exact Finset.sum_congr rfl fun B _ => if_congr and_assoc rfl rfl
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [Fin.forall_fin_succ]
    simp only [Fin.cons_zero]
    tauto

/-- One step of the transfer recursion, on codes of rows. -/
def Mop (f : ℕ → ℕ → ℕ → ℕ) (c s1 s2 : ℕ) : ℕ :=
  ∑ e ∈ range 27, if ple c e then
    ∑ t1 ∈ range 3, if stpN (d0 e) (d1 e) t1 = s1 then
      ∑ t2 ∈ range 3, if stpN (d1 e) (d2 e) t2 = s2 then f e t1 t2 else 0
    else 0
  else 0

/-- The transfer counts on codes: `g n c s1 s2 = G n r s1 s2` for the row `r` with code `c`. -/
def g : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, s1, s2 => if s1 = 0 ∧ s2 = 0 then 1 else 0
  | n + 1, c, s1, s2 => Mop (g n) c s1 s2

theorem G_eq_g (n : ℕ) :
    ∀ (r : R) (s1 s2 : ℕ), s1 < 3 → s2 < 3 → G n r s1 s2 = g n (code r) s1 s2 := by
  induction n with
  | zero =>
    intro r s1 s2 _ _
    rw [G_zero]
    rfl
  | succ n ih =>
    intro r s1 s2 hs1 hs2
    rw [G_succ n r s1 s2 hs1 hs2]
    show _ = Mop (g n) (code r) s1 s2
    unfold Mop
    rw [← sum_R]
    refine Finset.sum_congr rfl fun r' _ => ?_
    simp only [d0_code, d1_code, d2_code]
    refine if_congr (PLe_iff r r') ?_ rfl
    refine Finset.sum_congr rfl fun t1 ht1 => if_congr Iff.rfl ?_ rfl
    refine Finset.sum_congr rfl fun t2 ht2 => if_congr Iff.rfl ?_ rfl
    exact ih r' t1 t2 (Finset.mem_range.mp ht1) (Finset.mem_range.mp ht2)

/-- The count of the arrays with `n + 1` rows from the transfer counts of their last `n` rows. -/
def Aop (f : ℕ → ℕ → ℕ → ℕ) : ℕ :=
  ∑ e ∈ range 27, ∑ t1 ∈ range 3, if stpN (d0 e) (d1 e) t1 ≤ 1 then
    ∑ t2 ∈ range 3, if stpN (d1 e) (d2 e) t2 ≤ 1 then f e t1 t2 else 0 else 0

theorem a_succ (n : ℕ) : a (n + 1) = Aop (g n) := by
  classical
  have h1 : a (n + 1) = ∑ A : Fin (n + 1) → R, if RowsOK A ∧ pst (col A 0) (col A 1) ≤ 1 ∧
      pst (col A 1) (col A 2) ≤ 1 then 1 else 0 := by
    unfold a
    rw [Fintype.card_subtype, Finset.card_filter]
    exact Finset.sum_congr rfl fun A _ => if_congr (good_iff A) rfl rfl
  rw [h1, Fintype.sum_equiv (Fin.consEquiv fun _ => R).symm _
    (fun x => if RowsOK (Fin.cons x.1 x.2 : Fin (n + 1) → R) ∧
      pst (col (Fin.cons x.1 x.2 : Fin (n + 1) → R) 0)
        (col (Fin.cons x.1 x.2 : Fin (n + 1) → R) 1) ≤ 1 ∧
      pst (col (Fin.cons x.1 x.2 : Fin (n + 1) → R) 1)
        (col (Fin.cons x.1 x.2 : Fin (n + 1) → R) 2) ≤ 1 then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  unfold Aop
  rw [← sum_R]
  refine Finset.sum_congr rfl fun r' _ => ?_
  simp only [d0_code, d1_code, d2_code]
  have e : ∀ B : Fin n → R, (if RowsOK (Fin.cons r' B : Fin (n + 1) → R) ∧
      pst (col (Fin.cons r' B : Fin (n + 1) → R) 0) (col (Fin.cons r' B : Fin (n + 1) → R) 1)
        ≤ 1 ∧
      pst (col (Fin.cons r' B : Fin (n + 1) → R) 1) (col (Fin.cons r' B : Fin (n + 1) → R) 2)
        ≤ 1 then 1 else 0) =
      if (RowsOK B ∧ ∀ i, PLe r' (B i)) ∧
        stpN (r' 0) (r' 1) (pst (col B 0) (col B 1)) ≤ 1 ∧
        stpN (r' 1) (r' 2) (pst (col B 1) (col B 2)) ≤ 1 then 1 else 0 := by
    intro B
    refine if_congr ?_ rfl rfl
    rw [RowsOK_cons, col_cons, col_cons, col_cons, pst_cons, pst_cons]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h2, h1⟩, h3, h4⟩
    · rintro ⟨⟨h2, h1⟩, h3, h4⟩
      exact ⟨⟨h1, h2⟩, h3, h4⟩
  rw [Finset.sum_congr rfl (fun B _ => e B)]
  rw [split_sum (fun B => RowsOK B ∧ ∀ i, PLe r' (B i)) (fun B => pst (col B 0) (col B 1))
    (fun B => pst (col B 1) (col B 2)) (fun B => pst_le _ _) (fun B => pst_le _ _)
    (fun t => stpN (r' 0) (r' 1) t ≤ 1) (fun t => stpN (r' 1) (r' 2) t ≤ 1)
    (by simp only [stpN_three]; omega) (by simp only [stpN_three]; omega)]
  refine Finset.sum_congr rfl fun t1 ht1 => if_congr Iff.rfl ?_ rfl
  refine Finset.sum_congr rfl fun t2 ht2 => if_congr Iff.rfl ?_ rfl
  rw [← G_eq_g n r' t1 t2 (Finset.mem_range.mp ht1) (Finset.mem_range.mp ht2)]
  unfold G
  exact Finset.sum_congr rfl fun B _ => if_congr and_assoc rfl rfl

/-- The table of the coefficients `K j c (3 t1 + t2)` of the transfer counts in the basis of
binomial coefficients: `g (n + 1) c t1 t2 = Sum_{j < 5} C(n, j) K j c t1 t2`. -/
def KT : List (List (List ℕ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 1], [1, 0, 3, 0, 0, 0, 3, 0, 1],
    [0, 0, 0, 0, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 0, 2, 0, 1], [1, 0, 3, 0, 0, 0, 3, 0, 1],
    [0, 0, 1, 0, 0, 0, 2, 0, 1], [1, 0, 2, 0, 0, 0, 3, 0, 1], [1, 0, 3, 0, 0, 0, 3, 0, 1],
    [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 1, 0, 1], [1, 0, 3, 0, 0, 0, 2, 0, 1],
    [0, 0, 1, 0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0, 1, 0, 1], [0, 0, 2, 0, 0, 0, 2, 0, 1],
    [0, 0, 0, 0, 0, 0, 1, 0, 1], [0, 0, 1, 0, 0, 0, 2, 0, 1], [0, 0, 2, 0, 0, 0, 2, 0, 1],
    [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 2, 0, 0, 0, 1, 0, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0, 1, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 2, 0, 0, 0, 7, 0, 1, 1], [0, 3, 1, 2, 0, 15, 1, 6, 3],
    [0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 2, 0, 6, 0, 5, 1], [0, 0, 1, 0, 1, 12, 1, 12, 3],
    [0, 0, 0, 0, 0, 3, 0, 0, 1], [0, 0, 1, 0, 0, 6, 1, 5, 3], [0, 2, 1, 3, 0, 6, 1, 15, 3],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 3, 1], [0, 0, 1, 0, 0, 5, 1, 6, 3],
    [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 2, 1, 2, 1], [0, 2, 0, 0, 0, 5, 0, 6, 1],
    [0, 0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 3, 0, 2, 1], [0, 0, 0, 2, 0, 1, 0, 7, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0], [0, 0, 0, 0, 0, 0, 0, 3, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 2, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 7, 1, 0, 1, 0], [0, 1, 0, 0, 20, 23, 0, 13, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 5, 7, 0, 3, 0], [0, 0, 0, 0, 27, 17, 0, 17, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 13, 0, 5, 0], [0, 0, 0, 1, 20, 13, 0, 23, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 5, 0, 13, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 2, 0], [0, 0, 0, 0, 5, 3, 0, 7, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 7, 1, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 31, 8, 0, 5, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 1, 0, 0, 0], [0, 0, 0, 0, 34, 7, 0, 7, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 7, 0, 0, 0], [0, 0, 0, 0, 31, 5, 0, 8, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 7, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 11, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 14, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 11, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0]]]

/-- The entry of the table `KT`. -/
def K (j c t1 t2 : ℕ) : ℕ := ((KT.getD j []).getD c []).getD (3 * t1 + t2) 0

theorem K_step : ∀ j < 5, ∀ c < 27, ∀ s1 < 3, ∀ s2 < 3,
    Mop (K j) c s1 s2 = K j c s1 s2 + K (j + 1) c s1 s2 := by
  decide +kernel

theorem K_five : ∀ c < 27, ∀ s1 < 3, ∀ s2 < 3, K 5 c s1 s2 = 0 := by
  decide +kernel

theorem g_one : ∀ c < 27, ∀ s1 < 3, ∀ s2 < 3, g 1 c s1 s2 = K 0 c s1 s2 := by
  decide +kernel

theorem Mop_congr {f f' : ℕ → ℕ → ℕ → ℕ}
    (h : ∀ e < 27, ∀ t1 < 3, ∀ t2 < 3, f e t1 t2 = f' e t1 t2) (c s1 s2 : ℕ) :
    Mop f c s1 s2 = Mop f' c s1 s2 := by
  unfold Mop
  refine Finset.sum_congr rfl fun e he => if_congr Iff.rfl ?_ rfl
  refine Finset.sum_congr rfl fun t1 ht1 => if_congr Iff.rfl ?_ rfl
  refine Finset.sum_congr rfl fun t2 ht2 => if_congr Iff.rfl ?_ rfl
  exact h e (Finset.mem_range.mp he) t1 (Finset.mem_range.mp ht1) t2 (Finset.mem_range.mp ht2)

theorem Mop_add (f f' : ℕ → ℕ → ℕ → ℕ) (c s1 s2 : ℕ) :
    Mop (fun e t1 t2 => f e t1 t2 + f' e t1 t2) c s1 s2 = Mop f c s1 s2 + Mop f' c s1 s2 := by
  unfold Mop
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t1 _ => ?_
    split_ifs
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t2 _ => ?_
      split_ifs <;> simp
    · simp
  · simp

theorem Mop_smul (w : ℕ) (f : ℕ → ℕ → ℕ → ℕ) (c s1 s2 : ℕ) :
    Mop (fun e t1 t2 => w * f e t1 t2) c s1 s2 = w * Mop f c s1 s2 := by
  simp only [Mop, Finset.mul_sum, mul_ite, mul_zero]

theorem Mop_lin (S : Finset ℕ) (w : ℕ → ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℕ) (c s1 s2 : ℕ) :
    Mop (fun e t1 t2 => ∑ j ∈ S, w j * F j e t1 t2) c s1 s2 =
      ∑ j ∈ S, w j * Mop (F j) c s1 s2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Mop]
  | insert j S hj ih =>
    simp only [Finset.sum_insert hj]
    rw [Mop_add, Mop_smul, ih]

theorem Aop_congr {f f' : ℕ → ℕ → ℕ → ℕ}
    (h : ∀ e < 27, ∀ t1 < 3, ∀ t2 < 3, f e t1 t2 = f' e t1 t2) : Aop f = Aop f' := by
  unfold Aop
  refine Finset.sum_congr rfl fun e he => ?_
  refine Finset.sum_congr rfl fun t1 ht1 => if_congr Iff.rfl ?_ rfl
  refine Finset.sum_congr rfl fun t2 ht2 => if_congr Iff.rfl ?_ rfl
  exact h e (Finset.mem_range.mp he) t1 (Finset.mem_range.mp ht1) t2 (Finset.mem_range.mp ht2)

theorem Aop_add (f f' : ℕ → ℕ → ℕ → ℕ) :
    Aop (fun e t1 t2 => f e t1 t2 + f' e t1 t2) = Aop f + Aop f' := by
  unfold Aop
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t1 _ => ?_
  split_ifs
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t2 _ => ?_
    split_ifs <;> simp
  · simp

theorem Aop_smul (w : ℕ) (f : ℕ → ℕ → ℕ → ℕ) :
    Aop (fun e t1 t2 => w * f e t1 t2) = w * Aop f := by
  simp only [Aop, Finset.mul_sum, mul_ite, mul_zero]

theorem Aop_lin (S : Finset ℕ) (w : ℕ → ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℕ) :
    Aop (fun e t1 t2 => ∑ j ∈ S, w j * F j e t1 t2) = ∑ j ∈ S, w j * Aop (F j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Aop]
  | insert j S hj ih =>
    simp only [Finset.sum_insert hj]
    rw [Aop_add, Aop_smul, ih]

theorem g_closed (n : ℕ) : ∀ c < 27, ∀ s1 < 3, ∀ s2 < 3,
    g (n + 1) c s1 s2 = ∑ j ∈ range 5, n.choose j * K j c s1 s2 := by
  induction n with
  | zero =>
    intro c hc s1 hs1 s2 hs2
    rw [g_one c hc s1 hs1 s2 hs2]
    simp [Finset.sum_range_succ]
  | succ n ih =>
    intro c hc s1 hs1 s2 hs2
    show Mop (g (n + 1)) c s1 s2 = _
    rw [Mop_congr (f' := fun e t1 t2 => ∑ j ∈ range 5, n.choose j * K j e t1 t2)
      (fun e he t1 ht1 t2 ht2 => ih e he t1 ht1 t2 ht2), Mop_lin]
    rw [Finset.sum_congr rfl
      (fun j hj => by rw [K_step j (Finset.mem_range.mp hj) c hc s1 hs1 s2 hs2])]
    have h5 := K_five c hc s1 hs1 s2 hs2
    have p1 : (n + 1).choose 1 = n.choose 0 + n.choose 1 := Nat.choose_succ_succ n 0
    have p2 : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ n 1
    have p3 : (n + 1).choose 3 = n.choose 2 + n.choose 3 := Nat.choose_succ_succ n 2
    have p4 : (n + 1).choose 4 = n.choose 3 + n.choose 4 := Nat.choose_succ_succ n 3
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, p1, p2, p3, p4,
      Nat.choose_zero_right, h5]
    ring

theorem cK : Aop (K 0) = 18 ∧ Aop (K 1) = 98 ∧ Aop (K 2) = 181 ∧ Aop (K 3) = 134 ∧
    Aop (K 4) = 36 := by
  decide +kernel

theorem a_one : a 1 = 3 := by
  rw [a_succ]
  decide +kernel

theorem a_two (m : ℕ) :
    a (m + 2) = 18 + 98 * m + 181 * m.choose 2 + 134 * m.choose 3 + 36 * m.choose 4 := by
  rw [a_succ, Aop_congr (f' := fun e t1 t2 => ∑ j ∈ range 5, m.choose j * K j e t1 t2)
    (fun e he t1 ht1 t2 ht2 => g_closed m e he t1 ht1 t2 ht2), Aop_lin]
  obtain ⟨c0, c1, c2, c3, c4⟩ := cK
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3, c4,
    Nat.choose_zero_right, Nat.choose_one_right]
  ring


theorem choose2 (m : ℕ) : (m.choose 2 : ℚ) = m * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, Nat.choose_one_right]
    push_cast
    ring

theorem choose3 (m : ℕ) : (m.choose 3 : ℚ) = m * (m - 1) * (m - 2) / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose2]
    push_cast
    ring

theorem choose4 (m : ℕ) : (m.choose 4 : ℚ) = m * (m - 1) * (m - 2) * (m - 3) / 24 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose3]
    push_cast
    ring

theorem closedQ (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (3 / 2) * (n : ℚ) ^ 4 + (4 / 3) * (n : ℚ) ^ 3
      - 4 * (n : ℚ) ^ 2 - (29 / 6) * (n : ℚ) + 9 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [a_one]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [a_two]
    push_cast
    rw [choose2, choose3, choose4]
    ring

theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
      5 * a (n - 4) + a (n - 5) := by
  have h : ((a n : ℤ) : ℚ) = ((5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
      5 * a (n - 4) + a (n - 5) : ℤ) : ℚ) := by
    push_cast
    rw [closedQ n (by omega), closedQ (n - 1) (by omega), closedQ (n - 2) (by omega),
      closedQ (n - 3) (by omega), closedQ (n - 4) (by omega), closedQ (n - 5) (by omega)]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show 5 ≤ n by omega]
    ring
  exact_mod_cast h

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
        X * (3 + 3 * X + 56 * X ^ 2 - 35 * X ^ 3 + 9 * X ^ 4) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - X) ^ 5 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 5 * (PowerSeries.mk F * X ^ 1) +
        C 10 * (PowerSeries.mk F * X ^ 2) - C 10 * (PowerSeries.mk F * X ^ 3) +
        C 5 * (PowerSeries.mk F * X ^ 4) - C 1 * (PowerSeries.mk F * X ^ 5) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (3 + 3 * X + 56 * X ^ 2 - 35 * X ^ 3 + 9 * X ^ 4) =
      C 3 * X ^ 1 + C 3 * X ^ 2 + C 56 * X ^ 3 - C 35 * X ^ 4 + C 9 * X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 6
  · interval_cases k <;> norm_num [hF, closedQ]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    simp only [show 0 ≤ j + 6 by omega, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega,
      show 3 ≤ j + 6 by omega, show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega,
      show j + 6 - 0 = j + 6 by omega, show j + 6 - 1 = j + 5 by omega,
      show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega,
      show j + 6 - 4 = j + 2 by omega, show j + 6 - 5 = j + 1 by omega,
      show ¬ (j + 6 = 1) by omega, show ¬ (j + 6 = 2) by omega, show ¬ (j + 6 = 3) by omega,
      show ¬ (j + 6 = 4) by omega, show ¬ (j + 6 = 5) by omega, show ¬ (j + 6 = 0) by omega,
      show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega, show ¬ (j + 3 = 0) by omega,
      show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega, if_true, if_false, hF]
    rw [closedQ (j + 6) (by omega), closedQ (j + 5) (by omega), closedQ (j + 4) (by omega),
      closedQ (j + 3) (by omega), closedQ (j + 2) (by omega), closedQ (j + 1) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a201695.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence, OMA.Helpers.closedQ⟩
