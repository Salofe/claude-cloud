import OMAStatements.S_oeis_a202933

/-!
Proof of Barker's conjectures for A202933 ((n+3) X 5 binary arrays whose rows and columns have
nondecreasing consecutive windows of four bits).

Windows. For bits `c0, ..., c4`, the window `c0 c1 c2 c3` is at most the window `c1 c2 c3 c4`
iff `c0 = 1` forces `c1 = c2 = c3 = c4 = 1` (`win_le_iff`, a finite check). Hence a line has
nondecreasing windows iff every 1 at a position `i` with `i + 4 < L` is followed by four 1s
(`LineOK_iff`), and a row of width 5 has nondecreasing windows iff a first entry 1 forces all its
entries to be 1 (`LineOK_row`; there are 17 such rows).

Adding a row on top. `Fin.cons r X` is the array with the new top row `r` above an array `X` with
`m` rows. In each of its columns only the first pair of windows is new, and it exists iff
`m ≥ 4` (`LineOK_cons`). So `Fin.cons r X` is valid iff `r` is a good row, `X` is valid and, when
`m ≥ 4`, every column where `r` has a 1 starts with four 1s in `X` (`IsValid_cons`).

States. The state `st X` of an array is the set of columns whose first four entries (padded with
1s below the last row) are all 1. For `m ≥ 4` the state of a valid `Fin.cons r X` is the set of
the 1s of `r`; for `m < 4` it is that set intersected with `st X` (`key_ge`, `key_lt`). Let
`V m T` count the valid arrays with `m` rows and state `T`. Then `V 0 T = [T is full]`
(`V_zero`), and
* for `m < 4`: `V (m + 1) T = Sum_{good rows r} Sum_S [T = r ∩ S] V m S` (`V_succ_lt`);
* for `m ≥ 4`: `V (m + 1) T = [T is a good row] Sum_{S ⊇ T} V m S` (`V_succ_ge`);
and the number of valid arrays with `m` rows is `Sum_T V m T` (`card_eq_sum_V`).

Codes. Sets of columns are coded by `0, ..., 31` (bit `j` is column `j`), and on codes the two
steps are `Psi` and `Phi`. The tables `tv m` (`m ≤ 4`) and `tw j` (`j ≤ 5`) satisfy
`tv 0 = V 0`, `Psi (tv m) = tv (m + 1)`, `tw 0 = tv 4`, `Phi (tw j) = tw j + tw (j + 1)` and
`tw 6 = 0` (finite checks by `decide +kernel`). By induction, with Pascal's rule and the
linearity of `Phi`, `V (m + 4) = Sum_{j ≤ 5} C(m, j) tw j` (`V_big`). Summing over the 32 codes,
`a (n + 1) = 83521 + 30335 n + 9683 C(n, 2) + 2570 C(n, 3) + 444 C(n, 4) + 24 C(n, 5)`
(`a_closed`), a polynomial of degree 5 in `n`. The recurrence follows by substituting it, and the
generating function by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a202933 Finset

/-- A row of the array (5 entries), or a set of columns given by its indicator. -/
abbrev Row := Fin 5 → Bool

/-- Two consecutive windows of four bits `c0 c1 c2 c3` and `c1 c2 c3 c4`: the first is at most
the second iff `c0 = 1` forces `c1 = c2 = c3 = c4 = 1`. -/
theorem win_le_iff (c0 c1 c2 c3 c4 : Bool) :
    8 * c0.toNat + 4 * c1.toNat + 2 * c2.toNat + c3.toNat ≤
      8 * c1.toNat + 4 * c2.toNat + 2 * c3.toNat + c4.toNat ↔
    (c0 = true → c1 = true ∧ c2 = true ∧ c3 = true ∧ c4 = true) := by
  revert c0 c1 c2 c3 c4
  decide

/-- The entries of a line, padded with `true` beyond its end. -/
def pb {L : ℕ} (line : Fin L → Bool) (k : ℕ) : Bool := if h : k < L then line ⟨k, h⟩ else true

theorem pb_of_lt {L : ℕ} (line : Fin L → Bool) (k : ℕ) (h : k < L) : pb line k = line ⟨k, h⟩ :=
  dif_pos h

theorem pb_of_ge {L : ℕ} (line : Fin L → Bool) (k : ℕ) (h : L ≤ k) : pb line k = true :=
  dif_neg (by omega)

/-- Put a bit in front of a padded line. -/
def consF (x : Bool) (f : ℕ → Bool) : ℕ → Bool
  | 0 => x
  | k + 1 => f k

theorem pb_cons {L : ℕ} (x : Bool) (u : Fin L → Bool) :
    pb (Fin.cons x u : Fin (L + 1) → Bool) = consF x (pb u) := by
  funext k
  cases k with
  | zero => simp [pb, consF]
  | succ k =>
    show pb (Fin.cons x u : Fin (L + 1) → Bool) (k + 1) = pb u k
    by_cases h : k < L
    · rw [pb_of_lt _ _ (by omega), pb_of_lt _ _ h]
      show (Fin.cons x u : Fin (L + 1) → Bool) (Fin.succ ⟨k, h⟩) = u ⟨k, h⟩
      rw [Fin.cons_succ]
    · rw [pb_of_ge _ _ (by omega), pb_of_ge _ _ (by omega)]

/-- The window condition at position `i` of a padded line `f`. -/
def Q (f : ℕ → Bool) (i : ℕ) : Prop :=
  f i = true → f (i + 1) = true ∧ f (i + 2) = true ∧ f (i + 3) = true ∧ f (i + 4) = true

theorem LineOK_iff {L : ℕ} (line : Fin L → Bool) :
    LineOK line ↔ ∀ i, i + 4 < L → Q (pb line) i := by
  unfold LineOK
  constructor
  · intro h i hi
    have h' := h ⟨i, by omega⟩
    unfold win at h'
    unfold Q
    rw [pb_of_lt line i (by omega), pb_of_lt line (i + 1) (by omega),
      pb_of_lt line (i + 2) (by omega), pb_of_lt line (i + 3) (by omega),
      pb_of_lt line (i + 4) (by omega)]
    exact (win_le_iff _ _ _ _ _).mp h'
  · intro h i
    have hi := i.isLt
    have h' := h i.val (by omega)
    unfold Q at h'
    rw [pb_of_lt line i.val (by omega), pb_of_lt line (i.val + 1) (by omega),
      pb_of_lt line (i.val + 2) (by omega), pb_of_lt line (i.val + 3) (by omega),
      pb_of_lt line (i.val + 4) (by omega)] at h'
    unfold win
    exact (win_le_iff _ _ _ _ _).mpr h'

theorem LineOK_cons {L : ℕ} (x : Bool) (u : Fin L → Bool) :
    LineOK (Fin.cons x u : Fin (L + 1) → Bool) ↔
      (4 ≤ L → Q (consF x (pb u)) 0) ∧ LineOK u := by
  rw [LineOK_iff, LineOK_iff, pb_cons]
  constructor
  · intro h
    exact ⟨fun _ => h 0 (by omega), fun i hi => h (i + 1) (by omega)⟩
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => exact h0 (by omega)
    | succ k => exact h k (by omega)

/-- A row of width 5 has nondecreasing windows iff its first entry 1 forces all entries 1. -/
def RowOK (r : Row) : Prop := r 0 = true → r 1 = true ∧ r 2 = true ∧ r 3 = true ∧ r 4 = true

instance (r : Row) : Decidable (RowOK r) := by
  unfold RowOK
  infer_instance

theorem LineOK_row (r : Row) : LineOK r ↔ RowOK r := by
  rw [LineOK_iff]
  unfold RowOK
  constructor
  · intro h
    have h' := h 0 (by norm_num)
    unfold Q at h'
    rw [pb_of_lt r 0 (by norm_num), pb_of_lt r (0 + 1) (by norm_num),
      pb_of_lt r (0 + 2) (by norm_num), pb_of_lt r (0 + 3) (by norm_num),
      pb_of_lt r (0 + 4) (by norm_num)] at h'
    exact h'
  · intro h i hi
    obtain rfl : i = 0 := by omega
    unfold Q
    rw [pb_of_lt r 0 (by norm_num), pb_of_lt r (0 + 1) (by norm_num),
      pb_of_lt r (0 + 2) (by norm_num), pb_of_lt r (0 + 3) (by norm_num),
      pb_of_lt r (0 + 4) (by norm_num)]
    exact h

/-- Column `j` of the array `X`, read from top to bottom. -/
def col {m : ℕ} (X : Grid m) (j : Fin 5) : Fin m → Bool := fun i => X i j

theorem col_cons {m : ℕ} (r : Row) (X : Grid m) (j : Fin 5) :
    col (Fin.cons r X : Grid (m + 1)) j = Fin.cons (r j) (col X j) := by
  funext i
  cases i using Fin.cases <;> rfl

/-- The state of an array: the columns whose first four entries (padded with `true`) are 1. -/
def st {m : ℕ} (X : Grid m) (j : Fin 5) : Bool :=
  pb (col X j) 0 && pb (col X j) 1 && pb (col X j) 2 && pb (col X j) 3

theorem st_cons {m : ℕ} (r : Row) (X : Grid m) (j : Fin 5) :
    st (Fin.cons r X : Grid (m + 1)) j =
      (r j && pb (col X j) 0 && pb (col X j) 1 && pb (col X j) 2) := by
  unfold st
  rw [col_cons, pb_cons]
  rfl

theorem Q_consF_zero (x : Bool) (f : ℕ → Bool) :
    Q (consF x f) 0 ↔ (x = true → (f 0 && f 1 && f 2 && f 3) = true) := by
  simp only [Bool.and_eq_true]
  unfold Q
  constructor
  · intro h hx
    obtain ⟨h0, h1, h2, h3⟩ := h hx
    exact ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
  · intro h hx
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h hx
    exact ⟨h0, h1, h2, h3⟩

theorem IsValid_cons {m : ℕ} (r : Row) (X : Grid m) :
    IsValid (Fin.cons r X : Grid (m + 1)) ↔
      RowOK r ∧ IsValid X ∧ (4 ≤ m → ∀ j, r j = true → st X j = true) := by
  unfold IsValid
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have hc : ∀ j, LineOK (fun i => (Fin.cons r X : Grid (m + 1)) i j) ↔
      (4 ≤ m → (r j = true → st X j = true)) ∧ LineOK (col X j) := by
    intro j
    have e : (fun i => (Fin.cons r X : Grid (m + 1)) i j) = Fin.cons (r j) (col X j) :=
      col_cons r X j
    rw [e, LineOK_cons, Q_consF_zero]
    rfl
  simp only [hc, LineOK_row]
  constructor
  · rintro ⟨⟨hr, hrows⟩, hcols⟩
    exact ⟨hr, ⟨hrows, fun j => (hcols j).2⟩, fun hm j hj => (hcols j).1 hm hj⟩
  · rintro ⟨hr, ⟨hrows, hcols⟩, h4⟩
    exact ⟨⟨hr, hrows⟩, fun j => ⟨fun hm => h4 hm j, hcols j⟩⟩

theorem key_ge {m : ℕ} (hm : 4 ≤ m) (r : Row) (X : Grid m) (T : Row) :
    (IsValid (Fin.cons r X : Grid (m + 1)) ∧ st (Fin.cons r X : Grid (m + 1)) = T) ↔
      (RowOK r ∧ (∀ j, r j = true → st X j = true) ∧ T = r) ∧ IsValid X := by
  rw [IsValid_cons]
  have hst : (∀ j, r j = true → st X j = true) → st (Fin.cons r X : Grid (m + 1)) = r := by
    intro hsub
    funext j
    rw [st_cons]
    cases hrj : r j
    · simp
    · have h := hsub j hrj
      unfold st at h
      simp only [Bool.and_eq_true] at h
      simp [h.1.1.1, h.1.1.2, h.1.2]
  constructor
  · rintro ⟨⟨hr, hX, h4⟩, hT⟩
    exact ⟨⟨hr, h4 hm, by rw [← hT, hst (h4 hm)]⟩, hX⟩
  · rintro ⟨⟨hr, hsub, rfl⟩, hX⟩
    exact ⟨⟨hr, hX, fun _ => hsub⟩, hst hsub⟩

theorem key_lt {m : ℕ} (hm : m < 4) (r : Row) (X : Grid m) (T : Row) :
    (IsValid (Fin.cons r X : Grid (m + 1)) ∧ st (Fin.cons r X : Grid (m + 1)) = T) ↔
      (RowOK r ∧ ∀ j, T j = (r j && st X j)) ∧ IsValid X := by
  rw [IsValid_cons]
  have hst : ∀ j, st (Fin.cons r X : Grid (m + 1)) j = (r j && st X j) := by
    intro j
    rw [st_cons]
    unfold st
    rw [pb_of_ge (col X j) 3 (by omega), Bool.and_true]
    simp only [Bool.and_assoc]
  constructor
  · rintro ⟨⟨hr, hX, -⟩, hT⟩
    exact ⟨⟨hr, fun j => by rw [← hT, hst]⟩, hX⟩
  · rintro ⟨⟨hr, hT⟩, hX⟩
    exact ⟨⟨hr, hX, fun h => absurd h (by omega)⟩, funext fun j => by rw [hst, hT]⟩

/-- The number of valid arrays with `m` rows and state `T`. -/
def V (m : ℕ) (T : Row) : ℕ := ∑ X : Grid m, if IsValid X ∧ st X = T then 1 else 0

theorem sum_fiber {m : ℕ} (P : Row → Prop) [DecidablePred P] :
    (∑ X : Grid m, if P (st X) ∧ IsValid X then 1 else 0) =
      ∑ S : Row, if P S then V m S else 0 := by
  unfold V
  have h : ∀ X : Grid m, (if P (st X) ∧ IsValid X then 1 else 0) =
      ∑ S : Row, if P S then (if IsValid X ∧ st X = S then 1 else 0) else 0 := by
    intro X
    rw [Finset.sum_eq_single (st X)]
    · by_cases hP : P (st X) <;> by_cases hv : IsValid X <;> simp [hP, hv]
    · intro S _ hS
      have : st X ≠ S := fun h => hS h.symm
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl (fun X _ => h X), Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hP : P S
  · simp only [hP, if_true]
  · simp only [hP, if_false, Finset.sum_const_zero]

theorem V_succ_ge {m : ℕ} (hm : 4 ≤ m) (T : Row) :
    V (m + 1) T = if RowOK T then
      ∑ S : Row, (if (∀ j, T j = true → S j = true) then V m S else 0) else 0 := by
  have h1 : V (m + 1) T = ∑ r : Row, ∑ X : Grid m,
      if (RowOK r ∧ (∀ j, r j = true → st X j = true) ∧ T = r) ∧ IsValid X then 1 else 0 := by
    unfold V
    rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
      (fun x => if IsValid (Fin.cons x.1 x.2 : Grid (m + 1)) ∧
        st (Fin.cons x.1 x.2 : Grid (m + 1)) = T then 1 else 0) (fun X => by simp),
      Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun r _ =>
      Finset.sum_congr rfl fun X _ => if_congr (key_ge hm r X T) rfl rfl
  rw [h1, Finset.sum_congr rfl (fun r _ => sum_fiber (m := m)
    (fun S => RowOK r ∧ (∀ j, r j = true → S j = true) ∧ T = r))]
  rw [Finset.sum_eq_single T]
  · by_cases hT : RowOK T
    · rw [if_pos hT]
      exact Finset.sum_congr rfl fun S _ => if_congr (by simp [hT]) rfl rfl
    · rw [if_neg hT]
      exact Finset.sum_eq_zero fun S _ => if_neg (by tauto)
  · intro r _ hr
    refine Finset.sum_eq_zero fun S _ => if_neg ?_
    rintro ⟨-, -, h⟩
    exact hr h.symm
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem V_succ_lt {m : ℕ} (hm : m < 4) (T : Row) :
    V (m + 1) T = ∑ r : Row, ∑ S : Row,
      if RowOK r ∧ (∀ j, T j = (r j && S j)) then V m S else 0 := by
  have h1 : V (m + 1) T = ∑ r : Row, ∑ X : Grid m,
      if (RowOK r ∧ ∀ j, T j = (r j && st X j)) ∧ IsValid X then 1 else 0 := by
    unfold V
    rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
      (fun x => if IsValid (Fin.cons x.1 x.2 : Grid (m + 1)) ∧
        st (Fin.cons x.1 x.2 : Grid (m + 1)) = T then 1 else 0) (fun X => by simp),
      Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun r _ =>
      Finset.sum_congr rfl fun X _ => if_congr (key_lt hm r X T) rfl rfl
  rw [h1]
  exact Finset.sum_congr rfl fun r _ =>
    sum_fiber (m := m) (fun S => RowOK r ∧ ∀ j, T j = (r j && S j))

theorem V_zero (T : Row) : V 0 T = if (∀ j, T j = true) then 1 else 0 := by
  have hall : ∀ X : Grid 0, (IsValid X ∧ st X = T) ↔ ∀ j, T j = true := by
    intro X
    have hv : IsValid X := ⟨fun i => Fin.elim0 i, fun j i => absurd i.isLt (by omega)⟩
    have hs : st X = fun _ => true := by
      funext j
      unfold st
      rw [pb_of_ge _ 0 (by omega), pb_of_ge _ 1 (by omega), pb_of_ge _ 2 (by omega),
        pb_of_ge _ 3 (by omega)]
      rfl
    rw [hs]
    constructor
    · rintro ⟨-, h⟩ j
      rw [← h]
    · intro h
      exact ⟨hv, funext fun j => (h j).symm⟩
  unfold V
  rw [Fintype.sum_unique]
  exact if_congr (hall _) rfl rfl

theorem card_eq_sum_V (m : ℕ) :
    (Finset.univ.filter (fun g : Grid m => IsValid g)).card = ∑ T : Row, V m T := by
  rw [Finset.card_filter]
  have := sum_fiber (m := m) (fun _ => True)
  simp only [true_and, if_true] at this
  rw [← this]

/-- The row (or the set of columns) with code `u`: the entry of column `j` is bit `j` of `u`. -/
def row (u : Fin 32) : Row := fun j => Nat.testBit u.val j.val

theorem row_injective : Function.Injective row := by
  decide +kernel

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

theorem sum_row (F : Row → ℕ) : ∑ r : Row, F r = ∑ u : Fin 32, F (row u) :=
  (Fintype.sum_bijective row row_bijective _ _ (fun _ => rfl)).symm

/-- One step of the state recursion on codes while the array has fewer than 4 rows. -/
def Psi (f : Fin 32 → ℕ) (t : Fin 32) : ℕ :=
  ∑ e : Fin 32, ∑ s : Fin 32,
    if RowOK (row e) ∧ ∀ j, row t j = (row e j && row s j) then f s else 0

/-- One step of the state recursion on codes once the array has at least 4 rows. -/
def Phi (f : Fin 32 → ℕ) (t : Fin 32) : ℕ :=
  if RowOK (row t) then
    ∑ s : Fin 32, (if ∀ j, row t j = true → row s j = true then f s else 0) else 0

theorem v_succ_lt {m : ℕ} (hm : m < 4) (t : Fin 32) :
    V (m + 1) (row t) = Psi (fun s => V m (row s)) t := by
  rw [V_succ_lt hm, sum_row]
  unfold Psi
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [sum_row]

theorem v_succ_ge {m : ℕ} (hm : 4 ≤ m) (t : Fin 32) :
    V (m + 1) (row t) = Phi (fun s => V m (row s)) t := by
  rw [V_succ_ge hm, sum_row]
  rfl

/-- The state counts `V m` for `m ≤ 4`, on codes. -/
def TV : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
   [83, 0, 29, 0, 29, 0, 11, 0, 29, 0, 11, 0, 11, 0, 5, 0, 29, 0, 11, 0, 11, 0, 5, 0, 11, 0, 5, 0,
    5, 0, 3, 1],
   [2647, 0, 427, 0, 427, 0, 79, 0, 427, 0, 79, 0, 79, 0, 19, 0, 427, 0, 79, 0, 79, 0, 19, 0, 79, 0,
    19, 0, 19, 0, 7, 1],
   [60719, 0, 4913, 0, 4913, 0, 479, 0, 4913, 0, 479, 0, 479, 0, 65, 0, 4913, 0, 479, 0, 479, 0, 65,
    0, 479, 0, 65, 0, 65, 0, 15, 1]]

def tv (m : ℕ) (u : Fin 32) : ℕ := (TV.getD m []).getD u.val 0

/-- The coefficients `w j` of `V (m + 4) = Sum_j C(m, j) w j`, on codes. -/
def WT : List (List ℕ) :=
  [[60719, 0, 4913, 0, 4913, 0, 479, 0, 4913, 0, 479, 0, 479, 0, 65, 0, 4913, 0, 479, 0, 479, 0, 65,
    0, 479, 0, 65, 0, 65, 0, 15, 1],
   [22802, 0, 1648, 0, 1648, 0, 146, 0, 1648, 0, 146, 0, 146, 0, 16, 0, 1648, 0, 146, 0, 146, 0, 16,
    0, 146, 0, 16, 0, 16, 0, 1, 0],
   [7533, 0, 487, 0, 487, 0, 33, 0, 487, 0, 33, 0, 33, 0, 1, 0, 487, 0, 33, 0, 33, 0, 1, 0, 33, 0, 1,
    0, 1, 0, 0, 0],
   [2150, 0, 102, 0, 102, 0, 2, 0, 102, 0, 2, 0, 2, 0, 0, 0, 102, 0, 2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0,
    0, 0, 0],
   [420, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def tw (j : ℕ) (u : Fin 32) : ℕ := (WT.getD j []).getD u.val 0

theorem tv_zero : ∀ u : Fin 32, tv 0 u = if (∀ j, row u j = true) then 1 else 0 := by
  decide +kernel

theorem tv_step0 : ∀ u : Fin 32, Psi (tv 0) u = tv 1 u := by
  decide +kernel

theorem tv_step1 : ∀ u : Fin 32, Psi (tv 1) u = tv 2 u := by
  decide +kernel

theorem tv_step2 : ∀ u : Fin 32, Psi (tv 2) u = tv 3 u := by
  decide +kernel

theorem tv_step3 : ∀ u : Fin 32, Psi (tv 3) u = tv 4 u := by
  decide +kernel

theorem tv_step (m : ℕ) (hm : m < 4) (u : Fin 32) : Psi (tv m) u = tv (m + 1) u := by
  interval_cases m
  · exact tv_step0 u
  · exact tv_step1 u
  · exact tv_step2 u
  · exact tv_step3 u

theorem tw_zero : ∀ u : Fin 32, tw 0 u = tv 4 u := by
  decide +kernel

theorem tw_step : ∀ j < 6, ∀ u : Fin 32, Phi (tw j) u = tw j u + tw (j + 1) u := by
  decide +kernel

theorem tw_six (u : Fin 32) : tw 6 u = 0 := rfl

theorem tw_sums : (∑ u, tw 0 u) = 83521 ∧ (∑ u, tw 1 u) = 30335 ∧ (∑ u, tw 2 u) = 9683 ∧
    (∑ u, tw 3 u) = 2570 ∧ (∑ u, tw 4 u) = 444 ∧ (∑ u, tw 5 u) = 24 := by
  decide +kernel

theorem V_small (m : ℕ) (hm : m ≤ 4) (u : Fin 32) : V m (row u) = tv m u := by
  induction m generalizing u with
  | zero => rw [V_zero, tv_zero]
  | succ m ih =>
    have e : (fun s => V m (row s)) = tv m := funext fun s => ih (by omega) s
    rw [v_succ_lt (by omega), e, tv_step m (by omega) u]

theorem Phi_lin (S : Finset ℕ) (w : ℕ → ℕ) (F : ℕ → Fin 32 → ℕ) (t : Fin 32) :
    Phi (fun s => ∑ j ∈ S, w j * F j s) t = ∑ j ∈ S, w j * Phi (F j) t := by
  unfold Phi
  split_ifs with h
  · simp only [Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> simp
  · simp

theorem V_big (m : ℕ) : ∀ u : Fin 32, V (m + 4) (row u) = ∑ j ∈ range 6, m.choose j * tw j u := by
  induction m with
  | zero =>
    intro u
    rw [Nat.zero_add, V_small 4 le_rfl u, ← tw_zero u]
    simp [Finset.sum_range_succ]
  | succ m ih =>
    intro u
    rw [show m + 1 + 4 = (m + 4) + 1 by omega, v_succ_ge (by omega)]
    rw [show (fun s => V (m + 4) (row s)) = fun s => ∑ j ∈ range 6, m.choose j * tw j s from
      funext ih, Phi_lin]
    rw [Finset.sum_congr rfl (fun j hj => by rw [tw_step j (Finset.mem_range.mp hj) u])]
    have h6 := tw_six u
    have p1 : (m + 1).choose 1 = m.choose 0 + m.choose 1 := Nat.choose_succ_succ m 0
    have p2 : (m + 1).choose 2 = m.choose 1 + m.choose 2 := Nat.choose_succ_succ m 1
    have p3 : (m + 1).choose 3 = m.choose 2 + m.choose 3 := Nat.choose_succ_succ m 2
    have p4 : (m + 1).choose 4 = m.choose 3 + m.choose 4 := Nat.choose_succ_succ m 3
    have p5 : (m + 1).choose 5 = m.choose 4 + m.choose 5 := Nat.choose_succ_succ m 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, p1, p2, p3, p4, p5,
      Nat.choose_zero_right, h6]
    ring

theorem a_closed (n : ℕ) :
    a (n + 1) = 83521 + 30335 * (n : ℤ) + 9683 * (n.choose 2 : ℤ) + 2570 * (n.choose 3 : ℤ) +
      444 * (n.choose 4 : ℤ) + 24 * (n.choose 5 : ℤ) := by
  have h1 : a (n + 1) = ((Finset.univ.filter (fun g : Grid (n + 4) => IsValid g)).card : ℤ) :=
    rfl
  rw [h1, card_eq_sum_V, sum_row]
  simp only [V_big n]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := tw_sums
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3, c4, c5,
    Nat.choose_zero_right, Nat.choose_one_right]
  push_cast
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

theorem choose5 (m : ℕ) :
    (m.choose 5 : ℚ) = m * (m - 1) * (m - 2) * (m - 3) * (m - 4) / 120 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.cast_add, ih, choose4]
    push_cast
    ring

/-- The closed form of `a (n + 1)` as a polynomial in `n`. -/
def P (x : ℚ) : ℚ :=
  83521 + 30335 * x + 9683 * (x * (x - 1) / 2) + 2570 * (x * (x - 1) * (x - 2) / 6) +
    444 * (x * (x - 1) * (x - 2) * (x - 3) / 24) +
    24 * (x * (x - 1) * (x - 2) * (x - 3) * (x - 4) / 120)

theorem closedQ (n : ℕ) : ((a (n + 1) : ℤ) : ℚ) = P n := by
  rw [a_closed]
  push_cast
  rw [choose2, choose3, choose4, choose5]
  rfl

theorem recurrence (n : ℕ) (hn : 6 < n) :
    a n = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
      6 * a (n - 5) - a (n - 6) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  rw [show k + 7 - 1 = (k + 5) + 1 by omega, show k + 7 - 2 = (k + 4) + 1 by omega,
    show k + 7 - 3 = (k + 3) + 1 by omega, show k + 7 - 4 = (k + 2) + 1 by omega,
    show k + 7 - 5 = (k + 1) + 1 by omega, show k + 7 - 6 = k + 1 by omega,
    show k + 7 = (k + 6) + 1 by omega]
  have h : ((a ((k + 6) + 1) : ℤ) : ℚ) = ((6 * a ((k + 5) + 1) - 15 * a ((k + 4) + 1) +
      20 * a ((k + 3) + 1) - 15 * a ((k + 2) + 1) + 6 * a ((k + 1) + 1) - a (k + 1) : ℤ) : ℚ) := by
    push_cast
    rw [closedQ, closedQ, closedQ, closedQ, closedQ, closedQ, closedQ]
    unfold P
    push_cast
    ring
  exact_mod_cast h

theorem a_vals : a 0 = 0 ∧ a 1 = 83521 ∧ a 2 = 113856 ∧ a 3 = 153874 ∧ a 4 = 206145 ∧
    a 5 = 273683 ∧ a 6 = 359970 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a_closed]
    norm_num [Nat.choose]
  · rw [a_closed]
    norm_num [Nat.choose]
  · rw [a_closed]
    norm_num [Nat.choose]
  · rw [a_closed]
    norm_num [Nat.choose]
  · rw [a_closed]
    norm_num [Nat.choose]
  · rw [a_closed]
    norm_num [Nat.choose]

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk a * (1 - X) ^ 6 =
        X * (83521 - 387270 * X + 723553 * X ^ 2 - 679679 * X ^ 3 + 320618 * X ^ 4 -
          60719 * X ^ 5) := by
  have key : PowerSeries.mk a * (1 - X) ^ 6 =
      C 1 * (PowerSeries.mk a * X ^ 0) - C 6 * (PowerSeries.mk a * X ^ 1) +
        C 15 * (PowerSeries.mk a * X ^ 2) - C 20 * (PowerSeries.mk a * X ^ 3) +
        C 15 * (PowerSeries.mk a * X ^ 4) - C 6 * (PowerSeries.mk a * X ^ 5) +
        C 1 * (PowerSeries.mk a * X ^ 6) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℤ⟦X⟧) * (83521 - 387270 * X + 723553 * X ^ 2 - 679679 * X ^ 3 +
      320618 * X ^ 4 - 60719 * X ^ 5) =
      C 83521 * X ^ 1 - C 387270 * X ^ 2 + C 723553 * X ^ 3 - C 679679 * X ^ 4 +
        C 320618 * X ^ 5 - C 60719 * X ^ 6 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  obtain ⟨v0, v1, v2, v3, v4, v5, v6⟩ := a_vals
  by_cases hk : k < 7
  · interval_cases k <;> norm_num [v0, v1, v2, v3, v4, v5, v6]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
    have hr := recurrence (j + 7) (by omega)
    simp only [show j + 7 - 1 = j + 6 by omega, show j + 7 - 2 = j + 5 by omega,
      show j + 7 - 3 = j + 4 by omega, show j + 7 - 4 = j + 3 by omega,
      show j + 7 - 5 = j + 2 by omega, show j + 7 - 6 = j + 1 by omega] at hr
    simp only [show 0 ≤ j + 7 by omega, show 1 ≤ j + 7 by omega, show 2 ≤ j + 7 by omega,
      show 3 ≤ j + 7 by omega, show 4 ≤ j + 7 by omega, show 5 ≤ j + 7 by omega,
      show 6 ≤ j + 7 by omega,
      show j + 7 - 0 = j + 7 by omega, show j + 7 - 1 = j + 6 by omega,
      show j + 7 - 2 = j + 5 by omega, show j + 7 - 3 = j + 4 by omega,
      show j + 7 - 4 = j + 3 by omega, show j + 7 - 5 = j + 2 by omega,
      show j + 7 - 6 = j + 1 by omega,
      show ¬ (j + 7 = 1) by omega, show ¬ (j + 7 = 2) by omega, show ¬ (j + 7 = 3) by omega,
      show ¬ (j + 7 = 4) by omega, show ¬ (j + 7 = 5) by omega, show ¬ (j + 7 = 6) by omega,
      if_true, if_false]
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a202933.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
