import OMAStatements.S_oeis_a220033

/-!
Proof of Hardin's formula and of Barker's g.f. and recurrence for A220033 (distinct arrays
obtained from a sorted 0..1 3 X n array by taking the minimum of each entry and its horizontal
and diagonal neighbours, the diagonal running from upper left to lower right).

1. Sorted arrays are staircases. In a sorted array a one is never followed by a zero further down
   its column (`col_up`, by strong induction on the column) and a one has only ones to its left
   (`row_prefix`). Hence row `i` has ones exactly in its first `x_i` columns, with
   `x_0 ≤ x_1 ≤ x_2 ≤ n` (`sorted_stair`, `row_len`); conversely every such staircase is sorted
   (`stair_sorted`), and the staircase determines its row lengths (`stair_inj`).
2. Taking neighbourhood minima maps the staircase with row lengths `(x_0, x_1, x_2)` to the
   staircase with row lengths `bv n x = (f x_0, min (f x_1) (x_0 + 1), min (f x_2) (x_1 + 1))`,
   where `f x = n` if `x = n` and `f x = x - 1` otherwise (`erode_nat`, `nbhdMin_stair`). So
   `a n` is the number of points of `Sn n`, the image under `bv n` of the monotone triples
   bounded by `n` (`a_eq`).
3. Prepending a column of ones to a staircase with `x_0 ≥ 1` adds one to every coordinate of
   `bv` (`bv_succ`). Hence the points of `Sn (n + 1)` with first coordinate at least 2 are the
   points of `Sn n` with first coordinate at least 1, shifted by one (`shift_slices`). The points
   with first coordinate 0 form `2 n + 2` explicit triples for `n ≥ 5` (`slice0`) and those with
   first coordinate 1 form `n + 4` explicit triples for `n ≥ 6` (`slice1`), so
   `#Sn (n + 1) = #Sn n + n + 7` for `n ≥ 6` (`card_succ`).
4. With the values for `n ≤ 6` computed by the kernel this gives `2 a(n) + 30 = n^2 + 13 n` for
   `n ≥ 4`, which is Hardin's formula. The recurrence follows by substitution and the g.f. by
   comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a220033 Finset

theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

theorem fin2_lt : ∀ x y : Fin 2, x < y ↔ x = 0 ∧ y = 1 := by decide

theorem fin2_one_le : ∀ x : Fin 2, 1 ≤ x ↔ x = 1 := by decide

theorem fin2_ne : (0 : Fin 2) ≠ 1 := by decide

theorem lex_lt_iff' {m : ℕ} (x y : Fin m → Fin 2) :
    toLex x < toLex y ↔ ∃ i, (∀ j, j < i → x j = y j) ∧ x i < y i := Iff.rfl

/-- In a sorted array a one is never followed by a zero further down its column. -/
theorem col_up {n : ℕ} {A : Fin 3 → Fin n → Fin 2} (hA : Sorted A) :
    ∀ (j : Fin n) (i i' : Fin 3), i < i' → A i j = 1 → A i' j = 1 := by
  intro j
  induction j using WellFoundedLT.induction with
  | _ j ih =>
  intro i i' hii' hij
  by_contra hne
  have h0 : A i' j = 0 := (fin2_cases _).resolve_right hne
  have hrow : toLex (A i) ≤ toLex (A i') := hA.1 hii'.le
  have hne' : A i ≠ A i' := by
    intro h
    rw [h, h0] at hij
    exact fin2_ne hij
  obtain ⟨j0, hj0eq, hj0lt⟩ :=
    (lex_lt_iff' _ _).mp (lt_of_le_of_ne hrow (fun h => hne' (toLex_inj.mp h)))
  have hA0 : A i j0 = 0 ∧ A i' j0 = 1 := (fin2_lt _ _).mp hj0lt
  have hj0j : j0 < j := by
    rcases lt_trichotomy j0 j with h | h | h
    · exact h
    · subst h
      rw [hij] at hA0
      exact absurd hA0.1.symm fin2_ne
    · have : A i j = A i' j := hj0eq j h
      rw [hij, h0] at this
      exact absurd this.symm fin2_ne
  have hcol : toLex (fun l => A l j) ≤ toLex (fun l => A l j0) := hA.2 hj0j.le
  have hne2 : (fun l => A l j) ≠ (fun l => A l j0) := by
    intro h
    have : A i j = A i j0 := congrFun h i
    rw [hij, hA0.1] at this
    exact fin2_ne this.symm
  obtain ⟨i1, hi1eq, hi1lt⟩ :=
    (lex_lt_iff' _ _).mp (lt_of_le_of_ne hcol (fun h => hne2 (toLex_inj.mp h)))
  have hB : A i1 j = 0 ∧ A i1 j0 = 1 := (fin2_lt _ _).mp hi1lt
  have hi1i : i1 < i := by
    rcases lt_trichotomy i1 i with h | h | h
    · exact h
    · subst h
      rw [hij] at hB
      exact (fin2_ne hB.1.symm).elim
    · have : A i j = A i j0 := hi1eq i h
      rw [hij, hA0.1] at this
      exact (fin2_ne this.symm).elim
  have := ih j0 hj0j i1 i hi1i hB.2
  rw [hA0.1] at this
  exact fin2_ne this

/-- In a sorted array a one has only ones to its left. -/
theorem row_prefix {n : ℕ} {A : Fin 3 → Fin n → Fin 2} (hA : Sorted A) :
    ∀ (i : Fin 3) (j j' : Fin n), j' < j → A i j = 1 → A i j' = 1 := by
  intro i j j' hjj' hij
  by_contra hne
  have h0 : A i j' = 0 := (fin2_cases _).resolve_right hne
  have hcol : toLex (fun l => A l j) ≤ toLex (fun l => A l j') := hA.2 hjj'.le
  have hne2 : (fun l => A l j) ≠ (fun l => A l j') := by
    intro h
    have : A i j = A i j' := congrFun h i
    rw [hij, h0] at this
    exact fin2_ne this.symm
  obtain ⟨i1, hi1eq, hi1lt⟩ :=
    (lex_lt_iff' _ _).mp (lt_of_le_of_ne hcol (fun h => hne2 (toLex_inj.mp h)))
  have hB : A i1 j = 0 ∧ A i1 j' = 1 := (fin2_lt _ _).mp hi1lt
  have hi1i : i1 < i := by
    rcases lt_trichotomy i1 i with h | h | h
    · exact h
    · subst h
      rw [hij] at hB
      exact (fin2_ne hB.1.symm).elim
    · have : A i j = A i j' := hi1eq i h
      rw [hij, h0] at this
      exact (fin2_ne this.symm).elim
  have := col_up hA j' i1 i hi1i hB.2
  rw [h0] at this
  exact fin2_ne this

/-- A row whose ones are closed to the left has its ones exactly in its first `k` columns. -/
theorem row_len {n : ℕ} (r : Fin n → Fin 2) (hr : ∀ j j' : Fin n, j' < j → r j = 1 → r j' = 1) :
    ∃ k, k ≤ n ∧ ∀ j : Fin n, r j = 1 ↔ j.val < k := by
  classical
  by_cases h : ∃ j, r j = 0
  · have hS : (univ.filter (fun j => r j = 0)).Nonempty := by
      obtain ⟨j, hj⟩ := h
      exact ⟨j, by simp [hj]⟩
    have hmem : r ((univ.filter (fun j => r j = 0)).min' hS) = 0 := by
      have := Finset.min'_mem _ hS
      simpa using this
    refine ⟨((univ.filter (fun j => r j = 0)).min' hS).val, (Fin.isLt _).le, fun j => ?_⟩
    constructor
    · intro hj
      by_contra hlt
      have hle : (univ.filter (fun j => r j = 0)).min' hS ≤ j := Fin.le_def.mpr (by omega)
      rcases hle.lt_or_eq with hlt' | heq
      · have := hr j _ hlt' hj
        rw [hmem] at this
        exact fin2_ne this
      · rw [heq] at hmem
        rw [hmem] at hj
        exact fin2_ne hj
    · intro hj
      rcases fin2_cases (r j) with h0 | h1
      · have : (univ.filter (fun j => r j = 0)).min' hS ≤ j :=
          Finset.min'_le _ j (by simp [h0])
        exact absurd (Fin.le_def.mp this) (by omega)
      · exact h1
  · exact ⟨n, le_rfl, fun j => ⟨fun _ => j.isLt,
      fun _ => (fin2_cases (r j)).resolve_left (not_exists.mp h j)⟩⟩

/-- Row lengths of a staircase given by a triple. -/
def rowLen3 (x : ℕ × ℕ × ℕ) (k : ℕ) : ℕ := if k = 0 then x.1 else if k = 1 then x.2.1 else x.2.2

/-- The staircase array whose row `i` has ones exactly in its first `rowLen3 x i` columns. -/
def stair3 (n : ℕ) (x : ℕ × ℕ × ℕ) : Fin 3 → Fin n → Fin 2 :=
  fun i j => if j.val < rowLen3 x i.val then 1 else 0

/-- Monotone triples bounded by `n`. -/
def stairBox (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1)).filter
    (fun x => x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2)

theorem mem_stairBox {n : ℕ} {x : ℕ × ℕ × ℕ} :
    x ∈ stairBox n ↔ x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2 ∧ x.2.2 ≤ n := by
  unfold stairBox
  simp only [mem_filter, mem_product, mem_range]
  omega

theorem stair_eq_one {n : ℕ} (x : ℕ × ℕ × ℕ) (i : Fin 3) (j : Fin n) :
    stair3 n x i j = 1 ↔ j.val < rowLen3 x i.val := by
  unfold stair3
  split_ifs with h
  · simp [h]
  · simp [h]

theorem sorted_stair {n : ℕ} {A : Fin 3 → Fin n → Fin 2} (hA : Sorted A) :
    ∃ x ∈ stairBox n, A = stair3 n x := by
  have hrow : ∀ i : Fin 3, ∃ k, k ≤ n ∧ ∀ j : Fin n, A i j = 1 ↔ j.val < k :=
    fun i => row_len (A i) (row_prefix hA i)
  choose k hk hkA using hrow
  have hmono : ∀ i i' : Fin 3, i < i' → k i ≤ k i' := by
    intro i i' hii'
    by_contra hlt'
    have hlt : k i' < k i := not_le.mp hlt'
    have hj : k i' < n := lt_of_lt_of_le hlt (hk i)
    have h1 : A i ⟨k i', hj⟩ = 1 := (hkA i _).mpr hlt
    have h2 := (hkA i' _).mp (col_up hA _ i i' hii' h1)
    exact lt_irrefl _ h2
  refine ⟨(k 0, k 1, k 2), ?_, ?_⟩
  · rw [mem_stairBox]
    exact ⟨hmono 0 1 (by decide), hmono 1 2 (by decide), hk 2⟩
  · funext i j
    have htri : rowLen3 (k 0, k 1, k 2) i.val = k i := by
      fin_cases i <;> rfl
    unfold stair3
    rw [htri]
    split_ifs with h
    · exact (hkA i j).mpr h
    · exact (fin2_cases _).resolve_right (fun h' => h ((hkA i j).mp h'))

theorem tri_mono {n : ℕ} {x : ℕ × ℕ × ℕ} (hx : x ∈ stairBox n) {i i' : ℕ} (h : i ≤ i') :
    rowLen3 x i ≤ rowLen3 x i' := by
  rw [mem_stairBox] at hx
  unfold rowLen3
  split_ifs <;> omega

theorem stair_sorted {n : ℕ} {x : ℕ × ℕ × ℕ} (hx : x ∈ stairBox n) : Sorted (stair3 n x) := by
  constructor
  · intro i i' h
    show toLex (stair3 n x i) ≤ toLex (stair3 n x i')
    apply Pi.toLex_monotone
    intro j
    have := tri_mono hx (Fin.le_def.mp h)
    simp only [stair3]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · omega
    · exact Fin.zero_le _
    · exact le_rfl
  · intro j j' h
    show toLex (fun i => stair3 n x i j') ≤ toLex (fun i => stair3 n x i j)
    apply Pi.toLex_monotone
    intro i
    have := Fin.le_def.mp h
    simp only [stair3]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · omega
    · exact Fin.zero_le _
    · exact le_rfl

/-- Eroded row length: a row of length `x` keeps `fr n x` ones under its horizontal
neighbours. -/
def fr (n x : ℕ) : ℕ := if x = n then n else x - 1

/-- The row lengths of the eroded staircase. -/
def bv (n : ℕ) (x : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (fr n x.1, min (fr n x.2.1) (x.1 + 1), min (fr n x.2.2) (x.2.1 + 1))

/-- `Near` on indices. -/
def NearN (i j pi pj : ℕ) : Prop :=
  (pi = i ∧ pj = j) ∨ (pi = i ∧ (pj + 1 = j ∨ j + 1 = pj)) ∨
    ((pi + 1 = i ∧ pj + 1 = j) ∨ (i + 1 = pi ∧ j + 1 = pj))

theorem near_iff {n : ℕ} (i : Fin 3) (j : Fin n) (p : Fin 3 × Fin n) :
    Near i j p ↔ NearN i.val j.val p.1.val p.2.val := by
  unfold Near NearN
  simp only [Fin.ext_iff]

theorem erode_nat {n : ℕ} {x : ℕ × ℕ × ℕ} (hx : x ∈ stairBox n) (i j : ℕ) (hi : i < 3)
    (hj : j < n) :
    (∀ pi pj, pi < 3 → pj < n → NearN i j pi pj → pj < rowLen3 x pi) ↔
      j < rowLen3 (bv n x) i := by
  rw [mem_stairBox] at hx
  obtain ⟨x1, x2, x3⟩ := x
  simp only at hx
  constructor
  · intro h
    have h0 := h i j hi hj (Or.inl ⟨rfl, rfl⟩)
    have hR : j + 1 < n → j + 1 < rowLen3 (x1, x2, x3) i := fun hj1 =>
      h i (j + 1) hi hj1 (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩))
    have hNW : 1 ≤ i → 1 ≤ j → j - 1 < rowLen3 (x1, x2, x3) (i - 1) := fun h1 h2 =>
      h (i - 1) (j - 1) (by omega) (by omega) (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    have hSE : i + 1 < 3 → j + 1 < n → j + 1 < rowLen3 (x1, x2, x3) (i + 1) := fun h1 h2 =>
      h (i + 1) (j + 1) h1 h2 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    clear h
    interval_cases i <;> simp only [rowLen3, bv, fr] at h0 hR hNW hSE ⊢ <;> split_ifs at * <;>
      omega
  · intro h pi pj hpi hpj hN
    unfold NearN at hN
    interval_cases i <;> simp only [rowLen3, bv, fr] at h ⊢ <;> split_ifs at * <;> omega

theorem nbhdMin_eq_one {n : ℕ} (A : Fin 3 → Fin n → Fin 2) (i : Fin 3) (j : Fin n) :
    nbhdMin A i j = 1 ↔ ∀ p : Fin 3 × Fin n, Near i j p → A p.1 p.2 = 1 := by
  unfold nbhdMin
  rw [← fin2_one_le, Finset.le_inf_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, fin2_one_le]

theorem nbhdMin_stair {n : ℕ} {x : ℕ × ℕ × ℕ} (hx : x ∈ stairBox n) :
    nbhdMin (stair3 n x) = stair3 n (bv n x) := by
  funext i j
  have key : nbhdMin (stair3 n x) i j = 1 ↔ stair3 n (bv n x) i j = 1 := by
    rw [nbhdMin_eq_one, stair_eq_one, ← erode_nat hx i.val j.val i.isLt j.isLt]
    simp only [stair_eq_one]
    constructor
    · intro h pi pj hpi hpj hN
      exact h (⟨pi, hpi⟩, ⟨pj, hpj⟩) ((near_iff _ _ _).mpr hN)
    · intro h p hp
      exact h p.1.val p.2.val p.1.isLt p.2.isLt ((near_iff _ _ _).mp hp)
  rcases fin2_cases (nbhdMin (stair3 n x) i j) with h | h <;>
    rcases fin2_cases (stair3 n (bv n x) i j) with h' | h'
  · rw [h, h']
  · rw [h'] at key
    rw [key.mpr rfl] at h
    exact absurd h.symm fin2_ne
  · rw [h] at key
    rw [key.mp rfl] at h'
    exact absurd h' fin2_ne.symm
  · rw [h, h']

/-- The image of the monotone triples under erosion. -/
def Sn (n : ℕ) : Finset (ℕ × ℕ × ℕ) := (stairBox n).image (bv n)

theorem fr_le {n y : ℕ} (hy : y ≤ n) : fr n y ≤ n := by
  unfold fr; split_ifs <;> omega

theorem bv_le {n : ℕ} {x : ℕ × ℕ × ℕ} (hx : x ∈ stairBox n) (k : ℕ) :
    rowLen3 (bv n x) k ≤ n := by
  rw [mem_stairBox] at hx
  have h1 := fr_le (n := n) (y := x.1) (by omega)
  have h2 := fr_le (n := n) (y := x.2.1) (by omega)
  have h3 := fr_le (n := n) (y := x.2.2) (by omega)
  unfold rowLen3 bv
  split_ifs <;> simp only <;> omega

theorem stair_inj {n : ℕ} {b b' : ℕ × ℕ × ℕ} (hb : ∀ k, rowLen3 b k ≤ n)
    (hb' : ∀ k, rowLen3 b' k ≤ n) (h : stair3 n b = stair3 n b') : b = b' := by
  have key : ∀ k : Fin 3, rowLen3 b k.val = rowLen3 b' k.val := by
    intro k
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hj : rowLen3 b k.val < n := lt_of_lt_of_le hlt (hb' k.val)
      have e1 : stair3 n b' k ⟨rowLen3 b k.val, hj⟩ = 1 := (stair_eq_one _ _ _).mpr hlt
      rw [← h] at e1
      exact lt_irrefl _ ((stair_eq_one _ _ _).mp e1)
    · have hj : rowLen3 b' k.val < n := lt_of_lt_of_le hlt (hb k.val)
      have e1 : stair3 n b k ⟨rowLen3 b' k.val, hj⟩ = 1 := (stair_eq_one _ _ _).mpr hlt
      rw [h] at e1
      exact lt_irrefl _ ((stair_eq_one _ _ _).mp e1)
  obtain ⟨b1, b2, b3⟩ := b
  obtain ⟨c1, c2, c3⟩ := b'
  have e0 := key 0
  have e1 := key 1
  have e2 := key 2
  simp only [rowLen3, Fin.val_zero, Fin.val_one, Fin.val_two] at e0 e1 e2
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> simp_all

theorem a_eq (n : ℕ) : a n = (Sn n).card := by
  classical
  unfold a
  rw [Fintype.card_subtype]
  have himg : (univ.filter (fun B : Fin 3 → Fin n → Fin 2 =>
      ∃ A : Fin 3 → Fin n → Fin 2, Sorted A ∧ nbhdMin A = B)) = (Sn n).image (stair3 n) := by
    ext B
    simp only [mem_filter, mem_univ, true_and, mem_image, Sn]
    constructor
    · rintro ⟨A, hA, rfl⟩
      obtain ⟨x, hx, rfl⟩ := sorted_stair hA
      exact ⟨bv n x, ⟨x, hx, rfl⟩, (nbhdMin_stair hx).symm⟩
    · rintro ⟨b, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨stair3 n x, stair_sorted hx, nbhdMin_stair hx⟩
  rw [himg, card_image_of_injOn]
  intro b hb b' hb' h
  simp only [Sn, coe_image, Set.mem_image, mem_coe] at hb hb'
  obtain ⟨x, hx, rfl⟩ := hb
  obtain ⟨x', hx', rfl⟩ := hb'
  exact stair_inj (bv_le hx) (bv_le hx') h


theorem Sn_card_small : (Sn 1).card = 4 ∧ (Sn 2).card = 6 ∧ (Sn 3).card = 10 ∧
    (Sn 4).card = 19 ∧ (Sn 5).card = 30 ∧ (Sn 6).card = 42 := by
  decide +kernel


theorem mem_Sn {n : ℕ} {b : ℕ × ℕ × ℕ} : b ∈ Sn n ↔ ∃ x ∈ stairBox n, bv n x = b := by
  unfold Sn
  rw [mem_image]

/-- Shift of a triple by one in each coordinate. -/
def sh (b : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (b.1 + 1, b.2.1 + 1, b.2.2 + 1)

theorem sh_inj : Function.Injective sh := by
  rintro ⟨b1, b2, b3⟩ ⟨c1, c2, c3⟩ h
  simp only [sh, Prod.mk.injEq] at h ⊢
  omega

theorem fr_succ (n y : ℕ) (hy : 1 ≤ y) : fr (n + 1) (y + 1) = fr n y + 1 := by
  unfold fr
  split_ifs <;> omega

theorem bv_succ (n x1 x2 x3 : ℕ) (h1 : 1 ≤ x1) (h2 : x1 ≤ x2) (h3 : x2 ≤ x3) :
    bv (n + 1) (x1 + 1, x2 + 1, x3 + 1) = sh (bv n (x1, x2, x3)) := by
  simp only [bv, sh, fr_succ n x1 h1, fr_succ n x2 (by omega), fr_succ n x3 (by omega),
    Prod.mk.injEq, true_and]
  omega

/-- Prepending a column of ones: the image points with first coordinate at least 2 for `n + 1`
are the shifted image points with first coordinate at least 1 for `n`. -/
theorem shift_slices (n : ℕ) (hn : 2 ≤ n) :
    (Sn (n + 1)).filter (fun b => 2 ≤ b.1) = ((Sn n).filter (fun b => 1 ≤ b.1)).image sh := by
  ext b
  simp only [mem_filter, mem_image, mem_Sn]
  constructor
  · rintro ⟨⟨⟨x1, x2, x3⟩, hx, rfl⟩, h2⟩
    rw [mem_stairBox] at hx
    simp only at hx
    have hx1 : 3 ≤ x1 := by
      simp only [bv, fr] at h2
      split_ifs at h2 <;> omega
    obtain ⟨y1, rfl⟩ : ∃ y1, x1 = y1 + 1 := ⟨x1 - 1, by omega⟩
    obtain ⟨y2, rfl⟩ : ∃ y2, x2 = y2 + 1 := ⟨x2 - 1, by omega⟩
    obtain ⟨y3, rfl⟩ : ∃ y3, x3 = y3 + 1 := ⟨x3 - 1, by omega⟩
    rw [bv_succ n y1 y2 y3 (by omega) (by omega) (by omega)]
    refine ⟨bv n (y1, y2, y3), ⟨⟨(y1, y2, y3), ?_, rfl⟩, ?_⟩, rfl⟩
    · rw [mem_stairBox]
      simp only
      omega
    · simp only [bv, fr]
      split_ifs <;> omega
  · rintro ⟨b', ⟨⟨⟨x1, x2, x3⟩, hx, rfl⟩, h1⟩, rfl⟩
    rw [mem_stairBox] at hx
    simp only at hx
    have hx1 : 2 ≤ x1 := by
      simp only [bv, fr] at h1
      split_ifs at h1 <;> omega
    refine ⟨⟨(x1 + 1, x2 + 1, x3 + 1), ?_, bv_succ n x1 x2 x3 (by omega) hx.1 hx.2.1⟩, ?_⟩
    · rw [mem_stairBox]
      simp only
      omega
    · simp only [sh, bv, fr]
      split_ifs <;> omega

/-- The triples `(c, d, t)` with `t ∈ s`. -/
def colLine (c d : ℕ) (s : Finset ℕ) : Finset (ℕ × ℕ × ℕ) := s.image (fun t => (c, d, t))

theorem card_colLine (c d : ℕ) (s : Finset ℕ) : (colLine c d s).card = s.card := by
  unfold colLine
  apply card_image_of_injective
  intro t t' h
  simpa using h

theorem mem_colLine {c d : ℕ} {s : Finset ℕ} {b : ℕ × ℕ × ℕ} :
    b ∈ colLine c d s ↔ b.1 = c ∧ b.2.1 = d ∧ b.2.2 ∈ s := by
  obtain ⟨b1, b2, b3⟩ := b
  unfold colLine
  simp only [mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, ht⟩
  · rintro ⟨rfl, rfl, ht⟩
    exact ⟨b3, ht, rfl, rfl, rfl⟩

theorem disj_colLine {c d d' : ℕ} (h : d ≠ d') (s s' : Finset ℕ) :
    Disjoint (colLine c d s) (colLine c d' s') := by
  rw [Finset.disjoint_left]
  intro b hb hb'
  rw [mem_colLine] at hb hb'
  exact h (hb.2.1.symm.trans hb'.2.1)

/-- The image points with first coordinate 0, for `n ≥ 5`. -/
def sliceZero (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  colLine 0 0 (Icc 0 2) ∪ (colLine 0 1 (Icc 1 n) ∪ colLine 0 2 (Icc 2 n))

/-- The image points with first coordinate 1, for `n ≥ 6`. -/
def sliceOne (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  colLine 1 1 (Icc 1 3) ∪ (colLine 1 2 (Icc 2 4) ∪ colLine 1 3 (Icc 3 n))

theorem card_sliceZero (n : ℕ) (hn : 1 ≤ n) : (sliceZero n).card = 2 * n + 2 := by
  unfold sliceZero
  rw [card_union_of_disjoint (disjoint_union_right.mpr
      ⟨disj_colLine (by decide) _ _, disj_colLine (by decide) _ _⟩),
    card_union_of_disjoint (disj_colLine (by decide) _ _), card_colLine, card_colLine,
    card_colLine,
    Nat.card_Icc, Nat.card_Icc, Nat.card_Icc]
  omega

theorem card_sliceOne (n : ℕ) (hn : 2 ≤ n) : (sliceOne n).card = n + 4 := by
  unfold sliceOne
  rw [card_union_of_disjoint (disjoint_union_right.mpr
      ⟨disj_colLine (by decide) _ _, disj_colLine (by decide) _ _⟩),
    card_union_of_disjoint (disj_colLine (by decide) _ _), card_colLine, card_colLine,
    card_colLine,
    Nat.card_Icc, Nat.card_Icc, Nat.card_Icc]
  omega

theorem slice0 (n : ℕ) (hn : 5 ≤ n) : (Sn n).filter (fun b => b.1 = 0) = sliceZero n := by
  ext ⟨b1, b2, b3⟩
  simp only [mem_filter, mem_Sn, sliceZero, mem_union, mem_colLine, mem_Icc]
  constructor
  · rintro ⟨⟨⟨x1, x2, x3⟩, hx, hxb⟩, h0⟩
    rw [mem_stairBox] at hx
    simp only [bv, fr, Prod.mk.injEq] at hx hxb
    obtain ⟨e1, e2, e3⟩ := hxb
    split_ifs at e1 e2 e3 <;> omega
  · intro h
    have hb1 : b1 = 0 := by omega
    subst hb1
    refine ⟨?_, rfl⟩
    rcases h with ⟨-, hb2, hb3⟩ | ⟨-, hb2, hb3⟩ | ⟨-, hb2, hb3⟩
    · subst hb2
      refine ⟨(0, (if b3 = 2 then 1 else 0), (if b3 = 0 then 0 else n)), ?_, ?_⟩
      · rw [mem_stairBox]
        simp only
        split_ifs <;> omega
      · simp only [bv, fr, Prod.mk.injEq]
        split_ifs <;> omega
    · subst hb2
      refine ⟨(0, (if b3 + 2 ≤ n then b3 + 1 else if b3 + 1 = n then n - 2 else n),
        (if b3 + 2 ≤ n then b3 + 1 else n)), ?_, ?_⟩
      · rw [mem_stairBox]
        simp only
        split_ifs <;> omega
      · simp only [bv, fr, Prod.mk.injEq]
        split_ifs <;> omega
    · subst hb2
      refine ⟨(1, (if b3 + 2 ≤ n then b3 + 1 else if b3 + 1 = n then n - 2 else n),
        (if b3 + 2 ≤ n then b3 + 1 else n)), ?_, ?_⟩
      · rw [mem_stairBox]
        simp only
        split_ifs <;> omega
      · simp only [bv, fr, Prod.mk.injEq]
        split_ifs <;> omega

theorem slice1 (n : ℕ) (hn : 6 ≤ n) : (Sn n).filter (fun b => b.1 = 1) = sliceOne n := by
  ext ⟨b1, b2, b3⟩
  simp only [mem_filter, mem_Sn, sliceOne, mem_union, mem_colLine, mem_Icc]
  constructor
  · rintro ⟨⟨⟨x1, x2, x3⟩, hx, hxb⟩, h0⟩
    rw [mem_stairBox] at hx
    simp only [bv, fr, Prod.mk.injEq] at hx hxb
    obtain ⟨e1, e2, e3⟩ := hxb
    split_ifs at e1 e2 e3 <;> omega
  · intro h
    have hb1 : b1 = 1 := by omega
    subst hb1
    refine ⟨?_, rfl⟩
    rcases h with ⟨-, hb2, hb3⟩ | ⟨-, hb2, hb3⟩ | ⟨-, hb2, hb3⟩
    · subst hb2
      refine ⟨(2, 2, b3 + 1), ?_, ?_⟩
      · rw [mem_stairBox]
        simp only
        omega
      · simp only [bv, fr, Prod.mk.injEq]
        split_ifs <;> omega
    · subst hb2
      refine ⟨(2, 3, b3 + 1), ?_, ?_⟩
      · rw [mem_stairBox]
        simp only
        omega
      · simp only [bv, fr, Prod.mk.injEq]
        split_ifs <;> omega
    · subst hb2
      refine ⟨(2, (if b3 + 2 ≤ n then b3 + 1 else if b3 + 1 = n then n - 2 else n),
        (if b3 + 2 ≤ n then b3 + 1 else n)), ?_, ?_⟩
      · rw [mem_stairBox]
        simp only
        split_ifs <;> omega
      · simp only [bv, fr, Prod.mk.injEq]
        split_ifs <;> omega

theorem card_split0 (S : Finset (ℕ × ℕ × ℕ)) :
    S.card = (S.filter (fun b => b.1 = 0)).card + (S.filter (fun b => 1 ≤ b.1)).card := by
  rw [← card_filter_add_card_filter_not (s := S) (fun b : ℕ × ℕ × ℕ => b.1 = 0)]
  congr 2
  apply Finset.filter_congr
  intro b _
  omega

theorem card_split1 (S : Finset (ℕ × ℕ × ℕ)) :
    (S.filter (fun b => 1 ≤ b.1)).card =
      (S.filter (fun b => b.1 = 1)).card + (S.filter (fun b => 2 ≤ b.1)).card := by
  rw [← card_filter_add_card_filter_not (s := S.filter (fun b => 1 ≤ b.1))
    (fun b : ℕ × ℕ × ℕ => b.1 = 1), filter_filter, filter_filter]
  congr 2
  · apply Finset.filter_congr
    intro b _
    omega
  · apply Finset.filter_congr
    intro b _
    omega

theorem card_succ (n : ℕ) (hn : 6 ≤ n) : (Sn (n + 1)).card = (Sn n).card + n + 7 := by
  have h1 := card_split0 (Sn (n + 1))
  have h2 := card_split1 (Sn (n + 1))
  have h3 := card_split0 (Sn n)
  have h4 : ((Sn (n + 1)).filter (fun b => 2 ≤ b.1)).card =
      ((Sn n).filter (fun b => 1 ≤ b.1)).card := by
    rw [shift_slices n (by omega), card_image_of_injective _ sh_inj]
  rw [slice0 (n + 1) (by omega), card_sliceZero (n + 1) (by omega)] at h1
  rw [slice1 (n + 1) (by omega), card_sliceOne (n + 1) (by omega)] at h2
  rw [slice0 n (by omega), card_sliceZero n (by omega)] at h3
  omega

theorem closed2 (n : ℕ) (hn : 4 ≤ n) : 2 * (Sn n).card + 30 = n ^ 2 + 13 * n := by
  induction n, hn using Nat.le_induction with
  | base => rw [Sn_card_small.2.2.2.1]; norm_num
  | succ n hn ih =>
    rcases (show n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | h6
    · rw [Sn_card_small.2.2.2.2.1]; norm_num
    · rw [Sn_card_small.2.2.2.2.2]; norm_num
    · rw [card_succ n h6]
      have hsq : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      omega


theorem a_closed (n : ℕ) (hn : 4 ≤ n) : 2 * a n + 30 = n ^ 2 + 13 * n := by
  rw [a_eq]
  exact closed2 n hn

theorem closedQ (n : ℕ) (hn : 3 < n) :
    (a n : ℚ) = (1 / 2) * (n : ℚ) ^ 2 + (13 / 2) * (n : ℚ) - 15 := by
  have h : ((2 * a n + 30 : ℕ) : ℚ) = ((n ^ 2 + 13 * n : ℕ) : ℚ) := by
    rw [a_closed n (by omega)]
  push_cast at h
  linear_combination (1 / 2 : ℚ) * h

theorem a_one : a 1 = 4 := by
  rw [a_eq]
  exact Sn_card_small.1

theorem a_two : a 2 = 6 := by
  rw [a_eq]
  exact Sn_card_small.2.1

theorem a_three : a 3 = 10 := by
  rw [a_eq]
  exact Sn_card_small.2.2.1

theorem a_four : a 4 = 19 := by
  rw [a_eq]
  exact Sn_card_small.2.2.2.1

theorem a_five : a 5 = 30 := by
  rw [a_eq]
  exact Sn_card_small.2.2.2.2.1

theorem a_six : a 6 = 42 := by
  rw [a_eq]
  exact Sn_card_small.2.2.2.2.2

theorem recurrence (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  have h : ((a n : ℤ) : ℚ) = ((3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) : ℤ) : ℚ) := by
    push_cast
    rw [closedQ n (by omega), closedQ (n - 1) (by omega), closedQ (n - 2) (by omega),
      closedQ (n - 3) (by omega)]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega]
    ring
  exact_mod_cast h

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 3 =
      X * (4 - 6 * X + 4 * X ^ 2 + 3 * X ^ 3 - 3 * X ^ 4 - X ^ 5) := by
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℚ, F = fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) :=
    ⟨_, rfl⟩
  rw [← hF]
  have key : PowerSeries.mk F * (1 - X) ^ 3 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 3 * (PowerSeries.mk F * X ^ 1) +
        C 3 * (PowerSeries.mk F * X ^ 2) - C 1 * (PowerSeries.mk F * X ^ 3) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (4 - 6 * X + 4 * X ^ 2 + 3 * X ^ 3 - 3 * X ^ 4 - X ^ 5) =
      C 4 * X ^ 1 - C 6 * X ^ 2 + C 4 * X ^ 3 + C 3 * X ^ 4 - C 3 * X ^ 5 - C 1 * X ^ 6 := by
    simp only [map_one, map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 7
  · interval_cases k <;> simp only [hF] <;>
      norm_num [a_one, a_two, a_three, a_four, a_five, a_six]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
    simp only [show 0 ≤ j + 7 by omega, show 1 ≤ j + 7 by omega, show 2 ≤ j + 7 by omega,
      show 3 ≤ j + 7 by omega,
      show j + 7 - 0 = j + 7 by omega, show j + 7 - 1 = j + 6 by omega,
      show j + 7 - 2 = j + 5 by omega, show j + 7 - 3 = j + 4 by omega,
      show ¬ (j + 7 = 1) by omega, show ¬ (j + 7 = 2) by omega, show ¬ (j + 7 = 3) by omega,
      show ¬ (j + 7 = 4) by omega, show ¬ (j + 7 = 5) by omega, show ¬ (j + 7 = 6) by omega,
      show ¬ (j + 7 = 0) by omega, show ¬ (j + 6 = 0) by omega, show ¬ (j + 5 = 0) by omega,
      show ¬ (j + 4 = 0) by omega, if_true, if_false, hF]
    rw [closedQ (j + 7) (by omega), closedQ (j + 6) (by omega), closedQ (j + 5) (by omega),
      closedQ (j + 4) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a220033.main :=
  ⟨fun n hn => OMA.Helpers.closedQ n hn, OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
