import OMAStatements.S_oeis_a183983
import Mathlib

/-!
Proof of Barker's conjectures for A183983 (1/4 the number of (n+1) X 7 binary arrays with all
2 X 2 subblock sums the same).

* For `n >= 1` the common block sum `s` is determined by the array and lies in `0..4`, so the
  number of arrays is `Sum_{s < 5} #{arrays with every block sum equal to s}`.
* For a fixed `s`, reading the array row by row gives a chain of rows (7 bits) in which each row is
  compatible with the next one. With `N s m r` the number of ways to continue the row `r` by `m`
  rows, `N s (m + 1) r = Sum_t [Compat s r t] N s m t`. Rows are coded by 0..127; for each `s`
  and code `u` the compatible next rows form the explicit list `succT183983 s u` (at most two
  rows: the next row is determined by its first bit), checked by kernel computation. `G` is the
  transfer recursion on codes.
* For `m >= 1`, `G s m u` is `1`, `2 ^ m`, `2 ^ (m / 2)`, `2 ^ ((m + 1) / 2)` or `0` according to
  the class `cls183983 s u`; the base case and the induction step reduce to finite checks.
  Summing over the 640 pairs `(s, u)` gives
  `#arrays = 168 + 2 * 2 ^ n + 4 * 2 ^ (n / 2) + 2 * 2 ^ ((n + 1) / 2)`, hence
  `a (m + 1) = 42 + 2 ^ m + 2 ^ ((m + 1) / 2) + 2 ^ (m / 2)`. The closed forms, the recurrence and
  the generating function follow.
-/

namespace OMA.Helpers

open OMA.S_oeis_a183983 Finset

/-- A row of the array. -/
abbrev Row183983 := Fin 7 → Bool

/-- Every block of the two consecutive rows `r` (upper) and `t` (lower) has sum `s`. -/
def Compat183983 (s : ℕ) (r t : Row183983) : Prop :=
  ∀ j : Fin 6, blockSum (r j.castSucc) (r j.succ) (t j.castSucc) (t j.succ) = s

instance decCompat183983 (s : ℕ) (r t : Row183983) : Decidable (Compat183983 s r t) := by
  unfold Compat183983
  infer_instance

/-- Every block of the array has sum `s`. -/
def Good183983 (s n : ℕ) (x : Fin (n + 1) → Row183983) : Prop :=
  ∀ (i : Fin n) (j : Fin 6), blockSum (x i.castSucc j.castSucc) (x i.castSucc j.succ)
    (x i.succ j.castSucc) (x i.succ j.succ) = s

instance decGood183983 (s n : ℕ) (x : Fin (n + 1) → Row183983) :
    Decidable (Good183983 s n x) := by
  unfold Good183983
  infer_instance

theorem good_zero183983 (s : ℕ) (x : Fin 1 → Row183983) : Good183983 s 0 x :=
  fun i => absurd i.isLt (by omega)

theorem good_cons183983 (s : ℕ) {m : ℕ} (r : Row183983) (A : Fin (m + 1) → Row183983) :
    Good183983 s (m + 1) (Fin.cons r A : Fin (m + 2) → Row183983) ↔
      Compat183983 s r (A 0) ∧ Good183983 s m A := by
  unfold Good183983 Compat183983
  constructor
  · intro h
    refine ⟨fun j => ?_, fun i j => ?_⟩
    · have h0 := h 0 j
      simpa using h0
    · have h1 := h i.succ j
      simpa [← Fin.succ_castSucc] using h1
  · rintro ⟨h0, h⟩ i j
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using h0 j
    · have h1 := h i j
      simpa [← Fin.succ_castSucc] using h1

theorem blockSum_le183983 : ∀ a b c d : Bool, blockSum a b c d < 5 := by
  decide

/-- The number of ways to continue the row `r` by `m` more rows. -/
noncomputable def N183983 (s m : ℕ) (r : Row183983) : ℕ :=
  ∑ A : Fin m → Row183983,
    if Good183983 s m (Fin.cons r A : Fin (m + 1) → Row183983) then 1 else 0

theorem N_zero183983 (s : ℕ) (r : Row183983) : N183983 s 0 r = 1 := by
  unfold N183983
  rw [Fintype.sum_unique, if_pos (good_zero183983 _ _)]

theorem N_succ183983 (s m : ℕ) (r : Row183983) :
    N183983 s (m + 1) r = ∑ t : Row183983, if Compat183983 s r t then N183983 s m t else 0 := by
  unfold N183983
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row183983).symm _
    (fun p => if Good183983 s (m + 1) (Fin.cons r (Fin.cons p.1 p.2) : Fin (m + 2) → Row183983)
      then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hc : Compat183983 s r t
  · rw [if_pos hc]
    refine Finset.sum_congr rfl fun A _ => if_congr ?_ rfl rfl
    rw [good_cons183983]
    simp only [Fin.cons_zero]
    exact and_iff_right hc
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun A _ => if_neg ?_
    rw [good_cons183983]
    simp only [Fin.cons_zero]
    exact fun h => hc h.1

theorem card_good183983 (s n : ℕ) :
    (∑ x : Fin (n + 1) → Row183983, if Good183983 s n x then 1 else 0) =
      ∑ r : Row183983, N183983 s n r := by
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row183983).symm _
    (fun p => if Good183983 s n (Fin.cons p.1 p.2 : Fin (n + 1) → Row183983) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  rfl

open Classical in
/-- The statement's count, as a sum over row-major arrays. -/
theorem a_eq_sum183983 (m : ℕ) :
    4 * A183983 (m + 1) + (∑ x : Fin (m + 2) → Row183983,
      if ∃ s, Good183983 s (m + 1) x then 1 else 0) % 4 =
      ∑ x : Fin (m + 2) → Row183983, if ∃ s, Good183983 s (m + 1) x then 1 else 0 := by
  have h : (Finset.univ.filter (fun A : Fin (m + 1 + 1) × Fin 7 → Bool =>
      ∃ s : ℕ, ∀ (i : Fin (m + 1)) (j : Fin 6),
        blockSum (A (⟨i.1, by omega⟩, ⟨j.1, by omega⟩))
          (A (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩))
          (A (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩))
          (A (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩)) = s)).card =
      ∑ x : Fin (m + 2) → Row183983, if ∃ s, Good183983 s (m + 1) x then 1 else 0 := by
    classical
    rw [Finset.card_filter]
    exact Fintype.sum_equiv (Equiv.curry _ _ _) _ _ (fun A => if_congr Iff.rfl rfl rfl)
  unfold A183983
  rw [h]
  exact Nat.div_add_mod _ 4

open Classical in
theorem exists_split183983 (m : ℕ) (x : Fin (m + 2) → Row183983) :
    (if ∃ s, Good183983 s (m + 1) x then 1 else 0) =
      ∑ s ∈ range 5, if Good183983 s (m + 1) x then 1 else 0 := by
  have key : ∀ s, Good183983 s (m + 1) x →
      s = blockSum (x 0 0) (x 0 1) (x 1 0) (x 1 1) := by
    intro s hs
    exact (hs 0 0).symm
  by_cases h : ∃ s, Good183983 s (m + 1) x
  · obtain ⟨s, hs⟩ := h
    have hs5 : s < 5 := by
      rw [key s hs]
      exact blockSum_le183983 _ _ _ _
    rw [if_pos (Exists.intro s hs), Finset.sum_eq_single s]
    · rw [if_pos hs]
    · intro b _ hb
      rw [if_neg]
      intro hb'
      exact hb ((key b hb').trans (key s hs).symm)
    · intro hs'
      exact absurd (mem_range.2 hs5) hs'
  · rw [if_neg h]
    symm
    refine Finset.sum_eq_zero fun s _ => if_neg fun hs => h ⟨s, hs⟩

/-- The row with code `u`: the entry of column `j` is bit `j` of `u`. -/
def row183983 (u : Fin 128) : Row183983 :=
  fun j => decide (u.val / 2 ^ j.val % 2 = 1)

/-- The code of a row. -/
def code183983 (r : Row183983) : ℕ :=
  ∑ j : Fin 7, if r j then 2 ^ j.val else 0

theorem code_row183983 : ∀ u : Fin 128, code183983 (row183983 u) = u.val := by
  decide +kernel

theorem row_bijective183983 : Function.Bijective row183983 := by
  have hinj : Function.Injective row183983 := by
    intro u v huv
    apply Fin.ext
    rw [← code_row183983 u, ← code_row183983 v, huv]
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨hinj, by simp⟩

/-- Successor rows (codes) of the row with code `u` when every block sum is `s`. -/
def succT183983 : Fin 5 → Fin 128 → List (Fin 128) :=
  ![![[0], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], []],
    ![[42, 85], [84], [40], [], [81], [80], [], [],
      [34], [], [32], [], [], [], [], [],
      [69], [68], [], [], [65], [64], [], [],
      [], [], [], [], [], [], [], [],
      [10], [], [8], [], [], [], [], [],
      [2], [], [0], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [21], [20], [], [], [17], [16], [], [],
      [], [], [], [], [], [], [], [],
      [5], [4], [], [], [1], [0], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], []],
    ![[127], [126], [125], [124], [123], [122], [121], [120],
      [119], [118], [117], [116], [115], [114], [113], [112],
      [111], [110], [109], [108], [107], [106], [105], [104],
      [103], [102], [101], [100], [99], [98], [97], [96],
      [95], [94], [93], [92], [91], [90], [89], [88],
      [87], [86], [42, 85], [84], [83], [82], [81], [80],
      [79], [78], [77], [76], [75], [74], [73], [72],
      [71], [70], [69], [68], [67], [66], [65], [64],
      [63], [62], [61], [60], [59], [58], [57], [56],
      [55], [54], [53], [52], [51], [50], [49], [48],
      [47], [46], [45], [44], [43], [42, 85], [41], [40],
      [39], [38], [37], [36], [35], [34], [33], [32],
      [31], [30], [29], [28], [27], [26], [25], [24],
      [23], [22], [21], [20], [19], [18], [17], [16],
      [15], [14], [13], [12], [11], [10], [9], [8],
      [7], [6], [5], [4], [3], [2], [1], [0]],
    ![[], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [127], [126], [], [], [123], [122],
      [], [], [], [], [], [], [], [],
      [], [], [111], [110], [], [], [107], [106],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [127], [], [125],
      [], [], [], [], [], [119], [], [117],
      [], [], [], [], [], [], [], [],
      [], [], [63], [62], [], [], [59], [58],
      [], [], [], [], [], [95], [], [93],
      [], [], [47], [46], [], [87], [43], [42, 85]],
    ![[], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [],
      [], [], [], [], [], [], [], [127]]]

/-- Class of the row `u` for block sum `s`: 0 dead, 1 constant, 2 doubling, 3 and 4 the two
square-root-of-two classes. -/
def cls183983 : Fin 5 → Fin 128 → ℕ :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 4],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

theorem ok_iff0_183983 : ∀ u v : Fin 128,
    Compat183983 0 (row183983 u) (row183983 v) ↔ v ∈ succT183983 0 u := by
  decide +kernel

theorem ok_iff1_183983 : ∀ u v : Fin 128,
    Compat183983 1 (row183983 u) (row183983 v) ↔ v ∈ succT183983 1 u := by
  decide +kernel

theorem ok_iff2_183983 : ∀ u v : Fin 128,
    Compat183983 2 (row183983 u) (row183983 v) ↔ v ∈ succT183983 2 u := by
  decide +kernel

theorem ok_iff3_183983 : ∀ u v : Fin 128,
    Compat183983 3 (row183983 u) (row183983 v) ↔ v ∈ succT183983 3 u := by
  decide +kernel

theorem ok_iff4_183983 : ∀ u v : Fin 128,
    Compat183983 4 (row183983 u) (row183983 v) ↔ v ∈ succT183983 4 u := by
  decide +kernel

theorem ok_iff183983 (s : Fin 5) (u v : Fin 128) :
    Compat183983 s.val (row183983 u) (row183983 v) ↔ v ∈ succT183983 s u := by
  fin_cases s
  · exact ok_iff0_183983 u v
  · exact ok_iff1_183983 u v
  · exact ok_iff2_183983 u v
  · exact ok_iff3_183983 u v
  · exact ok_iff4_183983 u v

theorem nodup183983 : ∀ s : Fin 5, ∀ u : Fin 128, (succT183983 s u).Nodup := by
  decide +kernel

theorem sum_mem183983 (L : List (Fin 128)) (hL : L.Nodup) (f : Fin 128 → ℕ) :
    (∑ v : Fin 128, if v ∈ L then f v else 0) = (L.map f).sum := by
  rw [← Finset.sum_filter]
  have h : (Finset.univ.filter fun v : Fin 128 => v ∈ L) = L.toFinset := by
    ext v
    simp
  rw [h, List.sum_toFinset _ hL]

/-- The transfer recursion on codes. -/
def G183983 (s : Fin 5) : ℕ → Fin 128 → ℕ
  | 0, _ => 1
  | m + 1, u => ((succT183983 s u).map (G183983 s m)).sum

theorem N_eq_G183983 (s : Fin 5) (m : ℕ) :
    ∀ u : Fin 128, N183983 s.val m (row183983 u) = G183983 s m u := by
  induction m with
  | zero => intro u; rw [N_zero183983]; rfl
  | succ m ih =>
    intro u
    rw [N_succ183983, ← row_bijective183983.sum_comp]
    simp only [G183983]
    rw [← sum_mem183983 _ (nodup183983 s u)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [ih v]
    exact if_congr (ok_iff183983 s u v) rfl rfl

/-- The coefficient table: class `c` of `(s, u)` selects basis element `c - 1`. -/
def CT183983 (s : Fin 5) (u : Fin 128) (k : Fin 4) : ℕ :=
  if cls183983 s u = k.val + 1 then 1 else 0

/-- The basis values `1, 2 ^ m, 2 ^ (m / 2), 2 ^ ((m + 1) / 2)`. -/
def W183983 (m : ℕ) : Fin 4 → ℕ := ![1, 2 ^ m, 2 ^ (m / 2), 2 ^ ((m + 1) / 2)]

/-- The coefficients after the shift `m -> m + 1`. -/
def Tn183983 (s : Fin 5) (u : Fin 128) : Fin 4 → ℕ :=
  ![CT183983 s u 0, 2 * CT183983 s u 1, 2 * CT183983 s u 3, CT183983 s u 2]

theorem base_facts183983 : ∀ s : Fin 5, ∀ u : Fin 128,
    G183983 s 1 u = CT183983 s u 0 + 2 * CT183983 s u 1 + CT183983 s u 2 +
      2 * CT183983 s u 3 := by
  decide +kernel

theorem step_facts183983 : ∀ s : Fin 5, ∀ u : Fin 128, ∀ k : Fin 4,
    ((succT183983 s u).map (fun v => CT183983 s v k)).sum = Tn183983 s u k := by
  decide +kernel

theorem shift183983 (s : Fin 5) (u : Fin 128) (m : ℕ) :
    ∑ k : Fin 4, Tn183983 s u k * W183983 m k = ∑ k : Fin 4, CT183983 s u k * W183983 (m + 1) k := by
  simp only [Fin.sum_univ_four, Tn183983, W183983]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  have h1 : (m + 1 + 1) / 2 = m / 2 + 1 := by omega
  rw [h1, pow_succ, pow_succ]
  ring

theorem lsum_lin183983 (L : List (Fin 128)) (c : Fin 128 → Fin 4 → ℕ) (w : Fin 4 → ℕ) :
    (L.map (fun v => ∑ k : Fin 4, c v k * w k)).sum =
      ∑ k : Fin 4, (L.map (fun v => c v k)).sum * w k := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, ih, ← Finset.sum_add_distrib, add_mul]

theorem G_closed183983 (s : Fin 5) (m : ℕ) : ∀ u : Fin 128,
    G183983 s (m + 1) u = ∑ k : Fin 4, CT183983 s u k * W183983 (m + 1) k := by
  induction m with
  | zero =>
    intro u
    rw [base_facts183983 s u]
    simp only [Fin.sum_univ_four, W183983]
    simp
    ring
  | succ m ih =>
    intro u
    have h1 : G183983 s (m + 1 + 1) u =
        ((succT183983 s u).map (fun v => ∑ k : Fin 4, CT183983 s v k * W183983 (m + 1) k)).sum := by
      rw [G183983]
      congr 1
      exact List.map_congr_left fun v _ => ih v
    rw [h1, lsum_lin183983]
    simp only [step_facts183983 s u]
    exact shift183983 s u (m + 1)

/-- Column sums of `CT183983`. -/
def TOT183983 : Fin 4 → ℕ := ![168, 2, 4, 2]

theorem tot_facts183983 : ∀ k : Fin 4,
    (∑ s : Fin 5, ∑ u : Fin 128, CT183983 s u k) = TOT183983 k := by
  decide +kernel

theorem total183983 (m : ℕ) :
    (∑ s : Fin 5, ∑ u : Fin 128, G183983 s (m + 1) u) =
      ∑ k : Fin 4, TOT183983 k * W183983 (m + 1) k := by
  simp only [G_closed183983]
  have h : ∀ s : Fin 5, (∑ u : Fin 128, ∑ k : Fin 4, CT183983 s u k * W183983 (m + 1) k) =
      ∑ k : Fin 4, (∑ u : Fin 128, CT183983 s u k) * W183983 (m + 1) k := by
    intro s
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
  simp only [h]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, tot_facts183983]

open Classical in
theorem count183983 (m : ℕ) :
    (∑ x : Fin (m + 2) → Row183983, if ∃ s, Good183983 s (m + 1) x then 1 else 0) =
      4 * (42 + 2 ^ m + 2 ^ ((m + 1) / 2) + 2 ^ (m / 2)) := by
  simp only [exists_split183983]
  rw [Finset.sum_comm]
  have h1 : ∀ s ∈ range 5,
      (∑ x : Fin (m + 2) → Row183983, if Good183983 s (m + 1) x then 1 else 0) =
        ∑ r : Row183983, N183983 s (m + 1) r := fun s _ => card_good183983 s (m + 1)
  rw [Finset.sum_congr rfl h1, ← Fin.sum_univ_eq_sum_range
    (fun s => ∑ r : Row183983, N183983 s (m + 1) r) 5]
  have h2 : ∀ s : Fin 5, (∑ r : Row183983, N183983 s.val (m + 1) r) =
      ∑ u : Fin 128, G183983 s (m + 1) u := by
    intro s
    rw [← row_bijective183983.sum_comp]
    exact Finset.sum_congr rfl fun u _ => N_eq_G183983 s (m + 1) u
  rw [Finset.sum_congr rfl fun s _ => h2 s, total183983]
  simp only [Fin.sum_univ_four, TOT183983, W183983]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  have h3 : (m + 1 + 1) / 2 = m / 2 + 1 := by omega
  rw [h3, pow_succ, pow_succ]
  ring

theorem a_closed183983 (m : ℕ) :
    A183983 (m + 1) = 42 + 2 ^ m + 2 ^ ((m + 1) / 2) + 2 ^ (m / 2) := by
  have h := a_eq_sum183983 m
  rw [count183983 m] at h
  omega

theorem closed_parity183983 (n : ℕ) (hn : 1 ≤ n) :
    if Even n then 2 * A183983 n = 3 * 2 ^ (n / 2) + 2 ^ n + 84
    else A183983 n = 2 ^ ((n + 1) / 2) + 2 ^ (n - 1) + 42 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_closed183983 m]
  rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
  · -- m = 2t, n odd
    subst ht
    have hodd : ¬ Even (t + t + 1) := by
      rw [Nat.not_even_iff_odd]
      exact ⟨t, by ring⟩
    rw [if_neg hodd]
    have e1 : (t + t + 1) / 2 = t := by omega
    have e2 : (t + t) / 2 = t := by omega
    have e3 : (t + t + 1 + 1) / 2 = t + 1 := by omega
    have e4 : t + t + 1 - 1 = t + t := by omega
    rw [e1, e2, e3, e4, pow_succ]
    ring
  · -- m = 2t + 1, n even
    subst ht
    have hev : Even (2 * t + 1 + 1) := ⟨t + 1, by ring⟩
    rw [if_pos hev]
    have e1 : (2 * t + 1 + 1) / 2 = t + 1 := by omega
    have e2 : (2 * t + 1) / 2 = t := by omega
    rw [e1, e2]
    ring

/-- `2 ^ ((m + 1) / 2)`. -/
def P183983 (m : ℕ) : ℕ := 2 ^ ((m + 1) / 2)

/-- `2 ^ (m / 2)`. -/
def Q183983 (m : ℕ) : ℕ := 2 ^ (m / 2)

theorem P_two183983 (m : ℕ) : P183983 (m + 2) = 2 * P183983 m := by
  unfold P183983
  rw [show (m + 2 + 1) / 2 = (m + 1) / 2 + 1 by omega, pow_succ]
  ring

theorem Q_two183983 (m : ℕ) : Q183983 (m + 2) = 2 * Q183983 m := by
  unfold Q183983
  rw [show (m + 2) / 2 = m / 2 + 1 by omega, pow_succ]
  ring

theorem a_closed'183983 (m : ℕ) :
    A183983 (m + 1) = 42 + 2 ^ m + P183983 m + Q183983 m := a_closed183983 m

theorem recurrence183983 (n : ℕ) (hn : 4 < n) :
    (A183983 n : ℤ) = 3 * A183983 (n - 1) - 6 * A183983 (n - 3) + 4 * A183983 (n - 4) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 5 := ⟨n - 5, by omega⟩
  simp only [show j + 5 - 1 = j + 4 by omega, show j + 5 - 3 = j + 2 by omega,
    show j + 5 - 4 = j + 1 by omega]
  have e5 : A183983 (j + 5) = 42 + 2 ^ (j + 4) + P183983 (j + 4) + Q183983 (j + 4) :=
    a_closed'183983 (j + 4)
  have e4 : A183983 (j + 4) = 42 + 2 ^ (j + 3) + P183983 (j + 3) + Q183983 (j + 3) :=
    a_closed'183983 (j + 3)
  have e2 : A183983 (j + 2) = 42 + 2 ^ (j + 1) + P183983 (j + 1) + Q183983 (j + 1) :=
    a_closed'183983 (j + 1)
  have e1 : A183983 (j + 1) = 42 + 2 ^ j + P183983 j + Q183983 j := a_closed'183983 j
  have f1 : P183983 (j + 4) = 2 * P183983 (j + 2) := P_two183983 (j + 2)
  have f2 : P183983 (j + 2) = 2 * P183983 j := P_two183983 j
  have f3 : P183983 (j + 3) = 2 * P183983 (j + 1) := P_two183983 (j + 1)
  have g1 : Q183983 (j + 4) = 2 * Q183983 (j + 2) := Q_two183983 (j + 2)
  have g2 : Q183983 (j + 2) = 2 * Q183983 j := Q_two183983 j
  have g3 : Q183983 (j + 3) = 2 * Q183983 (j + 1) := Q_two183983 (j + 1)
  rw [e5, e4, e2, e1, f1, f2, f3, g1, g2, g3]
  push_cast
  ring

open PowerSeries in
theorem gen_fun183983 :
    (1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A183983 n : ℤ)) =
      PowerSeries.X * (45 - 88 * PowerSeries.X - 91 * PowerSeries.X ^ 2 + 176 * PowerSeries.X ^ 3) := by
  set f : ℕ → ℤ := fun n => if n = 0 then (0 : ℤ) else (A183983 n : ℤ) with hfdef
  have key : (1 - X) * (1 - 2 * X) * (1 - 2 * X ^ 2) * PowerSeries.mk f =
      C 1 * (PowerSeries.mk f * X ^ 0) - C 3 * (PowerSeries.mk f * X ^ 1) +
        C 6 * (PowerSeries.mk f * X ^ 3) - C 4 * (PowerSeries.mk f * X ^ 4) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℤ⟦X⟧) * (45 - 88 * X - 91 * X ^ 2 + 176 * X ^ 3) =
      C 45 * X ^ 1 - C 88 * X ^ 2 - C 91 * X ^ 3 + C 176 * X ^ 4 := by
    simp only [map_ofNat]
    ring
  have hf : ∀ t : ℕ, f (t + 1) = (A183983 (t + 1) : ℤ) := by
    intro t
    simp only [hfdef, if_neg (Nat.succ_ne_zero t)]
  have v1 : A183983 1 = 45 := by rw [a_closed183983]; norm_num
  have v2 : A183983 2 = 47 := by rw [a_closed183983]; norm_num
  have v3 : A183983 3 = 50 := by rw [a_closed183983]; norm_num
  have v4 : A183983 4 = 56 := by rw [a_closed183983]; norm_num
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 5
  · interval_cases k <;>
      simp only [hfdef, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true, if_false,
        v1, v2, v3, v4] <;>
      norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
    simp only [show 0 ≤ j + 5 by omega, show 1 ≤ j + 5 by omega, show 3 ≤ j + 5 by omega,
      show 4 ≤ j + 5 by omega,
      show j + 5 - 0 = (j + 4) + 1 by omega, show j + 5 - 1 = (j + 3) + 1 by omega,
      show j + 5 - 3 = (j + 1) + 1 by omega, show j + 5 - 4 = j + 1 by omega,
      show ¬ (j + 5 = 1) by omega, show ¬ (j + 5 = 2) by omega, show ¬ (j + 5 = 3) by omega,
      show ¬ (j + 5 = 4) by omega, if_true, if_false, hf]
    have hr := recurrence183983 (j + 5) (by omega)
    simp only [show j + 5 - 1 = j + 3 + 1 by omega, show j + 5 - 3 = j + 1 + 1 by omega,
      show j + 5 - 4 = j + 1 by omega] at hr
    simp only [map_one, one_mul, map_ofNat]
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a183983.main :=
  ⟨OMA.Helpers.gen_fun183983, OMA.Helpers.closed_parity183983, OMA.Helpers.recurrence183983⟩
