import OMAStatements.S_oeis_a183981
import Mathlib

/-!
Proof of Barker's conjectures for A183981 (one quarter of the number of (n+1) X 5 binary arrays
with all 2 X 2 subblock sums equal).

Read the array row by row (`Equiv.curry`). For a fixed value `s` the condition only involves two
consecutive rows (`Compat s`), so an array is good iff it is a `Chain s` for some `s`. For `n ≥ 1`
there is at least one block, so `s` is unique and at most 4: the count is the sum over
`s = 0, ..., 4` of the number of chains (`exists_split`). Removing the first row gives the
transfer recursion `N s (m + 1) r = Sum_t [Compat s r t] N s m t` (`N_succ`).

Rows are coded by the numbers below 32 (bit `j` is the entry of column `j`); `ok s u v` tests the
block sums on codes, checked once against `Compat` for all `s ≤ 4` and all pairs of codes. `G s m u`
is the transfer recursion on codes. Its values for `m ≤ 5` are tabulated (`stage`), and for every
state, `G s (m + 4) = 3 G s (m + 3) - 6 G s (m + 1) + 4 G s m` for `m ≥ 1` (`rec_G`): the
difference satisfies the same transfer recursion and vanishes at `m = 1` (a finite check).
Summing over states, the total `T m` satisfies the recurrence of `(1-x)(1-2x)(1-2x^2)`, and by a
two-step induction `T (2k+1) = 4 (2^(k+1) + 2^(2k) + 12)`, `T (2k+2) = 4 (3 2^k + 2 2^(2k) + 12)`.
The closed form, the recurrence for `a` and the generating function follow.
-/

namespace OMA.Helpers

open OMA.S_oeis_a183981 Finset

/-- A row of the array. -/
abbrev Row := Fin 5 → Bool

/-- All 2 X 2 block sums between the row `r` and the row `t` below it equal `s`. -/
def Compat (s : ℕ) (r t : Row) : Prop :=
  ∀ j : Fin 4, blockSum (r ⟨j.1, by omega⟩) (r ⟨j.1 + 1, by omega⟩)
    (t ⟨j.1, by omega⟩) (t ⟨j.1 + 1, by omega⟩) = s

instance decCompat (s : ℕ) (r t : Row) : Decidable (Compat s r t) := by
  unfold Compat
  infer_instance

/-- Each row of `A` is `Compat s` with the next one. -/
def Chain (s : ℕ) {m : ℕ} (A : Fin m → Row) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < m), Compat s (A ⟨i, by omega⟩) (A ⟨i + 1, hi⟩)

theorem blockSum_le (a b c d : Bool) : blockSum a b c d ≤ 4 := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem good_iff {n : ℕ} (A : Fin (n + 1) → Row) :
    (∃ s : ℕ, ∀ (i : Fin n) (j : Fin 4),
      blockSum (A ⟨i.1, by omega⟩ ⟨j.1, by omega⟩) (A ⟨i.1, by omega⟩ ⟨j.1 + 1, by omega⟩)
        (A ⟨i.1 + 1, by omega⟩ ⟨j.1, by omega⟩) (A ⟨i.1 + 1, by omega⟩ ⟨j.1 + 1, by omega⟩) = s) ↔
      ∃ s, Chain s A := by
  constructor
  · rintro ⟨s, h⟩
    exact ⟨s, fun i hi j => h ⟨i, by omega⟩ j⟩
  · rintro ⟨s, h⟩
    exact ⟨s, fun i j => h i.1 (by omega) j⟩

open Classical in
theorem card_eq (n : ℕ) :
    A183981 n = (∑ A : Fin (n + 1) → Row, if (∃ s, Chain s A) then 1 else 0) / 4 := by
  unfold A183981
  congr 1
  rw [Finset.card_filter, ← (Equiv.curry (Fin (n + 1)) (Fin 5) Bool).symm.sum_comp]
  exact Finset.sum_congr rfl fun A _ => if_congr (good_iff A) rfl rfl

open Classical in
theorem exists_split {m : ℕ} (A : Fin (m + 2) → Row) :
    (if (∃ s, Chain s A) then 1 else 0 : ℕ) = ∑ s ∈ range 5, if Chain s A then 1 else 0 := by
  by_cases h : ∃ s, Chain s A
  · obtain ⟨s0, hs0⟩ := h
    rw [if_pos ⟨s0, hs0⟩]
    have hlt : s0 < 5 := by
      have h0 := hs0 0 (by omega) ⟨0, by omega⟩
      exact Nat.lt_succ_of_le (h0.symm.trans_le (blockSum_le _ _ _ _))
    rw [Finset.sum_eq_single s0]
    · rw [if_pos hs0]
    · intro b _ hb
      rw [if_neg]
      intro hb'
      apply hb
      have e1 := hb' 0 (by omega) ⟨0, by omega⟩
      have e2 := hs0 0 (by omega) ⟨0, by omega⟩
      exact e1.symm.trans e2
    · intro hn
      exact absurd (mem_range.2 hlt) hn
  · rw [if_neg h]
    symm
    exact Finset.sum_eq_zero fun s _ => if_neg fun hc => h ⟨s, hc⟩

theorem chain_one (s : ℕ) (A : Fin 1 → Row) : Chain s A := fun i hi => absurd hi (by omega)

theorem chain_cons (s : ℕ) {m : ℕ} (r : Row) (A : Fin (m + 1) → Row) :
    Chain s (Fin.cons r A : Fin (m + 2) → Row) ↔ Compat s r (A ⟨0, by omega⟩) ∧ Chain s A := by
  constructor
  · intro h
    have h0 := h 0 (by omega)
    exact ⟨h0, fun i hi => h (i + 1) (by omega)⟩
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => exact h0
    | succ i => exact h i (by omega)

/-- The number of ways to continue the row `r` by `m` more rows into a `Chain s`. -/
noncomputable def N (s m : ℕ) (r : Row) : ℕ := by
  classical
  exact ∑ A : Fin m → Row, if Chain s (Fin.cons r A : Fin (m + 1) → Row) then 1 else 0

theorem N_zero (s : ℕ) (r : Row) : N s 0 r = 1 := by
  classical
  unfold N
  rw [Fintype.sum_unique, if_pos (chain_one _ _)]

theorem N_succ (s m : ℕ) (r : Row) :
    N s (m + 1) r = ∑ t : Row, if Compat s r t then N s m t else 0 := by
  classical
  unfold N
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if Chain s (Fin.cons r (Fin.cons p.1 p.2) : Fin (m + 2) → Row) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hc : Compat s r t
  · rw [if_pos hc]
    refine Finset.sum_congr rfl fun A _ => if_congr ?_ rfl rfl
    rw [chain_cons]
    exact and_iff_right hc
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun A _ => if_neg ?_
    rw [chain_cons]
    exact fun h => hc h.1

open Classical in
theorem sum_chain (s m : ℕ) :
    (∑ A : Fin (m + 1) → Row, if Chain s A then 1 else 0) = ∑ r : Row, N s m r := by
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if Chain s (Fin.cons p.1 p.2 : Fin (m + 1) → Row) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  unfold N
  rfl

/-- The row with code `u`: the entry of column `j` is bit `j` of `u`. -/
def row (u : Fin 32) : Row := fun j => Nat.testBit u.val j.val

theorem row_injective : Function.Injective row := by
  decide +kernel

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

/-- The block sum at columns `j`, `j + 1` of the rows with codes `u`, `v`. -/
def bs (u v j : ℕ) : ℕ := (u >>> j) % 2 + (u >>> (j + 1)) % 2 + (v >>> j) % 2 + (v >>> (j + 1)) % 2

/-- `Compat` on codes. -/
def ok (s : ℕ) (u v : Fin 32) : Bool := (bs u v 0 == s) && (bs u v 1 == s) && (bs u v 2 == s) && (bs u v 3 == s)

theorem ok_iff : ∀ s : Fin 5, ∀ u v : Fin 32, Compat s.val (row u) (row v) ↔ ok s.val u v = true := by
  decide +kernel

/-- The transfer recursion on codes. -/
def G (s : ℕ) : ℕ → Fin 32 → ℕ
  | 0, _ => 1
  | m + 1, u => ∑ v : Fin 32, if ok s u v then G s m v else 0

theorem N_eq_G (s : ℕ) (hs : s < 5) (m : ℕ) : ∀ u : Fin 32, N s m (row u) = G s m u := by
  induction m with
  | zero => intro u; rw [N_zero]; rfl
  | succ m ih =>
    intro u
    rw [N_succ, ← row_bijective.sum_comp]
    simp only [G]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [ih v]
    exact if_congr (ok_iff ⟨s, hs⟩ u v) rfl rfl

/-- The total number of chains of `m + 1` rows, over `s = 0, ..., 4`. -/
def T (m : ℕ) : ℕ := ∑ s ∈ range 5, ∑ u : Fin 32, G s m u

open Classical in
theorem sum_eq_T (m : ℕ) :
    (∑ A : Fin (m + 2) → Row, if (∃ s, Chain s A) then 1 else 0) = T (m + 1) := by
  rw [Finset.sum_congr rfl fun A _ => exists_split A, Finset.sum_comm]
  unfold T
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [sum_chain, ← row_bijective.sum_comp]
  exact Finset.sum_congr rfl fun u _ => N_eq_G s (mem_range.1 hs) _ u

theorem card_T (m : ℕ) : A183981 (m + 1) = T (m + 1) / 4 := by
  rw [card_eq, sum_eq_T]

/-- `tab k s u = G s k u` for `k ≤ 5`. -/
def tab (k s u : ℕ) : ℕ :=
  ((([[[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
     [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
     [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
     [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
     [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]],
    [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [2, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 2],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]],
    [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [2, 1, 1, 0, 1, 1, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 1, 0, 1, 1, 2],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]],
    [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [4, 1, 1, 0, 1, 1, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 1, 0, 1, 1, 4],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]],
    [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [4, 1, 1, 0, 1, 1, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 16, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 16, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0, 1, 1, 0, 1, 1, 4],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]],
    [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [8, 1, 1, 0, 1, 1, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 32, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 32, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0, 1, 1, 0, 1, 1, 8],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]] : List (List (List ℕ))).getD k []).getD s []).getD u 0

theorem stage_succ (k : ℕ) (hk : ∀ s, s < 5 → ∀ u : Fin 32, G s k u = tab k s u)
    (hstep : ∀ s : Fin 5, ∀ u : Fin 32,
      (∑ v : Fin 32, if ok s.val u v then tab k s.val v else 0) = tab (k + 1) s.val u) :
    ∀ s, s < 5 → ∀ u : Fin 32, G s (k + 1) u = tab (k + 1) s u := by
  intro s hs u
  simp only [G]
  rw [Finset.sum_congr rfl fun v _ => by rw [hk s hs v]]
  exact hstep ⟨s, hs⟩ u

theorem stage0 : ∀ s, s < 5 → ∀ u : Fin 32, G s 0 u = tab 0 s u := by
  intro s hs u
  have : ∀ s : Fin 5, ∀ u : Fin 32, tab 0 s.val u = 1 := by decide +kernel
  rw [this ⟨s, hs⟩ u]
  rfl

theorem stage1 : ∀ s, s < 5 → ∀ u : Fin 32, G s 1 u = tab 1 s u :=
  stage_succ 0 stage0 (by decide +kernel)

theorem stage2 : ∀ s, s < 5 → ∀ u : Fin 32, G s 2 u = tab 2 s u :=
  stage_succ 1 stage1 (by decide +kernel)

theorem stage3 : ∀ s, s < 5 → ∀ u : Fin 32, G s 3 u = tab 3 s u :=
  stage_succ 2 stage2 (by decide +kernel)

theorem stage4 : ∀ s, s < 5 → ∀ u : Fin 32, G s 4 u = tab 4 s u :=
  stage_succ 3 stage3 (by decide +kernel)

theorem stage5 : ∀ s, s < 5 → ∀ u : Fin 32, G s 5 u = tab 5 s u :=
  stage_succ 4 stage4 (by decide +kernel)

theorem G_succ_int (s k : ℕ) (u : Fin 32) :
    (G s (k + 1) u : ℤ) = ∑ v : Fin 32, if ok s u v then (G s k v : ℤ) else 0 := by
  simp only [G]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> rfl

theorem rec_G (s : ℕ) (hs : s < 5) (m : ℕ) (hm : 1 ≤ m) : ∀ u : Fin 32,
    (G s (m + 4) u : ℤ) = 3 * G s (m + 3) u - 6 * G s (m + 1) u + 4 * G s m u := by
  induction m, hm using Nat.le_induction with
  | base =>
    intro u
    have hb : ∀ s : Fin 5, ∀ u : Fin 32,
        (tab 5 s.val u : ℤ) = 3 * tab 4 s.val u - 6 * tab 2 s.val u + 4 * tab 1 s.val u := by
      decide +kernel
    rw [stage5 s hs u, stage4 s hs u, stage2 s hs u, stage1 s hs u]
    exact hb ⟨s, hs⟩ u
  | succ m hm ih =>
    intro u
    rw [show m + 1 + 4 = m + 4 + 1 by ring, show m + 1 + 3 = m + 3 + 1 by ring,
      G_succ_int s (m + 4), G_succ_int s (m + 3), G_succ_int s (m + 1), G_succ_int s m,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs
    · exact ih v
    · ring

theorem rec_T (m : ℕ) (hm : 1 ≤ m) :
    (T (m + 4) : ℤ) = 3 * T (m + 3) - 6 * T (m + 1) + 4 * T m := by
  unfold T
  push_cast
  rw [Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun u _ =>
    rec_G s (mem_range.1 hs) m hm u]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem T_eq_tab (k : ℕ) (hk : ∀ s, s < 5 → ∀ u : Fin 32, G s k u = tab k s u) :
    T k = ∑ s ∈ range 5, ∑ u : Fin 32, tab k s u := by
  unfold T
  exact Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun u _ => hk s (mem_range.1 hs) u

theorem T_vals : T 1 = 60 ∧ T 2 = 68 ∧ T 3 = 80 ∧ T 4 = 104 := by
  rw [T_eq_tab 1 stage1, T_eq_tab 2 stage2, T_eq_tab 3 stage3, T_eq_tab 4 stage4]
  decide +kernel

theorem T_closed (k : ℕ) :
    ((T (2 * k + 1) : ℤ) = 4 * (2 ^ (k + 1) + 2 ^ (2 * k) + 12) ∧
      (T (2 * k + 2) : ℤ) = 4 * (3 * 2 ^ k + 2 * 2 ^ (2 * k) + 12)) ∧
    ((T (2 * (k + 1) + 1) : ℤ) = 4 * (2 ^ (k + 1 + 1) + 2 ^ (2 * (k + 1)) + 12) ∧
      (T (2 * (k + 1) + 2) : ℤ) = 4 * (3 * 2 ^ (k + 1) + 2 * 2 ^ (2 * (k + 1)) + 12)) := by
  induction k with
  | zero =>
    obtain ⟨h1, h2, h3, h4⟩ := T_vals
    norm_num [h1, h2, h3, h4]
  | succ k ih =>
    obtain ⟨⟨e0, f0⟩, ⟨e1, f1⟩⟩ := ih
    refine ⟨⟨e1, f1⟩, ?_, ?_⟩
    · have r := rec_T (2 * k + 1) (by omega)
      rw [show 2 * (k + 1 + 1) + 1 = 2 * k + 1 + 4 by ring]
      rw [show 2 * k + 1 + 3 = 2 * (k + 1) + 2 by ring, show 2 * k + 1 + 1 = 2 * k + 2 by ring,
        f1, f0, e0] at r
      rw [r]
      ring
    · have r := rec_T (2 * k + 2) (by omega)
      rw [show 2 * (k + 1 + 1) + 2 = 2 * k + 2 + 4 by ring]
      rw [show 2 * k + 2 + 3 = 2 * (k + 1 + 1) + 1 by ring,
        show 2 * k + 2 + 1 = 2 * (k + 1) + 1 by ring] at r
      rw [show 2 * (k + 1 + 1) + 1 = 2 * k + 1 + 4 by ring] at r
      have r1 := rec_T (2 * k + 1) (by omega)
      rw [show 2 * k + 1 + 3 = 2 * (k + 1) + 2 by ring, show 2 * k + 1 + 1 = 2 * k + 2 by ring,
        f1, f0, e0] at r1
      rw [r, r1, e1, f0]
      ring

theorem a_odd (k : ℕ) : A183981 (2 * k + 1) = 2 ^ (k + 1) + 2 ^ (2 * k) + 12 := by
  rw [card_T]
  have h : T (2 * k + 1) = 4 * (2 ^ (k + 1) + 2 ^ (2 * k) + 12) := by
    exact_mod_cast (T_closed k).1.1
  rw [h, Nat.mul_div_cancel_left _ (by norm_num)]

theorem a_even (k : ℕ) : A183981 (2 * k + 2) = 3 * 2 ^ k + 2 * 2 ^ (2 * k) + 12 := by
  rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, card_T]
  have h : T (2 * k + 1 + 1) = 4 * (3 * 2 ^ k + 2 * 2 ^ (2 * k) + 12) := by
    exact_mod_cast (T_closed k).1.2
  rw [h, Nat.mul_div_cancel_left _ (by norm_num)]

theorem a_four (n : ℕ) (hn : 1 ≤ n) : (T n : ℤ) = 4 * A183981 n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    rw [show k + k + 1 = 2 * k + 1 by ring, a_odd, (T_closed k).1.1]
    push_cast
    ring
  · subst hk
    rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring, a_even, (T_closed k).1.2]
    push_cast
    ring

theorem closed (n : ℕ) (hn : 1 ≤ n) :
    if Even n then 2 * A183981 n = 3 * 2 ^ (n / 2) + 2 ^ n + 24
    else A183981 n = 2 ^ ((n + 1) / 2) + 2 ^ (n - 1) + 12 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    have hne : ¬ Even (k + k + 1) := by
      rw [Nat.not_even_iff_odd]
      exact ⟨k, by ring⟩
    rw [if_neg hne, show k + k + 1 = 2 * k + 1 by ring, a_odd,
      show (2 * k + 1 + 1) / 2 = k + 1 by omega, show 2 * k + 1 - 1 = 2 * k by omega]
  · subst hk
    have he : Even (2 * k + 1 + 1) := ⟨k + 1, by ring⟩
    rw [if_pos he, show 2 * k + 1 + 1 = 2 * k + 2 by ring, a_even,
      show (2 * k + 2) / 2 = k + 1 by omega]
    ring

theorem rec_a (m : ℕ) (hm : 1 ≤ m) :
    (A183981 (m + 4) : ℤ) = 3 * A183981 (m + 3) - 6 * A183981 (m + 1) + 4 * A183981 m := by
  have h := rec_T m hm
  rw [a_four (m + 4) (by omega), a_four (m + 3) (by omega), a_four (m + 1) (by omega),
    a_four m hm] at h
  linarith

theorem a_vals : A183981 1 = 15 ∧ A183981 2 = 17 ∧ A183981 3 = 20 ∧ A183981 4 = 26 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := a_odd 0
    norm_num at this
    exact this
  · have := a_even 0
    norm_num at this
    exact this
  · have := a_odd 1
    norm_num at this
    exact this
  · have := a_even 1
    norm_num at this
    exact this

open PowerSeries in
theorem gen_fun :
    (1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A183981 n : ℤ)) =
      PowerSeries.X * (15 - 28 * PowerSeries.X - 31 * PowerSeries.X ^ 2 + 56 * PowerSeries.X ^ 3) := by
  set F : ℕ → ℤ := fun n => if n = 0 then (0 : ℤ) else (A183981 n : ℤ) with hF
  have key : (1 - X) * (1 - 2 * X) * (1 - 2 * X ^ 2) * PowerSeries.mk F =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 3 * (PowerSeries.mk F * X ^ 1) +
        C 6 * (PowerSeries.mk F * X ^ 3) - C 4 * (PowerSeries.mk F * X ^ 4) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℤ⟦X⟧) * (15 - 28 * PowerSeries.X - 31 * PowerSeries.X ^ 2 + 56 * PowerSeries.X ^ 3) =
      C 15 * X ^ 1 - C 28 * X ^ 2 - C 31 * X ^ 3 + C 56 * X ^ 4 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  obtain ⟨v1, v2, v3, v4⟩ := a_vals
  by_cases hk : k < 5
  · interval_cases k <;> norm_num [hF, v1, v2, v3, v4]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
    have hr := rec_a (j + 1) (by omega)
    rw [show j + 1 + 4 = j + 5 by ring, show j + 1 + 3 = j + 4 by ring,
      show j + 1 + 1 = j + 2 by ring] at hr
    simp only [show 0 ≤ j + 5 by omega, show 1 ≤ j + 5 by omega, show 3 ≤ j + 5 by omega,
      show 4 ≤ j + 5 by omega,
      show j + 5 - 0 = j + 5 by omega, show j + 5 - 1 = j + 4 by omega,
      show j + 5 - 3 = j + 2 by omega, show j + 5 - 4 = j + 1 by omega,
      show ¬ (j + 5 = 1) by omega, show ¬ (j + 5 = 2) by omega, show ¬ (j + 5 = 3) by omega,
      show ¬ (j + 5 = 4) by omega, show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega, if_true, if_false, hF]
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a183981.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.closed⟩

