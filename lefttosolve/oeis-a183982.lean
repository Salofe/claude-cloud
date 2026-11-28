import OMAStatements.S_oeis_a183982
import Mathlib

/-!
Proof of the conjectures of OEIS A183982 (1/4 of the number of (n+1) X 6 binary arrays with all
2 X 2 subblock sums equal).

Read the array row by row (rows coded by 0..63, bit j = column j). For n >= 1 the common block
sum s is determined by the first block, so the count is the sum over s = 0..4 of the number of
row chains in which consecutive rows have all five block sums equal to s. With G s m u the number
of ways to continue the row u by m rows (a transfer recursion on codes), the defect
G(m+4) + 6 G(m+1) - 3 G(m+3) - 4 G(m) satisfies the same linear recursion, and it vanishes at
m = 1 (a finite check), hence for all m >= 1. The totals T then satisfy that recurrence, and with
T 1..4 = 100, 108, 120, 144 this gives the closed forms T(2k+1) = 8*2^k + 4*4^k + 88 and
T(2k) = 6*2^k + 2*4^k + 88; dividing by 4 gives the stated formulas, and the generating function
follows coefficientwise.
-/

namespace OMA.Helpers

open OMA.S_oeis_a183982 Finset

abbrev A183982Row := Fin 6 → Bool

/-- All five 2 X 2 blocks formed by the row `r` and the row `q` below it sum to `s`. -/
def a183982Compat (s : ℕ) (r q : A183982Row) : Prop :=
  ∀ j : Fin 5, blockSum (r ⟨j.1, by omega⟩) (r ⟨j.1 + 1, by omega⟩)
    (q ⟨j.1, by omega⟩) (q ⟨j.1 + 1, by omega⟩) = s

instance a183982DecCompat (s : ℕ) (r q : A183982Row) : Decidable (a183982Compat s r q) := by
  unfold a183982Compat
  infer_instance

/-- Each row of `R` is compatible (block sum `s`) with the next one. -/
def a183982Chain (s : ℕ) {m : ℕ} (R : Fin m → A183982Row) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < m), a183982Compat s (R ⟨i, by omega⟩) (R ⟨i + 1, hi⟩)

theorem a183982_chain_one (s : ℕ) (R : Fin 1 → A183982Row) : a183982Chain s R :=
  fun i hi => absurd hi (by omega)

theorem a183982_chain_cons (s : ℕ) {m : ℕ} (r : A183982Row) (R : Fin (m + 1) → A183982Row) :
    a183982Chain s (Fin.cons r R : Fin (m + 2) → A183982Row) ↔
      a183982Compat s r (R ⟨0, by omega⟩) ∧ a183982Chain s R := by
  constructor
  · intro h
    have h0 := h 0 (by omega)
    exact ⟨h0, fun i hi => h (i + 1) (by omega)⟩
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => exact h0
    | succ i => exact h i (by omega)

/-- The number of ways to continue the row `r` by `m` more rows into a chain. -/
noncomputable def a183982N (s m : ℕ) (r : A183982Row) : ℕ := by
  classical
  exact ∑ R : Fin m → A183982Row,
    if a183982Chain s (Fin.cons r R : Fin (m + 1) → A183982Row) then 1 else 0

theorem a183982N_zero (s : ℕ) (r : A183982Row) : a183982N s 0 r = 1 := by
  classical
  unfold a183982N
  rw [Fintype.sum_unique, if_pos (a183982_chain_one _ _)]

theorem a183982N_succ (s m : ℕ) (r : A183982Row) :
    a183982N s (m + 1) r = ∑ q : A183982Row, if a183982Compat s r q then a183982N s m q else 0 := by
  classical
  unfold a183982N
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => A183982Row).symm _
    (fun p => if a183982Chain s (Fin.cons r (Fin.cons p.1 p.2) : Fin (m + 2) → A183982Row)
      then 1 else 0)
    (fun R => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hc : a183982Compat s r q
  · rw [if_pos hc]
    refine Finset.sum_congr rfl fun R _ => if_congr ?_ rfl rfl
    rw [a183982_chain_cons]
    exact and_iff_right hc
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun R _ => if_neg ?_
    rw [a183982_chain_cons]
    exact fun h => hc h.1

open scoped Classical in
theorem a183982_chains_eq_N (s m : ℕ) :
    (∑ R : Fin (m + 1) → A183982Row, if a183982Chain s R then 1 else 0) =
      ∑ r : A183982Row, a183982N s m r := by
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => A183982Row).symm _
    (fun p => if a183982Chain s (Fin.cons p.1 p.2 : Fin (m + 1) → A183982Row) then 1 else 0)
    (fun R => by simp), Fintype.sum_prod_type]
  rfl

/-- The row with code `u`: the entry of column `j` is bit `j` of `u`. -/
def a183982Row (u : Fin 64) : A183982Row := fun j => Nat.testBit u.val j.val

theorem a183982Row_injective : Function.Injective a183982Row := by
  decide +kernel

theorem a183982Row_bijective : Function.Bijective a183982Row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨a183982Row_injective, by simp⟩

/-- Sum of the 2 X 2 block of the codes `u` (top) and `v` (bottom) at columns `j`, `j + 1`. -/
def a183982Blk (u v j : ℕ) : ℕ :=
  (u >>> j) % 2 + (u >>> (j + 1)) % 2 + (v >>> j) % 2 + (v >>> (j + 1)) % 2

/-- `a183982Compat` on codes. -/
def a183982Ok (s u v : ℕ) : Bool :=
  a183982Blk u v 0 == s && a183982Blk u v 1 == s && a183982Blk u v 2 == s &&
    a183982Blk u v 3 == s && a183982Blk u v 4 == s

theorem a183982_ok_iff0 : ∀ u v : Fin 64,
    a183982Compat 0 (a183982Row u) (a183982Row v) ↔ a183982Ok 0 u.val v.val = true := by
  decide +kernel

theorem a183982_ok_iff1 : ∀ u v : Fin 64,
    a183982Compat 1 (a183982Row u) (a183982Row v) ↔ a183982Ok 1 u.val v.val = true := by
  decide +kernel

theorem a183982_ok_iff2 : ∀ u v : Fin 64,
    a183982Compat 2 (a183982Row u) (a183982Row v) ↔ a183982Ok 2 u.val v.val = true := by
  decide +kernel

theorem a183982_ok_iff3 : ∀ u v : Fin 64,
    a183982Compat 3 (a183982Row u) (a183982Row v) ↔ a183982Ok 3 u.val v.val = true := by
  decide +kernel

theorem a183982_ok_iff4 : ∀ u v : Fin 64,
    a183982Compat 4 (a183982Row u) (a183982Row v) ↔ a183982Ok 4 u.val v.val = true := by
  decide +kernel

theorem a183982_ok_iff (s : ℕ) (hs : s < 5) : ∀ u v : Fin 64,
    a183982Compat s (a183982Row u) (a183982Row v) ↔ a183982Ok s u.val v.val = true := by
  interval_cases s
  exacts [a183982_ok_iff0, a183982_ok_iff1, a183982_ok_iff2, a183982_ok_iff3, a183982_ok_iff4]

/-- The transfer recursion on codes (block sum `s`). -/
def a183982G (s : ℕ) : ℕ → Fin 64 → ℕ
  | 0, _ => 1
  | m + 1, u => ((List.finRange 64).map
      (fun v => bif a183982Ok s u.val v.val then a183982G s m v else 0)).sum

theorem a183982G_succ (s m : ℕ) (u : Fin 64) :
    a183982G s (m + 1) u = ∑ v : Fin 64, if a183982Ok s u.val v.val then a183982G s m v else 0 := by
  rw [Fin.sum_univ_def]
  simp only [a183982G, cond_eq_ite]

theorem a183982N_eq_G (s : ℕ) (hs : s < 5) (m : ℕ) :
    ∀ u : Fin 64, a183982N s m (a183982Row u) = a183982G s m u := by
  induction m with
  | zero => intro u; rw [a183982N_zero]; rfl
  | succ m ih =>
    intro u
    rw [a183982N_succ, ← a183982Row_bijective.sum_comp, a183982G_succ]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [ih v]
    exact if_congr (a183982_ok_iff s hs u v) rfl rfl

/-- Total number of chains of `m + 1` rows, over the block sums `0, ..., 4`. -/
def a183982T (m : ℕ) : ℕ := ∑ s : Fin 5, ∑ u : Fin 64, a183982G s.val m u

theorem a183982_blockSum_le (a b c d : Bool) : blockSum a b c d ≤ 4 := by
  unfold blockSum
  split_ifs <;> omega

theorem a183982_chain_iff (s m : ℕ) (R : Fin (m + 2) → A183982Row) :
    a183982Chain s R ↔ ∀ (i : Fin (m + 1)) (j : Fin 5),
      blockSum (R ⟨i.1, by omega⟩ ⟨j.1, by omega⟩) (R ⟨i.1, by omega⟩ ⟨j.1 + 1, by omega⟩)
        (R ⟨i.1 + 1, by omega⟩ ⟨j.1, by omega⟩) (R ⟨i.1 + 1, by omega⟩ ⟨j.1 + 1, by omega⟩) = s := by
  constructor
  · intro h i j
    exact h i.1 (by omega) j
  · intro h i hi j
    exact h ⟨i, by omega⟩ j

theorem a183982_chain_lt (s m : ℕ) (R : Fin (m + 2) → A183982Row) (h : a183982Chain s R) :
    s < 5 := by
  have h0 := h 0 (by omega) 0
  rw [← h0]
  exact Nat.lt_succ_of_le (a183982_blockSum_le _ _ _ _)

theorem a183982_chain_unique (s t m : ℕ) (R : Fin (m + 2) → A183982Row) (h : a183982Chain s R)
    (h' : a183982Chain t R) : s = t := by
  have h0 := h 0 (by omega) 0
  have h1 := h' 0 (by omega) 0
  rw [← h0, ← h1]

open scoped Classical in
theorem a183982_card (m : ℕ) : A183982 (m + 1) = a183982T (m + 1) / 4 := by
  unfold A183982
  refine congrArg (fun x => x / 4) ?_
  rw [Finset.card_filter]
  rw [Fintype.sum_equiv (Equiv.curry (Fin (m + 2)) (Fin 6) Bool) _
    (fun R => if (∃ s : ℕ, ∀ (i : Fin (m + 1)) (j : Fin 5),
      blockSum (R ⟨i.1, by omega⟩ ⟨j.1, by omega⟩) (R ⟨i.1, by omega⟩ ⟨j.1 + 1, by omega⟩)
        (R ⟨i.1 + 1, by omega⟩ ⟨j.1, by omega⟩) (R ⟨i.1 + 1, by omega⟩ ⟨j.1 + 1, by omega⟩) = s)
      then 1 else 0) (fun A => by simp)]
  have hpt : ∀ R : Fin (m + 2) → A183982Row,
      (if (∃ s : ℕ, ∀ (i : Fin (m + 1)) (j : Fin 5),
        blockSum (R ⟨i.1, by omega⟩ ⟨j.1, by omega⟩) (R ⟨i.1, by omega⟩ ⟨j.1 + 1, by omega⟩)
          (R ⟨i.1 + 1, by omega⟩ ⟨j.1, by omega⟩) (R ⟨i.1 + 1, by omega⟩ ⟨j.1 + 1, by omega⟩) = s)
        then 1 else 0) = ∑ s : Fin 5, if a183982Chain s.val R then 1 else 0 := by
    intro R
    split_ifs with h
    · obtain ⟨s, hs⟩ := h
      have hc : a183982Chain s R := (a183982_chain_iff s m R).2 hs
      have h5 := a183982_chain_lt s m R hc
      rw [Finset.sum_eq_single (⟨s, h5⟩ : Fin 5)]
      · rw [if_pos hc]
      · intro b _ hb
        refine if_neg fun hb' => hb ?_
        exact Fin.ext (a183982_chain_unique _ _ m R hb' hc)
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    · symm
      refine Finset.sum_eq_zero fun t _ => if_neg fun ht => h ⟨t.val, ?_⟩
      exact (a183982_chain_iff t.val m R).1 ht
  rw [Finset.sum_congr rfl fun R _ => hpt R, Finset.sum_comm]
  unfold a183982T
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [a183982_chains_eq_N, ← a183982Row_bijective.sum_comp]
  exact Finset.sum_congr rfl fun u _ => a183982N_eq_G s.val s.isLt (m + 1) u

theorem a183982G_succ_int (s m : ℕ) (u : Fin 64) :
    (a183982G s (m + 1) u : ℤ) =
      ∑ v : Fin 64, if a183982Ok s u.val v.val then (a183982G s m v : ℤ) else 0 := by
  rw [a183982G_succ]
  push_cast
  rfl

/-- The defect of the recurrence `x(m+4) + 6 x(m+1) = 3 x(m+3) + 4 x(m)` at the code `u`. -/
def a183982D (s m : ℕ) (u : Fin 64) : ℤ :=
  (a183982G s (m + 4) u : ℤ) + 6 * a183982G s (m + 1) u - 3 * a183982G s (m + 3) u -
    4 * a183982G s m u

theorem a183982D_succ (s m : ℕ) (u : Fin 64) :
    a183982D s (m + 1) u = ∑ v : Fin 64, if a183982Ok s u.val v.val then a183982D s m v else 0 := by
  unfold a183982D
  rw [show m + 1 + 4 = (m + 4) + 1 by ring, show m + 1 + 3 = (m + 3) + 1 by ring,
    show m + 1 + 1 = (m + 1) + 1 by ring]
  rw [a183982G_succ_int s (m + 4), a183982G_succ_int s (m + 1), a183982G_succ_int s (m + 3),
    a183982G_succ_int s m]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> ring

theorem a183982_base : ∀ s : Fin 5, ∀ u : Fin 64,
    a183982G s.val 5 u + 6 * a183982G s.val 2 u = 3 * a183982G s.val 4 u + 4 * a183982G s.val 1 u := by
  decide +kernel

theorem a183982D_zero (s : ℕ) (hs : s < 5) (m : ℕ) (hm : 1 ≤ m) :
    ∀ u : Fin 64, a183982D s m u = 0 := by
  induction m, hm using Nat.le_induction with
  | base =>
    intro u
    have h := a183982_base ⟨s, hs⟩ u
    unfold a183982D
    simp only at h
    have h' : ((a183982G s 5 u + 6 * a183982G s 2 u : ℕ) : ℤ) =
        ((3 * a183982G s 4 u + 4 * a183982G s 1 u : ℕ) : ℤ) := by rw [h]
    push_cast at h'
    linarith
  | succ m hm ih =>
    intro u
    rw [a183982D_succ]
    exact Finset.sum_eq_zero fun v _ => by rw [ih v]; simp

theorem a183982T_rec (m : ℕ) (hm : 1 ≤ m) :
    (a183982T (m + 4) : ℤ) + 6 * a183982T (m + 1) = 3 * a183982T (m + 3) + 4 * a183982T m := by
  unfold a183982T
  push_cast
  have h : ∀ s : Fin 5, ∀ u : Fin 64,
      (a183982G s.val (m + 4) u : ℤ) = 3 * a183982G s.val (m + 3) u + 4 * a183982G s.val m u -
        6 * a183982G s.val (m + 1) u := by
    intro s u
    have := a183982D_zero s.val s.isLt m hm u
    unfold a183982D at this
    linarith
  simp only [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- The closed form of `a183982T` for even arguments `2 k`. -/
def a183982cE (k : ℕ) : ℤ := 6 * 2 ^ k + 2 * 4 ^ k + 88

/-- The closed form of `a183982T` for odd arguments `2 k + 1`. -/
def a183982cO (k : ℕ) : ℤ := 8 * 2 ^ k + 4 * 4 ^ k + 88

def a183982c (n : ℕ) : ℤ := if n % 2 = 0 then a183982cE (n / 2) else a183982cO (n / 2)

theorem a183982c_rec (m : ℕ) :
    a183982c (m + 4) + 6 * a183982c (m + 1) = 3 * a183982c (m + 3) + 4 * a183982c m := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · simp only [a183982c, show (2 * k + 4) % 2 = 0 by omega, show (2 * k + 4) / 2 = k + 2 by omega,
      show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega,
      show (2 * k + 3) % 2 = 1 by omega, show (2 * k + 3) / 2 = k + 1 by omega,
      show (2 * k) % 2 = 0 by omega, show (2 * k) / 2 = k by omega, if_true,
      show ¬ (1 = 0) by omega, if_false, a183982cE, a183982cO, pow_succ]
    ring
  · simp only [a183982c, show (2 * k + 1 + 4) % 2 = 1 by omega,
      show (2 * k + 1 + 4) / 2 = k + 2 by omega,
      show (2 * k + 1 + 1) % 2 = 0 by omega, show (2 * k + 1 + 1) / 2 = k + 1 by omega,
      show (2 * k + 1 + 3) % 2 = 0 by omega, show (2 * k + 1 + 3) / 2 = k + 2 by omega,
      show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega, if_true,
      show ¬ (1 = 0) by omega, if_false, a183982cE, a183982cO, pow_succ]
    ring

theorem a183982T_small : a183982T 1 = 100 ∧ a183982T 2 = 108 ∧ a183982T 3 = 120 ∧
    a183982T 4 = 144 := by
  decide +kernel

theorem a183982T_closed (n : ℕ) (hn : 1 ≤ n) : (a183982T n : ℤ) = a183982c n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := a183982T_small
    rcases Nat.lt_or_ge n 5 with h | h
    · interval_cases n
      · rw [h1]; norm_num [a183982c, a183982cO]
      · rw [h2]; norm_num [a183982c, a183982cE]
      · rw [h3]; norm_num [a183982c, a183982cO]
      · rw [h4]; norm_num [a183982c, a183982cE]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have r1 := a183982T_rec m (by omega)
      have r2 := a183982c_rec m
      have i1 := ih (m + 3) (by omega) (by omega)
      have i2 := ih (m + 1) (by omega) (by omega)
      have i3 := ih m (by omega) (by omega)
      linarith

/-- The closed form of the sequence (n ≥ 1). -/
theorem a183982_odd (k : ℕ) : A183982 (2 * k + 1) = 2 * 2 ^ k + 4 ^ k + 22 := by
  rw [a183982_card]
  have h := a183982T_closed (2 * k + 1) (by omega)
  simp only [a183982c, show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega,
    show ¬ (1 = 0) by omega, if_false, a183982cO] at h
  have h' : a183982T (2 * k + 1) = 4 * (2 * 2 ^ k + 4 ^ k + 22) := by
    have : ((a183982T (2 * k + 1) : ℕ) : ℤ) = ((4 * (2 * 2 ^ k + 4 ^ k + 22) : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast this
  rw [h']
  omega

theorem a183982_even (k : ℕ) : A183982 (2 * k + 2) = 3 * 2 ^ k + 2 * 4 ^ k + 22 := by
  have e : 2 * k + 2 = (2 * k + 1) + 1 := by ring
  rw [e, a183982_card, ← e]
  have h := a183982T_closed (2 * k + 2) (by omega)
  simp only [a183982c, show (2 * k + 2) % 2 = 0 by omega, show (2 * k + 2) / 2 = k + 1 by omega,
    if_true, a183982cE, pow_succ] at h
  have h' : a183982T (2 * k + 2) = 4 * (3 * 2 ^ k + 2 * 4 ^ k + 22) := by
    have : ((a183982T (2 * k + 2) : ℕ) : ℤ) = ((4 * (3 * 2 ^ k + 2 * 4 ^ k + 22) : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast this
  rw [h']
  omega

theorem a183982_closed (n : ℕ) (hn : 1 ≤ n) :
    if Even n then 2 * A183982 n = 3 * 2 ^ (n / 2) + 2 ^ n + 44
    else A183982 n = 2 ^ ((n + 1) / 2) + 2 ^ (n - 1) + 22 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [if_pos (even_two_mul _), show 2 * (j + 1) = 2 * j + 2 by ring, a183982_even,
      show (2 * j + 2) / 2 = j + 1 by omega, show 2 * j + 2 = 2 * (j + 1) by ring, pow_mul]
    norm_num [pow_succ]
    ring
  · rw [if_neg (Nat.not_even_two_mul_add_one k), a183982_odd,
      show (2 * k + 1 + 1) / 2 = k + 1 by omega, show 2 * k + 1 - 1 = 2 * k by omega, pow_mul]
    norm_num [pow_succ]
    ring

theorem a183982_four (n : ℕ) (hn : 1 ≤ n) : 4 * (A183982 n : ℤ) = a183982c n := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, a183982_even]
    simp only [a183982c, show (2 * j + 2) % 2 = 0 by omega, show (2 * j + 2) / 2 = j + 1 by omega,
      if_true, a183982cE, pow_succ]
    push_cast
    ring
  · rw [a183982_odd]
    simp only [a183982c, show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega,
      show ¬ (1 = 0) by omega, if_false, a183982cO]
    push_cast
    ring

theorem a183982_rec (m : ℕ) (hm : 1 ≤ m) :
    (A183982 (m + 4) : ℤ) + 6 * A183982 (m + 1) = 3 * A183982 (m + 3) + 4 * A183982 m := by
  have h1 := a183982_four (m + 4) (by omega)
  have h2 := a183982_four (m + 1) (by omega)
  have h3 := a183982_four (m + 3) (by omega)
  have h4 := a183982_four m hm
  have := a183982c_rec m
  linarith

theorem a183982_vals : A183982 1 = 25 ∧ A183982 2 = 27 ∧ A183982 3 = 30 ∧ A183982 4 = 36 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := a183982_odd 0
    norm_num at this
    exact this
  · have := a183982_even 0
    norm_num at this
    exact this
  · have := a183982_odd 1
    norm_num at this
    exact this
  · have := a183982_even 1
    norm_num at this
    exact this

open PowerSeries in
theorem a183982_gf :
    (1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A183982 n : ℤ)) =
      PowerSeries.X * (25 - 48 * PowerSeries.X - 51 * PowerSeries.X ^ 2 + 96 * PowerSeries.X ^ 3) := by
  set b : ℕ → ℤ := fun n => if n = 0 then (0 : ℤ) else (A183982 n : ℤ) with hb
  have key : (1 - X) * (1 - 2 * X) * (1 - 2 * X ^ 2) * PowerSeries.mk b =
      C 1 * (PowerSeries.mk b * X ^ 0) - C 3 * (PowerSeries.mk b * X ^ 1) +
        C 6 * (PowerSeries.mk b * X ^ 3) - C 4 * (PowerSeries.mk b * X ^ 4) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℤ⟦X⟧) * (25 - 48 * X - 51 * X ^ 2 + 96 * X ^ 3) =
      C 25 * X ^ 1 - C 48 * X ^ 2 - C 51 * X ^ 3 + C 96 * X ^ 4 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  obtain ⟨v1, v2, v3, v4⟩ := a183982_vals
  by_cases hk : k < 5
  · interval_cases k <;> norm_num [hb, v1, v2, v3, v4]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
    have hr := a183982_rec (j + 1) (by omega)
    simp only [show j + 1 + 4 = j + 5 by omega, show j + 1 + 3 = j + 4 by omega,
      show j + 1 + 1 = j + 2 by omega] at hr
    simp only [hb, show 0 ≤ j + 5 by omega, show 1 ≤ j + 5 by omega, show 3 ≤ j + 5 by omega,
      show 4 ≤ j + 5 by omega,
      show j + 5 - 0 = j + 5 by omega, show j + 5 - 1 = j + 4 by omega,
      show j + 5 - 3 = j + 2 by omega, show j + 5 - 4 = j + 1 by omega,
      show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega, show ¬ (j + 2 = 0) by omega,
      show ¬ (j + 1 = 0) by omega,
      show ¬ (j + 5 = 1) by omega, show ¬ (j + 5 = 2) by omega, show ¬ (j + 5 = 3) by omega,
      show ¬ (j + 5 = 4) by omega, if_true, if_false]
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a183982.main :=
  ⟨OMA.Helpers.a183982_gf, OMA.Helpers.a183982_closed⟩
