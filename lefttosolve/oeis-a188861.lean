import OMAStatements.S_oeis_a188861

/-!
Proof of the conjecture for A188861 (n X 4 binary arrays without the pattern 0 1 diagonally,
vertically or antidiagonally): `a 1 = 16` and `a n = 27 n - 13` for `n ≥ 2`.

Rows are converted to `Fin 4 → Bool` (`toRow`, entry 1 = `true`). The pattern conditions only
involve two consecutive rows (`Compat`, checked against the statement's adjacency on all 256 pairs
of rows in `compat_iff`), so an array avoids the pattern iff each row is compatible with the next
one (`noPattern_iff`). Removing the first row (`chain_cons`) gives a transfer recursion: if
`N m r` counts the ways to continue the row `r` by `m` more rows, then `N 0 r = 1`,
`N (m + 1) r = Sum_s [Compat r s] N m s`, and `a (m + 1) = Sum_r N m r` (`a_succ`).

Rows are coded by the numbers 0, ..., 15 (bit `j` of the code is the entry of column `j`). A row
`s` may follow the row `r` iff every 1 of `s` lies directly below a 1 of `r` whose neighbours in
`r` (those that exist) are 1s too (`E`, `ok`); this test on codes is checked once against
`Compat` on all 256 pairs of codes. `G` is the transfer recursion on codes.

For `m ≥ 2`, `G m u = c1 u * m + c0 u`, where `c1 u = 27` for the full row (code 15) and `0` for
the other rows, and `c0` is an explicit table (`G_closed`). This is proved by induction from
`m = 2` (a finite check); the step reduces to two identities between coefficients for each code
(`step_facts`, a finite check). Summing over the 16 codes gives `a (m + 1) = 27 m + 14` for
`m ≥ 2`; with `a 2 = 41` (a direct computation) this is `a n = 27 n - 13` for `n ≥ 2`
(`closed`), and `a 1 = 16`.
-/

namespace OMA.Helpers

open OMA.S_oeis_a188861 Finset

/-- A row of the array, read from left to right. -/
abbrev Row := Fin 4 → Bool

/-- The vertical, diagonal and antidiagonal conditions between a row `r` and the row `s` just
below it. -/
def Compat (r s : Row) : Prop :=
  (∀ j : Fin 4, ¬ (r j = false ∧ s j = true)) ∧
  (∀ (j : Fin 4) (hj : j.val + 1 < 4), ¬ (r j = false ∧ s ⟨j.val + 1, hj⟩ = true)) ∧
  (∀ (j : Fin 4) (hj : j.val + 1 < 4), ¬ (r ⟨j.val + 1, hj⟩ = false ∧ s j = true))

instance decCompat (r s : Row) : Decidable (Compat r s) := by
  unfold Compat
  infer_instance

/-- Each row of `A` is compatible with the next one. -/
def Chain {m : ℕ} (A : Fin m → Row) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < m), Compat (A ⟨i, by omega⟩) (A ⟨i + 1, hi⟩)

theorem chain_one (A : Fin 1 → Row) : Chain A := fun i hi => absurd hi (by omega)

theorem chain_cons {m : ℕ} (r : Row) (A : Fin (m + 1) → Row) :
    Chain (Fin.cons r A : Fin (m + 2) → Row) ↔ Compat r (A ⟨0, by omega⟩) ∧ Chain A := by
  constructor
  · intro h
    have h0 := h 0 (by omega)
    exact ⟨h0, fun i hi => h (i + 1) (by omega)⟩
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => exact h0
    | succ i => exact h i (by omega)

/-- The number of ways to continue the row `r` by `m` more rows into a `Chain`. -/
noncomputable def N (m : ℕ) (r : Row) : ℕ := by
  classical
  exact ∑ A : Fin m → Row, if Chain (Fin.cons r A : Fin (m + 1) → Row) then 1 else 0

theorem N_zero (r : Row) : N 0 r = 1 := by
  classical
  unfold N
  rw [Fintype.sum_unique, if_pos (chain_one _)]

theorem N_succ (m : ℕ) (r : Row) :
    N (m + 1) r = ∑ s : Row, if Compat r s then N m s else 0 := by
  classical
  unfold N
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
    (fun p => if Chain (Fin.cons r (Fin.cons p.1 p.2) : Fin (m + 2) → Row) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hc : Compat r s
  · rw [if_pos hc]
    refine Finset.sum_congr rfl fun A _ => if_congr ?_ rfl rfl
    rw [chain_cons]
    exact and_iff_right hc
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun A _ => if_neg ?_
    rw [chain_cons]
    exact fun h => hc h.1

/-- An entry of the array as a Boolean (1 is `true`). -/
def b2 (v : Fin 2) : Bool := v == 1

/-- A Boolean as an entry of the array. -/
def f2 (b : Bool) : Fin 2 := if b then 1 else 0

theorem f2_b2 : ∀ v : Fin 2, f2 (b2 v) = v := by decide

theorem b2_f2 : ∀ b : Bool, b2 (f2 b) = b := by decide

/-- A row of the statement's array as a `Row`. -/
def toRow (r : Fin 4 → Fin 2) : Row := fun c => b2 (r c)

/-- Arrays of the statement correspond to arrays of `Row`s. -/
def arrEquiv (n : ℕ) : (Fin n → Fin 4 → Fin 2) ≃ (Fin n → Row) where
  toFun x i := toRow (x i)
  invFun A i c := f2 (A i c)
  left_inv x := by
    funext i c
    exact f2_b2 (x i c)
  right_inv A := by
    funext i c
    exact b2_f2 (A i c)

theorem compat_iff : ∀ r s : Fin 4 → Fin 2, Compat (toRow r) (toRow s) ↔
    ∀ c d : Fin 4, (d.val = c.val ∨ d.val = c.val + 1 ∨ c.val = d.val + 1) →
      ¬ (r c = 0 ∧ s d = 1) := by
  decide +kernel

theorem noPattern_iff {n : ℕ} (x : Fin n → Fin 4 → Fin 2) :
    ¬ HasPattern x ↔ Chain (fun i => toRow (x i)) := by
  unfold HasPattern Chain
  constructor
  · intro h i hi
    rw [compat_iff]
    intro c d hcd hx
    exact h ⟨⟨i, by omega⟩, ⟨i + 1, hi⟩, rfl, c, d, hcd, hx⟩
  · rintro h ⟨i, j, hij, c, d, hcd, h0, h1⟩
    have hi : i.val + 1 < n := hij ▸ j.isLt
    have key := (compat_iff _ _).1 (h i.val hi) c d hcd
    obtain rfl : j = ⟨i.val + 1, hi⟩ := Fin.ext hij
    exact key ⟨h0, h1⟩

theorem a_succ (m : ℕ) : (a (m + 1) : ℤ) = ∑ r : Row, (N m r : ℤ) := by
  classical
  have h1 : a (m + 1) = ∑ A : Fin (m + 1) → Row, if Chain A then 1 else 0 := by
    unfold a
    rw [Finset.card_filter, ← (arrEquiv (m + 1)).sum_comp]
    exact Finset.sum_congr rfl fun x _ => if_congr (noPattern_iff x) rfl rfl
  have h2 : (∑ A : Fin (m + 1) → Row, if Chain A then 1 else 0) = ∑ r : Row, N m r := by
    rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row).symm _
      (fun p => if Chain (Fin.cons p.1 p.2 : Fin (m + 1) → Row) then 1 else 0)
      (fun A => by simp), Fintype.sum_prod_type]
    rfl
  rw [h1, h2, Nat.cast_sum]

/-- The row with code `u`: the entry of column `j` is bit `j` of `u`. -/
def row (u : Fin 16) : Row := fun j => Nat.testBit u.val j.val

theorem row_injective : Function.Injective row := by
  decide +kernel

theorem row_bijective : Function.Bijective row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective, by simp⟩

/-- For a row code `u`, the code of the columns `j` such that the entries of `u` in the columns
`j - 1`, `j`, `j + 1` (those that exist) are all 1. -/
def E (u : ℕ) : ℕ := u &&& ((u >>> 1) ||| 8) &&& ((u <<< 1) ||| 1)

/-- `Compat` on codes: the 1s of `v` are among those of `E u`. -/
def ok (u v : Fin 16) : Bool := v.val &&& E u.val == v.val

theorem ok_iff : ∀ u v : Fin 16, Compat (row u) (row v) ↔ ok u v = true := by
  decide +kernel

/-- The transfer recursion on codes. -/
def G : ℕ → Fin 16 → ℕ
  | 0, _ => 1
  | m + 1, u => ∑ v : Fin 16, if ok u v then G m v else 0

theorem N_eq_G (m : ℕ) : ∀ u : Fin 16, N m (row u) = G m u := by
  induction m with
  | zero => intro u; rw [N_zero]; rfl
  | succ m ih =>
    intro u
    rw [N_succ, ← row_bijective.sum_comp]
    simp only [G]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [ih v]
    exact if_congr (ok_iff u v) rfl rfl

theorem a_eq_G (m : ℕ) : (a (m + 1) : ℤ) = ∑ u : Fin 16, (G m u : ℤ) := by
  rw [a_succ, ← row_bijective.sum_comp]
  exact Finset.sum_congr rfl fun u _ => by rw [N_eq_G]

/-- Coefficient of `m` in `G m u` for `m ≥ 2`. -/
def c1 (u : Fin 16) : ℤ := if u.val = 15 then 27 else 0

/-- Constant term of `G m u` for `m ≥ 2`. -/
def c0 (u : Fin 16) : ℤ :=
  if u.val = 15 then -13 else if u.val = 7 ∨ u.val = 14 then 5
  else if u.val = 3 ∨ u.val = 11 ∨ u.val = 12 ∨ u.val = 13 then 2 else 1

theorem base_facts : ∀ u : Fin 16, (G 2 u : ℤ) = c1 u * ((2 : ℕ) : ℤ) + c0 u := by
  decide +kernel

/-- The induction step of `G_closed`, coefficient by coefficient. -/
theorem step_facts : ∀ u : Fin 16,
    (∑ v : Fin 16, if ok u v then c1 v else 0) = c1 u ∧
    (∑ v : Fin 16, if ok u v then c0 v else 0) = c1 u + c0 u := by
  decide +kernel

theorem G_closed (m : ℕ) (hm : 2 ≤ m) : ∀ u : Fin 16, (G m u : ℤ) = c1 u * m + c0 u := by
  induction m, hm using Nat.le_induction with
  | base => exact base_facts
  | succ m hm ih =>
    intro u
    have hsum : (G (m + 1) u : ℤ) = ∑ v : Fin 16, if ok u v then c1 v * m + c0 v else 0 := by
      rw [G]
      push_cast
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs
      · exact ih v
      · rfl
    rw [hsum]
    have hP : ∀ v : Fin 16, (if ok u v then c1 v * m + c0 v else 0) =
        (if ok u v then c1 v else 0) * (m : ℤ) + (if ok u v then c0 v else 0) := by
      intro v
      split_ifs <;> simp
    simp only [hP, Finset.sum_add_distrib, ← Finset.sum_mul]
    obtain ⟨h1, h0⟩ := step_facts u
    rw [h1, h0]
    push_cast
    ring

theorem sum_facts : (∑ u : Fin 16, c1 u) = 27 ∧ (∑ u : Fin 16, c0 u) = 14 := by
  decide +kernel

theorem closed (n : ℕ) (hn : 2 ≤ n) : (a n : ℤ) = 27 * n - 13 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_eq_G]
  rcases Nat.lt_or_ge m 2 with h | h
  · obtain rfl : m = 1 := by omega
    decide +kernel
  · simp only [G_closed m h]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    obtain ⟨h1, h0⟩ := sum_facts
    rw [h1, h0]
    push_cast
    ring

theorem main_proof : a 1 = 16 ∧ ∀ n : ℕ, 2 ≤ n → a n = 27 * n - 13 := by
  refine ⟨?_, fun n hn => ?_⟩
  · have h : (a 1 : ℤ) = 16 := (a_eq_G 0).trans (by decide +kernel)
    exact_mod_cast h
  · have h := closed n hn
    omega

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a188861.main :=
  OMA.Helpers.main_proof
