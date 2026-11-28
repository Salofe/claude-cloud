import OMAStatements.S_oeis_a207452
import Mathlib

/-!
Proof of the two conjectures of A207452 (width 7, horizontal 000/001 and vertical 001/101 forbidden).

`a (h + 1) = 42 * cnt h 127`, where `cnt h r` is the length of `tails RS h r` (`len_tails`) and
satisfies `cnt (h + 1) r = Sum_{s in below RS r} cnt h s`. The fifth difference identity
`cnt (h+5) - 5 cnt (h+4) + 10 cnt (h+3) - 10 cnt (h+2) + 5 cnt (h+1) - cnt h = 0` holds for every
admissible row `r` at `h = 0` (a finite check on the table `V` of all values, `base_check`) and
is linear in the recursion, so it propagates to every `h` by induction (`cnt_rec`). This gives the
recurrence, and the generating function follows by comparing coefficients with `a 0, ..., a 5`.
-/

namespace OMA.Helpers
open OMA.S_oeis_a207452

/-- The admissible rows. -/
def RS : List Nat := rows 7 0 1

/-- The number of length-`h` suffixes below the row `r`. -/
def cnt : Nat → Nat → Nat
  | 0, _ => 1
  | h+1, r => ((below RS r).map (cnt h)).sum

/-- One step of the counting recursion on the table of all `128` masks. -/
def step (v : List Nat) : List Nat :=
  (List.range 128).map fun r => ((below RS r).map fun s => v.getD s 0).sum

/-- The table of the values `cnt h r`, `r < 128`. -/
def V : Nat → List Nat
  | 0 => List.replicate 128 1
  | h+1 => step (V h)

theorem mem_RS_lt {s : Nat} (hs : s ∈ RS) : s < 128 := by
  unfold RS rows at hs
  have := (List.mem_filter.1 hs).1
  simpa using this

theorem mem_below {r s : Nat} (hs : s ∈ below RS r) : s ∈ RS :=
  (List.mem_filter.1 hs).1

theorem cnt_eq_V (h : Nat) : ∀ r, r < 128 → cnt h r = (V h).getD r 0 := by
  induction h with
  | zero =>
    intro r hr
    show 1 = (List.replicate 128 1).getD r 0
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hr]
    rfl
  | succ h ih =>
    intro r hr
    simp only [cnt, V, step, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hr,
      Option.map_some, Option.getD_some]
    congr 1
    refine List.map_congr_left fun s hs => ?_
    rw [ih s (mem_RS_lt (mem_below hs)), List.getD_eq_getElem?_getD]

theorem len_tails (h : Nat) : ∀ r, (tails RS h r).length = cnt h r := by
  induction h with
  | zero => intro r; rfl
  | succ h ih =>
    intro r
    simp only [tails, cnt, List.length_flatMap, List.length_map, ih]

theorem base_check : RS.all (fun r => (V 5).getD r 0 + 10 * (V 3).getD r 0 + 5 * (V 1).getD r 0
    == 5 * (V 4).getD r 0 + 10 * (V 2).getD r 0 + (V 0).getD r 0) = true := by
  decide +kernel

theorem sum_comb (l : List Nat) (A B C D E F : Nat → Nat)
    (h : ∀ s ∈ l, A s + 10 * B s + 5 * C s = 5 * D s + 10 * E s + F s) :
    (l.map A).sum + 10 * (l.map B).sum + 5 * (l.map C).sum =
      5 * (l.map D).sum + 10 * (l.map E).sum + (l.map F).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h x (by simp)
    have h2 := ih (fun s hs => h s (by simp [hs]))
    omega

theorem cnt_rec (h : Nat) : ∀ r ∈ RS,
    cnt (h + 5) r + 10 * cnt (h + 3) r + 5 * cnt (h + 1) r =
      5 * cnt (h + 4) r + 10 * cnt (h + 2) r + cnt h r := by
  induction h with
  | zero =>
    intro r hr
    have hb := List.all_eq_true.1 base_check r hr
    simp only [beq_iff_eq] at hb
    have l := mem_RS_lt hr
    rw [cnt_eq_V 5 r l, cnt_eq_V 3 r l, cnt_eq_V 1 r l, cnt_eq_V 4 r l, cnt_eq_V 2 r l,
      cnt_eq_V 0 r l]
    exact hb
  | succ h ih =>
    intro r _
    show cnt ((h + 5) + 1) r + 10 * cnt ((h + 3) + 1) r + 5 * cnt ((h + 1) + 1) r =
      5 * cnt ((h + 4) + 1) r + 10 * cnt ((h + 2) + 1) r + cnt (h + 1) r
    simp only [cnt]
    exact sum_comb _ _ _ _ _ _ _ fun s hs => ih s (mem_below hs)

theorem RS_length : RS.length = 42 := by decide +kernel

theorem top_mem : (127 : Nat) ∈ RS := by decide +kernel

theorem a_succ (h : Nat) : a (h + 1) = 42 * (cnt h 127 : Int) := by
  show ((RS.flatMap fun r => (tails RS h (2^7-1)).map (r :: ·)).length : Int) = _
  rw [List.length_flatMap]
  simp only [List.length_map, len_tails, List.map_const', List.sum_replicate, RS_length]
  norm_num

theorem a_zero : a 0 = 0 := rfl

theorem cnt_vals : (cnt 0 127, cnt 1 127, cnt 2 127, cnt 3 127, cnt 4 127) =
    (1, 42, 255, 868, 2205) := by
  rw [cnt_eq_V 0 127 (by norm_num), cnt_eq_V 1 127 (by norm_num), cnt_eq_V 2 127 (by norm_num),
    cnt_eq_V 3 127 (by norm_num), cnt_eq_V 4 127 (by norm_num)]
  decide +kernel

theorem a_rec (n : Nat) :
    a (n+6) = 5*a (n+5) - 10*a (n+4) + 10*a (n+3) - 5*a (n+2) + a (n+1) := by
  have hc := cnt_rec n 127 top_mem
  have hz : ((cnt (n + 5) 127 + 10 * cnt (n + 3) 127 + 5 * cnt (n + 1) 127 : Nat) : Int) =
      ((5 * cnt (n + 4) 127 + 10 * cnt (n + 2) 127 + cnt n 127 : Nat) : Int) := by
    rw [hc]
  push_cast at hz
  rw [a_succ (n + 5), a_succ (n + 4), a_succ (n + 3), a_succ (n + 2), a_succ (n + 1), a_succ n]
  linear_combination 42 * hz

theorem a_vals : a 1 = 42 ∧ a 2 = 1764 ∧ a 3 = 10710 ∧ a 4 = 36456 ∧ a 5 = 92610 := by
  have hv := cnt_vals
  simp only [Prod.mk.injEq] at hv
  obtain ⟨h0, h1, h2, h3, h4⟩ := hv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [a_succ 0, h0]; norm_num
  · rw [a_succ 1, h1]; norm_num
  · rw [a_succ 2, h2]; norm_num
  · rw [a_succ 3, h3]; norm_num
  · rw [a_succ 4, h4]; norm_num

open PowerSeries in
theorem gen_fun : PowerSeries.mk a * (1-PowerSeries.X)^5 =
      42 * PowerSeries.X * (1 + 37*PowerSeries.X + 55*PowerSeries.X^2 + 3*PowerSeries.X^3) := by
  have key : PowerSeries.mk a * (1 - X) ^ 5 =
      C 1 * (PowerSeries.mk a * X ^ 0) - C 5 * (PowerSeries.mk a * X ^ 1) +
        C 10 * (PowerSeries.mk a * X ^ 2) - C 10 * (PowerSeries.mk a * X ^ 3) +
        C 5 * (PowerSeries.mk a * X ^ 4) - C 1 * (PowerSeries.mk a * X ^ 5) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (42 : ℤ⟦X⟧) * X * (1 + 37 * X + 55 * X ^ 2 + 3 * X ^ 3) =
      C 42 * X ^ 1 + C 1554 * X ^ 2 + C 2310 * X ^ 3 + C 126 * X ^ 4 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  obtain ⟨v1, v2, v3, v4, v5⟩ := a_vals
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 6
  · interval_cases k <;> simp [a_zero, v1, v2, v3, v4, v5]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    have hr := a_rec j
    simp only [show 0 ≤ j + 6 by omega, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega,
      show 3 ≤ j + 6 by omega, show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega,
      show j + 6 - 0 = j + 6 by omega, show j + 6 - 1 = j + 5 by omega,
      show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega,
      show j + 6 - 4 = j + 2 by omega, show j + 6 - 5 = j + 1 by omega,
      show ¬ (j + 6 = 1) by omega, show ¬ (j + 6 = 2) by omega, show ¬ (j + 6 = 3) by omega,
      show ¬ (j + 6 = 4) by omega, if_true, if_false]
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a207452.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.a_rec⟩
