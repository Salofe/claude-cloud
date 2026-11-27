import OMAReductions.R_Green92_green_92_variants_chase_lower_R1_H1_R1_H2_R1
import Mathlib

/-!
# Step H1 of Green92.green_92.variants.chase_lower.R1.H1.R1.H2.R1

The deletion masks with a given trace are counted by the number of subsequence
embeddings. The defect string is an alternating string with one extra one inserted,
so the count splits by whether the extra one is used, and embeddings into an
alternating string are counted by a binomial coefficient.
-/

namespace OMA.Helpers

open Finset

/-- Number of embeddings of `w` as a subsequence of `x`. -/
def emb : List Bool → List Bool → ℕ
  | [], [] => 1
  | [], _ :: _ => 0
  | _ :: xs, [] => emb xs []
  | x :: xs, y :: ys => emb xs (y :: ys) + if y = x then emb xs ys else 0

lemma emb_nil_right (x : List Bool) : emb x [] = 1 := by
  induction x with
  | nil => rfl
  | cons a xs ih => simp [emb, ih]

lemma emb_nil_left (w : List Bool) : emb [] w = if w = [] then 1 else 0 := by
  cases w <;> simp [emb]

lemma emb_cons (x : Bool) (xs w : List Bool) :
    emb (x :: xs) w = emb xs w + if w.head? = some x then emb xs w.tail else 0 := by
  cases w with
  | nil => simp [emb]
  | cons y ys => simp [emb]

lemma emb_append (x y w : List Bool) :
    emb (x ++ y) w = ∑ j ∈ range (w.length + 1), emb x (w.take j) * emb y (w.drop j) := by
  induction x generalizing w with
  | nil =>
    cases w with
    | nil => simp [emb]
    | cons a w' =>
      rw [sum_range_succ']
      simp [emb]
  | cons z x' ih =>
    rw [List.cons_append, emb_cons, ih]
    simp only [emb_cons, add_mul, sum_add_distrib]
    congr 1
    cases w with
    | nil => simp
    | cons a w' =>
      rw [sum_range_succ', ih]
      simp only [List.head?_cons, Option.some.injEq, List.tail_cons, List.length_cons,
        List.take_succ_cons, List.drop_succ_cons, List.take_zero, List.head?_nil,
        reduceCtorEq, if_false, zero_mul, add_zero]
      by_cases h : a = z
      · simp [h]
      · simp [h]

lemma emb_insert (x y w : List Bool) :
    emb (x ++ true :: y) w = emb (x ++ y) w + ∑ j ∈ range w.length,
      if w[j]? = some true then emb x (w.take j) * emb y (w.drop (j + 1)) else 0 := by
  rw [emb_append, emb_append]
  simp only [emb_cons, mul_add, sum_add_distrib, List.head?_drop, List.tail_drop]
  congr 1
  rw [sum_range_succ]
  simp only [List.getElem?_eq_none (le_refl _), reduceCtorEq, if_false, mul_zero, add_zero]
  refine sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- The alternating string `(01)^a`. -/
def pat : ℕ → List Bool
  | 0 => []
  | a + 1 => false :: true :: pat a

lemma pat_length (a : ℕ) : (pat a).length = 2 * a := by
  induction a with
  | zero => rfl
  | succ a ih => simp [pat, ih]; ring

lemma pat_append (a b : ℕ) : pat a ++ pat b = pat (a + b) := by
  induction a with
  | zero => simp [pat]
  | succ a ih => rw [Nat.succ_add]; simp [pat, ih]

lemma pat_getElem (a i : ℕ) (h : i < (pat a).length) : (pat a)[i] = decide (i % 2 = 1) := by
  induction a generalizing i with
  | zero => simp [pat] at h
  | succ a ih =>
    match i, h with
    | 0, _ => simp [pat]
    | 1, _ => simp [pat]
    | i + 2, h =>
      simp only [pat, List.getElem_cons_succ]
      rw [ih i (by simp [pat] at h; omega)]
      simp [Nat.add_mod_right]

/-- Number of contiguous `01` pairs. -/
def c01 (v : List Bool) : ℕ := (v.zip v.tail).count (false, true)

lemma c01_lt (v : List Bool) (h : v ≠ []) : c01 v < v.length := by
  unfold c01
  have h1 := List.count_le_length (a := (false, true)) (l := v.zip v.tail)
  have h2 : (v.zip v.tail).length < v.length := by
    rw [List.length_zip, List.length_tail]
    have : 0 < v.length := List.length_pos_iff.mpr h
    omega
  omega

lemma c01_cons_cons (a b : Bool) (v : List Bool) :
    c01 (a :: b :: v) = c01 (b :: v) + if a = false ∧ b = true then 1 else 0 := by
  unfold c01
  simp only [List.tail_cons, List.zip_cons_cons, List.count_cons]
  congr 1
  simp only [beq_iff_eq, Prod.mk.injEq]

lemma c01_single (a : Bool) : c01 [a] = 0 := by simp [c01]

lemma emb_pat (a : ℕ) (v : List Bool) : emb (pat a) v = (a + c01 v).choose v.length := by
  induction a generalizing v with
  | zero =>
    simp only [pat, emb_nil_left, zero_add]
    by_cases hv : v = []
    · subst hv; simp [c01]
    · rw [if_neg hv, Nat.choose_eq_zero_of_lt (c01_lt v hv)]
  | succ a ih =>
    simp only [pat]
    match v with
    | [] => simp [emb_nil_right]
    | true :: v' =>
      rw [emb_cons, emb_cons]
      simp only [List.head?_cons, Option.some.injEq, reduceCtorEq, if_false, add_zero,
        if_true, List.tail_cons, ih, List.length_cons]
      have hc : c01 (true :: v') = c01 v' := by
        cases v' with
        | nil => simp [c01]
        | cons b v'' => rw [c01_cons_cons]; simp
      rw [hc, show a + 1 + c01 v' = (a + c01 v') + 1 by ring, Nat.choose_succ_succ']
      ring
    | false :: [] =>
      simp [emb, ih, c01]
    | false :: true :: v'' =>
      rw [emb_cons, emb_cons, emb_cons]
      simp only [List.head?_cons, Option.some.injEq, reduceCtorEq, if_false, add_zero,
        if_true, List.tail_cons, ih, List.length_cons]
      have hc : c01 (true :: v'') = c01 v'' := by
        cases v'' with
        | nil => simp [c01]
        | cons b v3 => rw [c01_cons_cons]; simp
      rw [c01_cons_cons, hc]
      simp only [and_self, if_true]
      rw [show a + 1 + (c01 v'' + 1) = (a + c01 v'' + 1) + 1 by ring, Nat.choose_succ_succ' (a + c01 v'' + 1),
        Nat.choose_succ_succ' (a + c01 v''), show a + (c01 v'' + 1) = a + c01 v'' + 1 by ring,
        Nat.choose_succ_succ' (a + c01 v'')]
      ring
    | false :: false :: v'' =>
      rw [emb_cons, emb_cons, emb_cons]
      simp only [List.head?_cons, Option.some.injEq, reduceCtorEq, if_false, add_zero,
        if_true, List.tail_cons, ih, List.length_cons]
      rw [c01_cons_cons]
      simp only [Bool.false_eq_true, and_false, if_false, add_zero]
      rw [show a + 1 + c01 (false :: v'') = (a + c01 (false :: v'')) + 1 by ring,
        Nat.choose_succ_succ' (a + c01 (false :: v''))]
      ring

/-- The positions after the first one. -/
def pull {n : ℕ} (S : Finset (Fin (n + 1))) : Finset (Fin n) :=
  univ.filter (fun i => i.succ ∈ S)

lemma pull_map {n : ℕ} (T : Finset (Fin n)) : pull (T.map (Fin.succEmb n)) = T := by
  ext i; simp [pull]

lemma pull_insert {n : ℕ} (T : Finset (Fin n)) :
    pull (insert 0 (T.map (Fin.succEmb n))) = T := by
  ext i; simp [pull, Fin.succ_ne_zero]

lemma map_pull {n : ℕ} (S : Finset (Fin (n + 1))) (h : (0 : Fin (n + 1)) ∉ S) :
    (pull S).map (Fin.succEmb n) = S := by
  ext j
  cases j using Fin.cases with
  | zero => simp [h, Fin.succ_ne_zero]
  | succ i => simp [pull]

lemma insert_map_pull {n : ℕ} (S : Finset (Fin (n + 1))) (h : (0 : Fin (n + 1)) ∈ S) :
    insert 0 ((pull S).map (Fin.succEmb n)) = S := by
  ext j
  cases j using Fin.cases with
  | zero => simp [h]
  | succ i => simp [pull, Fin.succ_ne_zero]

lemma trace_split {n : ℕ} (x : Fin (n + 1) → Bool) (S : Finset (Fin (n + 1))) :
    Green92.trace x S = (if (0 : Fin (n + 1)) ∈ S then [x 0] else []) ++
      Green92.trace (fun i => x i.succ) (pull S) := by
  unfold Green92.trace pull
  rw [List.finRange_succ]
  by_cases h : (0 : Fin (n + 1)) ∈ S <;> simp [h, List.filter_map, Function.comp_def]

lemma card_trace (n : ℕ) (x : Fin n → Bool) (w : List Bool) :
    (univ.filter (fun S : Finset (Fin n) => Green92.trace x S = w)).card = emb (List.ofFn x) w := by
  induction n generalizing w with
  | zero =>
    have h : ∀ S : Finset (Fin 0), Green92.trace x S = [] := fun S => by simp [Green92.trace]
    simp only [h, List.ofFn_zero, emb_nil_left]
    split_ifs with hw
    · subst hw; simp
    · simp [Ne.symm hw]
  | succ n ih =>
    rw [List.ofFn_succ, emb_cons, ← ih, ← ih,
      ← card_filter_add_card_filter_not (s := univ.filter _) (p := fun S => (0 : Fin (n + 1)) ∈ S),
      filter_filter, filter_filter, add_comm]
    congr 1
    · refine card_nbij' pull (fun T => T.map (Fin.succEmb n)) ?_ ?_ ?_ ?_
      · intro S hS
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢
        rw [trace_split, if_neg hS.2] at hS
        simpa using hS.1
      · intro T hT
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hT ⊢
        refine ⟨?_, by simp [Fin.succ_ne_zero]⟩
        rw [trace_split, pull_map, if_neg (by simp [Fin.succ_ne_zero])]
        simpa using hT
      · intro S hS
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS
        exact map_pull S hS.2
      · intro T _
        exact pull_map T
    · split_ifs with hw
      · have hw' : w = x 0 :: w.tail := by
          cases w with
          | nil => simp at hw
          | cons a w' => simp at hw; simp [hw]
        refine card_nbij' pull (fun T => insert 0 (T.map (Fin.succEmb n))) ?_ ?_ ?_ ?_
        · intro S hS
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢
          rw [trace_split, if_pos hS.2, hw'] at hS
          simpa using hS.1
        · intro T hT
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hT ⊢
          refine ⟨?_, by simp⟩
          rw [trace_split, pull_insert, if_pos (by simp), hw', hT]
          rfl
        · intro S hS
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS
          exact insert_map_pull S hS.2
        · intro T _
          exact pull_insert T
      · rw [card_eq_zero, filter_eq_empty_iff]
        rintro S - ⟨h1, h2⟩
        rw [trace_split, if_pos h2] at h1
        apply hw
        rw [← h1]
        rfl

lemma ofFn_W (n k b : ℕ) (hn : n = 4 * k + 3) (hb : b ≤ 2 * k + 1) :
    List.ofFn (fun i : Fin n => decide (i.val % 2 = if i.val < 2 * b then 1 else 0)) =
      pat b ++ true :: pat (2 * k + 1 - b) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_cons, pat_length]
    omega
  · intro i h1 h2
    rw [List.getElem_ofFn]
    by_cases h : i < 2 * b
    · rw [List.getElem_append_left (by rw [pat_length]; exact h), pat_getElem]
      simp [h]
    · rw [List.getElem_append_right (by rw [pat_length]; omega), List.getElem_cons]
      simp only [pat_length, if_neg h]
      split_ifs with h'
      · simp; omega
      · rw [pat_getElem]
        simp only [decide_eq_decide]
        omega

end OMA.Helpers

theorem OMA.solution : OMA.R_Green92_green_92_variants_chase_lower_R1_H1_R1_H2_R1.H1 := by
  intro n hn k W F B D b hb w
  have hk : n = 4 * k + 3 := by simp only [k]; omega
  have hW : List.ofFn (W b) = OMA.Helpers.pat b ++ true :: OMA.Helpers.pat (2 * k + 1 - b) :=
    OMA.Helpers.ofFn_W n k b hk hb
  have hF : ∀ a v, F a v = OMA.Helpers.emb (OMA.Helpers.pat a) v := by
    intro a v
    rw [OMA.Helpers.emb_pat]
    rfl
  rw [OMA.Helpers.card_trace, hW, OMA.Helpers.emb_insert, OMA.Helpers.pat_append,
    show b + (2 * k + 1 - b) = 2 * k + 1 by omega]
  simp only [B, D, hF]
