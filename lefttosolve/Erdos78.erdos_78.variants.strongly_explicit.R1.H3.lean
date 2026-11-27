import OMAReductions.R_Erdos78_erdos_78_variants_strongly_explicit_R1

/-!
# Step H3 of the reduction Erdos78.erdos_78.variants.strongly_explicit.R1

The map (n, b, c) to (2 ^ size n, b, c) is polynomial time. On the bitstring encoding the input is
delimit (bits n) ++ rest and the output is delimit (bits (2 ^ size n)) ++ rest, where
bits (2 ^ size n) is size n zeros followed by a one. An explicit three-stack TM2 machine reads the
first block pair by pair, writes the pair true false for each payload bit, writes true true false
at the terminator, copies the rest, all onto a temporary stack, and finally reverses the temporary
stack onto the output stack. It runs in 2 L + 4 steps on an input of length L.

Only upstream definitions (IsPolyTime, the bitstring encodings, delimit) are used: delimit is
unfolded definitionally (show / rfl), its length is computed by the local lemma len_delimit, and
every simp call is a simp only with an explicit list of Mathlib lemmas and local helpers.
-/

open Turing Computability ComplexityTheory StateTransition BitstringEncoding

namespace OMA.Helpers

/-- Stacks: input, temporary, output. -/
inductive SK
  | inp
  | tmp
  | out
  deriving DecidableEq

instance : Fintype SK :=
  ⟨{SK.inp, SK.tmp, SK.out}, by
    intro x
    cases x <;> simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_singleton, or_self,
      or_false, or_true]⟩

/-- Control labels. -/
inductive PL
  | head
  | skip
  | copy
  | rev
  deriving DecidableEq

instance : Fintype PL :=
  ⟨{PL.head, PL.skip, PL.copy, PL.rev}, by
    intro x
    cases x <;> simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_singleton, or_self,
      or_false, or_true]⟩

abbrev G3 : SK → Type := fun _ => Bool

def stk (a t o : List Bool) : ∀ k, List (G3 k)
  | SK.inp => a
  | SK.tmp => t
  | SK.out => o

theorem upd_inp (a t o l : List Bool) : Function.update (stk a t o) SK.inp l = stk l t o := by
  funext k; cases k <;> simp only [Function.update, reduceCtorEq, ↓reduceDIte, stk]

theorem upd_tmp (a t o l : List Bool) : Function.update (stk a t o) SK.tmp l = stk a l o := by
  funext k; cases k <;> simp only [Function.update, reduceCtorEq, ↓reduceDIte, stk]

theorem upd_out (a t o l : List Bool) : Function.update (stk a t o) SK.out l = stk a t l := by
  funext k; cases k <;> simp only [Function.update, reduceCtorEq, ↓reduceDIte, stk]

@[simp] theorem stk_inp (a t o : List Bool) : stk a t o SK.inp = a := rfl
@[simp] theorem stk_tmp (a t o : List Bool) : stk a t o SK.tmp = t := rfl
@[simp] theorem stk_out (a t o : List Bool) : stk a t o SK.out = o := rfl

def prog : PL → TM2.Stmt G3 PL (Option Bool)
  | PL.head =>
    .pop SK.inp (fun _ o => o) <|
      .branch (fun v => v.getD false)
        (.goto fun _ => PL.skip)
        (.push SK.tmp (fun _ => true) <| .push SK.tmp (fun _ => true) <|
          .push SK.tmp (fun _ => false) <| .goto fun _ => PL.copy)
  | PL.skip =>
    .pop SK.inp (fun _ o => o) <|
      .push SK.tmp (fun _ => true) <| .push SK.tmp (fun _ => false) <| .goto fun _ => PL.head
  | PL.copy =>
    .pop SK.inp (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.push SK.tmp (fun v => v.getD false) <| .goto fun _ => PL.copy)
        (.goto fun _ => PL.rev)
  | PL.rev =>
    .pop SK.tmp (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.push SK.out (fun v => v.getD false) <| .goto fun _ => PL.rev)
        .halt

def padTM : FinTM2 :=
  { K := SK
    k₀ := SK.inp
    k₁ := SK.out
    Γ := G3
    Λ := PL
    main := PL.head
    σ := Option Bool
    initialState := none
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := prog }

abbrev Cf := TM2.Cfg G3 PL (Option Bool)

def padStep : Cf → Option Cf := TM2.step prog

theorem head_true (v : Option Bool) (a t o : List Bool) :
    padStep ⟨some PL.head, v, stk (true :: a) t o⟩ = some ⟨some PL.skip, some true, stk a t o⟩ := by
  simp only [padStep, TM2.step.eq_2, prog, TM2.stepAux.eq_3, stk_inp, List.head?_cons,
    List.tail_cons, upd_inp, TM2.stepAux.eq_5, Option.getD_some, TM2.stepAux.eq_6, TM2.stepAux.eq_1,
    stk_tmp, Function.update_self, Function.update_idem, cond_true]

theorem head_false (v : Option Bool) (a t o : List Bool) :
    padStep ⟨some PL.head, v, stk (false :: a) t o⟩ =
      some ⟨some PL.copy, some false, stk a (false :: true :: true :: t) o⟩ := by
  simp only [padStep, TM2.step.eq_2, prog, TM2.stepAux.eq_3, stk_inp, List.head?_cons,
    List.tail_cons, upd_inp, TM2.stepAux.eq_5, Option.getD_some, TM2.stepAux.eq_6, TM2.stepAux.eq_1,
    stk_tmp, upd_tmp, cond_false]

theorem skip_step (v : Option Bool) (b : Bool) (a t o : List Bool) :
    padStep ⟨some PL.skip, v, stk (b :: a) t o⟩ =
      some ⟨some PL.head, some b, stk a (false :: true :: t) o⟩ := by
  simp only [padStep, TM2.step.eq_2, prog, TM2.stepAux.eq_3, stk_inp, List.head?_cons,
    List.tail_cons, upd_inp, TM2.stepAux.eq_1, stk_tmp, upd_tmp, TM2.stepAux.eq_6]

theorem copy_cons (v : Option Bool) (b : Bool) (a t o : List Bool) :
    padStep ⟨some PL.copy, v, stk (b :: a) t o⟩ = some ⟨some PL.copy, some b, stk a (b :: t) o⟩ := by
  simp only [padStep, TM2.step.eq_2, prog, TM2.stepAux.eq_3, stk_inp, List.head?_cons,
    List.tail_cons, upd_inp, TM2.stepAux.eq_5, Option.isSome_some, TM2.stepAux.eq_1,
    Option.getD_some, stk_tmp, upd_tmp, TM2.stepAux.eq_6, cond_true]

theorem copy_nil (v : Option Bool) (t o : List Bool) :
    padStep ⟨some PL.copy, v, stk [] t o⟩ = some ⟨some PL.rev, none, stk [] t o⟩ := by
  simp only [padStep, TM2.step.eq_2, prog, TM2.stepAux.eq_3, stk_inp, List.head?_nil,
    List.tail_nil, upd_inp, TM2.stepAux.eq_5, Option.isSome_none, TM2.stepAux.eq_1,
    Option.getD_none, stk_tmp, TM2.stepAux.eq_6, cond_false]

theorem rev_cons (v : Option Bool) (b : Bool) (t o : List Bool) :
    padStep ⟨some PL.rev, v, stk [] (b :: t) o⟩ = some ⟨some PL.rev, some b, stk [] t (b :: o)⟩ := by
  simp only [padStep, TM2.step.eq_2, prog, TM2.stepAux.eq_3, stk_tmp, List.head?_cons,
    List.tail_cons, upd_tmp, TM2.stepAux.eq_5, Option.isSome_some, TM2.stepAux.eq_1,
    Option.getD_some, stk_out, upd_out, TM2.stepAux.eq_6, TM2.stepAux.eq_7, cond_true]

theorem rev_nil (v : Option Bool) (o : List Bool) :
    padStep ⟨some PL.rev, v, stk [] [] o⟩ = some ⟨none, none, stk [] [] o⟩ := by
  simp only [padStep, TM2.step.eq_2, prog, TM2.stepAux.eq_3, stk_tmp, List.head?_nil,
    List.tail_nil, upd_tmp, TM2.stepAux.eq_5, Option.isSome_none, TM2.stepAux.eq_1,
    Option.getD_none, stk_out, TM2.stepAux.eq_6, TM2.stepAux.eq_7, cond_false]

theorem iter_succ_of {α : Type*} {f : α → Option α} {c d : α} (h : f c = some d) (n : ℕ) :
    (flip bind f)^[n + 1] (some c) = (flip bind f)^[n] (some d) := by
  rw [Function.iterate_succ_apply]
  show (flip bind f)^[n] (f c) = _
  rw [h]

def pairs : ℕ → List Bool → List Bool
  | 0, t => t
  | s + 1, t => pairs s (false :: true :: t)

theorem head_run (R o : List Bool) : ∀ (l t : List Bool) (v : Option Bool),
    (flip bind padStep)^[2 * l.length + 1] (some ⟨some PL.head, v, stk (delimit l ++ R) t o⟩) =
      some ⟨some PL.copy, some false, stk R (false :: true :: true :: pairs l.length t) o⟩
  | [], t, v => by
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add]
    rw [show delimit [] ++ R = false :: R from rfl, iter_succ_of (head_false v R t o)]
    rfl
  | b :: l, t, v => by
    have e : 2 * (b :: l).length + 1 = (2 * l.length + 1) + 1 + 1 := by
      simp only [List.length_cons, Nat.add_right_cancel_iff]; ring
    rw [e, show delimit (b :: l) ++ R = true :: b :: (delimit l ++ R) from rfl,
      iter_succ_of (head_true v (b :: (delimit l ++ R)) t o),
      iter_succ_of (skip_step (some true) b (delimit l ++ R) t o), head_run R o l _ (some b)]
    rfl

theorem copy_run (o : List Bool) : ∀ (R t : List Bool) (v : Option Bool),
    (flip bind padStep)^[R.length + 1] (some ⟨some PL.copy, v, stk R t o⟩) =
      some ⟨some PL.rev, none, stk [] (R.reverse ++ t) o⟩
  | [], t, v => by
    rw [List.length_nil, iter_succ_of (copy_nil v t o)]
    rfl
  | b :: R, t, v => by
    rw [List.length_cons, iter_succ_of (copy_cons v b R t o), copy_run o R (b :: t) (some b)]
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

theorem rev_run : ∀ (t o : List Bool) (v : Option Bool),
    (flip bind padStep)^[t.length + 1] (some ⟨some PL.rev, v, stk [] t o⟩) =
      some ⟨none, none, stk [] [] (t.reverse ++ o)⟩
  | [], o, v => by
    rw [List.length_nil, iter_succ_of (rev_nil v o)]
    rfl
  | b :: t, o, v => by
    rw [List.length_cons, iter_succ_of (rev_cons v b t o), rev_run t (b :: o) (some b)]
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

theorem pairs_eq : ∀ (s : ℕ) (t : List Bool),
    pairs s t = (List.replicate s [false, true]).flatten ++ t
  | 0, t => rfl
  | s + 1, t => by
    rw [pairs, pairs_eq s, List.replicate_succ', List.flatten_append]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc,
      List.cons_append, List.nil_append]

theorem length_pairs (s : ℕ) (t : List Bool) : (pairs s t).length = 2 * s + t.length := by
  rw [pairs_eq]
  simp only [List.length_append, List.length_flatten, List.map_replicate, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, List.sum_replicate, smul_eq_mul,
    Nat.add_right_cancel_iff]
  ring

theorem rev_pairs (s : ℕ) :
    ((List.replicate s [false, true]).flatten).reverse = (List.replicate s [true, false]).flatten := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [List.replicate_succ, List.flatten_cons, List.reverse_append, ih]
    rw [List.replicate_succ', List.flatten_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.flatten_cons, List.flatten_nil, List.append_nil]

theorem delimit_pow (s : ℕ) :
    delimit (List.replicate s false ++ [true]) =
      (List.replicate s [true, false]).flatten ++ [true, true, false] := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [List.replicate_succ, List.cons_append]
    show true :: false :: delimit (List.replicate s false ++ [true]) = _
    rw [ih, List.replicate_succ, List.flatten_cons]
    rfl

theorem full_run (l R : List Bool) :
    (flip bind padStep)^[(2 * R.length + 4 * l.length + 6)]
      (some ⟨some PL.head, none, stk (delimit l ++ R) [] []⟩) =
      some ⟨none, none, stk [] []
        (delimit (List.replicate l.length false ++ [true]) ++ R)⟩ := by
  have e : 2 * R.length + 4 * l.length + 6 =
      ((R.length + 3 + 2 * l.length) + 1) + ((R.length + 1) + (2 * l.length + 1)) := by ring
  rw [e, Function.iterate_add_apply _ (R.length + 3 + 2 * l.length + 1),
    Function.iterate_add_apply _ (R.length + 1), head_run, copy_run]
  have hlen : (R.reverse ++ false :: true :: true :: pairs l.length []).length =
      R.length + 3 + 2 * l.length := by
    simp only [List.length_append, List.length_reverse, List.length_cons, length_pairs,
      List.length_nil, add_zero]
    ring
  rw [← hlen, rev_run, delimit_pow, pairs_eq]
  simp only [List.append_nil, List.reverse_append, List.reverse_cons, rev_pairs, List.append_assoc,
    List.cons_append, List.nil_append, List.reverse_reverse]

theorem encodeNat_bit (b : Bool) (n : ℕ) (h : Nat.bit b n ≠ 0) :
    encodeNat (Nat.bit b n) = b :: encodeNat n := by
  unfold encodeNat
  rw [← Num.ofNat'_eq, ← Num.ofNat'_eq, Num.ofNat'_bit]
  have hc : ((Num.ofNat' n : Num) : ℕ) = n := by rw [Num.ofNat'_eq]; exact Num.to_of_nat n
  rcases hn : Num.ofNat' n with _ | p
  · rw [hn] at hc
    have h0 : n = 0 := by rw [← hc]; rfl
    subst h0
    cases b
    · exact absurd rfl h
    · rfl
  · cases b <;> rfl

theorem encodeNat_eq_bits (n : ℕ) : encodeNat n = n.bits := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hb ih =>
    have hne : Nat.bit b n ≠ 0 := by
      cases b <;> simp_all only [Bool.false_eq_true, imp_false, implies_true, Nat.bit, cond_false,
        cond_true, ne_eq, Nat.add_eq_zero_iff, mul_eq_zero, OfNat.ofNat_ne_zero, one_ne_zero,
        or_self, false_or, and_false, not_false_eq_true]
    rw [Nat.bits_append_bit n b hb, encodeNat_bit b n hne, ih]

theorem encodeNat_two_pow (s : ℕ) : encodeNat (2 ^ s) = List.replicate s false ++ [true] := by
  rw [encodeNat_eq_bits]
  induction s with
  | zero => exact Nat.one_bits
  | succ s ih =>
    have e : 2 ^ (s + 1) = Nat.bit false (2 ^ s) := by
      rw [Nat.bit_false, pow_succ]; ring
    rw [e, Nat.bits_append_bit _ _ (fun h => absurd h (pow_ne_zero s (by norm_num))), ih]
    rfl

theorem length_encodeNat (n : ℕ) : (encodeNat n).length = Nat.size n := by
  rw [encodeNat_eq_bits, Nat.size_eq_bits_len]

theorem init_eq (I : List Bool) :
    initList padTM (List.map (Equiv.refl Bool).invFun I) = (⟨some PL.head, none, stk I [] []⟩ : Cf) := by
  simp only [initList]
  congr 1
  funext k
  cases k
  · exact List.map_id I
  · rfl
  · rfl

theorem halt_eq (O : List Bool) :
    haltList padTM (List.map (Equiv.refl Bool).invFun O) = (⟨none, none, stk [] [] O⟩ : Cf) := by
  simp only [haltList]
  congr 1
  funext k
  cases k
  · rfl
  · rfl
  · exact List.map_id O

theorem len_delimit : ∀ l : List Bool, (delimit l).length = 2 * l.length + 1
  | [] => rfl
  | b :: l => by
    show (true :: b :: delimit l).length = _
    simp only [List.length_cons, len_delimit l]
    ring

theorem pad_isPolyTime :
    IsPolyTime (fun x : ℕ × ℕ × ℕ => ((2 : ℕ) ^ Nat.size x.1, x.2)) := by
  refine ⟨⟨⟨padTM, Equiv.refl Bool, Equiv.refl Bool⟩, 2 * Polynomial.X + 6, fun x => ?_⟩⟩
  obtain ⟨n, y⟩ := x
  have hin : (BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode (n, y) =
      delimit (encodeNat n) ++ bitEncode y := rfl
  have hout : (BitstringEncoding.toEncoding (α := ℕ × ℕ × ℕ)).encode (2 ^ Nat.size n, y) =
      delimit (List.replicate (encodeNat n).length false ++ [true]) ++ bitEncode y := by
    rw [length_encodeNat, ← encodeNat_two_pow]
    rfl
  refine ⟨⟨2 * (bitEncode y).length + 4 * (encodeNat n).length + 6, ?_⟩, ?_⟩
  · show (flip bind padStep)^[_] (some (initList padTM _)) = Option.map (haltList padTM) (some _)
    rw [hin, hout, init_eq, Option.map_some, halt_eq]
    exact full_run (encodeNat n) (bitEncode y)
  · show 2 * (bitEncode y).length + 4 * (encodeNat n).length + 6 ≤
      Polynomial.eval (delimit (encodeNat n) ++ bitEncode y).length (2 * Polynomial.X + 6)
    rw [List.length_append, len_delimit]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
      add_le_add_iff_right]
    omega

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos78_erdos_78_variants_strongly_explicit_R1.H3 :=
  OMA.Helpers.pad_isPolyTime
