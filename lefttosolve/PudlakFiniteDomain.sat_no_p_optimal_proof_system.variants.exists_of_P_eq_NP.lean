import FormalConjectures.Paper.PudlakFiniteDomainConjectures

-- Problem: If `P = NP` then every NP-complete language has a p-optimal proof system.
-- Upstream: formal-conjectures FormalConjectures/Paper/PudlakFiniteDomainConjectures.lean:202
-- Proved by building the retraction machine explicitly (no TM composition lemma is needed).

/-!
# A polynomial-time retraction onto a polynomial-time language

Given a polynomial-time decider `L` (a Mathlib `FinTM2` machine `M`) and a fixed word, we build a
machine `N` computing `fun w => if L w then w else fallback`:

1. `copy`: pop the encoded input from the main stack onto a scratch stack;
2. `restore`: pop it back, pushing every symbol both onto the main stack and onto the input
   stack of `M` (so both hold the input in its original order);
3. run `M` step for step on its own stacks (`liftStmt`); its `halt` becomes a jump to
4. `inspect`: pop the answer bit of `M`; on acceptance halt, the main stack already holding the
   encoded input, which is also the encoded output;
5. `clear`: on rejection empty the main stack and push the encoding of the fixed word.

The run takes at most `p(n) + 3n + 4` steps when `M` runs in time `p`. With `P = NP`, every
NP-complete language `L` is decided in polynomial time, the retraction onto `L` (fixed word in
`L`) is a proof system for `L`, and every proof system `Q` for `L` is p-simulated by it via `Q`.
-/

open Turing Computability ComplexityTheory StateTransition

namespace OMA.RetractTM

/-- Control phases added around the embedded decider. -/
inductive Ph
  | copy
  | restore
  | inspect
  | clear
  deriving DecidableEq

instance : Fintype Ph :=
  ⟨{Ph.copy, Ph.restore, Ph.inspect, Ph.clear}, by intro x; cases x <;> simp⟩

section
variable (M : FinTM2)

/-- Stack alphabets: two new Boolean stacks (`inl false` = main, `inl true` = temp)
next to the stacks of the decider. -/
abbrev G : Bool ⊕ M.K → Type := fun k => Sum.casesOn (motive := fun _ => Type) k (fun _ => Bool) M.Γ

/-- Stacks of the new machine, from the two new stacks and the decider's stacks. -/
def emb (a b : List Bool) (S : ∀ k, List (M.Γ k)) : ∀ k, List (G M k)
  | Sum.inl false => a
  | Sum.inl true => b
  | Sum.inr k => S k

theorem upd_main [DecidableEq (Bool ⊕ M.K)] (a b : List Bool) (S : ∀ k, List (M.Γ k))
    (l : List (G M (Sum.inl false))) :
    Function.update (emb M a b S) (Sum.inl false) l = emb M l b S := by
  funext k
  match k with
  | Sum.inl false => simp [emb]
  | Sum.inl true => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr k => rw [Function.update_of_ne (by simp)]; rfl

theorem upd_temp [DecidableEq (Bool ⊕ M.K)] (a b : List Bool) (S : ∀ k, List (M.Γ k))
    (l : List (G M (Sum.inl true))) :
    Function.update (emb M a b S) (Sum.inl true) l = emb M a l S := by
  funext k
  match k with
  | Sum.inl false => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl true => simp [emb]
  | Sum.inr k => rw [Function.update_of_ne (by simp)]; rfl

theorem upd_inr [DecidableEq (Bool ⊕ M.K)] [DecidableEq M.K] (a b : List Bool)
    (S : ∀ k, List (M.Γ k)) (k : M.K) (l : List (M.Γ k)) :
    Function.update (emb M a b S) (Sum.inr k) l = emb M a b (Function.update S k l) := by
  funext j
  match j with
  | Sum.inl false => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl true => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr j =>
    by_cases h : j = k
    · subst h; simp [emb]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j = Function.update S k l j
      rw [Function.update_of_ne h]

/-- The decider's statements, acting on its own stacks and on the first state component;
halting hands control to the inspection phase. -/
def liftStmt : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Option Bool)
  | .push k f q => .push (Sum.inr k) (fun v => f v.1) (liftStmt q)
  | .peek k f q => .peek (Sum.inr k) (fun v o => (f v.1 o, v.2)) (liftStmt q)
  | .pop k f q => .pop (Sum.inr k) (fun v o => (f v.1 o, v.2)) (liftStmt q)
  | .load a q => .load (fun v => (a v.1, v.2)) (liftStmt q)
  | .branch f q₁ q₂ => .branch (fun v => f v.1) (liftStmt q₁) (liftStmt q₂)
  | .goto f => .goto (fun v => Sum.inl (f v.1))
  | .halt => .goto (fun _ => Sum.inr Ph.inspect)

/-- A configuration of the decider, seen inside the new machine. -/
def liftCfg (o : Option Bool) (a b : List Bool) (c : TM2.Cfg M.Γ M.Λ M.σ) :
    TM2.Cfg (G M) (M.Λ ⊕ Ph) (M.σ × Option Bool) :=
  ⟨some (c.l.elim (Sum.inr Ph.inspect) Sum.inl), (c.var, o), emb M a b c.stk⟩

theorem stepAux_lift [DecidableEq (Bool ⊕ M.K)] [DecidableEq M.K] (o : Option Bool)
    (a b : List Bool) (q : TM2.Stmt M.Γ M.Λ M.σ) :
    ∀ (v : M.σ) (S : ∀ k, List (M.Γ k)),
    TM2.stepAux (liftStmt M q) (v, o) (emb M a b S) = liftCfg M o a b (TM2.stepAux q v S) := by
  induction q with
  | push k f q ih =>
    intro v S
    simp only [liftStmt, TM2.stepAux]
    rw [show emb M a b S (Sum.inr k) = S k from rfl, upd_inr]
    exact ih _ _
  | peek k f q ih =>
    intro v S
    simp only [liftStmt, TM2.stepAux]
    exact ih _ _
  | pop k f q ih =>
    intro v S
    simp only [liftStmt, TM2.stepAux]
    rw [show emb M a b S (Sum.inr k) = S k from rfl, upd_inr]
    exact ih _ _
  | load f q ih =>
    intro v S
    simp only [liftStmt, TM2.stepAux]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S
    simp only [liftStmt, TM2.stepAux]
    cases f v
    · exact ih₂ _ _
    · exact ih₁ _ _
  | goto f =>
    intro v S
    rfl
  | halt =>
    intro v S
    rfl


@[simp] theorem emb_main (a b : List Bool) (S : ∀ k, List (M.Γ k)) :
    emb M a b S (Sum.inl false) = a := rfl

@[simp] theorem emb_temp (a b : List Bool) (S : ∀ k, List (M.Γ k)) :
    emb M a b S (Sum.inl true) = b := rfl

@[simp] theorem emb_inr (a b : List Bool) (S : ∀ k, List (M.Γ k)) (k : M.K) :
    emb M a b S (Sum.inr k) = S k := rfl

end

section
variable (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool) (outE : M.Γ M.k₁ ≃ Bool) (F : List Bool)

/-- Push a fixed word on the main stack, so that afterwards it starts with that word. -/
def put : List Bool → TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Option Bool) →
    TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Option Bool)
  | [], q => q
  | b :: bs, q => put bs (.push (Sum.inl false) (fun _ => b) q)

/-- The program: copy the input to `temp`, restore it to `main` and to the decider's input,
run the decider, read its bit, and on rejection replace `main` by the fixed word `F`. -/
def prog : M.Λ ⊕ Ph → TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Option Bool)
  | Sum.inl l => liftStmt M (M.m l)
  | Sum.inr Ph.copy =>
    .pop (Sum.inl false) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2.isSome)
        (.push (Sum.inl true) (fun v => v.2.getD false) (.goto fun _ => Sum.inr Ph.copy))
        (.goto fun _ => Sum.inr Ph.restore)
  | Sum.inr Ph.restore =>
    .pop (Sum.inl true) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2.isSome)
        (.push (Sum.inl false) (fun v => v.2.getD false) <|
          .push (Sum.inr M.k₀) (fun v => e.symm (v.2.getD false))
            (.goto fun _ => Sum.inr Ph.restore))
        (.goto fun _ => Sum.inl M.main)
  | Sum.inr Ph.inspect =>
    .pop (Sum.inr M.k₁) (fun v o => (v.1, o.map outE)) <|
      .branch (fun v => v.2.getD false)
        (.load (fun _ => (M.initialState, none)) .halt)
        (.goto fun _ => Sum.inr Ph.clear)
  | Sum.inr Ph.clear =>
    .pop (Sum.inl false) (fun v o => (v.1, o)) <|
      .branch (fun v => v.2.isSome)
        (.goto fun _ => Sum.inr Ph.clear)
        (put M F (.load (fun _ => (M.initialState, none)) .halt))

/-- The new machine. Its input and output stack is `main`. -/
def N : FinTM2 :=
  letI := M.kFin
  letI := M.ΛFin
  letI := M.σFin
  { K := Bool ⊕ M.K
    k₀ := Sum.inl false
    k₁ := Sum.inl false
    Γ := G M
    Λ := M.Λ ⊕ Ph
    main := Sum.inr Ph.copy
    σ := M.σ × Option Bool
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := prog M e outE F }

theorem N_step : (N M e outE F).step = TM2.step (prog M e outE F) := rfl

variable [DecidableEq (Bool ⊕ M.K)]

theorem stepAux_put (m t : List Bool) (S : ∀ k, List (M.Γ k)) (v : M.σ × Option Bool) :
    ∀ (W : List Bool) (q : TM2.Stmt (G M) (M.Λ ⊕ Ph) (M.σ × Option Bool)),
    TM2.stepAux (put M W q) v (emb M m t S) = TM2.stepAux q v (emb M (W ++ m) t S) := by
  intro W
  induction W generalizing m with
  | nil => intro q; rfl
  | cons b bs ih =>
    intro q
    simp only [put]
    rw [ih]
    simp only [TM2.stepAux, emb_main, upd_main]
    rfl

theorem copy_cons (s : M.σ) (o : Option Bool) (x : Bool) (l t : List Bool)
    (S : ∀ k, List (M.Γ k)) :
    TM2.step (prog M e outE F) ⟨some (Sum.inr Ph.copy), (s, o), emb M (x :: l) t S⟩ =
      some ⟨some (Sum.inr Ph.copy), (s, some x), emb M l (x :: t) S⟩ := by
  simp [prog, upd_main, upd_temp]

theorem copy_nil (s : M.σ) (o : Option Bool) (t : List Bool) (S : ∀ k, List (M.Γ k)) :
    TM2.step (prog M e outE F) ⟨some (Sum.inr Ph.copy), (s, o), emb M [] t S⟩ =
      some ⟨some (Sum.inr Ph.restore), (s, none), emb M [] t S⟩ := by
  simp [prog, upd_main]

theorem restore_cons [DecidableEq M.K] (s : M.σ) (o : Option Bool) (y : Bool) (m t : List Bool)
    (S : ∀ k, List (M.Γ k)) :
    TM2.step (prog M e outE F) ⟨some (Sum.inr Ph.restore), (s, o), emb M m (y :: t) S⟩ =
      some ⟨some (Sum.inr Ph.restore), (s, some y),
        emb M (y :: m) t (Function.update S M.k₀ (e.symm y :: S M.k₀))⟩ := by
  simp [prog, upd_main, upd_temp, upd_inr]

theorem restore_nil (s : M.σ) (o : Option Bool) (m : List Bool) (S : ∀ k, List (M.Γ k)) :
    TM2.step (prog M e outE F) ⟨some (Sum.inr Ph.restore), (s, o), emb M m [] S⟩ =
      some ⟨some (Sum.inl M.main), (s, none), emb M m [] S⟩ := by
  simp [prog, upd_temp]

theorem clear_cons (s : M.σ) (o : Option Bool) (x : Bool) (l : List Bool)
    (S : ∀ k, List (M.Γ k)) :
    TM2.step (prog M e outE F) ⟨some (Sum.inr Ph.clear), (s, o), emb M (x :: l) [] S⟩ =
      some ⟨some (Sum.inr Ph.clear), (s, some x), emb M l [] S⟩ := by
  simp [prog, upd_main]

theorem clear_nil (s : M.σ) (o : Option Bool) (S : ∀ k, List (M.Γ k)) :
    TM2.step (prog M e outE F) ⟨some (Sum.inr Ph.clear), (s, o), emb M [] [] S⟩ =
      some ⟨none, (M.initialState, none), emb M F [] S⟩ := by
  simp [prog, upd_main, stepAux_put]


end

section
variable {α : Type*}

theorem iter_none (f : α → Option α) : ∀ n, (flip bind f)^[n] none = none
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply]; exact iter_none f n

theorem iter_succ_of {f : α → Option α} {c d : α} (h : f c = some d) (n : ℕ) :
    (flip bind f)^[n + 1] (some c) = (flip bind f)^[n] (some d) := by
  rw [Function.iterate_succ_apply]
  show (flip bind f)^[n] (f c) = _
  rw [h]

end

section
variable (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool) (outE : M.Γ M.k₁ ≃ Bool) (F : List Bool)
variable [DecidableEq (Bool ⊕ M.K)]

theorem copy_run (s : M.σ) (S : ∀ k, List (M.Γ k)) : ∀ (l t : List Bool) (o : Option Bool),
    (flip bind (TM2.step (prog M e outE F)))^[l.length + 1]
      (some ⟨some (Sum.inr Ph.copy), (s, o), emb M l t S⟩) =
    some ⟨some (Sum.inr Ph.restore), (s, none), emb M [] (l.reverse ++ t) S⟩
  | [], t, o => by
    rw [List.length_nil, iter_succ_of (copy_nil M e outE F s o t S)]
    rfl
  | x :: l, t, o => by
    rw [List.length_cons, iter_succ_of (copy_cons M e outE F s o x l t S),
      copy_run s S l (x :: t) (some x)]
    simp

theorem restore_run [DecidableEq M.K] (s : M.σ) : ∀ (t m : List Bool) (S : ∀ k, List (M.Γ k))
    (o : Option Bool),
    (flip bind (TM2.step (prog M e outE F)))^[t.length + 1]
      (some ⟨some (Sum.inr Ph.restore), (s, o), emb M m t S⟩) =
    some ⟨some (Sum.inl M.main), (s, none),
      emb M (t.reverse ++ m) [] (Function.update S M.k₀ (t.reverse.map e.symm ++ S M.k₀))⟩
  | [], m, S, o => by
    rw [List.length_nil, iter_succ_of (restore_nil M e outE F s o m S)]
    simp
  | y :: t, m, S, o => by
    rw [List.length_cons, iter_succ_of (restore_cons M e outE F s o y m t S),
      restore_run s t (y :: m) _ (some y)]
    simp [Function.update_idem]

theorem clear_run (s : M.σ) (S : ∀ k, List (M.Γ k)) : ∀ (l : List Bool) (o : Option Bool),
    (flip bind (TM2.step (prog M e outE F)))^[l.length + 1]
      (some ⟨some (Sum.inr Ph.clear), (s, o), emb M l [] S⟩) =
    some ⟨none, (M.initialState, none), emb M F [] S⟩
  | [], o => by
    rw [List.length_nil, iter_succ_of (clear_nil M e outE F s o S)]
    rfl
  | x :: l, o => by
    rw [List.length_cons, iter_succ_of (clear_cons M e outE F s o x l S), clear_run s S l (some x)]

theorem lift_step [DecidableEq M.K] (o : Option Bool) (a b : List Bool)
    {c d : TM2.Cfg M.Γ M.Λ M.σ} (h : TM2.step M.m c = some d) :
    TM2.step (prog M e outE F) (liftCfg M o a b c) = some (liftCfg M o a b d) := by
  rcases c with ⟨_ | l, v, S⟩
  · simp at h
  · simp only [TM2.step] at h
    cases h
    show some (TM2.stepAux (liftStmt M (M.m l)) (v, o) (emb M a b S)) = _
    rw [stepAux_lift]

theorem lift_run [DecidableEq M.K] (o : Option Bool) (a b : List Bool) :
    ∀ (n : ℕ) (c d : TM2.Cfg M.Γ M.Λ M.σ), (flip bind (TM2.step M.m))^[n] (some c) = some d →
    (flip bind (TM2.step (prog M e outE F)))^[n] (some (liftCfg M o a b c)) =
      some (liftCfg M o a b d)
  | 0, c, d, h => by
    simp only [Function.iterate_zero, id, Option.some.injEq] at h ⊢
    rw [h]
  | n + 1, c, d, h => by
    cases hc : TM2.step M.m c with
    | none =>
      rw [Function.iterate_succ_apply] at h
      change (flip bind (TM2.step M.m))^[n] (TM2.step M.m c) = some d at h
      rw [hc, iter_none] at h
      cases h
    | some c' =>
      rw [iter_succ_of hc] at h
      rw [iter_succ_of (lift_step M e outE F o a b hc)]
      exact lift_run o a b n c' d h

end

section
variable (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool) (outE : M.Γ M.k₁ ≃ Bool) (F : List Bool)

theorem init_N (I : List Bool) :
    initList (N M e outE F) I =
      TM2.Cfg.mk (some (Sum.inr Ph.copy)) (M.initialState, none)
        (emb M I [] fun k => ([] : List (M.Γ k))) := by
  unfold initList
  congr 1
  funext k
  match k with
  | Sum.inl false => rfl
  | Sum.inl true => rfl
  | Sum.inr k => rfl

theorem halt_N (I : List Bool) :
    haltList (N M e outE F) I =
      TM2.Cfg.mk none (M.initialState, none) (emb M I [] fun k => ([] : List (M.Γ k))) := by
  unfold haltList
  congr 1
  funext k
  match k with
  | Sum.inl false => rfl
  | Sum.inl true => rfl
  | Sum.inr k => rfl

theorem init_M_stk [DecidableEq M.K] (X : List (M.Γ M.k₀)) :
    Function.update (fun k => ([] : List (M.Γ k))) M.k₀ X = (initList M X).stk := by
  funext k
  by_cases h : k = M.k₀
  · subst h; simp [initList]
  · rw [Function.update_of_ne h]; simp [initList, h]

theorem halt_M_k1 (X : List (M.Γ M.k₁)) : (haltList M X).stk M.k₁ = X := by
  simp [haltList]

theorem halt_M_upd [DecidableEq M.K] (X : List (M.Γ M.k₁)) :
    Function.update (haltList M X).stk M.k₁ [] = fun k => ([] : List (M.Γ k)) := by
  funext k
  by_cases h : k = M.k₁
  · subst h; simp
  · rw [Function.update_of_ne h]; simp [haltList, h]

theorem halt_M_l (X : List (M.Γ M.k₁)) : (haltList M X).l = none := rfl
theorem halt_M_var (X : List (M.Γ M.k₁)) : (haltList M X).var = M.initialState := rfl

variable [DecidableEq (Bool ⊕ M.K)]

theorem inspect_true [DecidableEq M.K] (m : List Bool) :
    TM2.step (prog M e outE F) (liftCfg M none m [] (haltList M [outE.symm true])) =
      some (TM2.Cfg.mk none (M.initialState, none) (emb M m [] fun k => ([] : List (M.Γ k)))) := by
  simp [liftCfg, halt_M_l, halt_M_var, prog, upd_inr, halt_M_k1, halt_M_upd]

theorem inspect_false [DecidableEq M.K] (m : List Bool) :
    TM2.step (prog M e outE F) (liftCfg M none m [] (haltList M [outE.symm false])) =
      some (TM2.Cfg.mk (some (Sum.inr Ph.clear)) (M.initialState, some false)
        (emb M m [] fun k => ([] : List (M.Γ k)))) := by
  simp [liftCfg, halt_M_l, halt_M_var, prog, upd_inr, halt_M_k1, halt_M_upd]


end

section
variable (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool) (outE : M.Γ M.k₁ ≃ Bool) (F : List Bool)
variable [DecidableEq (Bool ⊕ M.K)] [DecidableEq M.K]

theorem run_true (I : List Bool) (t : ℕ)
    (h : (flip bind (TM2.step M.m))^[t] (some (initList M (I.map e.symm))) =
      some (haltList M [outE.symm true])) :
    (flip bind (TM2.step (prog M e outE F)))^[1 + t + (I.length + 1) + (I.length + 1)]
      (some (TM2.Cfg.mk (some (Sum.inr Ph.copy)) (M.initialState, none)
        (emb M I [] fun k => ([] : List (M.Γ k))))) =
    some (TM2.Cfg.mk none (M.initialState, none) (emb M I [] fun k => ([] : List (M.Γ k)))) := by
  have h1 := copy_run M e outE F M.initialState (fun k => ([] : List (M.Γ k))) I [] none
  have h2 := restore_run M e outE F M.initialState I.reverse [] (fun k => ([] : List (M.Γ k))) none
  have h3 := lift_run M e outE F none I [] t _ _ h
  simp only [List.append_nil, List.length_reverse, List.reverse_reverse] at h1 h2
  rw [init_M_stk] at h2
  rw [Function.iterate_add_apply _ (1 + t + (I.length + 1)) (I.length + 1), h1,
    Function.iterate_add_apply _ (1 + t) (I.length + 1), h2,
    Function.iterate_add_apply _ 1 t]
  rw [show (TM2.Cfg.mk (some (Sum.inl M.main)) (M.initialState, none)
      (emb M I [] (initList M (I.map e.symm)).stk) : TM2.Cfg (G M) (M.Λ ⊕ Ph) (M.σ × Option Bool))
      = liftCfg M none I [] (initList M (I.map e.symm)) from rfl, h3, Function.iterate_one]
  exact inspect_true M e outE F I

theorem run_false (I : List Bool) (t : ℕ)
    (h : (flip bind (TM2.step M.m))^[t] (some (initList M (I.map e.symm))) =
      some (haltList M [outE.symm false])) :
    (flip bind (TM2.step (prog M e outE F)))^[(I.length + 1) + 1 + t + (I.length + 1) + (I.length + 1)]
      (some (TM2.Cfg.mk (some (Sum.inr Ph.copy)) (M.initialState, none)
        (emb M I [] fun k => ([] : List (M.Γ k))))) =
    some (TM2.Cfg.mk none (M.initialState, none) (emb M F [] fun k => ([] : List (M.Γ k)))) := by
  have h1 := copy_run M e outE F M.initialState (fun k => ([] : List (M.Γ k))) I [] none
  have h2 := restore_run M e outE F M.initialState I.reverse [] (fun k => ([] : List (M.Γ k))) none
  have h3 := lift_run M e outE F none I [] t _ _ h
  have h4 := clear_run M e outE F M.initialState (fun k => ([] : List (M.Γ k))) I (some false)
  simp only [List.append_nil, List.length_reverse, List.reverse_reverse] at h1 h2
  rw [init_M_stk] at h2
  rw [Function.iterate_add_apply _ ((I.length + 1) + 1 + t + (I.length + 1)) (I.length + 1), h1,
    Function.iterate_add_apply _ ((I.length + 1) + 1 + t) (I.length + 1), h2,
    Function.iterate_add_apply _ ((I.length + 1) + 1) t]
  rw [show (TM2.Cfg.mk (some (Sum.inl M.main)) (M.initialState, none)
      (emb M I [] (initList M (I.map e.symm)).stk) : TM2.Cfg (G M) (M.Λ ⊕ Ph) (M.σ × Option Bool))
      = liftCfg M none I [] (initList M (I.map e.symm)) from rfl, h3,
    Function.iterate_add_apply _ (I.length + 1) 1, Function.iterate_one]
  rw [show flip bind (TM2.step (prog M e outE F))
      (some (liftCfg M none I [] (haltList M [outE.symm false]))) =
      TM2.step (prog M e outE F) (liftCfg M none I [] (haltList M [outE.symm false])) from rfl,
    inspect_false]
  exact h4

end

section
variable (M : FinTM2) (e : M.Γ M.k₀ ≃ Bool) (outE : M.Γ M.k₁ ≃ Bool) (F : List Bool)

theorem N_evals (I : List Bool) (b : Bool) (t : ℕ)
    (h : (flip bind M.step)^[t] (some (initList M (I.map e.invFun))) =
      some (haltList M [outE.invFun b])) :
    (flip bind (N M e outE F).step)^[(if b then 0 else I.length + 1) + 1 + t + (I.length + 1) +
        (I.length + 1)] (some (initList (N M e outE F) I)) =
      some (haltList (N M e outE F) (if b then I else F)) := by
  simp only [FinTM2.step, Equiv.invFun_as_coe] at h
  refine (congrArg (fun x => (flip bind (N M e outE F).step)^[_] (some x))
    (init_N M e outE F I)).trans ?_
  refine Eq.trans ?_ (congrArg some (halt_N M e outE F _)).symm
  cases b
  · exact run_false M e outE F I t h
  · exact run_true M e outE F I t h

theorem map_in (x : List Bool) :
    List.map (@Equiv.invFun ((N M e outE F).Γ (N M e outE F).k₀) Bool (Equiv.refl Bool)) x = x :=
  List.map_id x

theorem map_out (x : List Bool) :
    List.map (@Equiv.invFun ((N M e outE F).Γ (N M e outE F).k₁) Bool (Equiv.refl Bool)) x = x :=
  List.map_id x

end

/-- On acceptance keep the input word, otherwise return a fixed word: this is polynomial-time
whenever the language is. -/
theorem retract_isPolyTime (L : DecisionProblem) (fallback : List Bool) (hL : IsPolyTime L) :
    IsPolyTime (fun w => if L w then w else fallback) := by
  obtain ⟨T⟩ := hL
  refine ⟨{ tm := N T.tm T.inputAlphabet T.outputAlphabet
              ((BitstringEncoding.toEncoding (α := List Bool)).encode fallback)
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := T.time + 3 * Polynomial.X + 4
            outputsFun := fun w => ?_ }⟩
  obtain ⟨⟨t, ht⟩, htle⟩ := T.outputsFun w
  have ht' : (flip bind T.tm.step)^[t] (some (initList T.tm
      (((BitstringEncoding.toEncoding (α := List Bool)).encode w).map T.inputAlphabet.invFun))) =
      some (haltList T.tm [T.outputAlphabet.invFun (L w)]) := ht
  have key := N_evals T.tm T.inputAlphabet T.outputAlphabet
    ((BitstringEncoding.toEncoding (α := List Bool)).encode fallback)
    ((BitstringEncoding.toEncoding (α := List Bool)).encode w) (L w) t ht'
  refine ⟨⟨(if L w then 0 else ((BitstringEncoding.toEncoding (α := List Bool)).encode w).length + 1)
    + 1 + t + (((BitstringEncoding.toEncoding (α := List Bool)).encode w).length + 1) +
    (((BitstringEncoding.toEncoding (α := List Bool)).encode w).length + 1), ?_⟩, ?_⟩
  · rw [map_in, map_out, key]
    cases L w <;> rfl
  · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat] at htle ⊢
    split <;> omega

end OMA.RetractTM

theorem OMA.solution :
    type_of% @PudlakFiniteDomain.sat_no_p_optimal_proof_system.variants.exists_of_P_eq_NP := by
  intro hPNP L hL hne
  obtain ⟨y, hy⟩ := hne
  have hLP : L ∈ P := hPNP ▸ hL.1
  refine ⟨fun w => if L w then w else y,
    ⟨⟨OMA.RetractTM.retract_isPolyTime L y hLP, fun z => ⟨fun hz => ⟨z, by simp [hz]⟩, ?_⟩⟩, ?_⟩⟩
  · rintro ⟨w, rfl⟩
    by_cases h : L w = true <;> simp [h, hy]
  · intro Q hQ
    refine ⟨Q, hQ.1, fun π => ?_⟩
    have hQπ : L (Q π) = true := (hQ.2 (Q π)).2 ⟨π, rfl⟩
    simp [hQπ]
