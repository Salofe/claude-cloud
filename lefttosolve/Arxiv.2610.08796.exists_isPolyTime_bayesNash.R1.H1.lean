import OMAReductions.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R1

-- Step H1 of reduction R1: polynomial time is closed under `x ↦ h (x, f x)`.

/-!
# Closure of polynomial time under `x ↦ h (x, f x)`

Given Mathlib `FinTM2` machines `Mf` (computing `f`) and `Mh` (computing `h` on the pair encoding
`delimit (enc x) ++ enc y`), we build one machine `N` whose stacks are three Boolean scratch
stacks (`main`, which is the input stack, `tmp`, `tmp2`), all stacks of `Mf` and all stacks of `Mh`.
Its state is `Mf.σ × Mh.σ × Option Bool` (the last component is a one-bit register).

1. `copy`: pop the input from `main`, pushing every bit on `tmp` and on `tmp2`;
2. `feed`: pop `tmp` onto the input stack of `Mf`, so that it holds the input in order;
3. run `Mf` step for step on its own stacks (`liftF`); its `halt` jumps to
4. `unload`: pop the output of `Mf` onto `tmp` (reversed);
5. `load`: pop `tmp` onto the input stack of `Mh`, then push the terminator `false`;
6. `delim`: pop `tmp2` (the reversed input) pushing `b` and then `true` on the input stack of
   `Mh`, which then holds `delimit (enc x) ++ enc (f x)`;
7. run `Mh` step for step on its own stacks (`liftH`); its `halt` halts `N`, whose output stack
   is the output stack of `Mh`, all other stacks being empty and the state initial.

The run takes `3 (n + 1) + 2 (m + 1) + t_f + t_h` steps where `m = |enc (f x)|`. Since one step
of `Mf` pushes at most `B` symbols (`B` bounds the pushes in any of its finitely many statements),
`m ≤ n + B t_f`, which gives a polynomial bound.
-/

open Turing Computability ComplexityTheory StateTransition


namespace OMA.Helpers

/-- Three Boolean scratch stacks: `main` (input), `tmp`, `tmp2`. -/
inductive Aux
  | main
  | tmp
  | tmp2
  deriving DecidableEq

instance : Fintype Aux :=
  ⟨{Aux.main, Aux.tmp, Aux.tmp2}, by intro x; cases x <;> simp⟩

/-- Control phases added around the two embedded machines. -/
inductive Ph
  | copy
  | feed
  | unload
  | load
  | delim
  deriving DecidableEq

instance : Fintype Ph :=
  ⟨{Ph.copy, Ph.feed, Ph.unload, Ph.load, Ph.delim}, by intro x; cases x <;> simp⟩

section
variable (Mf Mh : FinTM2)

abbrev KK : Type := Aux ⊕ (Mf.K ⊕ Mh.K)

abbrev G : KK Mf Mh → Type := fun k =>
  Sum.casesOn (motive := fun _ => Type) k (fun _ => Bool)
    (fun k' => Sum.casesOn (motive := fun _ => Type) k' Mf.Γ Mh.Γ)

abbrev Lab : Type := (Mf.Λ ⊕ Mh.Λ) ⊕ Ph

abbrev Var : Type := Mf.σ × Mh.σ × Option Bool

/-- Stacks of the composite machine. -/
def emb (a b c : List Bool) (Sf : ∀ k, List (Mf.Γ k)) (Sh : ∀ k, List (Mh.Γ k)) :
    ∀ k, List (G Mf Mh k)
  | Sum.inl Aux.main => a
  | Sum.inl Aux.tmp => b
  | Sum.inl Aux.tmp2 => c
  | Sum.inr (Sum.inl k) => Sf k
  | Sum.inr (Sum.inr k) => Sh k

@[simp] theorem emb_main (a b c : List Bool) (Sf : ∀ k, List (Mf.Γ k))
    (Sh : ∀ k, List (Mh.Γ k)) : emb Mf Mh a b c Sf Sh (Sum.inl Aux.main) = a := rfl

@[simp] theorem emb_tmp (a b c : List Bool) (Sf : ∀ k, List (Mf.Γ k))
    (Sh : ∀ k, List (Mh.Γ k)) : emb Mf Mh a b c Sf Sh (Sum.inl Aux.tmp) = b := rfl

@[simp] theorem emb_tmp2 (a b c : List Bool) (Sf : ∀ k, List (Mf.Γ k))
    (Sh : ∀ k, List (Mh.Γ k)) : emb Mf Mh a b c Sf Sh (Sum.inl Aux.tmp2) = c := rfl

@[simp] theorem emb_f (a b c : List Bool) (Sf : ∀ k, List (Mf.Γ k))
    (Sh : ∀ k, List (Mh.Γ k)) (k : Mf.K) : emb Mf Mh a b c Sf Sh (Sum.inr (Sum.inl k)) = Sf k :=
  rfl

@[simp] theorem emb_h (a b c : List Bool) (Sf : ∀ k, List (Mf.Γ k))
    (Sh : ∀ k, List (Mh.Γ k)) (k : Mh.K) : emb Mf Mh a b c Sf Sh (Sum.inr (Sum.inr k)) = Sh k :=
  rfl

section
variable [DecidableEq (KK Mf Mh)]

theorem upd_main (a b c : List Bool) (Sf : ∀ k, List (Mf.Γ k)) (Sh : ∀ k, List (Mh.Γ k))
    (l : List (G Mf Mh (Sum.inl Aux.main))) :
    Function.update (emb Mf Mh a b c Sf Sh) (Sum.inl Aux.main) l = emb Mf Mh l b c Sf Sh := by
  funext k
  match k with
  | Sum.inl Aux.main => simp
  | Sum.inl Aux.tmp => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux.tmp2 => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr (Sum.inl k) => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr (Sum.inr k) => rw [Function.update_of_ne (by simp)]; rfl

theorem upd_tmp (a b c : List Bool) (Sf : ∀ k, List (Mf.Γ k)) (Sh : ∀ k, List (Mh.Γ k))
    (l : List (G Mf Mh (Sum.inl Aux.tmp))) :
    Function.update (emb Mf Mh a b c Sf Sh) (Sum.inl Aux.tmp) l = emb Mf Mh a l c Sf Sh := by
  funext k
  match k with
  | Sum.inl Aux.main => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux.tmp => simp
  | Sum.inl Aux.tmp2 => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr (Sum.inl k) => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr (Sum.inr k) => rw [Function.update_of_ne (by simp)]; rfl

theorem upd_tmp2 (a b c : List Bool) (Sf : ∀ k, List (Mf.Γ k)) (Sh : ∀ k, List (Mh.Γ k))
    (l : List (G Mf Mh (Sum.inl Aux.tmp2))) :
    Function.update (emb Mf Mh a b c Sf Sh) (Sum.inl Aux.tmp2) l = emb Mf Mh a b l Sf Sh := by
  funext k
  match k with
  | Sum.inl Aux.main => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux.tmp => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux.tmp2 => simp
  | Sum.inr (Sum.inl k) => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr (Sum.inr k) => rw [Function.update_of_ne (by simp)]; rfl

theorem upd_f [DecidableEq Mf.K] (a b c : List Bool) (Sf : ∀ k, List (Mf.Γ k))
    (Sh : ∀ k, List (Mh.Γ k)) (k : Mf.K) (l : List (Mf.Γ k)) :
    Function.update (emb Mf Mh a b c Sf Sh) (Sum.inr (Sum.inl k)) l =
      emb Mf Mh a b c (Function.update Sf k l) Sh := by
  funext j
  match j with
  | Sum.inl Aux.main => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux.tmp => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux.tmp2 => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr (Sum.inl j) =>
    by_cases h : j = k
    · subst h; simp
    · rw [Function.update_of_ne (by simpa using h)]
      show Sf j = Function.update Sf k l j
      rw [Function.update_of_ne h]
  | Sum.inr (Sum.inr j) => rw [Function.update_of_ne (by simp)]; rfl

theorem upd_h [DecidableEq Mh.K] (a b c : List Bool) (Sf : ∀ k, List (Mf.Γ k))
    (Sh : ∀ k, List (Mh.Γ k)) (k : Mh.K) (l : List (Mh.Γ k)) :
    Function.update (emb Mf Mh a b c Sf Sh) (Sum.inr (Sum.inr k)) l =
      emb Mf Mh a b c Sf (Function.update Sh k l) := by
  funext j
  match j with
  | Sum.inl Aux.main => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux.tmp => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inl Aux.tmp2 => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr (Sum.inl j) => rw [Function.update_of_ne (by simp)]; rfl
  | Sum.inr (Sum.inr j) =>
    by_cases h : j = k
    · subst h; simp
    · rw [Function.update_of_ne (by simpa using h)]
      show Sh j = Function.update Sh k l j
      rw [Function.update_of_ne h]

end

/-- The statements of the first machine, acting on its own stacks and on the first state
component; halting hands control to the unloading phase. -/
def liftF : TM2.Stmt Mf.Γ Mf.Λ Mf.σ → TM2.Stmt (G Mf Mh) (Lab Mf Mh) (Var Mf Mh)
  | .push k f q => .push (Sum.inr (Sum.inl k)) (fun v => f v.1) (liftF q)
  | .peek k f q => .peek (Sum.inr (Sum.inl k)) (fun v o => (f v.1 o, v.2)) (liftF q)
  | .pop k f q => .pop (Sum.inr (Sum.inl k)) (fun v o => (f v.1 o, v.2)) (liftF q)
  | .load a q => .load (fun v => (a v.1, v.2)) (liftF q)
  | .branch f q₁ q₂ => .branch (fun v => f v.1) (liftF q₁) (liftF q₂)
  | .goto f => .goto (fun v => Sum.inl (Sum.inl (f v.1)))
  | .halt => .goto (fun _ => Sum.inr Ph.unload)

/-- The statements of the second machine, acting on its own stacks and on the second state
component; halting halts the composite machine. -/
def liftH : TM2.Stmt Mh.Γ Mh.Λ Mh.σ → TM2.Stmt (G Mf Mh) (Lab Mf Mh) (Var Mf Mh)
  | .push k f q => .push (Sum.inr (Sum.inr k)) (fun v => f v.2.1) (liftH q)
  | .peek k f q => .peek (Sum.inr (Sum.inr k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (liftH q)
  | .pop k f q => .pop (Sum.inr (Sum.inr k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (liftH q)
  | .load a q => .load (fun v => (v.1, a v.2.1, v.2.2)) (liftH q)
  | .branch f q₁ q₂ => .branch (fun v => f v.2.1) (liftH q₁) (liftH q₂)
  | .goto f => .goto (fun v => Sum.inl (Sum.inr (f v.2.1)))
  | .halt => .halt

/-- A configuration of the first machine, seen inside the composite machine. -/
def liftCfgF (sh : Mh.σ) (o : Option Bool) (a b c : List Bool) (Sh : ∀ k, List (Mh.Γ k))
    (cf : TM2.Cfg Mf.Γ Mf.Λ Mf.σ) : TM2.Cfg (G Mf Mh) (Lab Mf Mh) (Var Mf Mh) :=
  ⟨some (cf.l.elim (Sum.inr Ph.unload) fun l => Sum.inl (Sum.inl l)), (cf.var, sh, o),
    emb Mf Mh a b c cf.stk Sh⟩

/-- A configuration of the second machine, seen inside the composite machine. -/
def liftCfgH (sf : Mf.σ) (o : Option Bool) (a b c : List Bool) (Sf : ∀ k, List (Mf.Γ k))
    (ch : TM2.Cfg Mh.Γ Mh.Λ Mh.σ) : TM2.Cfg (G Mf Mh) (Lab Mf Mh) (Var Mf Mh) :=
  ⟨ch.l.map fun l => Sum.inl (Sum.inr l), (sf, ch.var, o), emb Mf Mh a b c Sf ch.stk⟩

theorem stepAux_liftF [DecidableEq (KK Mf Mh)] [DecidableEq Mf.K] (sh : Mh.σ) (o : Option Bool)
    (a b c : List Bool) (Sh : ∀ k, List (Mh.Γ k)) (q : TM2.Stmt Mf.Γ Mf.Λ Mf.σ) :
    ∀ (v : Mf.σ) (S : ∀ k, List (Mf.Γ k)),
    TM2.stepAux (liftF Mf Mh q) (v, sh, o) (emb Mf Mh a b c S Sh) =
      liftCfgF Mf Mh sh o a b c Sh (TM2.stepAux q v S) := by
  induction q with
  | push k f q ih =>
    intro v S
    simp only [liftF, TM2.stepAux]
    rw [show emb Mf Mh a b c S Sh (Sum.inr (Sum.inl k)) = S k from rfl, upd_f]
    exact ih _ _
  | peek k f q ih =>
    intro v S
    simp only [liftF, TM2.stepAux]
    exact ih _ _
  | pop k f q ih =>
    intro v S
    simp only [liftF, TM2.stepAux]
    rw [show emb Mf Mh a b c S Sh (Sum.inr (Sum.inl k)) = S k from rfl, upd_f]
    exact ih _ _
  | load f q ih =>
    intro v S
    simp only [liftF, TM2.stepAux]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S
    simp only [liftF, TM2.stepAux]
    cases f v
    · exact ih₂ _ _
    · exact ih₁ _ _
  | goto f =>
    intro v S
    rfl
  | halt =>
    intro v S
    rfl

theorem stepAux_liftH [DecidableEq (KK Mf Mh)] [DecidableEq Mh.K] (sf : Mf.σ) (o : Option Bool)
    (a b c : List Bool) (Sf : ∀ k, List (Mf.Γ k)) (q : TM2.Stmt Mh.Γ Mh.Λ Mh.σ) :
    ∀ (v : Mh.σ) (S : ∀ k, List (Mh.Γ k)),
    TM2.stepAux (liftH Mf Mh q) (sf, v, o) (emb Mf Mh a b c Sf S) =
      liftCfgH Mf Mh sf o a b c Sf (TM2.stepAux q v S) := by
  induction q with
  | push k f q ih =>
    intro v S
    simp only [liftH, TM2.stepAux]
    rw [show emb Mf Mh a b c Sf S (Sum.inr (Sum.inr k)) = S k from rfl, upd_h]
    exact ih _ _
  | peek k f q ih =>
    intro v S
    simp only [liftH, TM2.stepAux]
    exact ih _ _
  | pop k f q ih =>
    intro v S
    simp only [liftH, TM2.stepAux]
    rw [show emb Mf Mh a b c Sf S (Sum.inr (Sum.inr k)) = S k from rfl, upd_h]
    exact ih _ _
  | load f q ih =>
    intro v S
    simp only [liftH, TM2.stepAux]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S
    simp only [liftH, TM2.stepAux]
    cases f v
    · exact ih₂ _ _
    · exact ih₁ _ _
  | goto f =>
    intro v S
    rfl
  | halt =>
    intro v S
    rfl

end

section
variable (Mf Mh : FinTM2) (ef : Mf.Γ Mf.k₀ ≃ Bool) (of : Mf.Γ Mf.k₁ ≃ Bool)
  (eh : Mh.Γ Mh.k₀ ≃ Bool)

/-- The program of the composite machine. -/
def prog : Lab Mf Mh → TM2.Stmt (G Mf Mh) (Lab Mf Mh) (Var Mf Mh)
  | Sum.inl (Sum.inl l) => liftF Mf Mh (Mf.m l)
  | Sum.inl (Sum.inr l) => liftH Mf Mh (Mh.m l)
  | Sum.inr Ph.copy =>
    .pop (Sum.inl Aux.main) (fun v o => (v.1, v.2.1, o)) <|
      .branch (fun v => v.2.2.isSome)
        (.push (Sum.inl Aux.tmp) (fun v => v.2.2.getD false) <|
          .push (Sum.inl Aux.tmp2) (fun v => v.2.2.getD false) (.goto fun _ => Sum.inr Ph.copy))
        (.goto fun _ => Sum.inr Ph.feed)
  | Sum.inr Ph.feed =>
    .pop (Sum.inl Aux.tmp) (fun v o => (v.1, v.2.1, o)) <|
      .branch (fun v => v.2.2.isSome)
        (.push (Sum.inr (Sum.inl Mf.k₀)) (fun v => ef.symm (v.2.2.getD false))
          (.goto fun _ => Sum.inr Ph.feed))
        (.goto fun _ => Sum.inl (Sum.inl Mf.main))
  | Sum.inr Ph.unload =>
    .pop (Sum.inr (Sum.inl Mf.k₁)) (fun v o => (v.1, v.2.1, o.map of)) <|
      .branch (fun v => v.2.2.isSome)
        (.push (Sum.inl Aux.tmp) (fun v => v.2.2.getD false) (.goto fun _ => Sum.inr Ph.unload))
        (.goto fun _ => Sum.inr Ph.load)
  | Sum.inr Ph.load =>
    .pop (Sum.inl Aux.tmp) (fun v o => (v.1, v.2.1, o)) <|
      .branch (fun v => v.2.2.isSome)
        (.push (Sum.inr (Sum.inr Mh.k₀)) (fun v => eh.symm (v.2.2.getD false))
          (.goto fun _ => Sum.inr Ph.load))
        (.push (Sum.inr (Sum.inr Mh.k₀)) (fun _ => eh.symm false)
          (.goto fun _ => Sum.inr Ph.delim))
  | Sum.inr Ph.delim =>
    .pop (Sum.inl Aux.tmp2) (fun v o => (v.1, v.2.1, o)) <|
      .branch (fun v => v.2.2.isSome)
        (.push (Sum.inr (Sum.inr Mh.k₀)) (fun v => eh.symm (v.2.2.getD false)) <|
          .push (Sum.inr (Sum.inr Mh.k₀)) (fun _ => eh.symm true)
            (.goto fun _ => Sum.inr Ph.delim))
        (.goto fun _ => Sum.inl (Sum.inr Mh.main))

/-- The composite machine. Input on `main`, output on the output stack of the second machine. -/
def N : FinTM2 :=
  letI := Mf.kFin
  letI := Mh.kFin
  letI := Mf.ΛFin
  letI := Mh.ΛFin
  letI := Mf.σFin
  letI := Mh.σFin
  { K := KK Mf Mh
    k₀ := Sum.inl Aux.main
    k₁ := Sum.inr (Sum.inr Mh.k₁)
    Γ := G Mf Mh
    Λ := Lab Mf Mh
    main := Sum.inr Ph.copy
    σ := Var Mf Mh
    initialState := (Mf.initialState, Mh.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := prog Mf Mh ef of eh }

variable [DecidableEq (KK Mf Mh)]

theorem copy_cons (sf : Mf.σ) (sh : Mh.σ) (o : Option Bool) (x : Bool) (l t t2 : List Bool)
    (Sf : ∀ k, List (Mf.Γ k)) (Sh : ∀ k, List (Mh.Γ k)) :
    TM2.step (prog Mf Mh ef of eh)
      ⟨some (Sum.inr Ph.copy), (sf, sh, o), emb Mf Mh (x :: l) t t2 Sf Sh⟩ =
      some ⟨some (Sum.inr Ph.copy), (sf, sh, some x), emb Mf Mh l (x :: t) (x :: t2) Sf Sh⟩ := by
  simp [prog, upd_main, upd_tmp, upd_tmp2]

theorem copy_nil (sf : Mf.σ) (sh : Mh.σ) (o : Option Bool) (t t2 : List Bool)
    (Sf : ∀ k, List (Mf.Γ k)) (Sh : ∀ k, List (Mh.Γ k)) :
    TM2.step (prog Mf Mh ef of eh)
      ⟨some (Sum.inr Ph.copy), (sf, sh, o), emb Mf Mh [] t t2 Sf Sh⟩ =
      some ⟨some (Sum.inr Ph.feed), (sf, sh, none), emb Mf Mh [] t t2 Sf Sh⟩ := by
  simp [prog, upd_main]

theorem feed_cons [DecidableEq Mf.K] (sf : Mf.σ) (sh : Mh.σ) (o : Option Bool) (y : Bool)
    (m t t2 : List Bool) (Sf : ∀ k, List (Mf.Γ k)) (Sh : ∀ k, List (Mh.Γ k)) :
    TM2.step (prog Mf Mh ef of eh)
      ⟨some (Sum.inr Ph.feed), (sf, sh, o), emb Mf Mh m (y :: t) t2 Sf Sh⟩ =
      some ⟨some (Sum.inr Ph.feed), (sf, sh, some y),
        emb Mf Mh m t t2 (Function.update Sf Mf.k₀ (ef.symm y :: Sf Mf.k₀)) Sh⟩ := by
  simp [prog, upd_tmp, upd_f]

theorem feed_nil (sf : Mf.σ) (sh : Mh.σ) (o : Option Bool) (m t2 : List Bool)
    (Sf : ∀ k, List (Mf.Γ k)) (Sh : ∀ k, List (Mh.Γ k)) :
    TM2.step (prog Mf Mh ef of eh)
      ⟨some (Sum.inr Ph.feed), (sf, sh, o), emb Mf Mh m [] t2 Sf Sh⟩ =
      some ⟨some (Sum.inl (Sum.inl Mf.main)), (sf, sh, none), emb Mf Mh m [] t2 Sf Sh⟩ := by
  simp [prog, upd_tmp]

theorem unload_cons [DecidableEq Mf.K] (sf : Mf.σ) (sh : Mh.σ) (o : Option Bool)
    (y : Mf.Γ Mf.k₁) (L : List (Mf.Γ Mf.k₁)) (m t t2 : List Bool) (Sf : ∀ k, List (Mf.Γ k))
    (Sh : ∀ k, List (Mh.Γ k)) (hS : Sf Mf.k₁ = y :: L) :
    TM2.step (prog Mf Mh ef of eh)
      ⟨some (Sum.inr Ph.unload), (sf, sh, o), emb Mf Mh m t t2 Sf Sh⟩ =
      some ⟨some (Sum.inr Ph.unload), (sf, sh, some (of y)),
        emb Mf Mh m (of y :: t) t2 (Function.update Sf Mf.k₁ L) Sh⟩ := by
  simp [prog, hS, upd_tmp, upd_f]

theorem unload_nil [DecidableEq Mf.K] (sf : Mf.σ) (sh : Mh.σ) (o : Option Bool)
    (m t t2 : List Bool) (Sf : ∀ k, List (Mf.Γ k))
    (Sh : ∀ k, List (Mh.Γ k)) (hS : Sf Mf.k₁ = []) :
    TM2.step (prog Mf Mh ef of eh)
      ⟨some (Sum.inr Ph.unload), (sf, sh, o), emb Mf Mh m t t2 Sf Sh⟩ =
      some ⟨some (Sum.inr Ph.load), (sf, sh, none),
        emb Mf Mh m t t2 (Function.update Sf Mf.k₁ []) Sh⟩ := by
  simp [prog, hS, upd_f]

theorem load_cons [DecidableEq Mh.K] (sf : Mf.σ) (sh : Mh.σ) (o : Option Bool) (y : Bool)
    (m t t2 : List Bool) (Sf : ∀ k, List (Mf.Γ k)) (Sh : ∀ k, List (Mh.Γ k)) :
    TM2.step (prog Mf Mh ef of eh)
      ⟨some (Sum.inr Ph.load), (sf, sh, o), emb Mf Mh m (y :: t) t2 Sf Sh⟩ =
      some ⟨some (Sum.inr Ph.load), (sf, sh, some y),
        emb Mf Mh m t t2 Sf (Function.update Sh Mh.k₀ (eh.symm y :: Sh Mh.k₀))⟩ := by
  simp [prog, upd_tmp, upd_h]

theorem load_nil [DecidableEq Mh.K] (sf : Mf.σ) (sh : Mh.σ) (o : Option Bool)
    (m t2 : List Bool) (Sf : ∀ k, List (Mf.Γ k)) (Sh : ∀ k, List (Mh.Γ k)) :
    TM2.step (prog Mf Mh ef of eh)
      ⟨some (Sum.inr Ph.load), (sf, sh, o), emb Mf Mh m [] t2 Sf Sh⟩ =
      some ⟨some (Sum.inr Ph.delim), (sf, sh, none),
        emb Mf Mh m [] t2 Sf (Function.update Sh Mh.k₀ (eh.symm false :: Sh Mh.k₀))⟩ := by
  simp [prog, upd_tmp, upd_h]

theorem delim_cons [DecidableEq Mh.K] (sf : Mf.σ) (sh : Mh.σ) (o : Option Bool) (y : Bool)
    (m t t2 : List Bool) (Sf : ∀ k, List (Mf.Γ k)) (Sh : ∀ k, List (Mh.Γ k)) :
    TM2.step (prog Mf Mh ef of eh)
      ⟨some (Sum.inr Ph.delim), (sf, sh, o), emb Mf Mh m t (y :: t2) Sf Sh⟩ =
      some ⟨some (Sum.inr Ph.delim), (sf, sh, some y),
        emb Mf Mh m t t2 Sf
          (Function.update Sh Mh.k₀ (eh.symm true :: eh.symm y :: Sh Mh.k₀))⟩ := by
  simp [prog, upd_tmp2, upd_h]

theorem delim_nil (sf : Mf.σ) (sh : Mh.σ) (o : Option Bool)
    (m t : List Bool) (Sf : ∀ k, List (Mf.Γ k)) (Sh : ∀ k, List (Mh.Γ k)) :
    TM2.step (prog Mf Mh ef of eh)
      ⟨some (Sum.inr Ph.delim), (sf, sh, o), emb Mf Mh m t [] Sf Sh⟩ =
      some ⟨some (Sum.inl (Sum.inr Mh.main)), (sf, sh, none), emb Mf Mh m t [] Sf Sh⟩ := by
  simp [prog, upd_tmp2]

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

theorem iter_trans {f : α → Option α} {x y z : Option α} {a b : ℕ}
    (h1 : (flip bind f)^[a] x = y) (h2 : (flip bind f)^[b] y = z) :
    (flip bind f)^[b + a] x = z := by
  rw [Function.iterate_add_apply, h1, h2]

end

section
variable (Mf Mh : FinTM2) (ef : Mf.Γ Mf.k₀ ≃ Bool) (of : Mf.Γ Mf.k₁ ≃ Bool)
  (eh : Mh.Γ Mh.k₀ ≃ Bool)
variable [DecidableEq (KK Mf Mh)]

theorem copy_run (sf : Mf.σ) (sh : Mh.σ) (Sf : ∀ k, List (Mf.Γ k)) (Sh : ∀ k, List (Mh.Γ k)) :
    ∀ (l t t2 : List Bool) (o : Option Bool),
    (flip bind (TM2.step (prog Mf Mh ef of eh)))^[l.length + 1]
      (some ⟨some (Sum.inr Ph.copy), (sf, sh, o), emb Mf Mh l t t2 Sf Sh⟩) =
    some ⟨some (Sum.inr Ph.feed), (sf, sh, none),
      emb Mf Mh [] (l.reverse ++ t) (l.reverse ++ t2) Sf Sh⟩
  | [], t, t2, o => by
    rw [List.length_nil, iter_succ_of (copy_nil Mf Mh ef of eh sf sh o t t2 Sf Sh)]
    rfl
  | x :: l, t, t2, o => by
    rw [List.length_cons, iter_succ_of (copy_cons Mf Mh ef of eh sf sh o x l t t2 Sf Sh),
      copy_run sf sh Sf Sh l (x :: t) (x :: t2) (some x)]
    simp

theorem feed_run [DecidableEq Mf.K] (sf : Mf.σ) (sh : Mh.σ) (Sh : ∀ k, List (Mh.Γ k)) :
    ∀ (t m t2 : List Bool) (Sf : ∀ k, List (Mf.Γ k)) (o : Option Bool),
    (flip bind (TM2.step (prog Mf Mh ef of eh)))^[t.length + 1]
      (some ⟨some (Sum.inr Ph.feed), (sf, sh, o), emb Mf Mh m t t2 Sf Sh⟩) =
    some ⟨some (Sum.inl (Sum.inl Mf.main)), (sf, sh, none),
      emb Mf Mh m [] t2 (Function.update Sf Mf.k₀ (t.reverse.map ef.symm ++ Sf Mf.k₀)) Sh⟩
  | [], m, t2, Sf, o => by
    rw [List.length_nil, iter_succ_of (feed_nil Mf Mh ef of eh sf sh o m t2 Sf Sh)]
    simp
  | y :: t, m, t2, Sf, o => by
    rw [List.length_cons, iter_succ_of (feed_cons Mf Mh ef of eh sf sh o y m t t2 Sf Sh),
      feed_run sf sh Sh t m t2 _ (some y)]
    simp [Function.update_idem]

theorem unload_run [DecidableEq Mf.K] (sf : Mf.σ) (sh : Mh.σ) (Sh : ∀ k, List (Mh.Γ k)) :
    ∀ (L : List (Mf.Γ Mf.k₁)) (m t t2 : List Bool) (Sf : ∀ k, List (Mf.Γ k)) (o : Option Bool),
    Sf Mf.k₁ = L →
    (flip bind (TM2.step (prog Mf Mh ef of eh)))^[L.length + 1]
      (some ⟨some (Sum.inr Ph.unload), (sf, sh, o), emb Mf Mh m t t2 Sf Sh⟩) =
    some ⟨some (Sum.inr Ph.load), (sf, sh, none),
      emb Mf Mh m (L.reverse.map of ++ t) t2 (Function.update Sf Mf.k₁ []) Sh⟩
  | [], m, t, t2, Sf, o, hS => by
    rw [List.length_nil, iter_succ_of (unload_nil Mf Mh ef of eh sf sh o m t t2 Sf Sh hS)]
    simp
  | y :: L, m, t, t2, Sf, o, hS => by
    rw [List.length_cons, iter_succ_of (unload_cons Mf Mh ef of eh sf sh o y L m t t2 Sf Sh hS),
      unload_run sf sh Sh L m (of y :: t) t2 _ (some (of y)) (by simp)]
    simp [Function.update_idem]

theorem load_run [DecidableEq Mh.K] (sf : Mf.σ) (sh : Mh.σ) (Sf : ∀ k, List (Mf.Γ k)) :
    ∀ (t m t2 : List Bool) (Sh : ∀ k, List (Mh.Γ k)) (o : Option Bool),
    (flip bind (TM2.step (prog Mf Mh ef of eh)))^[t.length + 1]
      (some ⟨some (Sum.inr Ph.load), (sf, sh, o), emb Mf Mh m t t2 Sf Sh⟩) =
    some ⟨some (Sum.inr Ph.delim), (sf, sh, none),
      emb Mf Mh m [] t2 Sf
        (Function.update Sh Mh.k₀ (eh.symm false :: (t.reverse.map eh.symm ++ Sh Mh.k₀)))⟩
  | [], m, t2, Sh, o => by
    rw [List.length_nil, iter_succ_of (load_nil Mf Mh ef of eh sf sh o m t2 Sf Sh)]
    simp
  | y :: t, m, t2, Sh, o => by
    rw [List.length_cons, iter_succ_of (load_cons Mf Mh ef of eh sf sh o y m t t2 Sf Sh),
      load_run sf sh Sf t m t2 _ (some y)]
    simp [Function.update_idem]

theorem delim_run [DecidableEq Mh.K] (sf : Mf.σ) (sh : Mh.σ) (Sf : ∀ k, List (Mf.Γ k)) :
    ∀ (t2 m t : List Bool) (Sh : ∀ k, List (Mh.Γ k)) (o : Option Bool),
    (flip bind (TM2.step (prog Mf Mh ef of eh)))^[t2.length + 1]
      (some ⟨some (Sum.inr Ph.delim), (sf, sh, o), emb Mf Mh m t t2 Sf Sh⟩) =
    some ⟨some (Sum.inl (Sum.inr Mh.main)), (sf, sh, none),
      emb Mf Mh m t [] Sf
        (Function.update Sh Mh.k₀
          (t2.reverse.flatMap (fun b => [eh.symm true, eh.symm b]) ++ Sh Mh.k₀))⟩
  | [], m, t, Sh, o => by
    rw [List.length_nil, iter_succ_of (delim_nil Mf Mh ef of eh sf sh o m t Sf Sh)]
    simp
  | y :: t2, m, t, Sh, o => by
    rw [List.length_cons, iter_succ_of (delim_cons Mf Mh ef of eh sf sh o y m t t2 Sf Sh),
      delim_run sf sh Sf t2 m t _ (some y)]
    simp [Function.update_idem]

theorem lift_stepF [DecidableEq Mf.K] (sh : Mh.σ) (o : Option Bool) (a b c : List Bool)
    (Sh : ∀ k, List (Mh.Γ k)) {cf df : TM2.Cfg Mf.Γ Mf.Λ Mf.σ} (h : TM2.step Mf.m cf = some df) :
    TM2.step (prog Mf Mh ef of eh) (liftCfgF Mf Mh sh o a b c Sh cf) =
      some (liftCfgF Mf Mh sh o a b c Sh df) := by
  rcases cf with ⟨_ | l, v, S⟩
  · simp at h
  · simp only [TM2.step] at h
    cases h
    show some (TM2.stepAux (liftF Mf Mh (Mf.m l)) (v, sh, o) (emb Mf Mh a b c S Sh)) = _
    rw [stepAux_liftF]

theorem lift_runF [DecidableEq Mf.K] (sh : Mh.σ) (o : Option Bool) (a b c : List Bool)
    (Sh : ∀ k, List (Mh.Γ k)) :
    ∀ (n : ℕ) (cf df : TM2.Cfg Mf.Γ Mf.Λ Mf.σ),
    (flip bind (TM2.step Mf.m))^[n] (some cf) = some df →
    (flip bind (TM2.step (prog Mf Mh ef of eh)))^[n] (some (liftCfgF Mf Mh sh o a b c Sh cf)) =
      some (liftCfgF Mf Mh sh o a b c Sh df)
  | 0, cf, df, h => by
    simp only [Function.iterate_zero, id, Option.some.injEq] at h ⊢
    rw [h]
  | n + 1, cf, df, h => by
    cases hc : TM2.step Mf.m cf with
    | none =>
      rw [Function.iterate_succ_apply] at h
      change (flip bind (TM2.step Mf.m))^[n] (TM2.step Mf.m cf) = some df at h
      rw [hc, iter_none] at h
      cases h
    | some cf' =>
      rw [iter_succ_of hc] at h
      rw [iter_succ_of (lift_stepF Mf Mh ef of eh sh o a b c Sh hc)]
      exact lift_runF sh o a b c Sh n cf' df h

theorem lift_stepH [DecidableEq Mh.K] (sf : Mf.σ) (o : Option Bool) (a b c : List Bool)
    (Sf : ∀ k, List (Mf.Γ k)) {ch dh : TM2.Cfg Mh.Γ Mh.Λ Mh.σ} (h : TM2.step Mh.m ch = some dh) :
    TM2.step (prog Mf Mh ef of eh) (liftCfgH Mf Mh sf o a b c Sf ch) =
      some (liftCfgH Mf Mh sf o a b c Sf dh) := by
  rcases ch with ⟨_ | l, v, S⟩
  · simp at h
  · simp only [TM2.step] at h
    cases h
    show some (TM2.stepAux (liftH Mf Mh (Mh.m l)) (sf, v, o) (emb Mf Mh a b c Sf S)) = _
    rw [stepAux_liftH]

theorem lift_runH [DecidableEq Mh.K] (sf : Mf.σ) (o : Option Bool) (a b c : List Bool)
    (Sf : ∀ k, List (Mf.Γ k)) :
    ∀ (n : ℕ) (ch dh : TM2.Cfg Mh.Γ Mh.Λ Mh.σ),
    (flip bind (TM2.step Mh.m))^[n] (some ch) = some dh →
    (flip bind (TM2.step (prog Mf Mh ef of eh)))^[n] (some (liftCfgH Mf Mh sf o a b c Sf ch)) =
      some (liftCfgH Mf Mh sf o a b c Sf dh)
  | 0, ch, dh, h => by
    simp only [Function.iterate_zero, id, Option.some.injEq] at h ⊢
    rw [h]
  | n + 1, ch, dh, h => by
    cases hc : TM2.step Mh.m ch with
    | none =>
      rw [Function.iterate_succ_apply] at h
      change (flip bind (TM2.step Mh.m))^[n] (TM2.step Mh.m ch) = some dh at h
      rw [hc, iter_none] at h
      cases h
    | some ch' =>
      rw [iter_succ_of hc] at h
      rw [iter_succ_of (lift_stepH Mf Mh ef of eh sf o a b c Sf hc)]
      exact lift_runH sf o a b c Sf n ch' dh h

end

section
variable (tm : FinTM2)

theorem halt_k1 (X : List (tm.Γ tm.k₁)) : (haltList tm X).stk tm.k₁ = X := by
  simp [haltList]

theorem halt_ne (X : List (tm.Γ tm.k₁)) (k : tm.K) (h : k ≠ tm.k₁) :
    (haltList tm X).stk k = [] := by
  simp [haltList, h]

theorem halt_upd [DecidableEq tm.K] (X : List (tm.Γ tm.k₁)) :
    Function.update (haltList tm X).stk tm.k₁ [] = fun k => ([] : List (tm.Γ k)) := by
  funext k
  by_cases h : k = tm.k₁
  · subst h; simp
  · rw [Function.update_of_ne h]; simp [haltList, h]

theorem init_upd [DecidableEq tm.K] (X : List (tm.Γ tm.k₀)) :
    Function.update (fun k => ([] : List (tm.Γ k))) tm.k₀ X = (initList tm X).stk := by
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp [initList]
  · rw [Function.update_of_ne h]; simp [initList, h]

theorem init_len (X : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((initList tm X).stk k).length ≤ X.length := by
  by_cases h : k = tm.k₀
  · subst h; simp [initList]
  · simp [initList, h]

end

theorem delim_map {Γ : Type} (g : Bool → Γ) (O : List Bool) : ∀ I : List Bool,
    I.flatMap (fun b => [g true, g b]) ++ g false :: O.map g =
      (BitstringEncoding.delimit I ++ O).map g
  | [] => rfl
  | b :: I => by
    show g true :: g b :: (I.flatMap (fun b => [g true, g b]) ++ g false :: O.map g) =
      g true :: g b :: (BitstringEncoding.delimit I ++ O).map g
    rw [delim_map g O I]

theorem len_delimit : ∀ l : List Bool,
    (BitstringEncoding.delimit l).length = 2 * l.length + 1
  | [] => rfl
  | b :: l => by
    rw [show BitstringEncoding.delimit (b :: l) = true :: b :: BitstringEncoding.delimit l from rfl,
      List.length_cons, List.length_cons, len_delimit l, List.length_cons]
    omega

section
variable (Mf Mh : FinTM2) (ef : Mf.Γ Mf.k₀ ≃ Bool) (of : Mf.Γ Mf.k₁ ≃ Bool)
  (eh : Mh.Γ Mh.k₀ ≃ Bool)

theorem init_N (I : List Bool) :
    initList (N Mf Mh ef of eh) I =
      TM2.Cfg.mk (some (Sum.inr Ph.copy)) (Mf.initialState, Mh.initialState, none)
        (emb Mf Mh I [] [] (fun k => ([] : List (Mf.Γ k))) (fun k => ([] : List (Mh.Γ k)))) := by
  unfold initList
  congr 1
  funext k
  match k with
  | Sum.inl Aux.main => rfl
  | Sum.inl Aux.tmp => rfl
  | Sum.inl Aux.tmp2 => rfl
  | Sum.inr (Sum.inl k) => rfl
  | Sum.inr (Sum.inr k) => rfl

theorem halt_N (R : List (Mh.Γ Mh.k₁)) :
    haltList (N Mf Mh ef of eh) R =
      TM2.Cfg.mk none (Mf.initialState, Mh.initialState, none)
        (emb Mf Mh [] [] [] (fun k => ([] : List (Mf.Γ k))) (haltList Mh R).stk) := by
  have hstk : (haltList (N Mf Mh ef of eh) R).stk =
      emb Mf Mh [] [] [] (fun k => ([] : List (Mf.Γ k))) (haltList Mh R).stk := by
    funext k
    match k with
    | Sum.inl Aux.main => exact halt_ne (N Mf Mh ef of eh) R _ (by intro h; cases h)
    | Sum.inl Aux.tmp => exact halt_ne (N Mf Mh ef of eh) R _ (by intro h; cases h)
    | Sum.inl Aux.tmp2 => exact halt_ne (N Mf Mh ef of eh) R _ (by intro h; cases h)
    | Sum.inr (Sum.inl k) => exact halt_ne (N Mf Mh ef of eh) R _ (by intro h; cases h)
    | Sum.inr (Sum.inr k) =>
      by_cases hk : k = Mh.k₁
      · subst hk
        rw [emb_h, halt_k1]
        exact halt_k1 (N Mf Mh ef of eh) R
      · rw [emb_h, halt_ne Mh R k hk]
        exact halt_ne (N Mf Mh ef of eh) R _ (fun h => hk (Sum.inr.inj (Sum.inr.inj h)))
  rw [← hstk]
  rfl

variable [DecidableEq (KK Mf Mh)]

theorem N_run [DecidableEq Mf.K] [DecidableEq Mh.K] (I O : List Bool) (R : List (Mh.Γ Mh.k₁))
    (tf th : ℕ)
    (hf : (flip bind (TM2.step Mf.m))^[tf] (some (initList Mf (I.map ef.symm))) =
      some (haltList Mf (O.map of.symm)))
    (hh : (flip bind (TM2.step Mh.m))^[th]
        (some (initList Mh ((BitstringEncoding.delimit I ++ O).map eh.symm))) =
      some (haltList Mh R)) :
    (flip bind (TM2.step (prog Mf Mh ef of eh)))^[th + ((I.length + 1) + ((O.length + 1) +
        ((O.length + 1) + (tf + ((I.length + 1) + (I.length + 1))))))]
      (some ⟨some (Sum.inr Ph.copy), (Mf.initialState, Mh.initialState, none),
        emb Mf Mh I [] [] (fun k => ([] : List (Mf.Γ k))) (fun k => ([] : List (Mh.Γ k)))⟩) =
    some ⟨none, (Mf.initialState, Mh.initialState, none),
      emb Mf Mh [] [] [] (fun k => ([] : List (Mf.Γ k))) (haltList Mh R).stk⟩ := by
  have h1 := copy_run Mf Mh ef of eh Mf.initialState Mh.initialState
    (fun k => ([] : List (Mf.Γ k))) (fun k => ([] : List (Mh.Γ k))) I [] [] none
  simp only [List.append_nil] at h1
  have h2 := feed_run Mf Mh ef of eh Mf.initialState Mh.initialState
    (fun k => ([] : List (Mh.Γ k))) I.reverse [] I.reverse (fun k => ([] : List (Mf.Γ k))) none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h2
  rw [init_upd] at h2
  have h3 := lift_runF Mf Mh ef of eh Mh.initialState none [] [] I.reverse
    (fun k => ([] : List (Mh.Γ k))) tf _ _ hf
  have h4 := unload_run Mf Mh ef of eh Mf.initialState Mh.initialState
    (fun k => ([] : List (Mh.Γ k))) (O.map of.symm) [] [] I.reverse
    (haltList Mf (O.map of.symm)).stk none (halt_k1 Mf _)
  rw [halt_upd] at h4
  simp only [List.length_map, List.append_nil, List.map_reverse, List.map_map,
    Equiv.self_comp_symm, List.map_id] at h4
  have h5 := load_run Mf Mh ef of eh Mf.initialState Mh.initialState
    (fun k => ([] : List (Mf.Γ k))) O.reverse [] I.reverse (fun k => ([] : List (Mh.Γ k))) none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h5
  have h6 := delim_run Mf Mh ef of eh Mf.initialState Mh.initialState
    (fun k => ([] : List (Mf.Γ k))) I.reverse [] []
    (Function.update (fun k => ([] : List (Mh.Γ k))) Mh.k₀ (eh.symm false :: O.map eh.symm)) none
  simp only [List.length_reverse, List.reverse_reverse, Function.update_idem,
    Function.update_self] at h6
  rw [delim_map, init_upd Mh ((BitstringEncoding.delimit I ++ O).map eh.symm)] at h6
  have h7 := lift_runH Mf Mh ef of eh Mf.initialState none [] [] []
    (fun k => ([] : List (Mf.Γ k))) th _ _ hh
  exact iter_trans (iter_trans (iter_trans (iter_trans (iter_trans (iter_trans h1 h2) h3) h4)
    h5) h6) h7

end

section
variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- Number of `push` instructions in a statement (both branches counted). -/
def pushes : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => pushes q₁ + pushes q₂
  | .goto _ => 0
  | .halt => 0

theorem len_stepAux [DecidableEq K] (k : K) (q : TM2.Stmt Γ Λ σ) :
    ∀ (v : σ) (S : ∀ k, List (Γ k)),
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushes q := by
  induction q with
  | push k' f q ih =>
    intro v S
    have h1 := ih v (Function.update S k' (f v :: S k'))
    have h2 : (Function.update S k' (f v :: S k') k).length ≤ (S k).length + 1 := by
      by_cases hk : k = k'
      · subst hk; simp
      · rw [Function.update_of_ne hk]; omega
    simp only [TM2.stepAux, pushes]
    omega
  | peek k' f q ih =>
    intro v S
    simp only [TM2.stepAux, pushes]
    exact ih _ _
  | pop k' f q ih =>
    intro v S
    have h1 := ih (f v (S k').head?) (Function.update S k' (S k').tail)
    have h2 : (Function.update S k' (S k').tail k).length ≤ (S k).length := by
      by_cases hk : k = k'
      · subst hk; simp
      · rw [Function.update_of_ne hk]
    simp only [TM2.stepAux, pushes]
    omega
  | load a q ih =>
    intro v S
    simp only [TM2.stepAux, pushes]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S
    have h1 := ih₁ v S
    have h2 := ih₂ v S
    simp only [TM2.stepAux, pushes]
    cases f v
    · simp only [cond_false]; omega
    · simp only [cond_true]; omega
  | goto f =>
    intro v S
    simp [TM2.stepAux, pushes]
  | halt =>
    intro v S
    simp [TM2.stepAux, pushes]

theorem len_step [DecidableEq K] (M : Λ → TM2.Stmt Γ Λ σ) (B : ℕ) (hB : ∀ l, pushes (M l) ≤ B)
    (k : K) {c d : TM2.Cfg Γ Λ σ} (h : TM2.step M c = some d) :
    (d.stk k).length ≤ (c.stk k).length + B := by
  rcases c with ⟨_ | l, v, S⟩
  · simp at h
  · simp only [TM2.step, Option.some.injEq] at h
    subst h
    have h1 := len_stepAux k (M l) v S
    have h2 := hB l
    simp only at h1 ⊢
    omega

theorem len_run [DecidableEq K] (M : Λ → TM2.Stmt Γ Λ σ) (B : ℕ) (hB : ∀ l, pushes (M l) ≤ B)
    (k : K) : ∀ (n : ℕ) (c d : TM2.Cfg Γ Λ σ), (flip bind (TM2.step M))^[n] (some c) = some d →
    (d.stk k).length ≤ (c.stk k).length + B * n
  | 0, c, d, h => by
    simp only [Function.iterate_zero, id, Option.some.injEq] at h
    subst h
    simp
  | n + 1, c, d, h => by
    cases hc : TM2.step M c with
    | none =>
      rw [Function.iterate_succ_apply] at h
      change (flip bind (TM2.step M))^[n] (TM2.step M c) = some d at h
      rw [hc, iter_none] at h
      cases h
    | some c' =>
      rw [iter_succ_of hc] at h
      have h1 := len_run M B hB k n c' d h
      have h2 := len_step M B hB k hc
      rw [Nat.mul_succ]
      omega

end

theorem poly_mono (p : Polynomial ℕ) {a b : ℕ} (hab : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval_add, Polynomial.eval_add]; exact Nat.add_le_add hp hq
  | monomial n c =>
    rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab n)

theorem map_in (Mf Mh : FinTM2) (ef : Mf.Γ Mf.k₀ ≃ Bool) (of : Mf.Γ Mf.k₁ ≃ Bool)
    (eh : Mh.Γ Mh.k₀ ≃ Bool) (I : List Bool) :
    List.map (@Equiv.invFun ((N Mf Mh ef of eh).Γ (N Mf Mh ef of eh).k₀) Bool (Equiv.refl Bool)) I =
      I :=
  List.map_id I

/-- Polynomial time is closed under `x ↦ h (x, f x)`. -/
theorem comp_isPolyTime {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] (f : α → β) (h : α × β → γ) (hf : IsPolyTime f) (hh : IsPolyTime h) :
    IsPolyTime (fun x => h (x, f x)) := by
  obtain ⟨Tf⟩ := hf
  obtain ⟨Th⟩ := hh
  obtain ⟨B, hB⟩ : ∃ B, ∀ l, pushes (Tf.tm.m l) ≤ B := by
    let _ := Tf.tm.ΛFin
    exact ⟨∑ l, pushes (Tf.tm.m l), fun l =>
      Finset.single_le_sum (f := fun l => pushes (Tf.tm.m l)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ l)⟩
  refine ⟨{ tm := N Tf.tm Th.tm Tf.inputAlphabet Tf.outputAlphabet Th.inputAlphabet
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Th.outputAlphabet
            time := 3 * (Polynomial.X + 1) + 2 * (Polynomial.X + (B : Polynomial ℕ) * Tf.time + 1) +
              Tf.time + Th.time.comp (3 * Polynomial.X + 1 + (B : Polynomial ℕ) * Tf.time)
            outputsFun := fun x => ?_ }⟩
  obtain ⟨⟨tf, htf⟩, htfle⟩ := Tf.outputsFun x
  obtain ⟨⟨th, hth⟩, hthle⟩ := Th.outputsFun (x, f x)
  have hf' : (flip bind (TM2.step Tf.tm.m))^[tf]
      (some (initList Tf.tm
        (List.map Tf.inputAlphabet.symm ((BitstringEncoding.toEncoding (α := α)).encode x)))) =
      some (haltList Tf.tm
        (List.map Tf.outputAlphabet.symm ((BitstringEncoding.toEncoding (α := β)).encode (f x)))) :=
    htf
  have hJ : (BitstringEncoding.toEncoding (α := α × β)).encode (x, f x) =
      BitstringEncoding.delimit ((BitstringEncoding.toEncoding (α := α)).encode x) ++
        (BitstringEncoding.toEncoding (α := β)).encode (f x) := rfl
  have hh' : (flip bind (TM2.step Th.tm.m))^[th]
      (some (initList Th.tm (List.map Th.inputAlphabet.symm
        (BitstringEncoding.delimit ((BitstringEncoding.toEncoding (α := α)).encode x) ++
          (BitstringEncoding.toEncoding (α := β)).encode (f x))))) =
      some (haltList Th.tm (List.map Th.outputAlphabet.invFun
        ((BitstringEncoding.toEncoding (α := γ)).encode (h (x, f x))))) := hth
  have htfle' : tf ≤ Tf.time.eval ((BitstringEncoding.toEncoding (α := α)).encode x).length :=
    htfle
  have hthle' : th ≤ Th.time.eval (2 * ((BitstringEncoding.toEncoding (α := α)).encode x).length +
      1 + ((BitstringEncoding.toEncoding (α := β)).encode (f x)).length) := by
    have h0 : th ≤ Th.time.eval
        ((BitstringEncoding.toEncoding (α := α × β)).encode (x, f x)).length := hthle
    rw [hJ, List.length_append, len_delimit] at h0
    exact h0
  clear htfle hthle htf hth
  generalize (BitstringEncoding.toEncoding (α := α)).encode x = I at hf' hh' htfle' hthle' ⊢
  generalize (BitstringEncoding.toEncoding (α := β)).encode (f x) = O at hf' hh' hthle'
  refine ⟨⟨th + ((I.length + 1) + ((O.length + 1) + ((O.length + 1) + (tf + ((I.length + 1) +
    (I.length + 1)))))), ?_⟩, ?_⟩
  · rw [map_in]
    show (flip bind (TM2.step (prog Tf.tm Th.tm Tf.inputAlphabet Tf.outputAlphabet
      Th.inputAlphabet)))^[_] (some (initList (N Tf.tm Th.tm Tf.inputAlphabet Tf.outputAlphabet
        Th.inputAlphabet) I)) = some (haltList (N Tf.tm Th.tm Tf.inputAlphabet Tf.outputAlphabet
        Th.inputAlphabet) _)
    rw [init_N]
    exact (N_run Tf.tm Th.tm Tf.inputAlphabet Tf.outputAlphabet Th.inputAlphabet I O _ tf th hf'
      hh').trans
      (congrArg some (halt_N Tf.tm Th.tm Tf.inputAlphabet Tf.outputAlphabet Th.inputAlphabet _).symm)
  · have hO : O.length ≤ I.length + B * tf := by
      have h1 := len_run Tf.tm.m B hB Tf.tm.k₁ tf _ _ hf'
      rw [halt_k1, List.length_map] at h1
      have h2 := init_len Tf.tm (I.map Tf.inputAlphabet.symm) Tf.tm.k₁
      rw [List.length_map] at h2
      omega
    have hBt : B * tf ≤ B * Tf.time.eval I.length := Nat.mul_le_mul_left B htfle'
    have hmono := poly_mono Th.time
      (show 2 * I.length + 1 + O.length ≤ 3 * I.length + 1 + B * Tf.time.eval I.length by omega)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_one,
      Polynomial.eval_natCast, Polynomial.eval_comp, Polynomial.eval_ofNat, Nat.cast_id]
    omega

end OMA.Helpers

theorem OMA.solution : OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R1.H1 :=
  fun f h hf hh => OMA.Helpers.comp_isPolyTime f h hf hh
