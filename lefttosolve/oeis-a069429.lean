import OMAStatements.S_oeis_a069429
import Mathlib

namespace OMA.Helpers
open OMA.S_oeis_a069429

/-- `x` lies between columns `c` and `j`. -/
def Btw {n : ℕ} (c j x : Fin n) : Prop :=
  (c.val ≤ x.val ∧ x.val ≤ j.val) ∨ (j.val ≤ x.val ∧ x.val ≤ c.val)

/-- Path characterization. -/
def PP {n : ℕ} (A : Fin 3 × Fin n → Bool) (b : Bool) : Prop :=
  ∃ c c' : Fin n, A (0, c) = b ∧ A (2, c') = b ∧ ∀ x, Btw c c' x → A (1, x) = b

/-- Invariant along a path. -/
def Inv {n : ℕ} (A : Fin 3 × Fin n → Bool) (b : Bool) (u : Fin 3 × Fin n) : Prop :=
  PP A b ∨ u.1 = 0 ∨ (u.1 = 1 ∧ ∃ c, A (0, c) = b ∧ ∀ x, Btw c u.2 x → A (1, x) = b)

theorem inv_step {n : ℕ} {A : Fin 3 × Fin n → Bool} {b : Bool} {u v : Fin 3 × Fin n}
    (hadj : GridAdj u v) (hu : A u = b) (hv : A v = b) (h : Inv A b u) : Inv A b v := by
  obtain ⟨r, j⟩ := u
  obtain ⟨r', j'⟩ := v
  unfold GridAdj at hadj
  simp only at hadj
  rcases h with h | h | ⟨h1, c, hc, hrow⟩
  · exact Or.inl h
  · simp only at h
    subst h
    rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; exact Or.inr (Or.inl rfl)
    · subst h1
      have : r' = 1 := by
        rcases h2 with h2 | h2
        · exact Fin.ext (by simp at h2 ⊢; omega)
        · simp at h2
      subst this
      refine Or.inr (Or.inr ⟨rfl, j, hu, fun x hx => ?_⟩)
      have : x = j := Fin.ext (by simp only [Btw] at hx; omega)
      subst this; exact hv
  · simp only at h1 hrow
    subst h1
    rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1
      refine Or.inr (Or.inr ⟨rfl, c, hc, fun x hx => ?_⟩)
      by_cases hx' : x = j'
      · subst hx'; exact hv
      · apply hrow
        have : x.val ≠ j'.val := fun e => hx' (Fin.ext e)
        simp only [Btw] at hx hrow ⊢; omega
    · subst h1
      rcases h2 with h2 | h2
      · have : r' = 2 := Fin.ext (by simp at h2 ⊢; omega)
        subst this
        exact Or.inl ⟨c, j, hc, hv, hrow⟩
      · have : r' = 0 := Fin.ext (by simp at h2 ⊢; omega)
        exact Or.inr (Or.inl this)

theorem inv_chain {n : ℕ} (A : Fin 3 × Fin n → Bool) (b : Bool) :
    ∀ (L : List (Fin 3 × Fin n)) (a : Fin 3 × Fin n), (a :: L).IsChain GridAdj →
      (∀ u ∈ a :: L, A u = b) → Inv A b a → Inv A b ((a :: L).getLast (List.cons_ne_nil a L))
  | [], a, _, _, h => by simpa using h
  | (x :: L), a, hc, hb, h => by
    rw [List.getLast_cons (List.cons_ne_nil x L)]
    rw [List.isChain_cons_cons] at hc
    exact inv_chain A b L x hc.2 (fun u hu => hb u (List.mem_cons_of_mem a hu))
      (inv_step hc.1 (hb a (by simp)) (hb x (by simp)) h)

/-- Reachability of row 2. -/
def Reach {n : ℕ} (A : Fin 3 × Fin n → Bool) (b : Bool) (u : Fin 3 × Fin n) : Prop :=
  ∃ L : List (Fin 3 × Fin n), (u :: L).IsChain GridAdj ∧ (∀ v ∈ u :: L, A v = b) ∧
    ((u :: L).getLast (List.cons_ne_nil u L)).1 = 2

theorem reach_cons {n : ℕ} {A : Fin 3 × Fin n → Bool} {b : Bool} {u v : Fin 3 × Fin n}
    (hadj : GridAdj u v) (hu : A u = b) (h : Reach A b v) : Reach A b u := by
  obtain ⟨L, hc, hb, hl⟩ := h
  refine ⟨v :: L, List.isChain_cons_cons.2 ⟨hadj, hc⟩, ?_, ?_⟩
  · intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact hu
    · exact hb w hw
  · rw [List.getLast_cons (List.cons_ne_nil v L)]; exact hl

theorem reach_row1 {n : ℕ} {A : Fin 3 × Fin n → Bool} {b : Bool} (c' : Fin n)
    (hc' : A (2, c') = b) : ∀ (d : ℕ) (j : Fin n), (j.val + d = c'.val ∨ c'.val + d = j.val) →
      (∀ x, Btw j c' x → A (1, x) = b) → Reach A b (1, j) := by
  intro d
  induction d with
  | zero =>
    intro j hj hrow
    have : j = c' := Fin.ext (by omega)
    subst this
    refine reach_cons (v := (2, j)) ?_ (hrow j (by unfold Btw; omega)) ⟨[], by simp, ?_, rfl⟩
    · right; exact ⟨rfl, Or.inl rfl⟩
    · intro v hv; simp at hv; subst hv; exact hc'
  | succ d ih =>
    intro j hj hrow
    rcases hj with hj | hj
    · let j1 : Fin n := ⟨j.val + 1, by omega⟩
      have h1 := ih j1 (Or.inl (by simp [j1]; omega)) (fun x hx => hrow x (by
        unfold Btw at hx ⊢; simp [j1] at hx; omega))
      refine reach_cons ?_ (hrow j (by unfold Btw; omega)) h1
      left; exact ⟨rfl, Or.inl rfl⟩
    · let j1 : Fin n := ⟨j.val - 1, by omega⟩
      have h1 := ih j1 (Or.inr (by simp [j1]; omega)) (fun x hx => hrow x (by
        unfold Btw at hx ⊢; simp [j1] at hx; omega))
      refine reach_cons ?_ (hrow j (by unfold Btw; omega)) h1
      left; exact ⟨rfl, Or.inr (by simp [j1]; omega)⟩

theorem path_iff {n : ℕ} (A : Fin 3 × Fin n → Bool) (b : Bool) :
    HasMonoPath A b ↔ PP A b := by
  constructor
  · rintro ⟨L, h0, hfirst, hlast, hall, hchain⟩
    cases L with
    | nil => simp at h0
    | cons a t =>
      have hc : (a :: t).IsChain GridAdj := hchain
      have hi := inv_chain A b t a hc hall (Or.inr (Or.inl (by simpa using hfirst)))
      rw [List.getLast_eq_getElem] at hi
      rcases hi with hi | hi | ⟨hi, _⟩
      · exact hi
      · rw [hi] at hlast; exact absurd hlast (by decide)
      · rw [hi] at hlast; exact absurd hlast (by decide)
  · rintro ⟨c, c', hc, hc', hrow⟩
    have h1 : Reach A b (1, c) := by
      by_cases hle : c.val ≤ c'.val
      · exact reach_row1 c' hc' (c'.val - c.val) c (Or.inl (by omega)) hrow
      · exact reach_row1 c' hc' (c.val - c'.val) c (Or.inr (by omega)) hrow
    obtain ⟨L, hch, hb, hl⟩ := reach_cons (u := (0, c)) (v := (1, c)) (Or.inr ⟨rfl, Or.inl rfl⟩) hc h1
    refine ⟨(0, c) :: L, by simp, rfl, ?_, hb, hch⟩
    rw [← List.getLast_eq_getElem]; exact hl

end OMA.Helpers

namespace OMA.Helpers

/-- A column: (top, middle, bottom). -/
abbrev Col := Bool × Bool × Bool

/-- Automaton step: state (middle colour, top flag, bottom flag). -/
def step (s : Bool × Bool × Bool) (col : Col) : Bool × Bool × Bool :=
  (col.2.1, (col.1 == col.2.1) || ((s.1 == col.2.1) && s.2.1),
    (col.2.2 == col.2.1) || ((s.1 == col.2.1) && s.2.2))

/-- State is alive. -/
def okB (s : Bool × Bool × Bool) : Bool := !(s.2.1 && s.2.2)

/-- State of a column sequence (scanned from the right). -/
def st : (n : ℕ) → (Fin n → Col) → Bool × Bool × Bool
  | 0, _ => (false, false, false)
  | n + 1, x => step (st n (Fin.tail x)) (x 0)

/-- Recursive goodness. -/
def goodB : (n : ℕ) → (Fin n → Col) → Bool
  | 0, _ => true
  | n + 1, x => goodB n (Fin.tail x) && okB (st (n + 1) x)

/-- Top flag. -/
def Tf {n : ℕ} (x : Fin (n + 1) → Col) : Prop :=
  ∃ c : Fin (n + 1), (∀ j : Fin (n + 1), j.val ≤ c.val → (x j).2.1 = (x 0).2.1) ∧
    (x c).1 = (x 0).2.1

/-- Bottom flag. -/
def Bf {n : ℕ} (x : Fin (n + 1) → Col) : Prop :=
  ∃ c : Fin (n + 1), (∀ j : Fin (n + 1), j.val ≤ c.val → (x j).2.1 = (x 0).2.1) ∧
    (x c).2.2 = (x 0).2.1

/-- Bad column sequences. -/
def Bad {n : ℕ} (x : Fin n → Col) : Prop :=
  ∃ b : Bool, ∃ c c' : Fin n, (x c).1 = b ∧ (x c').2.2 = b ∧
    ∀ j, Btw c c' j → (x j).2.1 = b

theorem flag_cons {n : ℕ} (x : Fin (n + 2) → Col) (f : Col → Bool)
    (P : (Fin (n + 2) → Col) → Prop)
    (hP : ∀ y : Fin (n + 2) → Col, P y ↔ ∃ c : Fin (n + 2),
      (∀ j : Fin (n + 2), j.val ≤ c.val → (y j).2.1 = (y 0).2.1) ∧ f (y c) = (y 0).2.1)
    (Q : (Fin (n + 1) → Col) → Prop)
    (hQ : ∀ y : Fin (n + 1) → Col, Q y ↔ ∃ c : Fin (n + 1),
      (∀ j : Fin (n + 1), j.val ≤ c.val → (y j).2.1 = (y 0).2.1) ∧ f (y c) = (y 0).2.1) :
    P x ↔ f (x 0) = (x 0).2.1 ∨ ((x 1).2.1 = (x 0).2.1 ∧ Q (Fin.tail x)) := by
  rw [hP, hQ]
  constructor
  · rintro ⟨c, hrun, hc⟩
    rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨c1, rfl⟩
    · exact Or.inl hc
    · have h1 : (x 1).2.1 = (x 0).2.1 := hrun 1 (by simp)
      refine Or.inr ⟨h1, c1, fun j hj => ?_, ?_⟩
      · simp only [Fin.tail]
        rw [hrun _ (by simp; omega)]
        exact h1.symm
      · simp only [Fin.tail]; rw [hc, ← h1]; rfl
  · rintro (h | ⟨h1, c1, hrun, hc⟩)
    · refine ⟨0, fun j hj => ?_, h⟩
      have : j = 0 := Fin.ext (by simp at hj ⊢; omega)
      rw [this]
    · refine ⟨c1.succ, fun j hj => ?_, ?_⟩
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j1, rfl⟩
        · rfl
        · have := hrun j1 (by simp at hj; omega)
          simp only [Fin.tail] at this
          rw [this, ← h1]; rfl
      · simp only [Fin.tail] at hc; rw [hc, ← h1]; rfl

theorem tf_cons {n : ℕ} (x : Fin (n + 2) → Col) :
    Tf x ↔ (x 0).1 = (x 0).2.1 ∨ ((x 1).2.1 = (x 0).2.1 ∧ Tf (Fin.tail x)) :=
  flag_cons x (fun c => c.1) Tf (fun _ => Iff.rfl) Tf (fun _ => Iff.rfl)

theorem bf_cons {n : ℕ} (x : Fin (n + 2) → Col) :
    Bf x ↔ (x 0).2.2 = (x 0).2.1 ∨ ((x 1).2.1 = (x 0).2.1 ∧ Bf (Fin.tail x)) :=
  flag_cons x (fun c => c.2.2) Bf (fun _ => Iff.rfl) Bf (fun _ => Iff.rfl)

theorem st_spec : ∀ (n : ℕ) (x : Fin (n + 1) → Col),
    (st (n + 1) x).1 = (x 0).2.1 ∧ ((st (n + 1) x).2.1 = true ↔ Tf x) ∧
      ((st (n + 1) x).2.2 = true ↔ Bf x)
  | 0, x => by
    have e : st 1 x = step (false, false, false) (x 0) := rfl
    have z : ∀ c : Fin (0 + 1), c = 0 := fun c => by
      rcases Fin.eq_zero_or_eq_succ c with h | ⟨c1, _⟩
      · exact h
      · exact c1.elim0
    rw [e]
    refine ⟨rfl, ?_, ?_⟩
    · simp only [step, Bool.and_false, Bool.or_false, beq_iff_eq]
      constructor
      · intro h; exact ⟨0, fun j _ => by rw [z j], h⟩
      · rintro ⟨c, _, hc⟩; rwa [z c] at hc
    · simp only [step, Bool.and_false, Bool.or_false, beq_iff_eq]
      constructor
      · intro h; exact ⟨0, fun j _ => by rw [z j], h⟩
      · rintro ⟨c, _, hc⟩; rwa [z c] at hc
  | n + 1, x => by
    obtain ⟨h1, h2, h3⟩ := st_spec n (Fin.tail x)
    have e : st (n + 2) x = step (st (n + 1) (Fin.tail x)) (x 0) := rfl
    rw [e, tf_cons, bf_cons]
    refine ⟨rfl, ?_, ?_⟩
    · simp only [step]
      rw [← h2, h1]
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]
      constructor
      · rintro (h | ⟨h, h'⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h, h'⟩
      · rintro (h | ⟨h, h'⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h, h'⟩
    · simp only [step]
      rw [← h3, h1]
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]
      constructor
      · rintro (h | ⟨h, h'⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h, h'⟩
      · rintro (h | ⟨h, h'⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h, h'⟩

theorem bad_succ {n : ℕ} (x : Fin (n + 1) → Col) :
    Bad x ↔ Bad (Fin.tail x) ∨ (Tf x ∧ Bf x) := by
  constructor
  · rintro ⟨b, c, c', hc, hc', hbet⟩
    rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨c1, rfl⟩
    · have hm : (x 0).2.1 = b := hbet 0 (by simp [Btw])
      right
      refine ⟨⟨0, fun j hj => ?_, by rw [hc, hm]⟩, ⟨c', fun j hj => ?_, by rw [hc', hm]⟩⟩
      · rw [show j = 0 from Fin.ext (by simp at hj ⊢; omega)]
      · rw [hm]; exact hbet j (by simp only [Btw, Fin.val_zero] at hj ⊢; omega)
    · rcases Fin.eq_zero_or_eq_succ c' with rfl | ⟨c1', rfl⟩
      · have hm : (x 0).2.1 = b := hbet 0 (by simp [Btw])
        right
        refine ⟨⟨c1.succ, fun j hj => ?_, by rw [hc, hm]⟩, ⟨0, fun j hj => ?_, by rw [hc', hm]⟩⟩
        · rw [hm]; exact hbet j (by simp only [Btw, Fin.val_zero] at hj ⊢; omega)
        · rw [show j = 0 from Fin.ext (by simp at hj ⊢; omega)]
      · left
        refine ⟨b, c1, c1', hc, hc', fun j hj => hbet j.succ ?_⟩
        simp only [Btw, Fin.val_succ] at hj ⊢; omega
  · rintro (⟨b, c, c', hc, hc', hbet⟩ | ⟨⟨c1, hr1, h1⟩, ⟨c2, hr2, h2⟩⟩)
    · refine ⟨b, c.succ, c'.succ, hc, hc', fun j hj => ?_⟩
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j1, rfl⟩
      · simp [Btw] at hj
      · exact hbet j1 (by simp only [Btw, Fin.val_succ] at hj ⊢; omega)
    · refine ⟨(x 0).2.1, c1, c2, h1, h2, fun j hj => ?_⟩
      by_cases hj1 : j.val ≤ c1.val
      · exact hr1 j hj1
      · exact hr2 j (by simp only [Btw] at hj; omega)

theorem good_iff : ∀ (n : ℕ) (x : Fin n → Col), goodB n x = true ↔ ¬ Bad x
  | 0, x => by
    simp only [goodB, true_iff]
    rintro ⟨_, c, _⟩; exact c.elim0
  | n + 1, x => by
    obtain ⟨_, h2, h3⟩ := st_spec n x
    have e : goodB (n + 1) x = (goodB n (Fin.tail x) && okB (st (n + 1) x)) := rfl
    rw [e, bad_succ, Bool.and_eq_true, good_iff n, okB, ← h2, ← h3]
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, not_or, not_and]
    constructor
    · rintro ⟨h, h'⟩
      refine ⟨h, fun ht hb => ?_⟩
      rcases h' with h' | h' <;> simp_all
    · rintro ⟨h, h'⟩
      refine ⟨h, ?_⟩
      cases ht : (st (n + 1) x).2.1
      · exact Or.inl rfl
      · right; cases hb : (st (n + 1) x).2.2
        · rfl
        · exact absurd hb (by simp [h' ht])

end OMA.Helpers

namespace OMA.Helpers

/-- Number of good sequences of length `n` ending in state `s`. -/
def g (n : ℕ) (s : Bool × Bool × Bool) : ℕ :=
  ∑ x : Fin n → Col, if goodB n x = true ∧ st n x = s then 1 else 0

/-- Transition counts. -/
def cc (s s' : Bool × Bool × Bool) : ℕ :=
  ∑ col : Col, if okB (step s col) = true ∧ step s col = s' then 1 else 0

theorem st_cons {n : ℕ} (col : Col) (x : Fin n → Col) :
    st (n + 1) (Fin.cons col x) = step (st n x) col := by
  simp [st]

theorem good_cons {n : ℕ} (col : Col) (x : Fin n → Col) :
    goodB (n + 1) (Fin.cons col x) = (goodB n x && okB (step (st n x) col)) := by
  simp [goodB, st]

theorem swap3 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℕ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ b, ∑ a, f a b c := by
  calc ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ a, ∑ c, f a b c := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, f a b c := by
      refine Finset.sum_congr rfl (fun b _ => ?_)
      exact Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ a, f a b c := Finset.sum_comm

theorem g_succ (n : ℕ) (s' : Bool × Bool × Bool) :
    g (n + 1) s' = ∑ s, g n s * cc s s' := by
  have hsum : ∀ F : (Fin (n + 1) → Col) → ℕ,
      ∑ y, F y = ∑ col, ∑ x, F (Fin.cons col x) := fun F => by
    rw [← Fintype.sum_prod_type']
    exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Col) _ _ (fun _ => rfl)).symm
  unfold g cc
  rw [hsum]
  simp only [st_cons, good_cons]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [swap3, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine Finset.sum_congr rfl (fun col _ => ?_)
  rw [Finset.sum_eq_single (st n x)]
  · by_cases hg : goodB n x = true
    · simp [hg]
    · simp [hg]
  · intro s _ hs
    have : ¬ (st n x = s) := fun e => hs e.symm
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Closed form for `g (n + 1)`. -/
def W (n : ℕ) (s : Bool × Bool × Bool) : ℕ :=
  if (s.2.1 && s.2.2) = true then 0
  else if (s.2.1 || s.2.2) = true then 2 ^ n * Nat.fib (2 * n + 2)
  else 2 ^ n * Nat.fib (2 * n + 1)

theorem g_zero (s : Bool × Bool × Bool) :
    g 0 s = if (false, false, false) = s then 1 else 0 := by
  unfold g
  rw [Fintype.sum_unique]
  simp [goodB, st]

theorem g_one (s : Bool × Bool × Bool) : g 1 s = W 0 s := by
  rw [g_succ]
  simp only [g_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  obtain ⟨m, t, b⟩ := s
  cases m <;> cases t <;> cases b <;> decide

theorem fib_a (n : ℕ) : Nat.fib (2 * (n + 1) + 1) = Nat.fib (2 * n + 1) + Nat.fib (2 * n + 2) := by
  rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, Nat.fib_add_two]

theorem fib_b (n : ℕ) :
    Nat.fib (2 * (n + 1) + 2) = Nat.fib (2 * n + 1) + 2 * Nat.fib (2 * n + 2) := by
  have h1 := Nat.fib_add_two (n := 2 * n + 1)
  have h2 := Nat.fib_add_two (n := 2 * n + 2)
  rw [show 2 * (n + 1) + 2 = (2 * n + 2) + 2 by ring, h2,
    show 2 * n + 2 + 1 = 2 * n + 1 + 2 by ring, h1]
  ring

theorem W_succ (n : ℕ) (s' : Bool × Bool × Bool) : ∑ s, W n s * cc s s' = W (n + 1) s' := by
  have hfa := fib_a n
  have hfb := fib_b n
  obtain ⟨m, t, b⟩ := s'
  cases m <;> cases t <;> cases b <;>
    simp only [cc, Fintype.sum_prod_type, Fintype.sum_bool] <;>
    simp [W, step, okB, hfa, hfb, pow_succ] <;> ring

theorem g_formula : ∀ (n : ℕ) (s : Bool × Bool × Bool), g (n + 1) s = W n s
  | 0, s => g_one s
  | n + 1, s => by
    rw [g_succ]
    simp only [g_formula n]
    exact W_succ n s

theorem total (n : ℕ) :
    ∑ x : Fin (n + 1) → Col, (if goodB (n + 1) x = true then 1 else 0) =
      2 ^ (n + 1) * Nat.fib (2 * (n + 1) + 2) := by
  have h : ∀ x : Fin (n + 1) → Col, (if goodB (n + 1) x = true then 1 else 0) =
      ∑ s, (if goodB (n + 1) x = true ∧ st (n + 1) x = s then 1 else 0) := by
    intro x
    rw [Finset.sum_eq_single (st (n + 1) x)]
    · simp
    · intro s _ hs
      have : ¬ (st (n + 1) x = s) := fun e => hs e.symm
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [h]
  rw [Finset.sum_comm]
  have e : ∀ s, (∑ x : Fin (n + 1) → Col,
      (if goodB (n + 1) x = true ∧ st (n + 1) x = s then 1 else 0)) = W n s :=
    fun s => g_formula n s
  simp only [e]
  have hfb := fib_b n
  simp [Fintype.sum_prod_type, W, hfb, pow_succ]
  ring

end OMA.Helpers

namespace OMA.Helpers
open OMA.S_oeis_a069429

/-- Arrays as column sequences. -/
def convE (n : ℕ) : (Fin 3 × Fin n → Bool) ≃ (Fin n → Col) where
  toFun A j := (A (0, j), A (1, j), A (2, j))
  invFun x p := ![(x p.2).1, (x p.2).2.1, (x p.2).2.2] p.1
  left_inv A := by
    funext ⟨r, j⟩
    fin_cases r <;> rfl
  right_inv x := by
    funext j
    rfl

theorem key (n : ℕ) (A : Fin 3 × Fin n → Bool) :
    (¬ HasMonoPath A true ∧ ¬ HasMonoPath A false) ↔ goodB n (convE n A) = true := by
  rw [good_iff, path_iff, path_iff]
  constructor
  · rintro ⟨h1, h2⟩ ⟨b, c, c', hc, hc', hrow⟩
    cases b
    · exact h2 ⟨c, c', hc, hc', hrow⟩
    · exact h1 ⟨c, c', hc, hc', hrow⟩
  · intro h
    exact ⟨fun ⟨c, c', hc, hc', hrow⟩ => h ⟨true, c, c', hc, hc', hrow⟩,
      fun ⟨c, c', hc, hc', hrow⟩ => h ⟨false, c, c', hc, hc', hrow⟩⟩

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a069429.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  classical
  have hset : {A : Fin 3 × Fin (m + 1) → Bool |
      ¬ OMA.S_oeis_a069429.HasMonoPath A true ∧ ¬ OMA.S_oeis_a069429.HasMonoPath A false} =
      ↑(Finset.univ.filter (fun A => goodB (m + 1) (convE (m + 1) A) = true)) := by
    ext A
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
    exact key (m + 1) A
  rw [hset, Set.ncard_coe_finset, Finset.card_filter]
  rw [Fintype.sum_equiv (convE (m + 1)) _
    (fun x => if goodB (m + 1) x = true then 1 else 0) (fun _ => rfl)]
  exact total m
