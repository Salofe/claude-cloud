import OMAStatements.S_oeis_a205354
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a205354 Finset

/-- A row of the array. -/
abbrev A205354Row := Fin 2 → Fin 3

/-- The number of equal diagonal and antidiagonal pairs of the block of rows `x` (top), `y`. -/
def a205354bn (x y : A205354Row) : ℕ :=
  (if x 0 = y 1 then 1 else 0) + (if x 1 = y 0 then 1 else 0)

/-- Every block of consecutive rows of `X` has the number `s`. -/
def a205354Blocks (s : ℕ) {k : ℕ} (X : Fin k → A205354Row) : Prop :=
  ∀ (i : ℕ) (h : i + 1 < k), a205354bn (X ⟨i, by omega⟩) (X ⟨i + 1, h⟩) = s

/-- Some entry 2 of `X` has no entry 1 before it in row major order. -/
def a205354Need {k : ℕ} (X : Fin k → A205354Row) : Prop :=
  ∃ i j, X i j = 2 ∧ ∀ i' j', (i' < i ∨ (i' = i ∧ j' < j)) → X i' j' ≠ 1

instance a205354decNeed {k : ℕ} (X : Fin k → A205354Row) : Decidable (a205354Need X) := by
  unfold a205354Need; infer_instance

/-- How `a205354Need` changes when a row `r` is put in front. -/
def a205354step (r : A205354Row) (e : Bool) : Bool :=
  decide (r 0 = 2) || (decide (r 1 = 2) && !decide (r 0 = 1)) ||
    (e && !decide (r 0 = 1) && !decide (r 1 = 1))

theorem a205354_need_nil (X : Fin 0 → A205354Row) : ¬ a205354Need X := by
  rintro ⟨i, _⟩
  exact i.elim0

theorem a205354_need_cons {m : ℕ} (r : A205354Row) (B : Fin m → A205354Row) :
    a205354Need (Fin.cons r B : Fin (m + 1) → A205354Row) ↔
      a205354step r (decide (a205354Need B)) = true := by
  unfold a205354step
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨i, j, h2, hno⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨a, rfl⟩
    · simp only [Fin.cons_zero] at h2
      fin_cases j
      · left; left; exact h2
      · left; right
        refine ⟨h2, fun h1 => hno 0 0 (Or.inr ⟨rfl, by decide⟩) ?_⟩
        simpa using h1
    · simp only [Fin.cons_succ] at h2
      right
      refine ⟨⟨⟨a, j, h2, fun i' j' hlt => ?_⟩, ?_⟩, ?_⟩
      · have := hno i'.succ j' (by
          rcases hlt with hlt | ⟨rfl, hlt⟩
          · exact Or.inl (Fin.succ_lt_succ_iff.mpr hlt)
          · exact Or.inr ⟨rfl, hlt⟩)
        simpa using this
      · intro h1
        exact hno 0 0 (Or.inl (Fin.succ_pos a)) (by simpa using h1)
      · intro h1
        exact hno 0 1 (Or.inl (Fin.succ_pos a)) (by simpa using h1)
  · rintro ((h | ⟨h2, h1⟩) | ⟨⟨⟨a, j, h2, hno⟩, h0⟩, h1⟩)
    · refine ⟨0, 0, by simpa using h, fun i' j' hlt => ?_⟩
      rcases hlt with hlt | ⟨_, hlt⟩
      · exact absurd hlt (Fin.not_lt_zero i')
      · exact absurd hlt (Fin.not_lt_zero j')
    · refine ⟨0, 1, by simpa using h2, fun i' j' hlt => ?_⟩
      rcases hlt with hlt | ⟨rfl, hlt⟩
      · exact absurd hlt (Fin.not_lt_zero i')
      · have : j' = 0 := by
          have := j'.isLt
          exact Fin.ext (by rw [Fin.lt_def] at hlt; simp at hlt ⊢; omega)
        subst this
        simpa using h1
    · refine ⟨a.succ, j, by simpa using h2, fun i' j' hlt => ?_⟩
      rcases Fin.eq_zero_or_eq_succ i' with rfl | ⟨b, rfl⟩
      · simp only [Fin.cons_zero]
        fin_cases j'
        · exact h0
        · exact h1
      · simp only [Fin.cons_succ]
        apply hno b j'
        rcases hlt with hlt | ⟨hb, hlt⟩
        · exact Or.inl (Fin.succ_lt_succ_iff.mp hlt)
        · exact Or.inr ⟨Fin.succ_injective _ hb, hlt⟩

theorem a205354_need_cons_dec {m : ℕ} (r : A205354Row) (B : Fin m → A205354Row) :
    decide (a205354Need (Fin.cons r B : Fin (m + 1) → A205354Row)) =
      a205354step r (decide (a205354Need B)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, a205354_need_cons]

theorem a205354_need_one (r : A205354Row) (B : Fin 0 → A205354Row) :
    decide (a205354Need (Fin.cons r B : Fin 1 → A205354Row)) = a205354step r false := by
  rw [a205354_need_cons_dec, decide_eq_false (a205354_need_nil B)]

theorem a205354_rmn_iff {k : ℕ} (X : Fin (k + 1) → A205354Row) :
    RowMajorNew X ↔ X 0 0 = 0 ∧ ¬ a205354Need X := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra h0
      have h1 : (0 : Fin 3) < X 0 0 := by
        rcases Fin.eq_zero_or_eq_succ (X 0 0) with e | ⟨j, e⟩
        · exact absurd e h0
        · rw [e]; exact Fin.succ_pos j
      obtain ⟨i', j', hlt, _⟩ := h 0 0 0 h1
      rcases hlt with hlt | ⟨_, hlt⟩
      · exact absurd hlt (Fin.not_lt_zero i')
      · exact absurd hlt (Fin.not_lt_zero j')
    · rintro ⟨i, j, h2, hno⟩
      obtain ⟨i', j', hlt, h1⟩ := h i j 1 (by rw [h2]; decide)
      exact hno i' j' hlt h1
  · rintro ⟨h0, hn⟩ i j u hu
    have hlt3 := (X i j).isLt
    rw [Fin.lt_def] at hu
    rcases Nat.lt_or_ge u.val 1 with hu0 | hu1
    · have e : u = 0 := Fin.ext (by simp; omega)
      subst e
      refine ⟨0, 0, ?_, h0⟩
      by_cases hi : i = 0
      · subst hi
        by_cases hj : j = 0
        · subst hj; rw [h0] at hu; simp at hu
        · right; exact ⟨rfl, Fin.pos_iff_ne_zero.mpr hj⟩
      · left; exact Fin.pos_iff_ne_zero.mpr hi
    · have e : u = 1 := Fin.ext (by simp; omega)
      have e2 : X i j = 2 := Fin.ext (by simp; omega)
      subst e
      by_contra hc
      push Not at hc
      exact hn ⟨i, j, e2, fun i' j' hlt h1 => hc i' j' hlt h1⟩

theorem a205354_blocks_cons {m : ℕ} (s : ℕ) (r : A205354Row) (B : Fin (m + 1) → A205354Row) :
    a205354Blocks s (Fin.cons r B : Fin (m + 2) → A205354Row) ↔
      a205354bn r (B ⟨0, by omega⟩) = s ∧ a205354Blocks s B := by
  constructor
  · intro h
    have h0 := h 0 (by omega)
    exact ⟨h0, fun i hi => h (i + 1) (by omega)⟩
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => exact h0
    | succ i => exact h i (by omega)

/-- The reference number of the first block. -/
def a205354s0 {n : ℕ} (X : Fin (n + 2) → A205354Row) : ℕ :=
  a205354bn (X ⟨0, by omega⟩) (X ⟨1, by omega⟩)

theorem a205354_bn_le (x y : A205354Row) : a205354bn x y < 3 := by
  unfold a205354bn; split_ifs <;> norm_num

theorem a205354_cond_blocks {n : ℕ} (X : Fin (n + 2) → A205354Row) (h : Cond X) :
    a205354Blocks (a205354s0 X) X := by
  intro i hi
  exact h ⟨i, by omega⟩ ⟨i + 1, hi⟩ ⟨0, by omega⟩ ⟨1, by omega⟩ 0 1 0 1 rfl rfl rfl rfl

theorem a205354_blocks_cond {n : ℕ} (s : ℕ) (X : Fin (n + 2) → A205354Row)
    (h : a205354Blocks s X) : Cond X := by
  intro i i' k k' j j' l l' hi hj hk hl
  have hj1 := j'.isLt
  have hl1 := l'.isLt
  have ej : j = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
  have ej' : j' = 1 := Fin.ext (by simp only [Fin.val_one]; omega)
  have el : l = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
  have el' : l' = 1 := Fin.ext (by simp only [Fin.val_one]; omega)
  subst ej ej' el el'
  rcases i' with ⟨i', hi'⟩
  rcases k' with ⟨k', hk'⟩
  simp only at hi hk
  subst hi hk
  have e1 := h i.val hi'
  have e2 := h k.val hk'
  exact e1.trans e2.symm

theorem a205354_blocks_s0 {n : ℕ} (s : ℕ) (X : Fin (n + 2) → A205354Row)
    (h : a205354Blocks s X) : s = a205354s0 X :=
  (h 0 (by omega)).symm

open Classical in
theorem a205354_pointwise {n : ℕ} (X : Fin (n + 2) → A205354Row) (R : Prop) [Decidable R] :
    (if Cond X ∧ R then 1 else 0) =
      ∑ s ∈ range 3, (if a205354Blocks s X ∧ R then 1 else 0) := by
  by_cases hc : Cond X ∧ R
  · rw [if_pos hc, Finset.sum_eq_single (a205354s0 X)]
    · rw [if_pos ⟨a205354_cond_blocks X hc.1, hc.2⟩]
    · intro s _ hs
      rw [if_neg]
      rintro ⟨hb, _⟩
      exact hs (a205354_blocks_s0 s X hb)
    · intro hn
      exact absurd (Finset.mem_range.mpr (a205354_bn_le _ _)) hn
  · rw [if_neg hc]
    symm
    refine Finset.sum_eq_zero fun s _ => if_neg ?_
    rintro ⟨hb, hr⟩
    exact hc ⟨a205354_blocks_cond s X hb, hr⟩

/-- The transfer count: the arrays `cons r B` with all blocks `s` and need flag `e`. -/
noncomputable def a205354T (s m : ℕ) (r : A205354Row) (e : Bool) : ℕ := by
  classical
  exact ∑ B : Fin m → A205354Row,
    if a205354Blocks s (Fin.cons r B : Fin (m + 1) → A205354Row) ∧
      decide (a205354Need (Fin.cons r B : Fin (m + 1) → A205354Row)) = e then 1 else 0

theorem a205354T_zero (s : ℕ) (r : A205354Row) (e : Bool) :
    a205354T s 0 r e = if a205354step r false = e then 1 else 0 := by
  classical
  unfold a205354T
  rw [Fintype.sum_unique, a205354_need_one]
  exact if_congr ⟨fun h => h.2, fun h => ⟨fun i hi => by omega, h⟩⟩ rfl rfl

theorem a205354_split (P : Prop) [Decidable P] (g : Bool → Bool) (d e : Bool) :
    (if P ∧ g d = e then 1 else 0) =
      ∑ e' : Bool, (if g e' = e then (if P ∧ d = e' then 1 else 0) else 0) := by
  rw [Fintype.sum_bool]
  cases d <;> by_cases hP : P <;> simp [hP]

theorem a205354T_succ (s m : ℕ) (r : A205354Row) (e : Bool) :
    a205354T s (m + 1) r e = ∑ r' : A205354Row, if a205354bn r r' = s then
      ∑ e' : Bool, (if a205354step r e' = e then a205354T s m r' e' else 0) else 0 := by
  classical
  unfold a205354T
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => A205354Row).symm _
    (fun p => if a205354Blocks s (Fin.cons r (Fin.cons p.1 p.2) : Fin (m + 2) → A205354Row) ∧
      decide (a205354Need (Fin.cons r (Fin.cons p.1 p.2) : Fin (m + 2) → A205354Row)) = e
      then 1 else 0) (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r' _ => ?_
  have hstep : ∀ B : Fin m → A205354Row,
      decide (a205354Need (Fin.cons r (Fin.cons r' B) : Fin (m + 2) → A205354Row)) =
        a205354step r (decide (a205354Need (Fin.cons r' B : Fin (m + 1) → A205354Row))) :=
    fun B => a205354_need_cons_dec r _
  by_cases hb : a205354bn r r' = s
  · rw [if_pos hb]
    have e1 : ∀ B : Fin m → A205354Row,
        (if a205354Blocks s (Fin.cons r (Fin.cons r' B) : Fin (m + 2) → A205354Row) ∧
          decide (a205354Need (Fin.cons r (Fin.cons r' B) : Fin (m + 2) → A205354Row)) = e
          then 1 else 0) =
        ∑ e' : Bool, (if a205354step r e' = e then
          (if a205354Blocks s (Fin.cons r' B : Fin (m + 1) → A205354Row) ∧
            decide (a205354Need (Fin.cons r' B : Fin (m + 1) → A205354Row)) = e'
            then 1 else 0) else 0) := by
      intro B
      rw [hstep B, ← a205354_split]
      refine if_congr ?_ rfl rfl
      rw [a205354_blocks_cons]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hb, h.1⟩, h.2⟩⟩
    simp only [e1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e' _ => ?_
    by_cases he : a205354step r e' = e
    · simp only [he, if_true]
    · simp only [he, if_false]; simp
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [a205354_blocks_cons]
    exact fun h => hb h.1.1

theorem a205354_a_eq (m : ℕ) :
    a (m + 1) = ∑ s ∈ range 3, ∑ r : A205354Row,
      if r 0 = 0 then a205354T s (m + 1) r false else 0 := by
  classical
  have h1 : a (m + 1) = ∑ X : Fin (m + 2) → A205354Row,
      ∑ s ∈ range 3, if a205354Blocks s X ∧ (X 0 0 = 0 ∧ ¬ a205354Need X) then 1 else 0 := by
    unfold a
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun X _ => ?_
    rw [← a205354_pointwise]
    exact if_congr (and_congr Iff.rfl (a205354_rmn_iff X)) rfl rfl
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => A205354Row).symm _
    (fun p => if a205354Blocks s (Fin.cons p.1 p.2 : Fin (m + 2) → A205354Row) ∧
      (p.1 0 = 0 ∧ ¬ a205354Need (Fin.cons p.1 p.2 : Fin (m + 2) → A205354Row)) then 1 else 0)
    (fun X => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : r 0 = 0
  · rw [if_pos hr]
    unfold a205354T
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    simp only [hr, true_and, decide_eq_false_iff_not]
  · rw [if_neg hr]
    exact Finset.sum_eq_zero fun B _ => if_neg fun h => hr h.2.1

/-- The row with code `c`. -/
def a205354row (c : Fin 9) : A205354Row :=
  ![⟨c.val / 3, by omega⟩, ⟨c.val % 3, by omega⟩]

theorem a205354row_bijective : Function.Bijective a205354row := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨by decide, by simp⟩

/-- `a205354bn` on codes. -/
def a205354bnc (c d : Fin 9) : ℕ :=
  (if c.val / 3 = d.val % 3 then 1 else 0) + (if c.val % 3 = d.val / 3 then 1 else 0)

/-- `a205354step` on codes. -/
def a205354stepc (c : Fin 9) (e : Bool) : Bool :=
  (c.val / 3 == 2) || ((c.val % 3 == 2) && !(c.val / 3 == 1)) ||
    (e && !(c.val / 3 == 1) && !(c.val % 3 == 1))

theorem a205354_bn_eq : ∀ c d : Fin 9, a205354bn (a205354row c) (a205354row d) = a205354bnc c d := by
  decide +kernel

theorem a205354_step_eq : ∀ (c : Fin 9) (e : Bool),
    a205354step (a205354row c) e = a205354stepc c e := by
  decide +kernel

theorem a205354_top_iff : ∀ c : Fin 9, a205354row c 0 = 0 ↔ c.val < 3 := by
  decide +kernel

/-- The transfer recursion on codes. -/
def a205354G (s : ℕ) : ℕ → Fin 9 → Bool → ℕ
  | 0, c, e => if a205354stepc c false = e then 1 else 0
  | m + 1, c, e => ∑ d : Fin 9, if a205354bnc c d = s then
      ∑ e' : Bool, (if a205354stepc c e' = e then a205354G s m d e' else 0) else 0

theorem a205354G_succ (s m : ℕ) (c : Fin 9) (e : Bool) : a205354G s (m + 1) c e =
    ∑ d : Fin 9, if a205354bnc c d = s then
      ∑ e' : Bool, (if a205354stepc c e' = e then a205354G s m d e' else 0) else 0 := rfl

theorem a205354T_eq_G (s m : ℕ) : ∀ (c : Fin 9) (e : Bool),
    a205354T s m (a205354row c) e = a205354G s m c e := by
  induction m with
  | zero =>
    intro c e
    rw [a205354T_zero, a205354_step_eq]
    rfl
  | succ m ih =>
    intro c e
    rw [a205354T_succ, a205354G_succ, ← a205354row_bijective.sum_comp]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [a205354_bn_eq]
    refine if_congr Iff.rfl (Finset.sum_congr rfl fun e' _ => ?_) rfl
    rw [a205354_step_eq, ih d e']

theorem a205354_a_eq_G (m : ℕ) :
    a (m + 1) = ∑ s ∈ range 3, ∑ c : Fin 9,
      if c.val < 3 then a205354G s (m + 1) c false else 0 := by
  rw [a205354_a_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← a205354row_bijective.sum_comp]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [a205354T_eq_G]
  exact if_congr (a205354_top_iff c) rfl rfl

theorem a205354_G_base0 : ∀ (c : Fin 9) (e : Bool),
    a205354G 0 3 c e + 4 * a205354G 0 1 c e = 5 * a205354G 0 2 c e := by
  decide +kernel

theorem a205354_G_base1 : ∀ (c : Fin 9) (e : Bool),
    a205354G 1 3 c e + 4 * a205354G 1 1 c e = 5 * a205354G 1 2 c e := by
  decide +kernel

theorem a205354_G_base2 : ∀ (c : Fin 9) (e : Bool),
    a205354G 2 3 c e + 4 * a205354G 2 1 c e = 5 * a205354G 2 2 c e := by
  decide +kernel

theorem a205354_G_rec (s : ℕ) (hs : s < 3) (m : ℕ) (hm : 1 ≤ m) : ∀ (c : Fin 9) (e : Bool),
    a205354G s (m + 2) c e + 4 * a205354G s m c e = 5 * a205354G s (m + 1) c e := by
  induction m, hm using Nat.le_induction with
  | base =>
    interval_cases s
    · exact a205354_G_base0
    · exact a205354_G_base1
    · exact a205354_G_base2
  | succ m hm ih =>
    intro c e
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, show m + 1 + 1 = (m + 1) + 1 by omega,
      a205354G_succ s (m + 2), a205354G_succ s (m + 1), a205354G_succ s m,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hb : a205354bnc c d = s
    · simp only [hb, if_true]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e' _ => ?_
      by_cases he : a205354stepc c e' = e
      · simp only [he, if_true]; exact ih d e'
      · simp only [he, if_false]; norm_num
    · simp only [hb, if_false]; norm_num

theorem a205354_a1 : a 1 = 14 := by
  rw [a205354_a_eq_G]; decide +kernel

theorem a205354_a2 : a 2 = 50 := by
  rw [a205354_a_eq_G]; decide +kernel

theorem a205354_rec (n : ℕ) (hn : 1 ≤ n) : a (n + 2) + 4 * a n = 5 * a (n + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show k + 1 + 2 = (k + 2) + 1 by omega, show k + 1 + 1 = (k + 1) + 1 by omega,
    a205354_a_eq_G, a205354_a_eq_G, a205354_a_eq_G,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : c.val < 3
  · simp only [hc, if_true]
    exact a205354_G_rec s (Finset.mem_range.mp hs) (k + 1) (by omega) c false
  · simp only [hc, if_false]; norm_num

theorem a205354_closed (n : ℕ) (hn : 1 ≤ n) : a n = 2 + 3 * 4 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n
      · rw [a205354_a1]; norm_num
      · rw [a205354_a2]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      have hr := a205354_rec k (by omega)
      rw [ih (k + 1) (by omega) (by omega), ih k (by omega) (by omega)] at hr
      have e1 : 4 ^ (k + 1) = 4 * 4 ^ k := by ring
      have e2 : 4 ^ (k + 2) = 16 * 4 ^ k := by ring
      rw [e1] at hr
      rw [e2]
      omega

theorem a205354_closedQ (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = 2 + 3 * 4 ^ n := by
  rw [a205354_closed n hn]; push_cast; ring

open PowerSeries in
theorem a205354_gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) * (1 - 4 * X)) =
      2 * X * (7 - 10 * X) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * ((1 - X) * (1 - 4 * X)) =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 5 * (PowerSeries.mk F * X ^ 1) +
        C 4 * (PowerSeries.mk F * X ^ 2) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (2 * X * (7 - 10 * X) : ℚ⟦X⟧) = C 14 * X ^ 1 - C 20 * X ^ 2 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 3
  · interval_cases k <;> norm_num [hF, a205354_a1, a205354_a2]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    simp only [show 0 ≤ j + 3 by omega, show 1 ≤ j + 3 by omega, show 2 ≤ j + 3 by omega,
      show j + 3 - 0 = j + 3 by omega, show j + 3 - 1 = j + 2 by omega,
      show j + 3 - 2 = j + 1 by omega,
      show ¬ (j + 3 = 1) by omega, show ¬ (j + 3 = 2) by omega, show ¬ (j + 3 = 0) by omega,
      show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega, if_true, if_false, hF]
    rw [a205354_closedQ (j + 3) (by omega), a205354_closedQ (j + 2) (by omega),
      a205354_closedQ (j + 1) (by omega)]
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a205354.main :=
  ⟨OMA.Helpers.a205354_gen_fun, OMA.Helpers.a205354_closed⟩
