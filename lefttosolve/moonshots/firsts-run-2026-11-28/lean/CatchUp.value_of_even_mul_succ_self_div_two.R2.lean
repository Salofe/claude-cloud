import FormalConjectures.Paper.CatchUpConjecture

/-!
# Catch-Up: the conjecture follows from the opening `1` alone

Reduction of `CatchUp.value_of_even_mul_succ_self_div_two` to the single position reached after the
first player takes `1`:

* `H1`: after the opening `1` the second player cannot win;
* `H2`: after the opening `1` the second player does not lose.

The proof rests on a *swap lemma* valid for every finite set `T` and `d < x` in `T`:
if the player who trails by `x` on `T \ {x}` loses, then the player who trails by `d` on `T \ {d}`
wins.  (The trailing player of the second position may pick `x`, which ends his turn and leaves the
opponent trailing by `x - d` on `T \ {d, x}`; the trailing player of the first position may pick `d`,
which does not end his turn and leaves himself trailing by `x - d` on the same set.)  Hence at most
one opening can be losing for the second player, and if the opening `1` is exactly a draw then no
other opening `x > 1` can be a loss for the second player.
-/

namespace OMA.R_CatchUp_value_of_even_mul_succ_self_div_two_R2

open CatchUp

def H1 : Prop := ∀ N : ℕ, Even (N * (N + 1) / 2) → 1 ≤ N →
    CatchUp.valueAux ((Finset.Icc 1 N).erase 1) 0 1 false ≠ CatchUp.Outcome.win

def H2 : Prop := ∀ N : ℕ, Even (N * (N + 1) / 2) → 1 ≤ N →
    CatchUp.valueAux ((Finset.Icc 1 N).erase 1) 0 1 false ≠ CatchUp.Outcome.loss

/-- A fold with a binary operation that behaves like `max` for `loss < draw < win`. -/
lemma foldl_char (g : Outcome → Outcome → Outcome)
    (h1 : ∀ b, g Outcome.win b = Outcome.win) (h2 : ∀ a, g a Outcome.win = Outcome.win)
    (h3 : g Outcome.draw Outcome.draw = Outcome.draw) (h4 : g Outcome.draw Outcome.loss = Outcome.draw)
    (h5 : g Outcome.loss Outcome.draw = Outcome.draw) (h6 : g Outcome.loss Outcome.loss = Outcome.loss) :
    ∀ (os : List Outcome) (acc : Outcome),
      (os.foldl g acc = Outcome.win ↔ acc = Outcome.win ∨ Outcome.win ∈ os) ∧
      (os.foldl g acc = Outcome.loss ↔ acc = Outcome.loss ∧ ∀ o ∈ os, o = Outcome.loss) := by
  intro os
  induction os with
  | nil => intro acc; simp
  | cons o os ih =>
    intro acc
    rw [List.foldl_cons]
    obtain ⟨ihw, ihl⟩ := ih (g acc o)
    constructor
    · rw [ihw]
      cases acc <;> cases o <;> simp [h1, h2, h3, h4, h5, h6]
    · rw [ihl]
      cases acc <;> cases o <;> simp [h1, h2, h3, h4, h5, h6]

lemma best_eq_win_iff (os : List Outcome) : Outcome.best os = Outcome.win ↔ Outcome.win ∈ os := by
  unfold Outcome.best
  refine ((foldl_char _ ?_ ?_ ?_ ?_ ?_ ?_ os Outcome.loss).1).trans ?_
  · intro b; rfl
  · intro a; cases a <;> rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp

lemma best_eq_loss_iff (os : List Outcome) :
    Outcome.best os = Outcome.loss ↔ ∀ o ∈ os, o = Outcome.loss := by
  unfold Outcome.best
  refine ((foldl_char _ ?_ ?_ ?_ ?_ ?_ ?_ os Outcome.loss).2).trans ?_
  · intro b; rfl
  · intro a; cases a <;> rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp

lemma neg_eq_win_iff (o : Outcome) : o.neg = Outcome.win ↔ o = Outcome.loss := by
  cases o <;> simp [Outcome.neg]

lemma neg_eq_loss_iff (o : Outcome) : o.neg = Outcome.loss ↔ o = Outcome.win := by
  cases o <;> simp [Outcome.neg]

/-- Unfolding of `valueAux` at a position that is not the first move, with a nonempty set and a
mover who can still catch up. -/
lemma valueAux_eq (R : Finset ℕ) (sm so : ℕ) (hne : R ≠ ∅) (hs : ¬ sm + ∑ y ∈ R, y < so) :
    valueAux R sm so false = Outcome.best (List.map (fun y : {y // y ∈ R} =>
        if sm + (y : ℕ) ≥ so then (valueAux (R.erase (y : ℕ)) so (sm + (y : ℕ)) false).neg
        else valueAux (R.erase (y : ℕ)) (sm + (y : ℕ)) so false) R.attach.toList) := by
  rw [valueAux]
  simp only [Bool.false_eq_true, if_false]
  rw [if_neg hne, if_neg hs]

/-- If the mover cannot catch up even with everything that is left, he loses. -/
lemma valueAux_pruned (R : Finset ℕ) (sm so : ℕ) (hs : sm + ∑ y ∈ R, y < so) :
    valueAux R sm so false = Outcome.loss := by
  rw [valueAux]
  simp only [Bool.false_eq_true, if_false]
  by_cases hne : R = ∅
  · subst hne
    have h1 : ¬ sm > so := by simp at hs; omega
    have h2 : so > sm := by simp at hs; omega
    rw [if_pos rfl, if_neg h1, if_pos h2]
  · rw [if_neg hne, if_pos hs]

/-- The option of picking `x` belongs to the list of options. -/
lemma opt_mem (R : Finset ℕ) (sm so x : ℕ) (hx : x ∈ R) :
    (if sm + x ≥ so then (valueAux (R.erase x) so (sm + x) false).neg
        else valueAux (R.erase x) (sm + x) so false) ∈
      List.map (fun y : {y // y ∈ R} =>
        if sm + (y : ℕ) ≥ so then (valueAux (R.erase (y : ℕ)) so (sm + (y : ℕ)) false).neg
        else valueAux (R.erase (y : ℕ)) (sm + (y : ℕ)) so false) R.attach.toList := by
  apply List.mem_map.mpr
  exact ⟨⟨x, hx⟩, by simp, rfl⟩

/-- **Swap lemma.** For `d < x` in `T`: if the player trailing by `x` on `T \ {x}` loses, then the
player trailing by `d` on `T \ {d}` wins. -/
lemma swap (T : Finset ℕ) (d x : ℕ) (hd : d ∈ T) (hx : x ∈ T) (hdx : d < x)
    (hB : valueAux (T.erase x) 0 x false = Outcome.loss) :
    valueAux (T.erase d) 0 d false = Outcome.win := by
  have hdx' : d ≠ x := Nat.ne_of_lt hdx
  have hd' : d ∈ T.erase x := Finset.mem_erase.mpr ⟨hdx', hd⟩
  have hx' : x ∈ T.erase d := Finset.mem_erase.mpr ⟨hdx'.symm, hx⟩
  have hcomm : (T.erase x).erase d = (T.erase d).erase x := Finset.erase_right_comm
  -- the common position: trailing by `x - d` on `T \ {d, x}`, with scores `d` and `x`
  have hE : valueAux ((T.erase d).erase x) d x false = Outcome.loss := by
    by_cases hpr : 0 + ∑ y ∈ T.erase x, y < x
    · apply valueAux_pruned
      have hsum : d + ∑ y ∈ (T.erase x).erase d, y = ∑ y ∈ T.erase x, y :=
        Finset.add_sum_erase (T.erase x) (fun y => y) hd'
      rw [← hcomm]
      omega
    · have hne : T.erase x ≠ ∅ := Finset.ne_empty_of_mem hd'
      rw [valueAux_eq _ _ _ hne hpr, best_eq_loss_iff] at hB
      have h := hB _ (opt_mem (T.erase x) 0 x d hd')
      have hlt : ¬ 0 + d ≥ x := by omega
      rw [if_neg hlt, Nat.zero_add, hcomm] at h
      exact h
  have hne : T.erase d ≠ ∅ := Finset.ne_empty_of_mem hx'
  have hpr : ¬ 0 + ∑ y ∈ T.erase d, y < d := by
    have hle : x ≤ ∑ y ∈ T.erase d, y :=
      Finset.single_le_sum (f := fun y => y) (fun _ _ => Nat.zero_le _) hx'
    omega
  rw [valueAux_eq _ _ _ hne hpr, best_eq_win_iff]
  have h := opt_mem (T.erase d) 0 d x hx'
  have hge : 0 + x ≥ d := by omega
  rw [if_pos hge, Nat.zero_add, hE] at h
  exact h

/-- The companion direction of the swap lemma: for `d < x` in `T`, if the player trailing by `d` on
`T \ {d}` loses, then the player trailing by `x` on `T \ {x}` wins. -/
lemma swap' (T : Finset ℕ) (d x : ℕ) (hd : d ∈ T) (hx : x ∈ T) (hdx : d < x)
    (hA : valueAux (T.erase d) 0 d false = Outcome.loss) :
    valueAux (T.erase x) 0 x false = Outcome.win := by
  have hdx' : d ≠ x := Nat.ne_of_lt hdx
  have hd' : d ∈ T.erase x := Finset.mem_erase.mpr ⟨hdx', hd⟩
  have hx' : x ∈ T.erase d := Finset.mem_erase.mpr ⟨hdx'.symm, hx⟩
  have hcomm : (T.erase x).erase d = (T.erase d).erase x := Finset.erase_right_comm
  have hneA : T.erase d ≠ ∅ := Finset.ne_empty_of_mem hx'
  have hprA : ¬ 0 + ∑ y ∈ T.erase d, y < d := by
    have hle : x ≤ ∑ y ∈ T.erase d, y :=
      Finset.single_le_sum (f := fun y => y) (fun _ _ => Nat.zero_le _) hx'
    omega
  have hE : valueAux ((T.erase d).erase x) d x false = Outcome.win := by
    rw [valueAux_eq _ _ _ hneA hprA, best_eq_loss_iff] at hA
    have h := hA _ (opt_mem (T.erase d) 0 d x hx')
    have hge : 0 + x ≥ d := by omega
    rw [if_pos hge, Nat.zero_add, neg_eq_loss_iff] at h
    exact h
  have hneB : T.erase x ≠ ∅ := Finset.ne_empty_of_mem hd'
  have hprB : ¬ 0 + ∑ y ∈ T.erase x, y < x := by
    intro hpr
    have hsum : d + ∑ y ∈ (T.erase x).erase d, y = ∑ y ∈ T.erase x, y :=
      Finset.add_sum_erase (T.erase x) (fun y => y) hd'
    have hl : valueAux ((T.erase x).erase d) d x false = Outcome.loss := by
      apply valueAux_pruned
      omega
    rw [hcomm, hE] at hl
    exact absurd hl (by simp)
  rw [valueAux_eq _ _ _ hneB hprB, best_eq_win_iff]
  have h := opt_mem (T.erase x) 0 x d hd'
  have hlt : ¬ 0 + d ≥ x := by omega
  rw [if_neg hlt, Nat.zero_add, hcomm, hE] at h
  exact h

/-- The value of a position that is not the first move depends only on the difference of the
scores. -/
lemma valueAux_shift (c : ℕ) : ∀ (n : ℕ) (R : Finset ℕ), R.card = n → ∀ sm so : ℕ,
    valueAux R (sm + c) (so + c) false = valueAux R sm so false := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro R hR sm so
    by_cases hne : R = ∅
    · subst hne
      rw [valueAux, valueAux]
      simp
    · by_cases hs : sm + ∑ y ∈ R, y < so
      · rw [valueAux_pruned R sm so hs, valueAux_pruned R (sm + c) (so + c) (by omega)]
      · rw [valueAux_eq R sm so hne hs, valueAux_eq R (sm + c) (so + c) hne (by omega)]
        congr 1
        apply List.map_congr_left
        intro y _
        have hcard : (R.erase (y : ℕ)).card < n := by
          rw [← hR]; exact Finset.card_erase_lt_of_mem y.2
        have e1 : sm + c + (y : ℕ) = (sm + (y : ℕ)) + c := by omega
        by_cases hge : sm + (y : ℕ) ≥ so
        · have hge' : sm + c + (y : ℕ) ≥ so + c := by omega
          rw [if_pos hge, if_pos hge', e1, ih _ hcard _ rfl so (sm + (y : ℕ))]
        · have hge' : ¬ sm + c + (y : ℕ) ≥ so + c := by omega
          rw [if_neg hge, if_neg hge', e1, ih _ hcard _ rfl (sm + (y : ℕ)) so]

/-- Unfolding of the first move on a nonempty set. -/
lemma value_eq (T : Finset ℕ) (hne : T ≠ ∅) :
    value T = Outcome.best (List.map (fun y : {y // y ∈ T} =>
        (valueAux (T.erase (y : ℕ)) 0 (0 + (y : ℕ)) false).neg) T.attach.toList) := by
  have hpr : ¬ 0 + ∑ y ∈ T, y < 0 := by omega
  unfold value
  rw [valueAux]
  simp only [if_true]
  rw [if_neg hne, if_neg hpr]

/-- If no opening loses for the second player and some opening does not win for him, the game is a
draw. -/
lemma value_eq_draw (T : Finset ℕ) (x : ℕ) (hx : x ∈ T)
    (hall : ∀ z ∈ T, valueAux (T.erase z) 0 z false ≠ Outcome.loss)
    (hw : valueAux (T.erase x) 0 x false ≠ Outcome.win) : value T = Outcome.draw := by
  have hne : T ≠ ∅ := Finset.ne_empty_of_mem hx
  rw [value_eq T hne]
  have hnw : ¬ Outcome.best (List.map (fun y : {y // y ∈ T} =>
      (valueAux (T.erase (y : ℕ)) 0 (0 + (y : ℕ)) false).neg) T.attach.toList) = Outcome.win := by
    rw [best_eq_win_iff]
    intro hmem
    obtain ⟨⟨y, hy⟩, -, hyv⟩ := List.mem_map.mp hmem
    rw [neg_eq_win_iff, Nat.zero_add] at hyv
    exact hall y hy hyv
  have hnl : ¬ Outcome.best (List.map (fun y : {y // y ∈ T} =>
      (valueAux (T.erase (y : ℕ)) 0 (0 + (y : ℕ)) false).neg) T.attach.toList) = Outcome.loss := by
    rw [best_eq_loss_iff]
    intro hl
    have hmem : (valueAux (T.erase x) 0 (0 + x) false).neg ∈
        List.map (fun y : {y // y ∈ T} =>
          (valueAux (T.erase (y : ℕ)) 0 (0 + (y : ℕ)) false).neg) T.attach.toList :=
      List.mem_map.mpr ⟨⟨x, hx⟩, by simp, rfl⟩
    have h := hl _ hmem
    rw [neg_eq_loss_iff, Nat.zero_add] at h
    exact hw h
  generalize Outcome.best (List.map (fun y : {y // y ∈ T} =>
      (valueAux (T.erase (y : ℕ)) 0 (0 + (y : ℕ)) false).neg) T.attach.toList) = v at hnw hnl ⊢
  cases v
  · exact absurd rfl hnw
  · exact absurd rfl hnl
  · rfl

/-- One opening that leads to an exactly drawn position makes the whole game a draw. -/
lemma value_eq_draw_of_opening (T : Finset ℕ) (x : ℕ) (hx : x ∈ T)
    (hw : valueAux (T.erase x) 0 x false ≠ Outcome.win)
    (hl : valueAux (T.erase x) 0 x false ≠ Outcome.loss) : value T = Outcome.draw := by
  refine value_eq_draw T x hx ?_ hw
  intro z hz hzl
  rcases Nat.lt_trichotomy z x with h | h | h
  · exact hw (swap' T z x hz hx h hzl)
  · subst h; exact hl hzl
  · exact hw (swap T x z hx hz h hzl)

/-- Two different openings that are safe for the first player make the game a draw. -/
lemma value_eq_draw_of_two_safe (T : Finset ℕ) (x y : ℕ) (hx : x ∈ T) (hy : y ∈ T) (hxy : x < y)
    (hwx : valueAux (T.erase x) 0 x false ≠ Outcome.win)
    (hwy : valueAux (T.erase y) 0 y false ≠ Outcome.win) : value T = Outcome.draw := by
  refine value_eq_draw_of_opening T x hx hwx ?_
  intro hlx
  exact hwy (swap' T x y hx hy hxy hlx)

theorem main : H1 → H2 → type_of% @CatchUp.value_of_even_mul_succ_self_div_two := by
  intro h1 h2 N h_even
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hempty : Finset.Icc 1 0 = (∅ : Finset ℕ) := by decide
    rw [hempty]
    unfold value
    rw [valueAux]
    simp
  · exact value_eq_draw_of_opening (Finset.Icc 1 N) 1 (Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩)
      (h1 N h_even hN) (h2 N h_even hN)

end OMA.R_CatchUp_value_of_even_mul_succ_self_div_two_R2
