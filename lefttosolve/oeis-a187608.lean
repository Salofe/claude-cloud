import OMAStatements.S_oeis_a187608
import Mathlib

/-!
Proof for A187608. The moves are `{-1, 2} × {-1, 2}`, so the column path and the row path of a
tour are independent one-dimensional paths with steps `-1` or `+2`. Steps over one or two moves
never cancel in a coordinate, so the only possible coincidence of squares is between the first
and the last square, which happens exactly when both coordinate paths return to their start.
Hence `a n = S n ^ 2 - R n ^ 2`, where `S n` counts the one-dimensional paths of 3 steps inside
a line of `n` positions and `R n` the returning ones. A path is a start position and a word of
3 steps, and the starts that keep a fixed word inside the line form an interval, which gives
`S n = Σ_w (n - span w)` and `R n = 3 (n - 2)`.
-/

namespace OMA.Helpers

open OMA.S_oeis_a187608 Finset

/-- A step: `+2` for `true` and `-1` for `false`. -/
def sd (b : Bool) : ℤ := if b then 2 else -1

/-- The positions reached by a word of three steps, relative to the start. -/
def off (w : Bool × Bool × Bool) : Fin 4 → ℤ :=
  ![0, sd w.1, sd w.1 + sd w.2.1, sd w.1 + sd w.2.1 + sd w.2.2]

/-- A one-dimensional path of three steps `-1` or `+2`. -/
def Step {n : ℕ} (q : Fin 4 → Fin n) : Prop :=
  (((q 1 : ℤ) - q 0 = -1 ∨ (q 1 : ℤ) - q 0 = 2) ∧
    ((q 2 : ℤ) - q 1 = -1 ∨ (q 2 : ℤ) - q 1 = 2) ∧
    ((q 3 : ℤ) - q 2 = -1 ∨ (q 3 : ℤ) - q 2 = 2))

instance decStep {n : ℕ} : DecidablePred (@Step n) := fun q => by
  unfold Step; infer_instance

/-- The word of a path. -/
def word {n : ℕ} (q : Fin 4 → Fin n) : Bool × Bool × Bool :=
  (decide ((q 1 : ℤ) - q 0 = 2), decide ((q 2 : ℤ) - q 1 = 2), decide ((q 3 : ℤ) - q 2 = 2))

theorem pos_eq {n : ℕ} (q : Fin 4 → Fin n) (h : Step q) (k : Fin 4) :
    (q k : ℤ) = q 0 + off (word q) k := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    fin_cases k <;> simp [off, word, sd, h1, h2, h3] <;> omega

/-- The starts that keep the word `w` inside a line of `n` positions. -/
def win (n : ℕ) (w : Bool × Bool × Bool) : Finset (Fin n) :=
  univ.filter (fun s : Fin n => ∀ k, 0 ≤ (s : ℤ) + off w k ∧ (s : ℤ) + off w k < n)

theorem fiber_card (n : ℕ) (w : Bool × Bool × Bool) :
    (univ.filter (fun q : Fin 4 → Fin n => Step q ∧ word q = w)).card = (win n w).card := by
  refine Finset.card_bij (fun q _ => q 0) ?_ ?_ ?_
  · intro q hq
    simp only [mem_filter, mem_univ, true_and] at hq
    simp only [win, mem_filter, mem_univ, true_and]
    intro k
    have e := pos_eq q hq.1 k
    rw [hq.2] at e
    have := (q k).isLt
    omega
  · intro q hq q' hq' h0
    simp only [mem_filter, mem_univ, true_and] at hq hq'
    funext k
    have e := pos_eq q hq.1 k
    have e' := pos_eq q' hq'.1 k
    rw [hq.2] at e
    rw [hq'.2] at e'
    rw [h0] at e
    apply Fin.ext
    omega
  · intro s hs
    simp only [win, mem_filter, mem_univ, true_and] at hs
    let q : Fin 4 → Fin n := fun k => ⟨((s : ℤ) + off w k).toNat, by have := hs k; omega⟩
    have hq : ∀ k, ((q k : ℕ) : ℤ) = (s : ℤ) + off w k := by
      intro k
      have := hs k
      simp only [q]
      omega
    refine ⟨q, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      have e1 := hq 1
      have e2 := hq 2
      have e3 := hq 3
      have e0 := hq 0
      obtain ⟨b1, b2, b3⟩ := w
      simp only [off, Matrix.cons_val, sd] at e0 e1 e2 e3
      refine ⟨?_, ?_⟩
      · unfold Step
        cases b1 <;> cases b2 <;> cases b3 <;> simp at e0 e1 e2 e3 <;> omega
      · unfold word
        cases b1 <;> cases b2 <;> cases b3 <;> simp at e0 e1 e2 e3 <;> simp <;> omega
    · apply Fin.ext
      have := hq 0
      simp [off] at this
      omega

theorem card_window (n lo hi : ℕ) (P : Fin n → Prop) [DecidablePred P]
    (hP : ∀ s : Fin n, P s ↔ lo ≤ s.val ∧ s.val + hi < n) :
    (univ.filter P).card = n - (lo + hi) := by
  rw [← card_map Fin.valEmbedding]
  have : (univ.filter P).map Fin.valEmbedding = Ico lo (n - hi) := by
    ext t
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [hP] at hs
      omega
    · intro ht
      exact ⟨⟨t, by omega⟩, (hP _).2 (by simp only; omega), rfl⟩
  rw [this, Nat.card_Ico]
  omega

theorem win_card (n : ℕ) (w : Bool × Bool × Bool) (lo hi : ℕ)
    (h : ∀ s : Fin n, (∀ k, 0 ≤ (s : ℤ) + off w k ∧ (s : ℤ) + off w k < n) ↔
      lo ≤ s.val ∧ s.val + hi < n) : (win n w).card = n - (lo + hi) :=
  card_window n lo hi _ h

theorem count_words (n : ℕ) (P : Bool × Bool × Bool → Prop) [DecidablePred P] :
    (univ.filter (fun q : Fin 4 → Fin n => Step q ∧ P (word q))).card =
      ∑ w ∈ univ.filter P, (win n w).card := by
  rw [card_eq_sum_card_fiberwise (f := word) (t := univ.filter P)]
  · refine Finset.sum_congr rfl ?_
    intro w hw
    rw [← fiber_card]
    congr 1
    ext q
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hw⟩, h3⟩
  · intro q hq
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hq ⊢
    exact hq.2

/-- The number of one-dimensional paths. -/
def Sn (n : ℕ) : ℕ :=
  (n - 3) + (n - 2) + (n - 2) + (n - 4) + (n - 2) + (n - 3) + (n - 4) + (n - 6)

theorem S_card (n : ℕ) : (univ.filter (fun q : Fin 4 → Fin n => Step q)).card = Sn n := by
  have := count_words n (fun _ => True)
  simp only [and_true] at this
  rw [this, Finset.filter_true_of_mem (fun _ _ => trivial)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [win_card n (true, true, true) 0 6 (by intro s; simp [Fin.forall_fin_succ, off, sd]; omega),
    win_card n (true, true, false) 0 4 (by intro s; simp [Fin.forall_fin_succ, off, sd]; omega),
    win_card n (true, false, true) 0 3 (by intro s; simp [Fin.forall_fin_succ, off, sd]; omega),
    win_card n (true, false, false) 0 2 (by intro s; simp [Fin.forall_fin_succ, off, sd]; omega),
    win_card n (false, true, true) 1 3 (by intro s; simp [Fin.forall_fin_succ, off, sd]; omega),
    win_card n (false, true, false) 1 1 (by intro s; simp [Fin.forall_fin_succ, off, sd]; omega),
    win_card n (false, false, true) 2 0 (by intro s; simp [Fin.forall_fin_succ, off, sd]; omega),
    win_card n (false, false, false) 3 0 (by intro s; simp [Fin.forall_fin_succ, off, sd]; omega)]
  unfold Sn
  omega

theorem R_card (n : ℕ) :
    (univ.filter (fun q : Fin 4 → Fin n => Step q ∧ q 0 = q 3)).card = 3 * (n - 2) := by
  have e : univ.filter (fun q : Fin 4 → Fin n => Step q ∧ q 0 = q 3) =
      univ.filter (fun q : Fin 4 → Fin n => Step q ∧ off (word q) 3 = 0) := by
    ext q
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have := pos_eq q h1 3
      rw [← h2] at this
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have := pos_eq q h1 3
      apply Fin.ext
      omega
  rw [e, count_words n (fun w => off w 3 = 0), Finset.sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [off, sd, Matrix.cons_val, if_true, if_false, Bool.false_eq_true]
  norm_num
  rw [win_card n (false, true, false) 1 1 (by intro s; simp [Fin.forall_fin_succ, off, sd]; omega),
    win_card n (false, false, true) 2 0 (by intro s; simp [Fin.forall_fin_succ, off, sd]; omega),
    win_card n (true, false, false) 0 2 (by intro s; simp [Fin.forall_fin_succ, off, sd]; omega)]
  omega

theorem moves_iff (d : ℤ × ℤ) : d ∈ moves ↔ ((d.1 = -1 ∨ d.1 = 2) ∧ (d.2 = -1 ∨ d.2 = 2)) := by
  obtain ⟨x, y⟩ := d
  simp only [moves, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  omega

theorem tour_iff {n : ℕ} (p : Fin 4 → Fin n × Fin n) :
    IsTour n 4 p ↔ Step (fun k => (p k).1) ∧ Step (fun k => (p k).2) ∧
      ¬ ((p 0).1 = (p 3).1 ∧ (p 0).2 = (p 3).2) := by
  unfold IsTour Step
  constructor
  · rintro ⟨hinj, hm⟩
    have h01 := hm 0 1 rfl
    have h12 := hm 1 2 rfl
    have h23 := hm 2 3 rfl
    rw [moves_iff] at h01 h12 h23
    simp only [OMA.S_oeis_a187608.toZ, Prod.fst_sub, Prod.snd_sub] at h01 h12 h23
    refine ⟨⟨h01.1, h12.1, h23.1⟩, ⟨h01.2, h12.2, h23.2⟩, ?_⟩
    rintro ⟨e1, e2⟩
    have := hinj (Prod.ext e1 e2)
    exact absurd this (by decide)
  · rintro ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, hne⟩
    dsimp only at a1 a2 a3 b1 b2 b3
    have hne' : ¬ (((p 0).1 : ℤ) = (p 3).1 ∧ ((p 0).2 : ℤ) = (p 3).2) := fun h =>
      hne ⟨Fin.ext (by exact_mod_cast h.1), Fin.ext (by exact_mod_cast h.2)⟩
    refine ⟨?_, ?_⟩
    · intro i j hij
      have hx : (((p i).1 : ℕ) : ℤ) = (((p j).1 : ℕ) : ℤ) := by rw [hij]
      have hy : (((p i).2 : ℕ) : ℤ) = (((p j).2 : ℕ) : ℤ) := by rw [hij]
      fin_cases i <;> fin_cases j <;> simp at hx hy ⊢ <;> omega
    · intro i j hj
      rw [moves_iff]
      fin_cases i <;> fin_cases j <;> simp at hj <;> simp only [OMA.S_oeis_a187608.toZ, Prod.fst_sub, Prod.snd_sub] <;>
        simp <;> omega

theorem a_form (n : ℕ) : a n = Sn n * Sn n - 3 * (n - 2) * (3 * (n - 2)) := by
  set S := univ.filter (fun q : Fin 4 → Fin n => Step q) with hS
  set R := univ.filter (fun q : Fin 4 → Fin n => Step q ∧ q 0 = q 3) with hR
  have h1 : a n = (univ.filter (fun pq : (Fin 4 → Fin n) × (Fin 4 → Fin n) =>
      Step pq.1 ∧ Step pq.2 ∧ ¬ (pq.1 0 = pq.1 3 ∧ pq.2 0 = pq.2 3))).card := by
    unfold a
    refine Finset.card_equiv (Equiv.arrowProdEquivProdArrow (Fin 4) (fun _ => Fin n)
      (fun _ => Fin n)) ?_
    intro p
    simp only [mem_filter, mem_univ, true_and]
    rw [tour_iff]
    rfl
  have h2 : univ.filter (fun pq : (Fin 4 → Fin n) × (Fin 4 → Fin n) =>
      Step pq.1 ∧ Step pq.2 ∧ ¬ (pq.1 0 = pq.1 3 ∧ pq.2 0 = pq.2 3)) = S ×ˢ S \ R ×ˢ R := by
    ext ⟨p, q⟩
    simp only [hS, hR, mem_filter, mem_univ, true_and, mem_sdiff, mem_product]
    tauto
  have hRS : R ⊆ S := by
    intro q hq
    simp only [hS, hR, mem_filter, mem_univ, true_and] at hq ⊢
    exact hq.1
  rw [h1, h2, card_sdiff_of_subset (product_subset_product hRS hRS), card_product, card_product,
    hS, hR, S_card, R_card]

theorem a_big (m : ℕ) : a (m + 6) = 55 * m ^ 2 + 280 * m + 340 := by
  rw [a_form]
  have e1 : Sn (m + 6) = 8 * m + 22 := by unfold Sn; omega
  have e2 : 3 * (m + 6 - 2) = 3 * m + 12 := by omega
  rw [e1, e2]
  apply Nat.sub_eq_of_eq_add
  ring

theorem a_bigZ (n : ℕ) (hn : 5 < n) : (a n : ℤ) = 55 * n ^ 2 - 380 * n + 640 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [a_big]
  push_cast
  ring

theorem a_small : a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0 ∧ a 4 = 28 ∧ a 5 = 144 := by
  simp only [a_form, Sn]
  norm_num

theorem recurrence (n : ℕ) (hn : 8 < n) :
    (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  rw [a_bigZ n (by omega), a_bigZ (n - 1) (by omega), a_bigZ (n - 2) (by omega),
    a_bigZ (n - 3) (by omega)]
  push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega]
  ring

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 =
      PowerSeries.X ^ 4 * (28 + 60 * PowerSeries.X - 8 * PowerSeries.X ^ 2 +
        59 * PowerSeries.X ^ 3 - 29 * PowerSeries.X ^ 4) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℤ)) with hA
  have hcube : ((1 : ℤ⟦X⟧) - X) ^ 3 =
      1 - X ^ 1 - X ^ 1 - X ^ 1 + X ^ 2 + X ^ 2 + X ^ 2 - X ^ 3 := by
    ring
  have hrhs : (X : ℤ⟦X⟧) ^ 4 * (28 + 60 * X - 8 * X ^ 2 + 59 * X ^ 3 - 29 * X ^ 4) =
      C (28 : ℤ) * X ^ 4 + C (60 : ℤ) * X ^ 5 - C (8 : ℤ) * X ^ 6 + C (59 : ℤ) * X ^ 7 -
        C (29 : ℤ) * X ^ 8 := by
    simp only [map_ofNat]
    ring
  rw [hcube, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mul_X_pow', hA, coeff_mk]
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := a_small
  have b6 : (a 6 : ℤ) = 340 := by rw [a_bigZ 6 (by omega)]; norm_num
  have b7 : (a 7 : ℤ) = 675 := by rw [a_bigZ 7 (by omega)]; norm_num
  have b8 : (a 8 : ℤ) = 1120 := by rw [a_bigZ 8 (by omega)]; norm_num
  have hbig := a_bigZ
  generalize a = b at s0 s1 s2 s3 s4 s5 b6 b7 b8 hbig ⊢
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  · simp [s0]
  · simp [s0, s1]
  · simp [s0, s1, s2]
  · simp [s0, s1, s2, s3]
  · simp [s0, s1, s2, s3, s4]
  · simp [s1, s2, s3, s4, s5]
  · norm_num [s2, s3, s4, s5, b6]
  · norm_num [s3, s4, s5, b6, b7]
  · norm_num [s4, s5, b6, b7, b8]
  · simp only [show 1 ≤ j + 9 by omega, show 2 ≤ j + 9 by omega, show 3 ≤ j + 9 by omega,
      show j + 9 - 1 = j + 8 by omega, show j + 9 - 2 = j + 7 by omega,
      show j + 9 - 3 = j + 6 by omega,
      show ¬ (j + 9 = 4) by omega, show ¬ (j + 9 = 5) by omega, show ¬ (j + 9 = 6) by omega,
      show ¬ (j + 9 = 7) by omega, show ¬ (j + 9 = 8) by omega, if_true, if_false]
    rw [hbig (j + 9) (by omega), hbig (j + 8) (by omega), hbig (j + 7) (by omega),
      hbig (j + 6) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a187608.main :=
  ⟨OMA.Helpers.a_bigZ, OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
