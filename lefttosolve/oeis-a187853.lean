import OMAStatements.S_oeis_a187853

/-!
Proof of Barker's conjectures for A187853 (5-step king-knight's tours on an n X n board).

A tour is its first square `s` together with its four moves, each one of the 16 king-knight
displacements (`mvK`). Conversely a first square and a move tuple give a tour exactly when the
five positions `0, P1, P2, P3, P4` reached by the moves (`pos`) are pairwise distinct and all the
squares `s + Pt` lie on the board. If the rows of the positions range over an interval of
length `w` and their columns over one of length `h` (maximum minus minimum), the admissible first
squares form a `(n - w) × (n - h)` rectangle (truncated subtraction). Hence
`a n = Σ_m [m self-avoiding] (n - w m) (n - h m)` over the `16 ^ 4` move tuples `m`.

The kernel evaluates this finite sum once, with the summand recording `1`, `w + h`, `w h` and
`(t - w)(t - h)` for `t = 1, ..., 7`. Since every span is at most 8, for `n ≥ 8` this gives
`a n = 50128 n^2 - 312688 n + 476944`, and it gives `a 1, ..., a 7` directly. The recurrence
(for `n > 10`) and the generating function follow by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a187853 Finset

/-- A move tuple: four indices into the list `mvK` of king-knight displacements. -/
abbrev MT := Fin 16 × Fin 16 × Fin 16 × Fin 16

/-- The 16 king-knight displacements: the 8 king moves, then the 8 knight moves. -/
def mvK : Fin 16 → ℤ × ℤ := ![(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0),
  (1, 1), (-2, -1), (-2, 1), (-1, -2), (-1, 2), (1, -2), (1, 2), (2, -1), (2, 1)]

theorem mvK_injective : Function.Injective mvK := by
  decide +kernel

/-- The displacement of a king-knight move. -/
def KKD (d : ℤ × ℤ) : Prop :=
  (d.1.natAbs ≤ 1 ∧ d.2.natAbs ≤ 1 ∧ d ≠ 0) ∨ (d.1.natAbs = 1 ∧ d.2.natAbs = 2) ∨
    (d.1.natAbs = 2 ∧ d.2.natAbs = 1)

theorem mvK_kkd (j : Fin 16) : KKD (mvK j) := by
  unfold KKD
  revert j
  decide +kernel

theorem kkd_exists (d : ℤ × ℤ) (h : KKD d) : ∃ j, mvK j = d := by
  obtain ⟨x, y⟩ := d
  simp only [KKD, ne_eq, Prod.mk_eq_zero] at h
  have hx : x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 := by omega
  have hy : y = -2 ∨ y = -1 ∨ y = 0 ∨ y = 1 ∨ y = 2 := by omega
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl | rfl <;>
    first | (exfalso; omega) | decide

/-- A king-knight move on the `n × n` board, as a relation between squares. -/
def KKMove {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  (((p.1 : ℤ) - q.1).natAbs ≤ 1 ∧ ((p.2 : ℤ) - q.2).natAbs ≤ 1 ∧ p ≠ q) ∨
    (((p.1 : ℤ) - q.1).natAbs = 1 ∧ ((p.2 : ℤ) - q.2).natAbs = 2) ∨
    (((p.1 : ℤ) - q.1).natAbs = 2 ∧ ((p.2 : ℤ) - q.2).natAbs = 1)

/-- A 5-step tour, with the moves described by `KKMove`. -/
def TourK {n : ℕ} (w : Fin 5 → Fin n × Fin n) : Prop :=
  Function.Injective w ∧ ∀ i : Fin 4, KKMove (w i.castSucc) (w i.succ)

/-- The list of moves of the statement is the set of king-knight displacements. -/
theorem mem_moves_iff (d : ℤ × ℤ) : d ∈ moves ↔ KKD d := by
  obtain ⟨x, y⟩ := d
  constructor
  · intro h
    simp only [moves, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (unfold KKD; decide)
  · intro h
    simp only [KKD, ne_eq, Prod.mk_eq_zero] at h
    have hx : x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 := by omega
    have hy : y = -2 ∨ y = -1 ∨ y = 0 ∨ y = 1 ∨ y = 2 := by omega
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl | rfl <;>
      first | (exfalso; omega) | decide

theorem toZ_injective {n : ℕ} : Function.Injective (S_oeis_a187853.toZ : Fin n × Fin n → ℤ × ℤ) := by
  intro p q h
  simp only [S_oeis_a187853.toZ, Prod.mk.injEq, Nat.cast_inj] at h
  exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

theorem kkMove_iff {n : ℕ} (p q : Fin n × Fin n) : KKMove p q ↔ KKD (S_oeis_a187853.toZ q - S_oeis_a187853.toZ p) := by
  simp only [KKMove, KKD, S_oeis_a187853.toZ, Prod.fst_sub, Prod.snd_sub, ne_eq, Prod.ext_iff, Fin.ext_iff,
    Prod.fst_zero, Prod.snd_zero]
  omega

theorem isTour_iff {n : ℕ} (w : Fin 5 → Fin n × Fin n) : IsTour n 5 w ↔ TourK w := by
  unfold IsTour TourK
  refine and_congr Iff.rfl ⟨fun h i => ?_, fun h i j hij => ?_⟩
  · rw [kkMove_iff, ← mem_moves_iff]
    exact h i.castSucc i.succ (by simp)
  · rw [mem_moves_iff]
    have hi : i.val < 4 := by omega
    have e1 : i = (⟨i.val, hi⟩ : Fin 4).castSucc := Fin.ext rfl
    have e2 : j = (⟨i.val, hi⟩ : Fin 4).succ := Fin.ext (by simp [hij])
    rw [e1, e2, ← kkMove_iff]
    exact h _

/-- The five positions visited by the moves of a move tuple, starting from `0`. -/
def pos (m : MT) : Fin 5 → ℤ × ℤ :=
  ![0, mvK m.1, mvK m.1 + mvK m.2.1, mvK m.1 + mvK m.2.1 + mvK m.2.2.1,
    mvK m.1 + mvK m.2.1 + mvK m.2.2.1 + mvK m.2.2.2]

theorem pos0 (m : MT) : pos m 0 = 0 := rfl
theorem pos1 (m : MT) : pos m 1 = mvK m.1 := rfl
theorem pos2 (m : MT) : pos m 2 = mvK m.1 + mvK m.2.1 := rfl
theorem pos3 (m : MT) : pos m 3 = mvK m.1 + mvK m.2.1 + mvK m.2.2.1 := rfl
theorem pos4 (m : MT) : pos m 4 = mvK m.1 + mvK m.2.1 + mvK m.2.2.1 + mvK m.2.2.2 := rfl

/-- The four moves of a move tuple, by step. -/
def mvAt (m : MT) : Fin 4 → Fin 16 := ![m.1, m.2.1, m.2.2.1, m.2.2.2]

theorem pos_step (m : MT) (i : Fin 4) : pos m i.succ - pos m i.castSucc = mvK (mvAt m i) := by
  fin_cases i <;> simp [pos, mvAt]

/-- A point of `ℤ × ℤ` lies on the `n × n` board. -/
abbrev InB (n : ℕ) (x : ℤ × ℤ) : Prop := 0 ≤ x.1 ∧ x.1 < n ∧ 0 ≤ x.2 ∧ x.2 < n

/-- A point of `ℤ × ℤ` as a square of the `(k + 1) × (k + 1)` board (meaningful on the board). -/
def ofZ (k : ℕ) (x : ℤ × ℤ) : Fin (k + 1) × Fin (k + 1) :=
  (⟨x.1.toNat % (k + 1), Nat.mod_lt _ k.succ_pos⟩, ⟨x.2.toNat % (k + 1), Nat.mod_lt _ k.succ_pos⟩)

theorem toZ_ofZ {k : ℕ} {x : ℤ × ℤ} (h : InB (k + 1) x) : S_oeis_a187853.toZ (ofZ k x) = x := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e1 : x.1.toNat % (k + 1) = x.1.toNat := Nat.mod_eq_of_lt (by omega)
  have e2 : x.2.toNat % (k + 1) = x.2.toNat := Nat.mod_eq_of_lt (by omega)
  refine Prod.ext ?_ ?_
  · simp only [S_oeis_a187853.toZ, ofZ, e1]; omega
  · simp only [S_oeis_a187853.toZ, ofZ, e2]; omega

theorem ofZ_toZ {k : ℕ} (p : Fin (k + 1) × Fin (k + 1)) : ofZ k (S_oeis_a187853.toZ p) = p := by
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · simp only [ofZ, S_oeis_a187853.toZ, Int.toNat_natCast]; exact Nat.mod_eq_of_lt p.1.isLt
  · simp only [ofZ, S_oeis_a187853.toZ, Int.toNat_natCast]; exact Nat.mod_eq_of_lt p.2.isLt

theorem inB_toZ {n : ℕ} (p : Fin n × Fin n) : InB n (S_oeis_a187853.toZ p) := by
  have := p.1.isLt
  have := p.2.isLt
  simp only [InB, S_oeis_a187853.toZ]
  omega

/-- The index of a king-knight displacement in `mvK`. -/
noncomputable def dec : ℤ × ℤ → Fin 16 := Function.invFun mvK

theorem mvK_dec {d : ℤ × ℤ} (h : KKD d) : mvK (dec d) = d := Function.invFun_eq (kkd_exists d h)

theorem dec_mvK (j : Fin 16) : dec (mvK j) = j := Function.leftInverse_invFun mvK_injective j

/-- A tour as its first square and its move tuple. -/
noncomputable def tmap {n : ℕ} (w : Fin 5 → Fin n × Fin n) : (Fin n × Fin n) × MT :=
  (w 0, dec (S_oeis_a187853.toZ (w 1) - S_oeis_a187853.toZ (w 0)), dec (S_oeis_a187853.toZ (w 2) - S_oeis_a187853.toZ (w 1)), dec (S_oeis_a187853.toZ (w 3) - S_oeis_a187853.toZ (w 2)),
    dec (S_oeis_a187853.toZ (w 4) - S_oeis_a187853.toZ (w 3)))

/-- A first square and a move tuple as a sequence of five squares. -/
def smap (k : ℕ) (q : (Fin (k + 1) × Fin (k + 1)) × MT) : Fin 5 → Fin (k + 1) × Fin (k + 1) :=
  fun t => ofZ k (S_oeis_a187853.toZ q.1 + pos q.2 t)

/-- A statement about the five indices of `Fin 5`, one index at a time. -/
theorem fin5_forall {P : Fin 5 → Prop} : (∀ t, P t) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ t
    fin_cases t
    exacts [h0, h1, h2, h3, h4]

theorem pos_tmap {n : ℕ} {w : Fin 5 → Fin n × Fin n} (hw : TourK w) (t : Fin 5) :
    pos (tmap w).2 t = S_oeis_a187853.toZ (w t) - S_oeis_a187853.toZ (w 0) := by
  have e0 : mvK (dec (S_oeis_a187853.toZ (w 1) - S_oeis_a187853.toZ (w 0))) = S_oeis_a187853.toZ (w 1) - S_oeis_a187853.toZ (w 0) :=
    mvK_dec ((kkMove_iff _ _).1 (hw.2 0))
  have e1 : mvK (dec (S_oeis_a187853.toZ (w 2) - S_oeis_a187853.toZ (w 1))) = S_oeis_a187853.toZ (w 2) - S_oeis_a187853.toZ (w 1) :=
    mvK_dec ((kkMove_iff _ _).1 (hw.2 1))
  have e2 : mvK (dec (S_oeis_a187853.toZ (w 3) - S_oeis_a187853.toZ (w 2))) = S_oeis_a187853.toZ (w 3) - S_oeis_a187853.toZ (w 2) :=
    mvK_dec ((kkMove_iff _ _).1 (hw.2 2))
  have e3 : mvK (dec (S_oeis_a187853.toZ (w 4) - S_oeis_a187853.toZ (w 3))) = S_oeis_a187853.toZ (w 4) - S_oeis_a187853.toZ (w 3) :=
    mvK_dec ((kkMove_iff _ _).1 (hw.2 3))
  revert t
  rw [fin5_forall]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [pos0, sub_self]
  · simp only [tmap, pos1, e0]
  · simp only [tmap, pos2, e0, e1]; abel
  · simp only [tmap, pos3, e0, e1, e2]; abel
  · simp only [tmap, pos4, e0, e1, e2, e3]; abel

theorem card_tours (k : ℕ) :
    a (k + 1) = ∑ m : MT, if Function.Injective (pos m) then
      #(univ.filter (fun s : Fin (k + 1) × Fin (k + 1) => ∀ t, InB (k + 1) (S_oeis_a187853.toZ s + pos m t)))
      else 0 := by
  classical
  unfold a
  rw [Finset.filter_congr (fun w _ => isTour_iff w)]
  calc #(univ.filter fun w => TourK w)
      = #(univ.filter fun q : (Fin (k + 1) × Fin (k + 1)) × MT =>
          Function.Injective (pos q.2) ∧ ∀ t, InB (k + 1) (S_oeis_a187853.toZ q.1 + pos q.2 t)) := by
        apply Finset.card_nbij' tmap (smap k)
        · intro w hw
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          refine ⟨?_, fun t => ?_⟩
          · have hp : pos (tmap w).2 = fun t => S_oeis_a187853.toZ (w t) - S_oeis_a187853.toZ (w 0) := funext (pos_tmap hw)
            rw [hp]
            intro t t' h
            exact hw.1 (toZ_injective (sub_left_injective h))
          · rw [pos_tmap hw t]
            have e : S_oeis_a187853.toZ (tmap w).1 + (S_oeis_a187853.toZ (w t) - S_oeis_a187853.toZ (w 0)) = S_oeis_a187853.toZ (w t) := by
              simp only [tmap]; abel
            rw [e]
            exact inB_toZ _
        · rintro ⟨s, m⟩ hq
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
          obtain ⟨hinj, hfit⟩ := hq
          have hz : ∀ t, S_oeis_a187853.toZ (smap k (s, m) t) = S_oeis_a187853.toZ s + pos m t := fun t => toZ_ofZ (hfit t)
          refine ⟨fun t t' h => hinj ?_, fun i => ?_⟩
          · have h' := congrArg S_oeis_a187853.toZ h
            rw [hz, hz] at h'
            exact add_left_cancel h'
          · rw [kkMove_iff, hz, hz, add_sub_add_left_eq_sub, pos_step]
            exact mvK_kkd _
        · intro w hw
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hw
          funext t
          simp only [smap]
          rw [pos_tmap hw t]
          have e : S_oeis_a187853.toZ (tmap w).1 + (S_oeis_a187853.toZ (w t) - S_oeis_a187853.toZ (w 0)) = S_oeis_a187853.toZ (w t) := by
            simp only [tmap]; abel
          rw [e, ofZ_toZ]
        · rintro ⟨s, m⟩ hq
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq
          obtain ⟨hinj, hfit⟩ := hq
          have hz : ∀ t, S_oeis_a187853.toZ (smap k (s, m) t) = S_oeis_a187853.toZ s + pos m t := fun t => toZ_ofZ (hfit t)
          have hd : ∀ i : Fin 4, S_oeis_a187853.toZ (smap k (s, m) i.succ) - S_oeis_a187853.toZ (smap k (s, m) i.castSucc) =
              mvK (mvAt m i) := by
            intro i
            rw [hz, hz, add_sub_add_left_eq_sub, pos_step]
          have h0 : smap k (s, m) 0 = s := by
            simp only [smap]
            rw [pos0, add_zero, ofZ_toZ]
          have h1 : S_oeis_a187853.toZ (smap k (s, m) 1) - S_oeis_a187853.toZ (smap k (s, m) 0) = mvK m.1 := hd 0
          have h2 : S_oeis_a187853.toZ (smap k (s, m) 2) - S_oeis_a187853.toZ (smap k (s, m) 1) = mvK m.2.1 := hd 1
          have h3 : S_oeis_a187853.toZ (smap k (s, m) 3) - S_oeis_a187853.toZ (smap k (s, m) 2) = mvK m.2.2.1 := hd 2
          have h4 : S_oeis_a187853.toZ (smap k (s, m) 4) - S_oeis_a187853.toZ (smap k (s, m) 3) = mvK m.2.2.2 := hd 3
          simp only [tmap]
          rw [h1, h2, h3, h4, dec_mvK, dec_mvK, dec_mvK, dec_mvK, h0]
    _ = ∑ m : MT, if Function.Injective (pos m) then
          #(univ.filter (fun s : Fin (k + 1) × Fin (k + 1) => ∀ t, InB (k + 1) (S_oeis_a187853.toZ s + pos m t)))
          else 0 := by
        rw [Finset.card_filter, Fintype.sum_prod_type_right]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        by_cases hm : Function.Injective (pos m)
        · simp only [hm, true_and, if_true, Finset.card_filter]
        · simp only [hm, false_and, if_false, Finset.sum_const_zero]

/-- The span `max - min` of five integers. -/
def span5 (a b c d e : ℤ) : ℕ :=
  (max a (max b (max c (max d e))) - min a (min b (min c (min d e)))).toNat

/-- The positions `r` of a line of `n` positions from which the five offsets `x t` stay on the
line. -/
def line (n : ℕ) (x : Fin 5 → ℤ) : Finset (Fin n) :=
  univ.filter (fun r : Fin n => ∀ t, 0 ≤ ((r : ℕ) : ℤ) + x t ∧ ((r : ℕ) : ℤ) + x t < n)

theorem card_line (n : ℕ) (x : Fin 5 → ℤ) (h0 : x 0 = 0) :
    #(line n x) = n - span5 (x 0) (x 1) (x 2) (x 3) (x 4) := by
  set L := (-(min (x 0) (min (x 1) (min (x 2) (min (x 3) (x 4)))))).toNat with hL
  set R := (max (x 0) (max (x 1) (max (x 2) (max (x 3) (x 4))))).toNat with hR
  have key : line n x = univ.filter (fun r : Fin n => L ≤ (r : ℕ) ∧ (r : ℕ) + R < n) := by
    unfold line
    refine Finset.filter_congr (fun r _ => ?_)
    rw [fin5_forall]
    omega
  have e1 : (∑ r : Fin n, if L ≤ (r : ℕ) ∧ (r : ℕ) + R < n then 1 else 0) =
      ∑ v ∈ range n, if L ≤ v ∧ v + R < n then 1 else 0 :=
    Fin.sum_univ_eq_sum_range (fun v => if L ≤ v ∧ v + R < n then 1 else 0) n
  have e2 : (range n).filter (fun v => L ≤ v ∧ v + R < n) = Ico L (n - R) := by
    ext v
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [key, Finset.card_filter, e1, ← Finset.card_filter, e2, Nat.card_Ico]
  unfold span5
  omega

theorem card_fit (n : ℕ) (m : MT) :
    #(univ.filter (fun s : Fin n × Fin n => ∀ t, InB n (S_oeis_a187853.toZ s + pos m t))) =
      #(line n (fun t => (pos m t).1)) * #(line n (fun t => (pos m t).2)) := by
  rw [← Finset.card_product]
  congr 1
  unfold line
  rw [← Finset.filter_product, Finset.univ_product_univ]
  refine Finset.filter_congr (fun s _ => ?_)
  simp only [InB, S_oeis_a187853.toZ, Prod.fst_add, Prod.snd_add]
  constructor
  · intro h
    exact ⟨fun t => ⟨(h t).1, (h t).2.1⟩, fun t => ⟨(h t).2.2.1, (h t).2.2.2⟩⟩
  · intro h t
    exact ⟨(h.1 t).1, (h.1 t).2, (h.2 t).1, (h.2 t).2⟩

/-- The width of the bounding box of the positions of a move tuple. -/
def W (m : MT) : ℕ := span5 0 (pos m 1).1 (pos m 2).1 (pos m 3).1 (pos m 4).1

/-- The height of the bounding box of the positions of a move tuple. -/
def H (m : MT) : ℕ := span5 0 (pos m 1).2 (pos m 2).2 (pos m 3).2 (pos m 4).2

theorem a_succ (k : ℕ) : a (k + 1) = ∑ m : MT, if Function.Injective (pos m) then
    (k + 1 - W m) * (k + 1 - H m) else 0 := by
  rw [card_tours]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [card_fit, card_line (k + 1) (fun t => (pos m t).1) rfl,
    card_line (k + 1) (fun t => (pos m t).2) rfl]
  rfl

theorem injective5 {α : Type*} (f : Fin 5 → α) : Function.Injective f ↔
    (f 0 ≠ f 1 ∧ f 0 ≠ f 2 ∧ f 0 ≠ f 3 ∧ f 0 ≠ f 4 ∧ f 1 ≠ f 2 ∧ f 1 ≠ f 3 ∧ f 1 ≠ f 4 ∧
      f 2 ≠ f 3 ∧ f 2 ≠ f 4 ∧ f 3 ≠ f 4) := by
  constructor
  · intro h
    refine ⟨h.ne ?_, h.ne ?_, h.ne ?_, h.ne ?_, h.ne ?_, h.ne ?_, h.ne ?_, h.ne ?_, h.ne ?_,
      h.ne ?_⟩ <;> decide
  · rintro ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩ i j hij
    by_contra hne
    have key : ∀ i j : Fin 5, i ≠ j → f i ≠ f j := by
      rw [fin5_forall]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [fin5_forall] <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        intro hij' <;> first | exact absurd rfl hij' | assumption | exact Ne.symm ‹_›
    exact key i j hne hij

/-- The pairwise distinctness of five points, as a boolean. -/
def dist5 (p0 p1 p2 p3 p4 : ℤ × ℤ) : Bool :=
  decide (p0 ≠ p1) && decide (p0 ≠ p2) && decide (p0 ≠ p3) && decide (p0 ≠ p4) &&
    decide (p1 ≠ p2) && decide (p1 ≠ p3) && decide (p1 ≠ p4) && decide (p2 ≠ p3) &&
    decide (p2 ≠ p4) && decide (p3 ≠ p4)

/-- A move tuple is self-avoiding: its five positions are pairwise distinct. -/
def okB (m : MT) : Bool := dist5 0 (pos m 1) (pos m 2) (pos m 3) (pos m 4)

theorem inj_iff_ok (m : MT) : Function.Injective (pos m) ↔ okB m = true := by
  rw [injective5]
  simp only [okB, dist5, Bool.and_eq_true, decide_eq_true_eq, pos0, and_assoc]

/-- The number of tours of a move tuple on the `t × t` board. -/
def g (t : ℕ) (m : MT) : ℕ := if okB m = true then (t - W m) * (t - H m) else 0

theorem a_succ_eq (k : ℕ) : a (k + 1) = ∑ m : MT, g (k + 1) m := by
  rw [a_succ]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  unfold g
  by_cases h : Function.Injective (pos m)
  · rw [if_pos h, if_pos ((inj_iff_ok m).1 h)]
  · rw [if_neg h, if_neg (fun h' => h ((inj_iff_ok m).2 h'))]

/-- The summand computed by the kernel, written with explicit positions. -/
def leafK (a b c d : Fin 16) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let p1 := mvK a
  let p2 := p1 + mvK b
  let p3 := p2 + mvK c
  let p4 := p3 + mvK d
  if dist5 0 p1 p2 p3 p4 = true then
    let w := span5 0 p1.1 p2.1 p3.1 p4.1
    let h := span5 0 p1.2 p2.2 p3.2 p4.2
    (1, w + h, w * h, (1 - w) * (1 - h), (2 - w) * (2 - h), (3 - w) * (3 - h), (4 - w) * (4 - h),
      (5 - w) * (5 - h), (6 - w) * (6 - h), (7 - w) * (7 - h))
  else 0

/-- The same summand, in terms of `okB`, `W` and `H`. -/
def leafV (m : MT) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  if okB m = true then
    (1, W m + H m, W m * H m, (1 - W m) * (1 - H m), (2 - W m) * (2 - H m),
      (3 - W m) * (3 - H m), (4 - W m) * (4 - H m), (5 - W m) * (5 - H m), (6 - W m) * (6 - H m),
      (7 - W m) * (7 - H m))
  else 0

theorem leafK_eq (a b c d : Fin 16) : leafK a b c d = leafV (a, b, c, d) := rfl

def c0 (m : MT) : ℕ := if okB m = true then 1 else 0
def c1 (m : MT) : ℕ := if okB m = true then W m + H m else 0
def c2 (m : MT) : ℕ := if okB m = true then W m * H m else 0

theorem leafV_eq (m : MT) :
    leafV m = (c0 m, c1 m, c2 m, g 1 m, g 2 m, g 3 m, g 4 m, g 5 m, g 6 m, g 7 m) := by
  unfold leafV c0 c1 c2 g
  split_ifs <;> rfl

/-! ### The finite computation

The sum of `leafK` over all `16 ^ 4` move tuples, checked by the kernel. It is split by the first
move into 16 declarations, each over `16 ^ 3` move tuples, so that the kernel caches stay small. -/

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem leaf_part0 : (∑ b : Fin 16, ∑ c : Fin 16, ∑ d : Fin 16, leafK 0 b c d) =
    (3107, 18756, 27630, 0, 0, 376, 3436, 11935, 27004, 48581) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem leaf_part1 : (∑ b : Fin 16, ∑ c : Fin 16, ∑ d : Fin 16, leafK 1 b c d) =
    (3089, 17446, 23840, 0, 0, 564, 4410, 14115, 30400, 53079) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem leaf_part2 : (∑ b : Fin 16, ∑ c : Fin 16, ∑ d : Fin 16, leafK 2 b c d) =
    (3107, 18756, 27630, 0, 0, 376, 3436, 11935, 27004, 48581) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem leaf_part3 : (∑ b : Fin 16, ∑ c : Fin 16, ∑ d : Fin 16, leafK 3 b c d) =
    (3089, 17446, 23840, 0, 0, 564, 4410, 14115, 30400, 53079) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem leaf_part4 : (∑ b : Fin 16, ∑ c : Fin 16, ∑ d : Fin 16, leafK 4 b c d) =
    (3089, 17446, 23840, 0, 0, 564, 4410, 14115, 30400, 53079) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem leaf_part5 : (∑ b : Fin 16, ∑ c : Fin 16, ∑ d : Fin 16, leafK 5 b c d) =
    (3107, 18756, 27630, 0, 0, 376, 3436, 11935, 27004, 48581) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem leaf_part6 : (∑ b : Fin 16, ∑ c : Fin 16, ∑ d : Fin 16, leafK 6 b c d) =
    (3089, 17446, 23840, 0, 0, 564, 4410, 14115, 30400, 53079) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem leaf_part7 : (∑ b : Fin 16, ∑ c : Fin 16, ∑ d : Fin 16, leafK 7 b c d) =
    (3107, 18756, 27630, 0, 0, 376, 3436, 11935, 27004, 48581) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem leaf_part8 : (∑ b : Fin 16, ∑ c : Fin 16, ∑ d : Fin 16, leafK 8 b c d) =
    (3168, 20985, 33883, 0, 0, 196, 2299, 9105, 22304, 42257) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem leaf_part9 : (∑ b : Fin 16, ∑ c : Fin 16, ∑ d : Fin 16, leafK 9 b c d) =
    (3168, 20985, 33883, 0, 0, 196, 2299, 9105, 22304, 42257) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem leaf_part10 : (∑ b : Fin 16, ∑ c : Fin 16, ∑ d : Fin 16, leafK 10 b c d) =
    (3168, 20985, 33883, 0, 0, 196, 2299, 9105, 22304, 42257) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem leaf_part11 : (∑ b : Fin 16, ∑ c : Fin 16, ∑ d : Fin 16, leafK 11 b c d) =
    (3168, 20985, 33883, 0, 0, 196, 2299, 9105, 22304, 42257) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem leaf_part12 : (∑ b : Fin 16, ∑ c : Fin 16, ∑ d : Fin 16, leafK 12 b c d) =
    (3168, 20985, 33883, 0, 0, 196, 2299, 9105, 22304, 42257) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem leaf_part13 : (∑ b : Fin 16, ∑ c : Fin 16, ∑ d : Fin 16, leafK 13 b c d) =
    (3168, 20985, 33883, 0, 0, 196, 2299, 9105, 22304, 42257) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem leaf_part14 : (∑ b : Fin 16, ∑ c : Fin 16, ∑ d : Fin 16, leafK 14 b c d) =
    (3168, 20985, 33883, 0, 0, 196, 2299, 9105, 22304, 42257) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem leaf_part15 : (∑ b : Fin 16, ∑ c : Fin 16, ∑ d : Fin 16, leafK 15 b c d) =
    (3168, 20985, 33883, 0, 0, 196, 2299, 9105, 22304, 42257) := by
  decide +kernel

/-- The 16 partial sums, by first move. -/
def leafTbl : Fin 16 → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  ![(3107, 18756, 27630, 0, 0, 376, 3436, 11935, 27004, 48581),
    (3089, 17446, 23840, 0, 0, 564, 4410, 14115, 30400, 53079),
    (3107, 18756, 27630, 0, 0, 376, 3436, 11935, 27004, 48581),
    (3089, 17446, 23840, 0, 0, 564, 4410, 14115, 30400, 53079),
    (3089, 17446, 23840, 0, 0, 564, 4410, 14115, 30400, 53079),
    (3107, 18756, 27630, 0, 0, 376, 3436, 11935, 27004, 48581),
    (3089, 17446, 23840, 0, 0, 564, 4410, 14115, 30400, 53079),
    (3107, 18756, 27630, 0, 0, 376, 3436, 11935, 27004, 48581),
    (3168, 20985, 33883, 0, 0, 196, 2299, 9105, 22304, 42257),
    (3168, 20985, 33883, 0, 0, 196, 2299, 9105, 22304, 42257),
    (3168, 20985, 33883, 0, 0, 196, 2299, 9105, 22304, 42257),
    (3168, 20985, 33883, 0, 0, 196, 2299, 9105, 22304, 42257),
    (3168, 20985, 33883, 0, 0, 196, 2299, 9105, 22304, 42257),
    (3168, 20985, 33883, 0, 0, 196, 2299, 9105, 22304, 42257),
    (3168, 20985, 33883, 0, 0, 196, 2299, 9105, 22304, 42257),
    (3168, 20985, 33883, 0, 0, 196, 2299, 9105, 22304, 42257)]

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem leaf_total : (∑ a : Fin 16, ∑ b : Fin 16, ∑ c : Fin 16, ∑ d : Fin 16, leafK a b c d) =
    (50128, 312688, 476944, 0, 0, 5328, 49776, 177040, 408048, 744696) := by
  have h : ∀ a : Fin 16,
      (∑ b : Fin 16, ∑ c : Fin 16, ∑ d : Fin 16, leafK a b c d) = leafTbl a := by
    intro a
    fin_cases a
    exacts [leaf_part0, leaf_part1, leaf_part2, leaf_part3, leaf_part4, leaf_part5, leaf_part6,
      leaf_part7, leaf_part8, leaf_part9, leaf_part10, leaf_part11, leaf_part12, leaf_part13,
      leaf_part14, leaf_part15]
  rw [Finset.sum_congr rfl (fun a _ => h a)]
  decide +kernel

theorem leafV_total : ∑ m : MT, leafV m =
    (50128, 312688, 476944, 0, 0, 5328, 49776, 177040, 408048, 744696) := by
  rw [← leaf_total]
  simp only [Fintype.sum_prod_type, leafK_eq]

theorem sum_c0 : ∑ m : MT, c0 m = 50128 := by
  have h := congrArg (fun v => v.1) leafV_total
  simpa only [Prod.fst_sum, leafV_eq] using h

theorem sum_c1 : ∑ m : MT, c1 m = 312688 := by
  have h := congrArg (fun v => v.2.1) leafV_total
  simpa only [Prod.fst_sum, Prod.snd_sum, leafV_eq] using h

theorem sum_c2 : ∑ m : MT, c2 m = 476944 := by
  have h := congrArg (fun v => v.2.2.1) leafV_total
  simpa only [Prod.fst_sum, Prod.snd_sum, leafV_eq] using h

theorem sum_g1 : ∑ m : MT, g 1 m = 0 := by
  have h := congrArg (fun v => v.2.2.2.1) leafV_total
  simpa only [Prod.fst_sum, Prod.snd_sum, leafV_eq] using h

theorem sum_g2 : ∑ m : MT, g 2 m = 0 := by
  have h := congrArg (fun v => v.2.2.2.2.1) leafV_total
  simpa only [Prod.fst_sum, Prod.snd_sum, leafV_eq] using h

theorem sum_g3 : ∑ m : MT, g 3 m = 5328 := by
  have h := congrArg (fun v => v.2.2.2.2.2.1) leafV_total
  simpa only [Prod.fst_sum, Prod.snd_sum, leafV_eq] using h

theorem sum_g4 : ∑ m : MT, g 4 m = 49776 := by
  have h := congrArg (fun v => v.2.2.2.2.2.2.1) leafV_total
  simpa only [Prod.fst_sum, Prod.snd_sum, leafV_eq] using h

theorem sum_g5 : ∑ m : MT, g 5 m = 177040 := by
  have h := congrArg (fun v => v.2.2.2.2.2.2.2.1) leafV_total
  simpa only [Prod.fst_sum, Prod.snd_sum, leafV_eq] using h

theorem sum_g6 : ∑ m : MT, g 6 m = 408048 := by
  have h := congrArg (fun v => v.2.2.2.2.2.2.2.2.1) leafV_total
  simpa only [Prod.fst_sum, Prod.snd_sum, leafV_eq] using h

theorem sum_g7 : ∑ m : MT, g 7 m = 744696 := by
  have h := congrArg (fun v => v.2.2.2.2.2.2.2.2.2) leafV_total
  simpa only [Prod.fst_sum, Prod.snd_sum, leafV_eq] using h

theorem a_one : a 1 = 0 := (a_succ_eq 0).trans sum_g1
theorem a_two : a 2 = 0 := (a_succ_eq 1).trans sum_g2
theorem a_three : a 3 = 5328 := (a_succ_eq 2).trans sum_g3
theorem a_four : a 4 = 49776 := (a_succ_eq 3).trans sum_g4
theorem a_five : a 5 = 177040 := (a_succ_eq 4).trans sum_g5
theorem a_six : a 6 = 408048 := (a_succ_eq 5).trans sum_g6
theorem a_seven : a 7 = 744696 := (a_succ_eq 6).trans sum_g7

theorem mvK_bd (j : Fin 16) :
    -2 ≤ (mvK j).1 ∧ (mvK j).1 ≤ 2 ∧ -2 ≤ (mvK j).2 ∧ (mvK j).2 ≤ 2 := by
  revert j
  decide +kernel

theorem span5_le (x1 x2 x3 x4 : ℤ) (h1 : -2 ≤ x1 ∧ x1 ≤ 2) (h2 : -2 ≤ x2 - x1 ∧ x2 - x1 ≤ 2)
    (h3 : -2 ≤ x3 - x2 ∧ x3 - x2 ≤ 2) (h4 : -2 ≤ x4 - x3 ∧ x4 - x3 ≤ 2) :
    span5 0 x1 x2 x3 x4 ≤ 8 := by
  unfold span5
  omega

theorem W_le (m : MT) : W m ≤ 8 := by
  have ha := mvK_bd m.1
  have hb := mvK_bd m.2.1
  have hc := mvK_bd m.2.2.1
  have hd := mvK_bd m.2.2.2
  unfold W
  rw [pos1, pos2, pos3, pos4]
  simp only [Prod.fst_add]
  apply span5_le <;> omega

theorem H_le (m : MT) : H m ≤ 8 := by
  have ha := mvK_bd m.1
  have hb := mvK_bd m.2.1
  have hc := mvK_bd m.2.2.1
  have hd := mvK_bd m.2.2.2
  unfold H
  rw [pos1, pos2, pos3, pos4]
  simp only [Prod.snd_add]
  apply span5_le <;> omega

theorem a_closed (n : ℕ) (hn : 8 ≤ n) :
    (a n : ℤ) = 50128 * (n : ℤ) ^ 2 - 312688 * n + 476944 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hterm : ∀ m : MT, ((g (k + 1) m : ℕ) : ℤ) =
      ((k : ℤ) + 1) ^ 2 * (c0 m : ℤ) - ((k : ℤ) + 1) * (c1 m : ℤ) + (c2 m : ℤ) := by
    intro m
    have hW := W_le m
    have hH := H_le m
    unfold g c0 c1 c2
    split_ifs
    · push_cast [Nat.cast_sub (show W m ≤ k + 1 by omega),
        Nat.cast_sub (show H m ≤ k + 1 by omega)]
      ring
    · simp
  have e0 : ∑ m : MT, (c0 m : ℤ) = 50128 := by exact_mod_cast sum_c0
  have e1 : ∑ m : MT, (c1 m : ℤ) = 312688 := by exact_mod_cast sum_c1
  have e2 : ∑ m : MT, (c2 m : ℤ) = 476944 := by exact_mod_cast sum_c2
  rw [a_succ_eq, Nat.cast_sum, Finset.sum_congr rfl (fun m _ => hterm m), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e0, e1, e2]
  push_cast
  ring

theorem a_closedQ (n : ℕ) (hn : 8 ≤ n) :
    (a n : ℚ) = 50128 * (n : ℚ) ^ 2 - 312688 * n + 476944 := by
  have h := a_closed n hn
  exact_mod_cast h

theorem recurrence (n : ℕ) (hn : 10 < n) :
    (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  rw [a_closed n (by omega), a_closed (n - 1) (by omega), a_closed (n - 2) (by omega),
    a_closed (n - 3) (by omega)]
  push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega]
  ring

theorem a_zero : a 0 = 0 := by
  unfold a
  simp

open PowerSeries in
theorem gen_fun_aux (f : ℕ → ℤ) (h0 : f 0 = 0) (h1 : f 1 = 0) (h2 : f 2 = 0) (h3 : f 3 = 5328)
    (h4 : f 4 = 49776) (h5 : f 5 = 177040) (h6 : f 6 = 408048) (h7 : f 7 = 744696)
    (hc : ∀ n : ℕ, 8 ≤ n → f n = 50128 * (n : ℤ) ^ 2 - 312688 * n + 476944) :
    PowerSeries.mk f * (1 - X) ^ 3 =
      8 * X ^ 3 * (666 + 4224 * X + 5462 * X ^ 2 + 2616 * X ^ 3 + 237 * X ^ 4 - 419 * X ^ 5 -
        217 * X ^ 6 - 37 * X ^ 7) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk f with hA
  have hcube : ((1 : ℤ⟦X⟧) - X) ^ 3 =
      1 - X ^ 1 - X ^ 1 - X ^ 1 + X ^ 2 + X ^ 2 + X ^ 2 - X ^ 3 := by
    ring
  have hrhs : (8 : ℤ⟦X⟧) * X ^ 3 * (666 + 4224 * X + 5462 * X ^ 2 + 2616 * X ^ 3 + 237 * X ^ 4 -
      419 * X ^ 5 - 217 * X ^ 6 - 37 * X ^ 7) =
      C (5328 : ℤ) * X ^ 3 + C (33792 : ℤ) * X ^ 4 + C (43696 : ℤ) * X ^ 5 +
        C (20928 : ℤ) * X ^ 6 + C (1896 : ℤ) * X ^ 7 - C (3352 : ℤ) * X ^ 8 -
        C (1736 : ℤ) * X ^ 9 - C (296 : ℤ) * X ^ 10 := by
    simp only [map_ofNat]
    ring
  rw [hcube, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mul_X_pow', hA, coeff_mk]
  have h8 : f 8 = 1183632 := by rw [hc 8 (by norm_num)]; norm_num
  have h9 : f 9 = 1723120 := by rw [hc 9 (by norm_num)]; norm_num
  have h10 : f 10 = 2362864 := by rw [hc 10 (by norm_num)]; norm_num
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  · simp [h0]
  · norm_num [h0, h1]
  · norm_num [h0, h1, h2]
  · norm_num [h0, h1, h2, h3]
  · norm_num [h0, h1, h2, h3, h4]
  · norm_num [h2, h3, h4, h5]
  · norm_num [h3, h4, h5, h6]
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.one_le_ofNat, Nat.reduceLeDiff, if_true, if_false,
      Nat.reduceEqDiff, OfNat.ofNat_ne_zero]
    rw [h7, h6, h5, h4]
    norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.one_le_ofNat, Nat.reduceLeDiff, if_true, if_false,
      Nat.reduceEqDiff, OfNat.ofNat_ne_zero]
    rw [h8, h7, h6, h5]
    norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.one_le_ofNat, Nat.reduceLeDiff, if_true, if_false,
      Nat.reduceEqDiff, OfNat.ofNat_ne_zero]
    rw [h9, h8, h7, h6]
    norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.one_le_ofNat, Nat.reduceLeDiff, if_true, if_false,
      Nat.reduceEqDiff, OfNat.ofNat_ne_zero]
    rw [h10, h9, h8, h7]
    norm_num
  · simp only [show ¬ (j + 11 = 0) by omega, show 1 ≤ j + 11 by omega, show 2 ≤ j + 11 by omega,
      show 3 ≤ j + 11 by omega, show j + 11 - 1 = j + 10 by omega,
      show j + 11 - 2 = j + 9 by omega, show j + 11 - 3 = j + 8 by omega,
      show ¬ (j + 10 = 0) by omega, show ¬ (j + 9 = 0) by omega, show ¬ (j + 8 = 0) by omega,
      show ¬ (j + 11 = 3) by omega, show ¬ (j + 11 = 4) by omega, show ¬ (j + 11 = 5) by omega,
      show ¬ (j + 11 = 6) by omega, show ¬ (j + 11 = 7) by omega, show ¬ (j + 11 = 8) by omega,
      show ¬ (j + 11 = 9) by omega, show ¬ (j + 11 = 10) by omega, if_true, if_false]
    rw [hc (j + 11) (by omega), hc (j + 10) (by omega), hc (j + 9) (by omega),
      hc (j + 8) (by omega)]
    push_cast
    ring

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - X) ^ 3 =
      8 * X ^ 3 * (666 + 4224 * X + 5462 * X ^ 2 + 2616 * X ^ 3 + 237 * X ^ 4 - 419 * X ^ 5 -
        217 * X ^ 6 - 37 * X ^ 7) :=
  gen_fun_aux (fun n => (a n : ℤ)) (by rw [a_zero]; rfl) (by rw [a_one]; rfl) (by rw [a_two]; rfl)
    (by rw [a_three]; rfl) (by rw [a_four]; rfl) (by rw [a_five]; rfl) (by rw [a_six]; rfl)
    (by rw [a_seven]; rfl) a_closed

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a187853.main :=
  ⟨fun n hn => OMA.Helpers.a_closed n hn, OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
