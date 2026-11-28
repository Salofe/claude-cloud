import OMAStatements.S_oeis_a183897

/-!
Proof of Barker's conjectures for A183897 (nondecreasing arrangements of n+3 numbers in 0..2 with
each number being the sum mod 3 of three others).

Write `a, b, c` for the numbers of zeros, ones and twos of an arrangement `f`.
* Whether the condition holds at a position `i` depends only on `f i` and on `a, b, c`: three other
  positions exist iff some values `x, y, z` with `x + y + z ≡ f i (mod 3)` fit into the counts once
  position `i` is removed. This is an explicit threshold condition `Qv` (`E_iff`), so
  `Good f ↔ Monotone f ∧ P a b c` (`good_iff`).
* A nondecreasing arrangement is determined by `p = #{k | f k ≤ 0}` and `q = #{k | f k ≤ 1}`
  (Mathlib's `Tuple.lt_card_le_iff_apply_le_of_monotone`), so the good arrangements of length `N`
  are in bijection with the pairs `p ≤ q ≤ N` such that `P p (q - p) (N - q)` (`card_good`).
* For `N ≥ 6` exactly eleven of the `(N + 1)(N + 2)/2` pairs fail `P` (`bad_eq`, through a finite
  check on the counts capped at 6), so `2 a(n) = (n + 4)(n + 5) - 22 = n^2 + 9n - 2` for `n ≥ 3`;
  directly, `a(1) = 1` and `a(2) = 7`.
* The recurrence and the generating function follow by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a183897 Finset

/-- The condition at a position holding `0`, in terms of the numbers `a, b, c` of zeros, ones and
twos of the whole arrangement. -/
def Q0 (a b c : ℕ) : Prop := 4 ≤ a ∨ 3 ≤ b ∨ 3 ≤ c ∨ (2 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c)

/-- The condition at a position holding `1`. -/
def Q1 (a b c : ℕ) : Prop := (2 ≤ a ∧ 2 ≤ b) ∨ (1 ≤ a ∧ 2 ≤ c) ∨ (3 ≤ b ∧ 1 ≤ c)

/-- The condition at a position holding `2`. -/
def Q2 (a b c : ℕ) : Prop := (2 ≤ a ∧ 2 ≤ c) ∨ (1 ≤ a ∧ 2 ≤ b) ∨ (1 ≤ b ∧ 3 ≤ c)

instance (a b c : ℕ) : Decidable (Q0 a b c) := inferInstanceAs (Decidable (_ ∨ _))
instance (a b c : ℕ) : Decidable (Q1 a b c) := inferInstanceAs (Decidable (_ ∨ _))
instance (a b c : ℕ) : Decidable (Q2 a b c) := inferInstanceAs (Decidable (_ ∨ _))

/-- The condition at a position holding `v`. -/
def Qv (v : Fin 3) (a b c : ℕ) : Prop :=
  (v = 0 → Q0 a b c) ∧ (v = 1 → Q1 a b c) ∧ (v = 2 → Q2 a b c)

instance (v : Fin 3) (a b c : ℕ) : Decidable (Qv v a b c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The whole arrangement is good when the condition holds for every value that occurs. -/
def P (a b c : ℕ) : Prop := (1 ≤ a → Q0 a b c) ∧ (1 ≤ b → Q1 a b c) ∧ (1 ≤ c → Q2 a b c)

instance (a b c : ℕ) : Decidable (P a b c) := inferInstanceAs (Decidable (_ ∧ _))

/-- Indicator of `v = w`. -/
def ind (v w : Fin 3) : ℕ := if v = w then 1 else 0

/-- The count among `a, b, c` that belongs to the value `w`. -/
def sel (a b c : ℕ) (w : Fin 3) : ℕ := if w = 0 then a else if w = 1 then b else c

/-- The existential of the definition, at the position `i`. -/
def E {N : ℕ} (x : Fin N → Fin 3) (i : Fin N) : Prop :=
  ∃ j₁ j₂ j₃ : Fin N, j₁ ≠ i ∧ j₂ ≠ i ∧ j₃ ≠ i ∧ j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃ ∧
    ((x j₁ : ℕ) + (x j₂ : ℕ) + (x j₃ : ℕ)) % 3 = (x i : ℕ)

theorem good_iff_E {N : ℕ} (x : Fin N → Fin 3) : Good x ↔ Monotone x ∧ ∀ i, E x i := Iff.rfl

theorem Qv_mono {v : Fin 3} {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (h : Qv v a b c) : Qv v a' b' c' := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨fun hv => ?_, fun hv => ?_, fun hv => ?_⟩
  · have := h0 hv
    unfold Q0 at *
    omega
  · have := h1 hv
    unfold Q1 at *
    omega
  · have := h2 hv
    unfold Q2 at *
    omega

/-- Four distinct positions holding `v, x, y, z`: the condition holds already for the counts of
these four values. -/
theorem key_fin : ∀ v x y z : Fin 3, ((x : ℕ) + (y : ℕ) + (z : ℕ)) % 3 = (v : ℕ) →
    Qv v (ind v 0 + ind x 0 + ind y 0 + ind z 0) (ind v 1 + ind x 1 + ind y 1 + ind z 1)
      (ind v 2 + ind x 2 + ind y 2 + ind z 2) := by
  decide

theorem cnt_ge {N : ℕ} (f : Fin N → Fin 3) (i j₁ j₂ j₃ : Fin N) (h1 : j₁ ≠ i) (h2 : j₂ ≠ i)
    (h3 : j₃ ≠ i) (h12 : j₁ ≠ j₂) (h13 : j₁ ≠ j₃) (h23 : j₂ ≠ j₃) (w : Fin 3) :
    ind (f i) w + ind (f j₁) w + ind (f j₂) w + ind (f j₃) w ≤ #{k | f k = w} := by
  have hsub : ({i, j₁, j₂, j₃} : Finset (Fin N)).filter (fun k => f k = w) ⊆
      univ.filter (fun k => f k = w) := filter_subset_filter _ (subset_univ _)
  refine le_trans (le_of_eq ?_) (card_le_card hsub)
  rw [card_filter, sum_insert, sum_insert, sum_insert, sum_singleton]
  · simp only [ind, add_assoc]
  · simpa using h23
  · simp [h12, h13]
  · simp [h1.symm, h2.symm, h3.symm]

theorem forward {N : ℕ} (f : Fin N → Fin 3) (i : Fin N) (h : E f i) :
    Qv (f i) #{k | f k = 0} #{k | f k = 1} #{k | f k = 2} := by
  obtain ⟨j₁, j₂, j₃, h1, h2, h3, h12, h13, h23, hs⟩ := h
  exact Qv_mono (cnt_ge f i j₁ j₂ j₃ h1 h2 h3 h12 h13 h23 0)
    (cnt_ge f i j₁ j₂ j₃ h1 h2 h3 h12 h13 h23 1) (cnt_ge f i j₁ j₂ j₃ h1 h2 h3 h12 h13 h23 2)
    (key_fin (f i) (f j₁) (f j₂) (f j₃) hs)

/-- Erasing a position from a set of positions holding `w` loses at most one element, and only
when that position holds `w`. -/
theorem card_erase_ge {N : ℕ} (f : Fin N → Fin 3) (w : Fin 3) (s : Finset (Fin N))
    (hs : ∀ k ∈ s, f k = w) (a : Fin N) : #s ≤ #(s.erase a) + ind (f a) w := by
  by_cases h : a ∈ s
  · rw [card_erase_of_mem h, ind, if_pos (hs a h)]
    have := card_pos.2 ⟨a, h⟩
    omega
  · rw [erase_eq_of_notMem h]
    omega

/-- Picking three other positions holding `x, y, z`, when the counts allow it. -/
theorem pick {N : ℕ} (f : Fin N → Fin 3) (i : Fin N) (x y z : Fin 3)
    (hs : ((x : ℕ) + (y : ℕ) + (z : ℕ)) % 3 = (f i : ℕ))
    (hx : 1 + ind (f i) x ≤ #{k | f k = x})
    (hy : 1 + ind (f i) y + ind x y ≤ #{k | f k = y})
    (hz : 1 + ind (f i) z + ind x z + ind y z ≤ #{k | f k = z}) : E f i := by
  -- the first position
  have hX := card_erase_ge f x (univ.filter (fun k => f k = x)) (by simp) i
  obtain ⟨j₁, hj₁⟩ := card_pos.1 (show 0 < #((univ.filter (fun k => f k = x)).erase i) by omega)
  rw [mem_erase, mem_filter] at hj₁
  obtain ⟨h1, -, hf1⟩ := hj₁
  -- the second position
  have hY1 := card_erase_ge f y (univ.filter (fun k => f k = y)) (by simp) i
  have hY2 := card_erase_ge f y ((univ.filter (fun k => f k = y)).erase i)
    (fun k hk => by simp only [mem_erase, mem_filter] at hk; exact hk.2.2) j₁
  rw [hf1] at hY2
  obtain ⟨j₂, hj₂⟩ := card_pos.1
    (show 0 < #(((univ.filter (fun k => f k = y)).erase i).erase j₁) by omega)
  rw [mem_erase, mem_erase, mem_filter] at hj₂
  obtain ⟨h12, h2, -, hf2⟩ := hj₂
  -- the third position
  have hZ1 := card_erase_ge f z (univ.filter (fun k => f k = z)) (by simp) i
  have hZ2 := card_erase_ge f z ((univ.filter (fun k => f k = z)).erase i)
    (fun k hk => by simp only [mem_erase, mem_filter] at hk; exact hk.2.2) j₁
  have hZ3 := card_erase_ge f z (((univ.filter (fun k => f k = z)).erase i).erase j₁)
    (fun k hk => by simp only [mem_erase, mem_filter] at hk; exact hk.2.2.2) j₂
  rw [hf1] at hZ2
  rw [hf2] at hZ3
  obtain ⟨j₃, hj₃⟩ := card_pos.1
    (show 0 < #((((univ.filter (fun k => f k = z)).erase i).erase j₁).erase j₂) by omega)
  rw [mem_erase, mem_erase, mem_erase, mem_filter] at hj₃
  obtain ⟨h23, h13, h3, -, hf3⟩ := hj₃
  refine ⟨j₁, j₂, j₃, h1, h2, h3, fun h => h12 h.symm, fun h => h13 h.symm,
    fun h => h23 h.symm, ?_⟩
  rw [hf1, hf2, hf3]
  exact hs

/-- For each value and each way the condition can hold, three suitable values. -/
theorem witness (v : Fin 3) (a b c : ℕ) (h : Qv v a b c) :
    ∃ x y z : Fin 3, ((x : ℕ) + (y : ℕ) + (z : ℕ)) % 3 = (v : ℕ) ∧
      1 + ind v x ≤ sel a b c x ∧ 1 + ind v y + ind x y ≤ sel a b c y ∧
      1 + ind v z + ind x z + ind y z ≤ sel a b c z := by
  obtain ⟨h0, h1, h2⟩ := h
  fin_cases v
  · rcases h0 rfl with h | h | h | ⟨ha, hb, hc⟩
    · exact ⟨0, 0, 0, by decide, by simp [ind, sel]; omega⟩
    · exact ⟨1, 1, 1, by decide, by simp [ind, sel]; omega⟩
    · exact ⟨2, 2, 2, by decide, by simp [ind, sel]; omega⟩
    · exact ⟨0, 1, 2, by decide, by simp [ind, sel]; omega⟩
  · rcases h1 rfl with ⟨ha, hb⟩ | ⟨ha, hc⟩ | ⟨hb, hc⟩
    · exact ⟨0, 0, 1, by decide, by simp [ind, sel]; omega⟩
    · exact ⟨0, 2, 2, by decide, by simp [ind, sel]; omega⟩
    · exact ⟨1, 1, 2, by decide, by simp [ind, sel]; omega⟩
  · rcases h2 rfl with ⟨ha, hc⟩ | ⟨ha, hb⟩ | ⟨hb, hc⟩
    · exact ⟨0, 0, 2, by decide, by simp [ind, sel]; omega⟩
    · exact ⟨0, 1, 1, by decide, by simp [ind, sel]; omega⟩
    · exact ⟨1, 2, 2, by decide, by simp [ind, sel]; omega⟩

theorem sel_cnt {N : ℕ} (f : Fin N → Fin 3) (w : Fin 3) :
    sel #{k | f k = 0} #{k | f k = 1} #{k | f k = 2} w = #{k | f k = w} := by
  fin_cases w <;> rfl

/-- Lemma A: the existential at `i` holds iff the counts satisfy the condition for `f i`. -/
theorem E_iff {N : ℕ} (f : Fin N → Fin 3) (i : Fin N) :
    E f i ↔ Qv (f i) #{k | f k = 0} #{k | f k = 1} #{k | f k = 2} := by
  refine ⟨forward f i, fun h => ?_⟩
  obtain ⟨x, y, z, hs, hx, hy, hz⟩ := witness _ _ _ _ h
  rw [sel_cnt] at hx hy hz
  exact pick f i x y z hs hx hy hz

theorem all_iff_P {N : ℕ} (f : Fin N → Fin 3) :
    (∀ i, Qv (f i) #{k | f k = 0} #{k | f k = 1} #{k | f k = 2}) ↔
      P #{k | f k = 0} #{k | f k = 1} #{k | f k = 2} := by
  constructor
  · intro h
    refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 => ?_⟩
    · obtain ⟨k, hk⟩ := card_pos.1 (show 0 < #{k | f k = 0} by omega)
      rw [mem_filter] at hk
      exact (h k).1 hk.2
    · obtain ⟨k, hk⟩ := card_pos.1 (show 0 < #{k | f k = 1} by omega)
      rw [mem_filter] at hk
      exact (h k).2.1 hk.2
    · obtain ⟨k, hk⟩ := card_pos.1 (show 0 < #{k | f k = 2} by omega)
      rw [mem_filter] at hk
      exact (h k).2.2 hk.2
  · rintro ⟨h0, h1, h2⟩ i
    have hpos : ∀ w, f i = w → 1 ≤ #{k | f k = w} := fun w hw =>
      card_pos.2 ⟨i, by rw [mem_filter]; exact ⟨mem_univ _, hw⟩⟩
    exact ⟨fun hv => h0 (hpos 0 hv), fun hv => h1 (hpos 1 hv), fun hv => h2 (hpos 2 hv)⟩

/-- Whether an arrangement is good depends only on monotonicity and on the three counts. -/
theorem good_iff {N : ℕ} (f : Fin N → Fin 3) :
    Good f ↔ Monotone f ∧ P #{k | f k = 0} #{k | f k = 1} #{k | f k = 2} := by
  rw [good_iff_E, ← all_iff_P]
  exact and_congr Iff.rfl (forall_congr' fun i => E_iff f i)

theorem fin3_le0 : ∀ v : Fin 3, v ≤ 0 ↔ v = 0 := by decide
theorem fin3_le1 : ∀ v : Fin 3, v ≤ 1 ↔ v = 0 ∨ v = 1 := by decide
theorem fin3_not_le1 : ∀ v : Fin 3, v = 2 ↔ ¬ v ≤ 1 := by decide
theorem fin3_ite : ∀ v : Fin 3, (if v ≤ 0 then 0 else if v ≤ 1 then 1 else 2) = v := by decide

theorem card_le0 {N : ℕ} (f : Fin N → Fin 3) : #{k | f k ≤ 0} = #{k | f k = 0} := by
  rw [filter_congr (fun k _ => fin3_le0 (f k))]

theorem card_le1 {N : ℕ} (f : Fin N → Fin 3) :
    #{k | f k ≤ 1} = #{k | f k = 0} + #{k | f k = 1} := by
  rw [filter_congr (fun k _ => fin3_le1 (f k)), filter_or, card_union_of_disjoint]
  rw [disjoint_filter]
  intro k _ h0 h1
  rw [h0] at h1
  exact absurd h1 (by decide)

theorem card_total {N : ℕ} (f : Fin N → Fin 3) : #{k | f k ≤ 1} + #{k | f k = 2} = N := by
  rw [filter_congr (fun k _ => fin3_not_le1 (f k)), card_filter_add_card_filter_not, card_univ,
    Fintype.card_fin]

/-- The arrangement with `p` zeros, then `q - p` ones, then twos. -/
def g (N p q : ℕ) : Fin N → Fin 3 := fun k => if (k : ℕ) < p then 0 else if (k : ℕ) < q then 1 else 2

theorem g_le0 (N p q : ℕ) (k : Fin N) : g N p q k ≤ 0 ↔ (k : ℕ) < p := by
  unfold g
  split_ifs with h1 h2
  · simp [h1]
  · simp only [h1, iff_false]
    decide
  · simp only [h1, iff_false]
    decide

theorem g_le1 (N p q : ℕ) (hpq : p ≤ q) (k : Fin N) : g N p q k ≤ 1 ↔ (k : ℕ) < q := by
  unfold g
  split_ifs with h1 h2
  · exact ⟨fun _ => by omega, fun _ => by decide⟩
  · exact ⟨fun _ => h2, fun _ => by decide⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h2⟩

theorem g_mono (N p q : ℕ) : Monotone (g N p q) := by
  intro k l hkl
  have hkl' : (k : ℕ) ≤ l := hkl
  unfold g
  split_ifs <;> first | decide | (exfalso; omega)

theorem card_g_le0 (N p q : ℕ) (hp : p ≤ N) : #{k | g N p q k ≤ 0} = p := by
  rw [filter_congr (fun k _ => g_le0 N p q k), Fin.card_filter_val_lt]
  omega

theorem card_g_le1 (N p q : ℕ) (hpq : p ≤ q) (hq : q ≤ N) : #{k | g N p q k ≤ 1} = q := by
  rw [filter_congr (fun k _ => g_le1 N p q hpq k), Fin.card_filter_val_lt]
  omega

theorem g_inv {N : ℕ} (f : Fin N → Fin 3) (hf : Monotone f) :
    g N #{k | f k ≤ 0} #{k | f k ≤ 1} = f := by
  funext k
  have h0 := Tuple.lt_card_le_iff_apply_le_of_monotone (j := k) (a := (0 : Fin 3)) hf
  have h1 := Tuple.lt_card_le_iff_apply_le_of_monotone (j := k) (a := (1 : Fin 3)) hf
  unfold g
  simp only [h0, h1]
  exact fin3_ite (f k)

/-- Pairs `p ≤ q ≤ N`: a nondecreasing arrangement has `p` entries `≤ 0` and `q` entries `≤ 1`. -/
def V (N : ℕ) : Finset (ℕ × ℕ) := ((range (N + 1)) ×ˢ (range (N + 1))).filter (fun x => x.1 ≤ x.2)

/-- The pairs of good arrangements: `p` zeros, `q - p` ones and `N - q` twos. -/
def T (N : ℕ) : Finset (ℕ × ℕ) := (V N).filter (fun x => P x.1 (x.2 - x.1) (N - x.2))

theorem mem_T {N : ℕ} {x : ℕ × ℕ} :
    x ∈ T N ↔ (x.1 < N + 1 ∧ x.2 < N + 1) ∧ x.1 ≤ x.2 ∧ P x.1 (x.2 - x.1) (N - x.2) := by
  simp only [T, V, mem_filter, mem_product, mem_range, and_assoc]

theorem card_good (N : ℕ) [DecidablePred (fun f : Fin N → Fin 3 => Good f)] :
    #(univ.filter (fun f : Fin N → Fin 3 => Good f)) = #(T N) := by
  apply card_nbij' (fun f => (#{k | f k ≤ 0}, #{k | f k ≤ 1})) (fun x => g N x.1 x.2)
  · intro f hf
    rw [mem_coe, mem_filter] at hf
    obtain ⟨-, hP⟩ := (good_iff f).1 hf.2
    have e0 := card_le0 f
    have e1 := card_le1 f
    have e2 := card_total f
    rw [mem_coe, mem_T]
    dsimp only
    refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
    rw [e0, e1, show #{k | f k = 0} + #{k | f k = 1} - #{k | f k = 0} = #{k | f k = 1} by omega,
      show N - (#{k | f k = 0} + #{k | f k = 1}) = #{k | f k = 2} by omega]
    exact hP
  · intro x hx
    rw [mem_coe, mem_T] at hx
    obtain ⟨⟨hp, hq⟩, hpq, hP⟩ := hx
    rw [mem_coe, mem_filter]
    refine ⟨mem_univ _, (good_iff _).2 ⟨g_mono N x.1 x.2, ?_⟩⟩
    have e0 := card_le0 (g N x.1 x.2)
    have e1 := card_le1 (g N x.1 x.2)
    have e2 := card_total (g N x.1 x.2)
    rw [card_g_le0 N x.1 x.2 (by omega)] at e0
    rw [card_g_le1 N x.1 x.2 hpq (by omega)] at e1 e2
    rw [← e0, show #{k | g N x.1 x.2 k = 1} = x.2 - x.1 by omega,
      show #{k | g N x.1 x.2 k = 2} = N - x.2 by omega]
    exact hP
  · intro f hf
    rw [mem_coe, mem_filter] at hf
    exact g_inv f ((good_iff f).1 hf.2).1
  · intro x hx
    rw [mem_coe, mem_T] at hx
    obtain ⟨⟨hp, hq⟩, hpq, -⟩ := hx
    dsimp only
    rw [card_g_le0 N x.1 x.2 (by omega), card_g_le1 N x.1 x.2 hpq (by omega)]

theorem a_eq_card_T (n : ℕ) : a n = #(T (n + 3)) := by
  classical
  rw [a, Nat.card_eq_fintype_card, Fintype.card_subtype, card_good]

theorem T4 : #(T 4) = 1 := by decide
theorem T5 : #(T 5) = 7 := by decide

theorem card_V (N : ℕ) : 2 * #(V N) = (N + 1) * (N + 2) := by
  induction N with
  | zero => decide
  | succ N ih =>
    have h : V (N + 1) = V N ∪ (range (N + 2)) ×ˢ {N + 1} := by
      ext ⟨p, q⟩
      simp only [V, mem_filter, mem_product, mem_range, mem_union, mem_singleton]
      omega
    have hd : Disjoint (V N) ((range (N + 2)) ×ˢ {N + 1}) := by
      rw [disjoint_left]
      rintro ⟨p, q⟩ h1 h2
      simp only [V, mem_filter, mem_product, mem_range, mem_singleton] at h1 h2
      omega
    rw [h, card_union_of_disjoint hd, card_product, card_range, card_singleton, mul_add, ih]
    ring

/-- The eleven pairs `(p, q)` of bad nondecreasing arrangements when `N ≥ 6`. -/
def B (N : ℕ) : Finset (ℕ × ℕ) :=
  {(0, 0), (0, 1), (0, 2), (0, N - 2), (0, N - 1), (0, N), (1, 1), (1, N), (N - 2, N - 1),
    (N - 1, N - 1), (N - 1, N)}

/-- The bad shapes when there are at least six numbers, in terms of the three counts. -/
def Fam (a b c : ℕ) : Prop :=
  (a ≤ 0 ∧ b ≤ 2) ∨ (a ≤ 0 ∧ c ≤ 2) ∨ (1 ≤ a ∧ a ≤ 1 ∧ b ≤ 0) ∨ (1 ≤ a ∧ a ≤ 1 ∧ c ≤ 0) ∨
    (1 ≤ b ∧ b ≤ 1 ∧ c ≤ 1) ∨ (b ≤ 0 ∧ 1 ≤ c ∧ c ≤ 1)

instance (a b c : ℕ) : Decidable (Fam a b c) := inferInstanceAs (Decidable (_ ∨ _))

theorem small : ∀ a < 7, ∀ b < 7, ∀ c < 7, 6 ≤ a + b + c → (¬ P a b c ↔ Fam a b c) := by
  decide

theorem P_cap (a b c : ℕ) : P (min a 6) (min b 6) (min c 6) ↔ P a b c := by
  simp only [P, Q0, Q1, Q2, le_min_iff, show (1 : ℕ) ≤ 6 by norm_num, show (2 : ℕ) ≤ 6 by norm_num,
    show (3 : ℕ) ≤ 6 by norm_num, show (4 : ℕ) ≤ 6 by norm_num, and_true]

theorem Fam_cap (a b c : ℕ) : Fam (min a 6) (min b 6) (min c 6) ↔ Fam a b c := by
  simp only [Fam, le_min_iff, min_le_iff, show ¬ (6 : ℕ) ≤ 0 by norm_num,
    show ¬ (6 : ℕ) ≤ 1 by norm_num, show ¬ (6 : ℕ) ≤ 2 by norm_num, show (1 : ℕ) ≤ 6 by norm_num,
    or_false, and_true]

theorem notP_iff (a b c : ℕ) (h : 6 ≤ a + b + c) : ¬ P a b c ↔ Fam a b c := by
  rw [← P_cap, ← Fam_cap]
  exact small _ (by omega) _ (by omega) _ (by omega) (by omega)

theorem bad_eq (N : ℕ) (hN : 6 ≤ N) :
    (V N).filter (fun x => ¬ P x.1 (x.2 - x.1) (N - x.2)) = B N := by
  ext ⟨p, q⟩
  simp only [V, mem_filter, mem_product, mem_range]
  constructor
  · rintro ⟨⟨⟨hp, hq⟩, hpq⟩, h⟩
    rw [notP_iff _ _ _ (by omega)] at h
    unfold Fam at h
    unfold B
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · obtain rfl : p = 0 := by omega
      obtain rfl | rfl | rfl : q = 0 ∨ q = 1 ∨ q = 2 := by omega
      all_goals simp
    · obtain rfl : p = 0 := by omega
      obtain rfl | rfl | rfl : q = N - 2 ∨ q = N - 1 ∨ q = N := by omega
      all_goals simp
    · obtain ⟨rfl, rfl⟩ : p = 1 ∧ q = 1 := by omega
      simp
    · obtain ⟨rfl, rfl⟩ : p = 1 ∧ q = N := ⟨by omega, by omega⟩
      simp
    · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (p = N - 2 ∧ q = N - 1) ∨ (p = N - 1 ∧ q = N) := by omega
      all_goals simp
    · obtain ⟨rfl, rfl⟩ : p = N - 1 ∧ q = N - 1 := by omega
      simp
  · intro h
    unfold B at h
    simp only [mem_insert, mem_singleton, Prod.mk.injEq] at h
    refine ⟨⟨⟨by omega, by omega⟩, by omega⟩, ?_⟩
    rw [notP_iff _ _ _ (by omega)]
    unfold Fam
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals omega

theorem card_B (N : ℕ) (hN : 6 ≤ N) : #(B N) = 11 := by
  unfold B
  rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem,
    card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem,
    card_insert_of_notMem, card_insert_of_notMem, card_singleton]
  all_goals
    simp only [mem_insert, mem_singleton, Prod.mk.injEq, not_or]
    omega

theorem card_T (N : ℕ) (hN : 6 ≤ N) : 2 * #(T N) + 22 = (N + 1) * (N + 2) := by
  have h := card_filter_add_card_filter_not (s := V N)
    (fun x : ℕ × ℕ => P x.1 (x.2 - x.1) (N - x.2))
  rw [bad_eq N hN, card_B N hN] at h
  have hV := card_V N
  unfold T
  omega

/-- The closed form `a(n) = (n^2 + 9n - 2)/2` for `n ≥ 3`. -/
theorem a_closed (n : ℕ) (hn : 3 ≤ n) : 2 * a n + 2 = n ^ 2 + 9 * n := by
  rw [a_eq_card_T]
  have h := card_T (n + 3) (by omega)
  have e : (n + 3 + 1) * (n + 3 + 2) = n ^ 2 + 9 * n + 20 := by ring
  rw [e] at h
  omega

theorem a_closedZ (n : ℕ) (hn : 3 ≤ n) : 2 * (a n : ℤ) = (n : ℤ) ^ 2 + 9 * n - 2 := by
  have h := a_closed n hn
  have h' : (2 * a n + 2 : ℤ) = (n : ℤ) ^ 2 + 9 * n := by exact_mod_cast h
  linarith

theorem a_one : (a 1 : ℤ) = 1 := by
  rw [a_eq_card_T, T4]
  rfl

theorem a_two : (a 2 : ℤ) = 7 := by
  rw [a_eq_card_T, T5]
  rfl

theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 3 * (a (n - 1) : ℤ) - 3 * (a (n - 2) : ℤ) + (a (n - 3) : ℤ) := by
  have h0 := a_closedZ n (by omega)
  have h1 := a_closedZ (n - 1) (by omega)
  have h2 := a_closedZ (n - 2) (by omega)
  have h3 := a_closedZ (n - 3) (by omega)
  push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega] at h1 h2 h3
  linarith

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
        ((1 - X) ^ 3 : PowerSeries ℤ) =
      X * (1 + X - X ^ 2) * (1 + 3 * X - 3 * X ^ 2) := by
  set A : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ))
    with hA
  have hcube : ((1 : PowerSeries ℤ) - X) ^ 3 =
      1 - X ^ 1 - X ^ 1 - X ^ 1 + X ^ 2 + X ^ 2 + X ^ 2 - X ^ 3 := by
    ring
  have hrhs : (X : PowerSeries ℤ) * (1 + X - X ^ 2) * (1 + 3 * X - 3 * X ^ 2) =
      C (1 : ℤ) * X ^ 1 + C (4 : ℤ) * X ^ 2 - C (1 : ℤ) * X ^ 3 - C (6 : ℤ) * X ^ 4 +
        C (3 : ℤ) * X ^ 5 := by
    simp only [map_one, map_ofNat]
    ring
  rw [hcube, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mul_X_pow', hA, coeff_mk]
  have a3 : (a 3 : ℤ) = 17 := by
    have := a_closedZ 3 le_rfl
    push_cast at this
    linarith
  have a4 : (a 4 : ℤ) = 25 := by
    have := a_closedZ 4 (by norm_num)
    push_cast at this
    linarith
  have a5 : (a 5 : ℤ) = 34 := by
    have := a_closedZ 5 (by norm_num)
    push_cast at this
    linarith
  rcases k with _ | _ | _ | _ | _ | _ | j
  · simp
  · simp [a_one]
  · norm_num [a_one, a_two]
  · norm_num [a_one, a_two, a3]
  · norm_num [a_one, a_two, a3, a4]
  · norm_num [a_one, a_two, a3, a4, a5]
  · simp only [show ¬ (j + 6 = 0) by omega, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega,
      show 3 ≤ j + 6 by omega, show j + 6 - 1 = j + 5 by omega, show j + 6 - 2 = j + 4 by omega,
      show j + 6 - 3 = j + 3 by omega, show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 3 = 0) by omega, show ¬ (j + 6 = 1) by omega, show ¬ (j + 6 = 2) by omega,
      show ¬ (j + 6 = 3) by omega, show ¬ (j + 6 = 4) by omega, show ¬ (j + 6 = 5) by omega,
      if_true, if_false]
    have h0 := a_closedZ (j + 6) (by omega)
    have h1 := a_closedZ (j + 5) (by omega)
    have h2 := a_closedZ (j + 4) (by omega)
    have h3 := a_closedZ (j + 3) (by omega)
    push_cast at h0 h1 h2 h3
    linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a183897.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
