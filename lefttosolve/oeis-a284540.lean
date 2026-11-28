import OMAStatements.S_oeis_a284540
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a284540

theorem c_succ (t : ℕ) (i j : ℤ) : cell 974 (t + 1) i j =
    Nat.testBit 974 ((cell 974 t i j).toNat + 2 * ((cell 974 t (i + 1) j).toNat +
      (cell 974 t (i - 1) j).toNat + (cell 974 t i (j + 1)).toNat +
      (cell 974 t i (j - 1)).toNat)) := rfl

theorem cone (t : ℕ) : ∀ i j : ℤ, (t : ℤ) < |i| + |j| → cell 974 t i j = false := by
  induction t with
  | zero =>
    intro i j h
    show decide (i = 0 ∧ j = 0) = false
    rw [decide_eq_false_iff_not]
    rintro ⟨rfl, rfl⟩
    simp at h
  | succ t ih =>
    intro i j h
    push_cast at h
    rw [c_succ, ih i j (by linarith),
      ih (i + 1) j (by cases abs_cases i <;> cases abs_cases (i + 1) <;> linarith),
      ih (i - 1) j (by cases abs_cases i <;> cases abs_cases (i - 1) <;> linarith),
      ih i (j + 1) (by cases abs_cases j <;> cases abs_cases (j + 1) <;> linarith),
      ih i (j - 1) (by cases abs_cases j <;> cases abs_cases (j - 1) <;> linarith)]
    rfl

theorem symm_i (t : ℕ) : ∀ i j : ℤ, cell 974 t (-i) j = cell 974 t i j := by
  induction t with
  | zero =>
    intro i j
    show decide (-i = 0 ∧ j = 0) = decide (i = 0 ∧ j = 0)
    simp
  | succ t ih =>
    intro i j
    rw [c_succ, c_succ, ih i j, ih i (j + 1), ih i (j - 1), show -i + 1 = -(i - 1) by ring,
      show -i - 1 = -(i + 1) by ring, ih (i - 1) j, ih (i + 1) j]
    congr 1
    ring

/-- Cell (u, j) of a tip pattern q, where u is the distance from the left corner of the diamond. -/
def Qb (q u : ℕ) (j : ℤ) : Bool := q.testBit (u * 17 + (j + 8).toNat)

def Qx (q : ℕ) (u j : ℤ) : Bool := if 0 ≤ u ∧ |j| ≤ u then Qb q u.toNat j else false

def rule (q u : ℕ) (j : ℤ) : Bool :=
  Nat.testBit 974 ((Qx q ((u : ℤ) - 1) j).toNat + 2 * ((Qx q (u : ℤ) j).toNat +
    (Qx q ((u : ℤ) - 2) j).toNat + (Qx q ((u : ℤ) - 1) (j + 1)).toNat +
    (Qx q ((u : ℤ) - 1) (j - 1)).toNat))

def stepOK (q q' : ℕ) : Bool :=
  (List.range 9).all fun u => (List.range (2 * u + 1)).all fun k =>
    Qb q' u ((k : ℤ) - u) == rule q u ((k : ℤ) - u)

theorem stepOK_spec {q q' : ℕ} (h : stepOK q q' = true) (u : ℕ) (hu : u ≤ 8) (j : ℤ)
    (hj : |j| ≤ u) : Qb q' u j = rule q u j := by
  simp only [stepOK, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := abs_le.mp hj
  have hk := h u (by omega) (j + u).toNat (by omega)
  have e : (((j + u).toNat : ℕ) : ℤ) - u = j := by omega
  rw [e] at hk
  exact hk

/-- The tip invariant: the cells at distance at most 8 from the left corner follow q. -/
def TipInv (t q : ℕ) : Prop :=
  ∀ u : ℕ, u ≤ 8 → ∀ j : ℤ, |j| ≤ u → cell 974 t ((u : ℤ) - t) j = Qb q u j

theorem tipX {t q : ℕ} (h : TipInv t q) (u : ℤ) (hu : u ≤ 8) (j : ℤ) :
    cell 974 t (u - t) j = Qx q u j := by
  unfold Qx
  split_ifs with hc
  · obtain ⟨h0, h1⟩ := hc
    have := h u.toNat (by omega) j (by omega)
    rw [show ((u.toNat : ℕ) : ℤ) = u by omega] at this
    exact this
  · apply cone
    have ha : (t : ℤ) - u ≤ |u - t| := by rw [abs_sub_comm]; exact le_abs_self _
    have hb : u - t ≤ |u - t| := le_abs_self _
    have hj0 : 0 ≤ |j| := abs_nonneg j
    rcases not_and_or.mp hc with h' | h' <;> push Not at h' <;> linarith

theorem tip_step {t q q' : ℕ} (h : TipInv t q) (hs : stepOK q q' = true) : TipInv (t + 1) q' := by
  intro u hu j hj
  rw [c_succ, stepOK_spec hs u hu j hj]
  unfold rule
  have e0 : (u : ℤ) - ((t + 1 : ℕ) : ℤ) = ((u : ℤ) - 1) - t := by push_cast; ring
  have e1 : (u : ℤ) - ((t + 1 : ℕ) : ℤ) + 1 = (u : ℤ) - t := by push_cast; ring
  have e2 : (u : ℤ) - ((t + 1 : ℕ) : ℤ) - 1 = ((u : ℤ) - 2) - t := by push_cast; ring
  rw [e1, e2, e0, tipX h _ (by omega), tipX h _ (by omega), tipX h _ (by omega),
    tipX h _ (by omega), tipX h _ (by omega)]

def pats : List ℕ := [256, 4398163951872, 75558440220751520858368, 1298108877275935528796711005716736, 22300915344257385454170996901250801629921536, 595520509772419504768617272013341327616, 413961038887338297133519689253087132040298752, 1544712436110810656023960303722447530773971200, 10703587277489834663479082035114297133767852288, 7848914958476966474908540961232660186389283072, 7135635445967291842834993104286388321129595136, 8023832313358916445620669625562945776024289536, 6596234836943471490443016048451968648278442240, 6421310633899738057686301217134767968257835264, 6063110364128648603410875773840285798512984320, 7135672232466569746337177062508868297788752128, 5708838321737492600449822236553392400195649792, 1426556228323159572731115064799492521240559872, 354025648630905683486890246304775957345468672, 172832093924241498438611777288242451898695936, 531047378779447035826905951197079196699459840, 2854155087114870435908778062014505135997190400, 1426553495575926757489239817209037707085349120, 2139864296731268643244864144329175507725713664, 10703595460206829862427296762330107648900333824, 7135634111432930857210905566496975599433679104, 6063103531740676967966680748002259035538587904, 5881909977034012782918402278985725530091815168, 6240125261889218320306696452894562274892579072, 8563232970224641720388568563711988214190309632, 7135631378685698041969030318906520785278468352, 7848942179841039927724654646026658585918832896, 4994517577097058577947506260632624570707214592]

def P (s : ℕ) : ℕ := pats.getD s 0

def idx (t : ℕ) : ℕ := if t < 33 then t else 17 + (t - 17) % 16

def nxt (s : ℕ) : ℕ := if s < 32 then s + 1 else 17

theorem idx_succ (t : ℕ) : idx (t + 1) = nxt (idx t) := by
  unfold idx nxt
  split_ifs <;> omega

theorem idx_lt (t : ℕ) : idx t < 33 := by unfold idx; split_ifs <;> omega

theorem allOK : (List.range 33).all (fun s => stepOK (P s) (P (nxt s))) = true := by
  decide +kernel

theorem initOK : (List.range 9).all (fun u => (List.range (2 * u + 1)).all fun k =>
    Qb (P 0) u ((k : ℤ) - u) == decide (u = 0 ∧ k = u)) = true := by
  decide +kernel

theorem tip_zero : TipInv 0 (P 0) := by
  intro u hu j hj
  have h0 := initOK
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h0
  obtain ⟨h1, h2⟩ := abs_le.mp hj
  have hk := h0 u (by omega) (j + u).toNat (by omega)
  have e : (((j + u).toNat : ℕ) : ℤ) - u = j := by omega
  rw [e] at hk
  rw [hk]
  show decide (((u : ℤ) - ((0 : ℕ) : ℤ)) = 0 ∧ j = 0) = decide (u = 0 ∧ (j + u).toNat = u)
  apply decide_eq_decide.mpr
  omega

theorem tip_all (t : ℕ) : TipInv t (P (idx t)) := by
  induction t with
  | zero => exact tip_zero
  | succ t ih =>
    rw [idx_succ]
    apply tip_step ih
    have h0 := allOK
    simp only [List.all_eq_true, List.mem_range] at h0
    exact h0 _ (idx_lt t)

def edgeOK : Bool := (List.range 25).all fun s =>
  ([(-1 : ℤ), 0, 1]).all fun j => Qb (P (s + 8)) 6 j && Qb (P (s + 8)) 7 j

theorem edgeOK_true : edgeOK = true := by decide +kernel

theorem baseOK : ([(-1 : ℤ), 0, 1]).all (fun j => Qb (P 8) 6 j && Qb (P 8) 7 j && Qb (P 8) 8 j)
    = true := by decide +kernel

theorem idx_ge (t : ℕ) (ht : 8 ≤ t) : 8 ≤ idx t := by unfold idx; split_ifs <;> omega

theorem idx_mod (t : ℕ) : idx t % 4 = t % 4 := by unfold idx; split_ifs <;> omega

theorem mem3 {j : ℤ} (hj : |j| ≤ 1) : j ∈ [(-1 : ℤ), 0, 1] := by
  have := abs_le.mp hj
  have h : j = -1 ∨ j = 0 ∨ j = 1 := by omega
  rcases h with rfl | rfl | rfl <;> simp

theorem edge (t : ℕ) (ht : 8 ≤ t) (u : ℕ) (hu : u = 6 ∨ u = 7) (j : ℤ) (hj : |j| ≤ 1) :
    cell 974 t ((u : ℤ) - t) j = true := by
  rw [tip_all t u (by omega) j (by rcases hu with rfl | rfl <;> push_cast <;> linarith)]
  have h0 := List.all_eq_true.mp edgeOK_true (idx t - 8)
    (List.mem_range.mpr (by have := idx_lt t; omega))
  have h1 := List.all_eq_true.mp h0 j (mem3 hj)
  rw [show idx t - 8 + 8 = idx t by have := idx_ge t ht; omega] at h1
  rw [Bool.and_eq_true] at h1
  rcases hu with rfl | rfl
  · exact h1.1
  · exact h1.2

theorem band (t : ℕ) (ht : 8 ≤ t) : ∀ i : ℤ, -(t : ℤ) + 6 ≤ i → i ≤ (t : ℤ) - 6 →
    ∀ j : ℤ, |j| ≤ 1 → cell 974 t i j = true := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i hi1 hi2 j hj
    have key : ∀ i : ℤ, -2 ≤ i → i ≤ 0 → cell 974 8 i j = true := by
      intro i a b
      obtain ⟨u, hu⟩ : ∃ u : ℕ, (u : ℤ) = i + 8 := ⟨(i + 8).toNat, by omega⟩
      have hj' := abs_le.mp hj
      have := tip_all 8 u (by omega) j (by rw [abs_le]; omega)
      rw [show (u : ℤ) - ((8 : ℕ) : ℤ) = i by push_cast; omega] at this
      rw [this, show idx 8 = 8 from rfl]
      have h1 := List.all_eq_true.mp baseOK j (mem3 hj)
      simp only [Bool.and_eq_true] at h1
      have hu' : u = 6 ∨ u = 7 ∨ u = 8 := by omega
      rcases hu' with rfl | rfl | rfl
      · exact h1.1.1
      · exact h1.1.2
      · exact h1.2
    push_cast at hi1 hi2
    rcases le_or_gt i 0 with h | h
    · exact key i (by omega) h
    · rw [← symm_i]
      exact key (-i) (by omega) (by omega)
  | succ t ht ih =>
    intro i hi1 hi2 j hj
    push_cast at hi1 hi2
    by_cases hl : i ≤ -(t : ℤ) + 6
    · obtain ⟨u, hu⟩ : ∃ u : ℕ, (u : ℤ) = i + t + 1 := ⟨(i + t + 1).toNat, by omega⟩
      have := edge (t + 1) (by omega) u (by omega) j hj
      rwa [show (u : ℤ) - ((t + 1 : ℕ) : ℤ) = i by push_cast; omega] at this
    by_cases hr : (t : ℤ) - 6 ≤ i
    · rw [← symm_i]
      obtain ⟨u, hu⟩ : ∃ u : ℕ, (u : ℤ) = -i + t + 1 := ⟨(-i + t + 1).toNat, by omega⟩
      have := edge (t + 1) (by omega) u (by omega) j hj
      rwa [show (u : ℤ) - ((t + 1 : ℕ) : ℤ) = -i by push_cast; omega] at this
    · push Not at hl hr
      have hjc : j = -1 ∨ j = 0 ∨ j = 1 := by have := abs_le.mp hj; omega
      rw [c_succ, ih (i + 1) (by omega) (by omega) j hj, ih (i - 1) (by omega) (by omega) j hj]
      rcases hjc with rfl | rfl | rfl
      · rw [ih i (by omega) (by omega) (-1 + 1) (by norm_num)]
        cases cell 974 t i (-1) <;> cases cell 974 t i (-1 - 1) <;> rfl
      · rw [ih i (by omega) (by omega) (0 + 1) (by norm_num),
          ih i (by omega) (by omega) (0 - 1) (by norm_num)]
        cases cell 974 t i 0 <;> rfl
      · rw [ih i (by omega) (by omega) (1 - 1) (by norm_num)]
        cases cell 974 t i 1 <;> cases cell 974 t i (1 + 1) <;> rfl

/-- The six leading digits of the row, by residue of n mod 4. -/
def A (r : ℕ) : ℤ := if r = 0 then 111011 else if r = 1 then 110101 else if r = 2 then 111000 else 110110

def V (s : ℕ) : ℤ := ∑ k ∈ Finset.range 6, if Qb (P s) k 0 then (10 : ℤ) ^ (5 - k) else 0

theorem vOK : (List.range 25).all (fun s => decide (V (s + 8) = A ((s + 8) % 4))) = true := by
  decide +kernel

theorem V_idx (n : ℕ) (hn : 8 ≤ n) : V (idx n) = A (n % 4) := by
  have h0 := List.all_eq_true.mp vOK (idx n - 8)
    (List.mem_range.mpr (by have := idx_lt n; omega))
  rw [show idx n - 8 + 8 = idx n by have := idx_ge n hn; omega, idx_mod, decide_eq_true_iff] at h0
  exact h0

theorem rep (m : ℕ) : 9 * ∑ x ∈ Finset.range m, (10 : ℤ) ^ (m - 1 - x) = 10 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ']
    have e : ∑ x ∈ Finset.range m, (10 : ℤ) ^ (m + 1 - 1 - (x + 1)) =
        ∑ x ∈ Finset.range m, (10 : ℤ) ^ (m - 1 - x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [show m + 1 - 1 - (x + 1) = m - 1 - x by omega]
    rw [e, show m + 1 - 1 - 0 = m by omega, mul_add, ih, pow_succ]
    ring

theorem closed (n : ℕ) (hn : 8 ≤ n) :
    9 * a n = 9 * 10 ^ (n - 5) * A (n % 4) + 10 ^ (n - 5) - 1 := by
  unfold a
  rw [show n + 1 = 6 + (n - 5) by omega, Finset.sum_range_add]
  have h1 : ∑ k ∈ Finset.range 6, (if cell 974 n ((k : ℤ) - n) 0 then (10 : ℤ) ^ (n - k) else 0)
      = 10 ^ (n - 5) * V (idx n) := by
    unfold V
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [tip_all n k (by omega) 0 (by simp)]
    split_ifs
    · rw [← pow_add]
      congr 1
      omega
    · simp
  have h2 : ∑ x ∈ Finset.range (n - 5),
      (if cell 974 n (((6 + x : ℕ) : ℤ) - n) 0 then (10 : ℤ) ^ (n - (6 + x)) else 0)
      = ∑ x ∈ Finset.range (n - 5), (10 : ℤ) ^ (n - 5 - 1 - x) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hx' := Finset.mem_range.mp hx
    rw [band n hn _ (by push_cast; omega) (by push_cast; omega) 0 (by simp), if_pos rfl]
    congr 1
    omega
  rw [h1, h2, mul_add, rep, V_idx n hn]
  ring

theorem a_small (n : ℕ) (hn : n ≤ 8) :
    a n = ∑ k ∈ Finset.range (n + 1), if Qb (P n) k 0 then (10 : ℤ) ^ (n - k) else 0 := by
  unfold a
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [tip_all n k (by omega) 0 (by simp), show idx n = n by unfold idx; split_ifs <;> omega]

theorem vals : a 0 = 1 ∧ a 1 = 11 ∧ a 2 = 111 ∧ a 3 = 1101 ∧ a 4 = 11101 ∧ a 5 = 110101 ∧
    a 6 = 1110001 ∧ a 7 = 11011011 ∧ a 8 = 111011111 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [a_small _ (by norm_num)] <;> decide +kernel

theorem vals2 : a 9 = 1101011111 ∧ a 10 = 11100011111 ∧ a 11 = 110110111111 ∧
    a 12 = 1110111111111 := by
  have h9 := closed 9 (by norm_num)
  have h10 := closed 10 (by norm_num)
  have h11 := closed 11 (by norm_num)
  have h12 := closed 12 (by norm_num)
  norm_num [A] at h9 h10 h11 h12
  omega

theorem recZ (n : ℕ) (hn : 9 ≤ n) :
    (a n : ℚ) = a (n - 1) + 10000 * a (n - 4) - 10000 * a (n - 5) := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8⟩ := vals
  obtain ⟨v9, v10, v11, v12⟩ := vals2
  rcases (show n ≤ 12 ∨ 13 ≤ n by omega) with h | h
  · interval_cases n
    · rw [show 9 - 1 = 8 from rfl, show 9 - 4 = 5 from rfl, show 9 - 5 = 4 from rfl, v9, v8, v5, v4]
      norm_num
    · rw [show 10 - 1 = 9 from rfl, show 10 - 4 = 6 from rfl, show 10 - 5 = 5 from rfl, v10, v9, v6, v5]
      norm_num
    · rw [show 11 - 1 = 10 from rfl, show 11 - 4 = 7 from rfl, show 11 - 5 = 6 from rfl, v11, v10, v7,
        v6]
      norm_num
    · rw [show 12 - 1 = 11 from rfl, show 12 - 4 = 8 from rfl, show 12 - 5 = 7 from rfl, v12, v11, v8,
        v7]
      norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 13 := ⟨n - 13, by omega⟩
    have c0 := closed (m + 13) (by omega)
    have c1 := closed (m + 13 - 1) (by omega)
    have c4 := closed (m + 13 - 4) (by omega)
    have c5 := closed (m + 13 - 5) (by omega)
    rw [show m + 13 - 1 - 5 = m + 7 by omega, show (m + 13 - 1) % 4 = (m + 12) % 4 by omega] at c1
    rw [show m + 13 - 4 - 5 = m + 4 by omega, show (m + 13 - 4) % 4 = (m + 13) % 4 by omega] at c4
    rw [show m + 13 - 5 - 5 = m + 3 by omega, show (m + 13 - 5) % 4 = (m + 12) % 4 by omega] at c5
    rw [show m + 13 - 5 = m + 8 by omega] at c0
    have q0 : (9 : ℚ) * a (m + 13) = 9 * 10 ^ (m + 8) * A ((m + 13) % 4) + 10 ^ (m + 8) - 1 := by
      exact_mod_cast c0
    have q1 : (9 : ℚ) * a (m + 13 - 1) = 9 * 10 ^ (m + 7) * A ((m + 12) % 4) + 10 ^ (m + 7) - 1 := by
      exact_mod_cast c1
    have q4 : (9 : ℚ) * a (m + 13 - 4) = 9 * 10 ^ (m + 4) * A ((m + 13) % 4) + 10 ^ (m + 4) - 1 := by
      exact_mod_cast c4
    have q5 : (9 : ℚ) * a (m + 13 - 5) = 9 * 10 ^ (m + 3) * A ((m + 12) % 4) + 10 ^ (m + 3) - 1 := by
      exact_mod_cast c5
    linear_combination (1 / 9 : ℚ) * q0 - (1 / 9 : ℚ) * q1 - (10000 / 9 : ℚ) * q4 + (10000 / 9 : ℚ) * q5

end OMA.Helpers

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a284540.main := by
  refine ⟨?_, fun n hn => OMA.Helpers.recZ n hn⟩
  set g : ℕ → ℚ := fun n => (OMA.S_oeis_a284540.a n : ℚ) with hg
  have e1 : PowerSeries.mk g * ((1 - X) * (1 - 10 * X) * (1 + 10 * X) * (1 + 100 * X ^ 2))
      = PowerSeries.mk g - PowerSeries.mk g * X ^ 1 - C (10000 : ℚ) * (PowerSeries.mk g * X ^ 4)
        + C (10000 : ℚ) * (PowerSeries.mk g * X ^ 5) := by
    simp only [map_ofNat]
    ring
  have e2 : (1 + 10 * X + 100 * X ^ 2 + 990 * X ^ 3 - 1000 * X ^ 5 - 100 * X ^ 6 + 1010 * X ^ 7
      + 100 * X ^ 8 : PowerSeries ℚ)
      = C (1 : ℚ) * X ^ 0 + C (10 : ℚ) * X ^ 1 + C (100 : ℚ) * X ^ 2 + C (990 : ℚ) * X ^ 3
        - C (1000 : ℚ) * X ^ 5 - C (100 : ℚ) * X ^ 6 + C (1010 : ℚ) * X ^ 7
        + C (100 : ℚ) * X ^ 8 := by
    simp only [map_one, map_ofNat]
    ring
  rw [e1, e2]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8⟩ := OMA.Helpers.vals
  rcases Nat.lt_or_ge k 9 with hk | hk
  · interval_cases k <;> simp [hg, v0, v1, v2, v3, v4, v5, v6, v7, v8] <;> norm_num
  · have r := OMA.Helpers.recZ k hk
    simp only [show 5 ≤ k by omega, show 4 ≤ k by omega, show 1 ≤ k by omega, if_true,
      show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, show k ≠ 3 by omega,
      show k ≠ 5 by omega, show k ≠ 6 by omega, show k ≠ 7 by omega, show k ≠ 8 by omega,
      if_false, hg]
    rw [r]
    ring
