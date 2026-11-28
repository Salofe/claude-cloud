import OMAStatements.S_oeis_a183906

/-!
Proof of Barker's conjectures for A183906 (nondecreasing arrangements of n+2 numbers in 0..3 with
each number being the sum mod 4 of two others).

* Whether position `i` of an arrangement `x` satisfies the condition depends only on `x i` and on
  the counts `m v = #{k | x k = v}`: two other positions exist iff some `u` makes the multiset
  `{x i, u, x i - u}` fit into the counts (`forward`, `backward`). Hence
  `Good x ↔ Monotone x ∧ W m` (`good_iff`).
* A nondecreasing arrangement of length `N` is determined by its counts, which form a composition
  of `N` into four parts (`arr`, `card_good`). So `a n = #(S (n + 2))`, where `S N` is the set of
  compositions of `N` satisfying `W` (`a_eq`).
* `W m` only depends on the capped counts `min (m v) 3` (`W_cap`). Grouping the compositions by
  their capped pattern `c` gives `F = ∑ #(S N) X^N = ∑_{c valid} ∏_v phi (c v)` (`F_eq`), where
  `phi j = X^j` for `j < 3` and `(1 - X) phi 3 = X^3` (`phi_mul`). A kernel computation over the
  256 patterns (154 of them valid) then gives
  `(1 - X)^4 F = Q = 1 - 4x + 6x^2 - 2x^3 - 2x^4 + 9x^5 - 8x^6 - x^7 + 2x^8`
  (`one_sub_X_pow_mul_F`).
* `F = 1 + X^2 A` for the series `A` of the statement (`X_sq_mul_A`), and
  `Q - (1 - x)^4 = x^3 (2 - 3x + 9x^2 - 8x^3 - x^4 + 2x^5)`, which gives the generating function
  (`gen_fun`). The recurrence compares the coefficients of index `n + 2 ≥ 9` of
  `(1 - X)^4 F = Q` (`recurrence`).
-/

namespace OMA.Helpers

open OMA.S_oeis_a183906 Finset

/-- Indicator of `v = w`. -/
def ind (v w : Fin 4) : ℕ := if v = w then 1 else 0

/-- The condition on the counts `m v` of the values `v`: for every value `v` that occurs, some `u`
makes the multiset `{v, u, v - u}` fit into the counts. -/
def W (m : Fin 4 → ℕ) : Prop :=
  ∀ v : Fin 4, 0 < m v → ∃ u : Fin 4, ∀ y : Fin 4, ind v y + ind u y + ind (v - u) y ≤ m y

instance (m : Fin 4 → ℕ) : Decidable (W m) := by
  unfold W
  infer_instance

/-- The existential of the definition, at the position `i`. -/
def E {N : ℕ} (x : Fin N → Fin 4) (i : Fin N) : Prop :=
  ∃ j k : Fin N, j ≠ i ∧ k ≠ i ∧ j ≠ k ∧ ((x j : ℕ) + (x k : ℕ)) % 4 = (x i : ℕ)

/-- The number of positions holding `v`. -/
def cnt {N : ℕ} (x : Fin N → Fin 4) (v : Fin 4) : ℕ := #{i | x i = v}

theorem fin4_add : ∀ a b c : Fin 4, ((a : ℕ) + (b : ℕ)) % 4 = (c : ℕ) ↔ b = c - a := by
  decide

theorem cnt_ge3 {N : ℕ} (x : Fin N → Fin 4) (i j k : Fin N) (hj : j ≠ i) (hk : k ≠ i)
    (hjk : j ≠ k) (y : Fin 4) : ind (x i) y + ind (x j) y + ind (x k) y ≤ cnt x y := by
  have hsub : ({i, j, k} : Finset (Fin N)).filter (fun t => x t = y) ⊆
      univ.filter (fun t => x t = y) := filter_subset_filter _ (subset_univ _)
  refine le_trans (le_of_eq ?_) (card_le_card hsub)
  rw [card_filter, sum_insert, sum_insert, sum_singleton]
  · simp only [ind, add_assoc]
  · simpa using hjk
  · simp [hj.symm, hk.symm]

theorem forward {N : ℕ} (x : Fin N → Fin 4) (i : Fin N) (h : E x i) :
    ∃ u : Fin 4, ∀ y : Fin 4, ind (x i) y + ind u y + ind (x i - u) y ≤ cnt x y := by
  obtain ⟨j, k, hj, hk, hjk, hs⟩ := h
  refine ⟨x j, fun y => ?_⟩
  have hxk : x k = x i - x j := (fin4_add _ _ _).1 hs
  rw [← hxk]
  exact cnt_ge3 x i j k hj hk hjk y

/-- Erasing a position from a set of positions holding `w` loses at most one element, and only
when that position holds `w`. -/
theorem card_erase_ge {N : ℕ} (x : Fin N → Fin 4) (w : Fin 4) (s : Finset (Fin N))
    (hs : ∀ t ∈ s, x t = w) (a : Fin N) : #s ≤ #(s.erase a) + ind (x a) w := by
  by_cases h : a ∈ s
  · rw [card_erase_of_mem h, ind, if_pos (hs a h)]
    have := card_pos.2 ⟨a, h⟩
    omega
  · rw [erase_eq_of_notMem h]
    omega

theorem backward {N : ℕ} (x : Fin N → Fin 4) (i : Fin N) (u : Fin 4)
    (h : ∀ y : Fin 4, ind (x i) y + ind u y + ind (x i - u) y ≤ cnt x y) : E x i := by
  -- a position `j ≠ i` holding `u`
  have hu := h u
  have hU := card_erase_ge x u (univ.filter (fun t => x t = u)) (by simp) i
  have h1 : ind u u = 1 := by simp [ind]
  unfold cnt at hu
  obtain ⟨j, hj⟩ := card_pos.1 (show 0 < #((univ.filter (fun t => x t = u)).erase i) by omega)
  rw [mem_erase, mem_filter] at hj
  obtain ⟨hji, -, hxj⟩ := hj
  -- a position `k ∉ {i, j}` holding `x i - u`
  have hw := h (x i - u)
  unfold cnt at hw
  have hW1 := card_erase_ge x (x i - u) (univ.filter (fun t => x t = x i - u)) (by simp) i
  have hW2 := card_erase_ge x (x i - u) ((univ.filter (fun t => x t = x i - u)).erase i)
    (fun t ht => by simp only [mem_erase, mem_filter] at ht; exact ht.2.2) j
  rw [hxj] at hW2
  have h2 : ind (x i - u) (x i - u) = 1 := by simp [ind]
  obtain ⟨k, hk⟩ := card_pos.1
    (show 0 < #(((univ.filter (fun t => x t = x i - u)).erase i).erase j) by omega)
  rw [mem_erase, mem_erase, mem_filter] at hk
  obtain ⟨hkj, hki, -, hxk⟩ := hk
  refine ⟨j, k, hji, hki, fun h => hkj h.symm, ?_⟩
  rw [fin4_add, hxj, hxk]

theorem allE_iff {N : ℕ} (x : Fin N → Fin 4) : (∀ i, E x i) ↔ W (cnt x) := by
  constructor
  · intro h v hv
    obtain ⟨i, hi⟩ := card_pos.1 hv
    rw [mem_filter] at hi
    obtain ⟨u, hu⟩ := forward x i (h i)
    rw [hi.2] at hu
    exact ⟨u, hu⟩
  · intro h i
    have hpos : 0 < cnt x (x i) := card_pos.2 ⟨i, by rw [mem_filter]; exact ⟨mem_univ _, rfl⟩⟩
    obtain ⟨u, hu⟩ := h (x i) hpos
    exact backward x i u hu

/-- Whether an arrangement is good depends only on monotonicity and on the four counts. -/
theorem good_iff {N : ℕ} (x : Fin N → Fin 4) : Good x ↔ Monotone x ∧ W (cnt x) :=
  and_congr Iff.rfl (allE_iff x)

/-- The number of positions holding a value `≤ w` is the sum of the counts of these values. -/
theorem card_le_eq {N : ℕ} (x : Fin N → Fin 4) (w : Fin 4) :
    #{t | x t ≤ w} = ∑ v ∈ (univ.filter (· ≤ w) : Finset (Fin 4)), cnt x v := by
  rw [card_eq_sum_card_fiberwise (f := x) (t := univ.filter (· ≤ w))]
  · refine sum_congr rfl fun v hv => ?_
    rw [mem_filter] at hv
    unfold cnt
    congr 1
    ext t
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hv.2, h⟩⟩
  · intro t ht
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
    exact ht

theorem card_le0 {N : ℕ} (x : Fin N → Fin 4) : #{t | x t ≤ 0} = cnt x 0 := by
  rw [card_le_eq, show (univ.filter (· ≤ (0 : Fin 4)) : Finset (Fin 4)) = {0} by decide,
    sum_singleton]

theorem card_le1 {N : ℕ} (x : Fin N → Fin 4) : #{t | x t ≤ 1} = cnt x 0 + cnt x 1 := by
  rw [card_le_eq, show (univ.filter (· ≤ (1 : Fin 4)) : Finset (Fin 4)) = {0, 1} by decide,
    sum_pair (by decide)]

theorem card_le2 {N : ℕ} (x : Fin N → Fin 4) :
    #{t | x t ≤ 2} = cnt x 0 + cnt x 1 + cnt x 2 := by
  rw [card_le_eq, show (univ.filter (· ≤ (2 : Fin 4)) : Finset (Fin 4)) = {0, 1, 2} by decide,
    sum_insert (by decide), sum_pair (by decide), add_assoc]

theorem cnt_sum {N : ℕ} (x : Fin N → Fin 4) : cnt x 0 + cnt x 1 + cnt x 2 + cnt x 3 = N := by
  have h := card_eq_sum_card_fiberwise (f := x) (s := univ) (t := univ) (by simp)
  rw [card_univ, Fintype.card_fin, Fin.sum_univ_four] at h
  exact h.symm

/-- The arrangement with `a` zeros, then `b` ones, then `c` twos, then threes. -/
def arr (N a b c : ℕ) : Fin N → Fin 4 := fun i =>
  if (i : ℕ) < a then 0 else if (i : ℕ) < a + b then 1 else if (i : ℕ) < a + b + c then 2 else 3

theorem arr_mono (N a b c : ℕ) : Monotone (arr N a b c) := by
  intro i j hij
  have hij' : (i : ℕ) ≤ j := hij
  unfold arr
  split_ifs <;> first | decide | (exfalso; omega)

theorem arr_le0 (N a b c : ℕ) (i : Fin N) : arr N a b c i ≤ 0 ↔ (i : ℕ) < a := by
  unfold arr
  split_ifs with h1 h2 h3
  · exact iff_of_true (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1
  · exact iff_of_false (by decide) h1

theorem arr_le1 (N a b c : ℕ) (i : Fin N) : arr N a b c i ≤ 1 ↔ (i : ℕ) < a + b := by
  unfold arr
  split_ifs with h1 h2 h3
  · exact iff_of_true (by decide) (by omega)
  · exact iff_of_true (by decide) h2
  · exact iff_of_false (by decide) h2
  · exact iff_of_false (by decide) h2

theorem arr_le2 (N a b c : ℕ) (i : Fin N) : arr N a b c i ≤ 2 ↔ (i : ℕ) < a + b + c := by
  unfold arr
  split_ifs with h1 h2 h3
  · exact iff_of_true (by decide) (by omega)
  · exact iff_of_true (by decide) (by omega)
  · exact iff_of_true (by decide) h3
  · exact iff_of_false (by decide) h3

theorem cnt_arr (N a b c : ℕ) (h : a + b + c ≤ N) :
    cnt (arr N a b c) 0 = a ∧ cnt (arr N a b c) 1 = b ∧ cnt (arr N a b c) 2 = c ∧
      cnt (arr N a b c) 3 = N - (a + b + c) := by
  have e0 := card_le0 (arr N a b c)
  have e1 := card_le1 (arr N a b c)
  have e2 := card_le2 (arr N a b c)
  have e3 := cnt_sum (arr N a b c)
  rw [filter_congr (fun t _ => arr_le0 N a b c t), Fin.card_filter_val_lt] at e0
  rw [filter_congr (fun t _ => arr_le1 N a b c t), Fin.card_filter_val_lt] at e1
  rw [filter_congr (fun t _ => arr_le2 N a b c t), Fin.card_filter_val_lt] at e2
  have m0 : min N a = a := by omega
  have m1 : min N (a + b) = a + b := by omega
  have m2 : min N (a + b + c) = a + b + c := by omega
  omega

theorem fin4_ite : ∀ v : Fin 4,
    (if v ≤ 0 then 0 else if v ≤ 1 then 1 else if v ≤ 2 then 2 else 3) = v := by
  decide

theorem arr_cnt {N : ℕ} (x : Fin N → Fin 4) (hx : Monotone x) :
    arr N (cnt x 0) (cnt x 1) (cnt x 2) = x := by
  funext i
  have h0 := Tuple.lt_card_le_iff_apply_le_of_monotone (j := i) (a := (0 : Fin 4)) hx
  have h1 := Tuple.lt_card_le_iff_apply_le_of_monotone (j := i) (a := (1 : Fin 4)) hx
  have h2 := Tuple.lt_card_le_iff_apply_le_of_monotone (j := i) (a := (2 : Fin 4)) hx
  rw [card_le0] at h0
  rw [card_le1] at h1
  rw [card_le2] at h2
  unfold arr
  simp only [h0, h1, h2]
  exact fin4_ite (x i)

/-- The compositions of `N` into four parts (the counts of `0, 1, 2, 3`) satisfying `W`. -/
def S (N : ℕ) : Finset (Fin 4 →₀ ℕ) :=
  (finsuppAntidiag (univ : Finset (Fin 4)) N).filter (fun l => W ⇑l)

theorem mem_S {N : ℕ} {l : Fin 4 →₀ ℕ} : l ∈ S N ↔ l 0 + l 1 + l 2 + l 3 = N ∧ W ⇑l := by
  rw [S, mem_filter, mem_finsuppAntidiag, Fin.sum_univ_four]
  constructor
  · rintro ⟨⟨h, -⟩, hW⟩
    exact ⟨h, hW⟩
  · rintro ⟨h, hW⟩
    exact ⟨⟨h, subset_univ _⟩, hW⟩

theorem cnt_arr_fun (N : ℕ) (l : Fin 4 →₀ ℕ) (h : l 0 + l 1 + l 2 + l 3 = N) :
    cnt (arr N (l 0) (l 1) (l 2)) = ⇑l := by
  obtain ⟨c0, c1, c2, c3⟩ := cnt_arr N (l 0) (l 1) (l 2) (by omega)
  funext v
  fin_cases v
  · exact c0
  · exact c1
  · exact c2
  · show cnt (arr N (l 0) (l 1) (l 2)) 3 = l 3
    rw [c3]
    omega

theorem card_good (N : ℕ) [DecidablePred (fun x : Fin N → Fin 4 => Good x)] :
    #(univ.filter (fun x : Fin N → Fin 4 => Good x)) = #(S N) := by
  apply card_nbij' (fun x => Finsupp.equivFunOnFinite.symm (cnt x))
    (fun l => arr N (l 0) (l 1) (l 2))
  · intro x hx
    rw [mem_coe, mem_filter] at hx
    obtain ⟨-, hW⟩ := (good_iff x).1 hx.2
    rw [mem_coe, mem_S, Finsupp.coe_equivFunOnFinite_symm]
    exact ⟨cnt_sum x, hW⟩
  · intro l hl
    rw [mem_coe, mem_S] at hl
    rw [mem_coe, mem_filter]
    refine ⟨mem_univ _, (good_iff _).2 ⟨arr_mono N _ _ _, ?_⟩⟩
    rw [cnt_arr_fun N l hl.1]
    exact hl.2
  · intro x hx
    rw [mem_coe, mem_filter] at hx
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    exact arr_cnt x ((good_iff x).1 hx.2).1
  · intro l hl
    rw [mem_coe, mem_S] at hl
    apply Finsupp.ext
    intro v
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    rw [cnt_arr_fun N l hl.1]

theorem a_eq (n : ℕ) : a n = #(S (n + 2)) := by
  classical
  rw [a, Nat.card_eq_fintype_card, Fintype.card_subtype, card_good]

/-! ### The generating function of the good compositions -/

open PowerSeries

/-- The generating function `∑ #(S N) X^N` of the good compositions. -/
noncomputable def F : PowerSeries ℤ := PowerSeries.mk (fun N => ((#(S N) : ℕ) : ℤ))

/-- The series `∑ X^k` over the `k` with `min k 3 = j`. -/
noncomputable def phi (j : Fin 4) : PowerSeries ℤ :=
  PowerSeries.mk (fun k => if min k 3 = (j : ℕ) then 1 else 0)

theorem coeff_prod_phi (c : Fin 4 → Fin 4) (N : ℕ) :
    coeff N (∏ v, phi (c v)) =
      ∑ l ∈ finsuppAntidiag (univ : Finset (Fin 4)) N,
        if ∀ v, min (l v) 3 = (c v : ℕ) then 1 else 0 := by
  rw [coeff_prod]
  refine sum_congr rfl fun l _ => ?_
  simp only [phi, coeff_mk]
  rw [Fintype.prod_boole]
  by_cases h : ∀ v : Fin 4, min (l v) 3 = (c v : ℕ) <;> simp [h]

/-- The capped patterns satisfying `W`. -/
def P : Finset (Fin 4 → Fin 4) := univ.filter (fun c => W (fun v => (c v : ℕ)))

theorem W_cap (m : Fin 4 → ℕ) : W (fun v => min (m v) 3) ↔ W m := by
  have hind : ∀ a b : Fin 4, ind a b ≤ 1 := fun a b => by
    unfold ind
    split_ifs <;> omega
  simp only [W]
  refine forall_congr' fun v => imp_congr ?_ (exists_congr fun u => forall_congr' fun y => ?_)
  · rw [lt_min_iff]
    omega
  · rw [le_min_iff]
    have := hind v y
    have := hind u y
    have := hind (v - u) y
    omega

theorem sum_P_indicator (l : Fin 4 →₀ ℕ) :
    (∑ c ∈ P, if ∀ v, min (l v) 3 = (c v : ℕ) then (1 : ℤ) else 0) =
      if W ⇑l then 1 else 0 := by
  set cl : Fin 4 → Fin 4 := fun v => ⟨min (l v) 3, by omega⟩
  have key : ∀ c : Fin 4 → Fin 4, (∀ v, min (l v) 3 = (c v : ℕ)) ↔ c = cl := by
    intro c
    constructor
    · intro h
      funext v
      exact Fin.ext (h v).symm
    · rintro rfl v
      rfl
  have hmem : cl ∈ P ↔ W ⇑l := by
    rw [P, mem_filter]
    have hc := W_cap ⇑l
    exact ⟨fun h => hc.1 h.2, fun h => ⟨mem_univ _, hc.2 h⟩⟩
  by_cases hW : W ⇑l
  · rw [if_pos hW, sum_eq_single_of_mem cl (hmem.2 hW)]
    · exact if_pos ((key cl).2 rfl)
    · intro c _ hc
      exact if_neg fun h => hc ((key c).1 h)
  · rw [if_neg hW]
    refine sum_eq_zero fun c hc => if_neg fun h => hW (hmem.1 ?_)
    rw [← (key c).1 h]
    exact hc

theorem F_eq : F = ∑ c ∈ P, ∏ v, phi (c v) := by
  ext N
  rw [F, coeff_mk, map_sum]
  simp only [coeff_prod_phi]
  rw [sum_comm]
  simp only [sum_P_indicator]
  rw [S, card_filter]
  push_cast
  rfl

/-- The exponent of `1 - X` in `(1 - X) * phi j`. -/
def e3 (j : Fin 4) : ℕ := if j = 3 then 0 else 1

theorem phi_zero : phi 0 = 1 := by
  ext k
  rw [phi, coeff_mk, coeff_one]
  simp only [Fin.isValue, Fin.val_zero]
  split_ifs <;> omega

theorem phi_one : phi 1 = X := by
  ext k
  rw [phi, coeff_mk, coeff_X]
  simp only [Fin.isValue, Fin.val_one]
  split_ifs <;> omega

theorem phi_two : phi 2 = X ^ 2 := by
  ext k
  rw [phi, coeff_mk, coeff_X_pow]
  simp only [Fin.isValue, Fin.val_two]
  split_ifs <;> omega

theorem phi_three : (1 - X) * phi 3 = X ^ 3 := by
  ext k
  rw [sub_mul, one_mul, map_sub, coeff_X_pow]
  rcases k with _ | k
  · rw [coeff_zero_X_mul, phi, coeff_mk]
    simp
  · rw [coeff_succ_X_mul, phi, coeff_mk, coeff_mk]
    show ((if min (k + 1) 3 = 3 then 1 else 0) - (if min k 3 = 3 then 1 else 0) : ℤ) =
      if k + 1 = 3 then 1 else 0
    split_ifs <;> omega

theorem phi_mul (j : Fin 4) : (1 - X) * phi j = X ^ (j : ℕ) * (1 - X) ^ (e3 j) := by
  fin_cases j
  · show (1 - X) * phi 0 = X ^ 0 * (1 - X) ^ 1
    rw [phi_zero]
    ring
  · show (1 - X) * phi 1 = X ^ 1 * (1 - X) ^ 1
    rw [phi_one]
    ring
  · show (1 - X) * phi 2 = X ^ 2 * (1 - X) ^ 1
    rw [phi_two]
    ring
  · show (1 - X) * phi 3 = X ^ 3 * (1 - X) ^ 0
    rw [phi_three]
    ring

theorem prod_phi_mul (c : Fin 4 → Fin 4) :
    ∏ v, ((1 - X) * phi (c v)) = X ^ (∑ v, (c v : ℕ)) * (1 - X) ^ (∑ v, e3 (c v)) := by
  simp only [phi_mul, prod_mul_distrib, prod_pow_eq_pow_sum]

/-- The pair (sum, number of entries different from 3) of a capped pattern. -/
def bs (c : Fin 4 → Fin 4) : ℕ × ℕ := (∑ v, (c v : ℕ), ∑ v, e3 (c v))

/-- The multiset of the pairs `bs c` of the 154 capped patterns in `P`. -/
def M : Multiset (ℕ × ℕ) :=
  Multiset.replicate 1 (0, 4) + Multiset.replicate 1 (3, 3) + Multiset.replicate 1 (3, 4) +
  Multiset.replicate 1 (4, 3) + Multiset.replicate 3 (4, 4) + Multiset.replicate 6 (5, 3) +
  Multiset.replicate 9 (5, 4) + Multiset.replicate 3 (6, 2) + Multiset.replicate 17 (6, 3) +
  Multiset.replicate 10 (6, 4) + Multiset.replicate 8 (7, 2) + Multiset.replicate 24 (7, 3) +
  Multiset.replicate 4 (7, 4) + Multiset.replicate 18 (8, 2) + Multiset.replicate 12 (8, 3) +
  Multiset.replicate 1 (8, 4) + Multiset.replicate 4 (9, 1) + Multiset.replicate 12 (9, 2) +
  Multiset.replicate 4 (9, 3) + Multiset.replicate 4 (10, 1) + Multiset.replicate 6 (10, 2) +
  Multiset.replicate 4 (11, 1) + Multiset.replicate 1 (12, 0)

set_option maxHeartbeats 4000000 in
theorem map_bs : P.1.map bs = M := by
  decide +kernel

/-- The numerator `(1 - X)^4 F`. -/
noncomputable def Q : PowerSeries ℤ :=
  C 1 - C 4 * X ^ 1 + C 6 * X ^ 2 - C 2 * X ^ 3 - C 2 * X ^ 4 + C 9 * X ^ 5 - C 8 * X ^ 6 -
    C 1 * X ^ 7 + C 2 * X ^ 8

theorem sum_M : (M.map (fun p : ℕ × ℕ => (X : PowerSeries ℤ) ^ p.1 * (1 - X) ^ p.2)).sum = Q := by
  simp only [M, Q, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
    Multiset.sum_replicate, map_one, map_ofNat]
  simp only [nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

theorem one_sub_X_pow_mul_F : (1 - X) ^ 4 * F = Q := by
  rw [F_eq, mul_sum]
  set g : ℕ × ℕ → PowerSeries ℤ := fun p => X ^ p.1 * (1 - X) ^ p.2
  have h : ∀ c ∈ P, (1 - X) ^ 4 * ∏ v, phi (c v) = g (bs c) := by
    intro c _
    show _ = X ^ (∑ v, (c v : ℕ)) * (1 - X) ^ (∑ v, e3 (c v))
    rw [← prod_phi_mul, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
  rw [sum_congr rfl h, sum_eq_multiset_sum]
  have h2 : P.1.map (fun c => g (bs c)) = (P.1.map bs).map g := by
    rw [Multiset.map_map]
    rfl
  rw [h2, map_bs]
  exact sum_M

/-! ### Comparing coefficients -/

theorem coeff_one_sub_X_pow4_mul (f : PowerSeries ℤ) (k : ℕ) :
    coeff k ((1 - X) ^ 4 * f) =
      coeff k f - 4 * (if 1 ≤ k then coeff (k - 1) f else 0) +
        6 * (if 2 ≤ k then coeff (k - 2) f else 0) -
        4 * (if 3 ≤ k then coeff (k - 3) f else 0) + (if 4 ≤ k then coeff (k - 4) f else 0) := by
  have h : (1 - X) ^ 4 * f =
      f - C 4 * (X ^ 1 * f) + C 6 * (X ^ 2 * f) - C 4 * (X ^ 3 * f) + X ^ 4 * f := by
    simp only [map_ofNat]
    ring
  rw [h]
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul']

theorem coeff_Q (k : ℕ) : coeff k Q =
    (if k = 0 then 1 else 0) - (if k = 1 then 4 else 0) + (if k = 2 then 6 else 0) -
      (if k = 3 then 2 else 0) - (if k = 4 then 2 else 0) + (if k = 5 then 9 else 0) -
      (if k = 6 then 8 else 0) - (if k = 7 then 1 else 0) + (if k = 8 then 2 else 0) := by
  simp only [Q, map_add, map_sub, coeff_C, coeff_C_mul_X_pow]

theorem coeff_F (N : ℕ) : coeff N F = ((#(S N) : ℕ) : ℤ) := by
  rw [F, coeff_mk]

theorem S_zero : ((#(S 0) : ℕ) : ℤ) = 1 := by
  have h := congrArg (coeff 0) one_sub_X_pow_mul_F
  rw [coeff_one_sub_X_pow4_mul, coeff_Q] at h
  simp only [coeff_F] at h
  norm_num at h
  exact_mod_cast h

theorem S_one : ((#(S 1) : ℕ) : ℤ) = 0 := by
  have h := congrArg (coeff 1) one_sub_X_pow_mul_F
  rw [coeff_one_sub_X_pow4_mul, coeff_Q] at h
  simp only [coeff_F] at h
  norm_num [S_zero] at h
  simp [h]

theorem S_two : ((#(S 2) : ℕ) : ℤ) = 0 := by
  have h := congrArg (coeff 2) one_sub_X_pow_mul_F
  rw [coeff_one_sub_X_pow4_mul, coeff_Q] at h
  simp only [coeff_F] at h
  norm_num [S_zero, S_one] at h
  simp [h]

/-- The generating function of the statement. -/
noncomputable def A : PowerSeries ℤ :=
  PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ))

theorem X_sq_mul_A : X ^ 2 * A = F - 1 := by
  ext N
  rw [coeff_X_pow_mul', map_sub, coeff_F, coeff_one]
  rcases N with _ | _ | _ | m
  · simp [S_zero]
  · simp [S_one]
  · simp [A, S_two]
  · rw [if_pos (by omega), A, coeff_mk, if_neg (by omega), if_neg (by omega), sub_zero,
      a_eq]
    congr 3

theorem gen_fun :
    A * ((1 - X) ^ 4 : PowerSeries ℤ) =
      X * (2 - 3 * X + 9 * X ^ 2 - 8 * X ^ 3 - X ^ 4 + 2 * X ^ 5) := by
  apply X_pow_mul_cancel (k := 2)
  calc X ^ 2 * (A * (1 - X) ^ 4) = (1 - X) ^ 4 * (X ^ 2 * A) := by ring
    _ = (1 - X) ^ 4 * F - (1 - X) ^ 4 := by rw [X_sq_mul_A]; ring
    _ = Q - (1 - X) ^ 4 := by rw [one_sub_X_pow_mul_F]
    _ = X ^ 2 * (X * (2 - 3 * X + 9 * X ^ 2 - 8 * X ^ 3 - X ^ 4 + 2 * X ^ 5)) := by
      simp only [Q, map_one, map_ofNat]
      ring

theorem coeff_Q_high (k : ℕ) (hk : 9 ≤ k) : coeff k Q = 0 := by
  rw [coeff_Q]
  split_ifs <;> omega

theorem recurrence (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 4 * (a (n - 1) : ℤ) - 6 * (a (n - 2) : ℤ) + 4 * (a (n - 3) : ℤ) -
      (a (n - 4) : ℤ) := by
  have h := congrArg (coeff (n + 2)) one_sub_X_pow_mul_F
  rw [coeff_one_sub_X_pow4_mul, coeff_Q_high _ (by omega)] at h
  simp only [coeff_F] at h
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)] at h
  rw [a_eq n, a_eq (n - 1), a_eq (n - 2), a_eq (n - 3), a_eq (n - 4)]
  rw [show n - 1 + 2 = n + 2 - 1 by omega, show n - 2 + 2 = n + 2 - 2 by omega,
    show n - 3 + 2 = n + 2 - 3 by omega, show n - 4 + 2 = n + 2 - 4 by omega]
  linarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a183906.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
