import OMAStatements.S_oeis_a290835

/-!
Proof of Barker's three conjectures for OEIS A290835 (Rule 969 from a single ON cell).

Rule 969 turns an OFF cell with no ON neighbour ON and keeps an ON cell with four ON neighbours
ON. Starting from the origin, the cells that differ from the (ON) background after stages
1, 2, 3, 4 are the plus shape, the four diagonal neighbours, the four orthogonal neighbours, and
the four diagonal neighbours together with the origin; at stage 5 every cell is ON and stays ON.
So a(n) = 11...1 (n + 1 ones) for n ≥ 5, and the closed form, the recurrence and the generating
function follow, the small values a(0..4) = 1, 1, 101, 1111, 111 by kernel computation.
-/

namespace OMA.Helpers

open OMA.S_oeis_a290835 PowerSeries

theorem a290835_step (t : ℕ) (f g : ℤ × ℤ → Bool) (hf : ∀ p, state t p = f p)
    (hg : ∀ p, rule (f p) ((nbrs p).countP f) = g p) : ∀ p, state (t + 1) p = g p := by
  intro p
  have e : state t = f := funext hf
  show rule (state t p) ((nbrs p).countP (fun q => state t q)) = g p
  rw [e]
  exact hg p

/-- Membership of a point outside the box `[-1, 1]^2` in a list of points of that box. -/
theorem a290835_notMem (E : List (ℤ × ℤ))
    (hE : ∀ q ∈ E, -1 ≤ q.1 ∧ q.1 ≤ 1 ∧ -1 ≤ q.2 ∧ q.2 ≤ 1) (a b : ℤ)
    (h : a ≤ -2 ∨ 2 ≤ a ∨ b ≤ -2 ∨ 2 ≤ b) : decide ((a, b) ∉ E) = true := by
  rw [decide_eq_true_eq]
  intro hm
  have := hE _ hm
  simp only at this
  omega

/-- One stage between two configurations that are ON outside finite sets of the box `[-1,1]^2`:
it suffices to check the cells of the box `[-2, 2]^2`. -/
theorem a290835_gen (E E' : List (ℤ × ℤ))
    (hE : ∀ q ∈ E, -1 ≤ q.1 ∧ q.1 ≤ 1 ∧ -1 ≤ q.2 ∧ q.2 ≤ 1)
    (hE' : ∀ q ∈ E', -1 ≤ q.1 ∧ q.1 ≤ 1 ∧ -1 ≤ q.2 ∧ q.2 ≤ 1)
    (hin : ∀ x y : ℤ, -2 ≤ x → x ≤ 2 → -2 ≤ y → y ≤ 2 →
      rule (decide ((x, y) ∉ E)) ((nbrs (x, y)).countP (fun q => decide (q ∉ E)))
        = decide ((x, y) ∉ E')) :
    ∀ p : ℤ × ℤ, rule (decide (p ∉ E)) ((nbrs p).countP (fun q => decide (q ∉ E)))
      = decide (p ∉ E') := by
  rintro ⟨x, y⟩
  by_cases hb : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2
  · exact hin x y hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
  · have h0 := a290835_notMem E hE x y (by omega)
    have h1 := a290835_notMem E hE (x + 1) y (by omega)
    have h2 := a290835_notMem E hE (x - 1) y (by omega)
    have h3 := a290835_notMem E hE x (y + 1) (by omega)
    have h4 := a290835_notMem E hE x (y - 1) (by omega)
    have h5 := a290835_notMem E' hE' x y (by omega)
    simp only [nbrs, List.countP_cons, List.countP_nil, h0, h1, h2, h3, h4, h5]
    decide

def a290835E1 : List (ℤ × ℤ) := [(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)]
def a290835E2 : List (ℤ × ℤ) := [(1, 1), (1, -1), (-1, 1), (-1, -1)]
def a290835E3 : List (ℤ × ℤ) := [(1, 0), (-1, 0), (0, 1), (0, -1)]
def a290835E4 : List (ℤ × ℤ) := [(0, 0), (1, 1), (1, -1), (-1, 1), (-1, -1)]

theorem a290835_state1 : ∀ p, state 1 p = decide (p ∉ a290835E1) := by
  refine a290835_step 0 (fun p => decide (p = (0, 0))) _ (fun p => rfl) ?_
  rintro ⟨x, y⟩
  by_cases hb : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2
  · obtain ⟨h1, h2, h3, h4⟩ := hb
    interval_cases x <;> interval_cases y <;> decide
  · have k : ∀ a b : ℤ, (a ≤ -1 ∨ 1 ≤ a ∨ b ≤ -1 ∨ 1 ≤ b) → decide ((a, b) = (0, 0)) = false := by
      intro a b h
      rw [decide_eq_false_iff_not, Prod.mk.injEq]
      omega
    have h0 := k x y (by omega)
    have h1 := k (x + 1) y (by omega)
    have h2 := k (x - 1) y (by omega)
    have h3 := k x (y + 1) (by omega)
    have h4 := k x (y - 1) (by omega)
    have h5 := a290835_notMem a290835E1 (by decide) x y (by omega)
    simp only [nbrs, List.countP_cons, List.countP_nil, h0, h1, h2, h3, h4, h5]
    decide

theorem a290835_box (E E' : List (ℤ × ℤ))
    (h : ∀ x ∈ [(-2 : ℤ), -1, 0, 1, 2], ∀ y ∈ [(-2 : ℤ), -1, 0, 1, 2],
      rule (decide ((x, y) ∉ E)) ((nbrs (x, y)).countP (fun q => decide (q ∉ E)))
        = decide ((x, y) ∉ E')) :
    ∀ x y : ℤ, -2 ≤ x → x ≤ 2 → -2 ≤ y → y ≤ 2 →
      rule (decide ((x, y) ∉ E)) ((nbrs (x, y)).countP (fun q => decide (q ∉ E)))
        = decide ((x, y) ∉ E') := by
  intro x y h1 h2 h3 h4
  apply h
  · simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false]; omega

theorem a290835_state2 : ∀ p, state 2 p = decide (p ∉ a290835E2) :=
  a290835_step 1 _ _ a290835_state1
    (a290835_gen _ _ (by decide) (by decide) (a290835_box _ _ (by decide)))

theorem a290835_state3 : ∀ p, state 3 p = decide (p ∉ a290835E3) :=
  a290835_step 2 _ _ a290835_state2
    (a290835_gen _ _ (by decide) (by decide) (a290835_box _ _ (by decide)))

theorem a290835_state4 : ∀ p, state 4 p = decide (p ∉ a290835E4) :=
  a290835_step 3 _ _ a290835_state3
    (a290835_gen _ _ (by decide) (by decide) (a290835_box _ _ (by decide)))

theorem a290835_state5 : ∀ p, state 5 p = true := by
  have := a290835_step 4 _ _ a290835_state4
    (a290835_gen a290835E4 [] (by decide) (by decide) (a290835_box _ _ (by decide)))
  intro p
  rw [this p]
  simp

theorem a290835_state_ge (m : ℕ) : ∀ p, state (m + 5) p = true := by
  induction m with
  | zero => exact a290835_state5
  | succ k ih =>
    refine a290835_step (k + 5) (fun _ => true) (fun _ => true) ih ?_
    intro p
    simp only [nbrs, List.countP_cons, List.countP_nil]
    decide

theorem a290835_geom (m : ℕ) :
    9 * (∑ k ∈ Finset.range (m + 1), 10 ^ (m - k)) + 1 = 10 ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ']
    have e : ∑ k ∈ Finset.range (m + 1), 10 ^ (m + 1 - (k + 1)) =
        ∑ k ∈ Finset.range (m + 1), 10 ^ (m - k) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.add_sub_add_right]
    rw [e, Nat.sub_zero, pow_succ 10 (m + 1)]
    omega

theorem a290835_a_ge (n : ℕ) (hn : 5 ≤ n) : 9 * a n + 1 = 10 ^ (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have e : a (m + 5) = ∑ k ∈ Finset.range (m + 5 + 1), 10 ^ (m + 5 - k) := by
    unfold a
    apply Finset.sum_congr rfl
    intro k _
    rw [a290835_state_ge m]
    rfl
  rw [e]
  exact a290835_geom (m + 5)

theorem a290835_small : a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 101 ∧ a 3 = 1111 ∧ a 4 = 111 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem a290835_closed (n : ℕ) (hn : 4 < n) : (a n : ℚ) = (10 ^ (1 + n) - 1) / 9 := by
  have h := a290835_a_ge n hn
  have hq : (9 * (a n : ℚ) + 1) = 10 ^ (n + 1) := by exact_mod_cast h
  rw [add_comm 1 n, eq_div_iff (by norm_num)]
  linarith

theorem a290835_rec (n : ℕ) (hn : 6 < n) : (a n : ℤ) = 11 * a (n - 1) - 10 * a (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  have h0 := a290835_a_ge (m + 2) (by omega)
  have h1 := a290835_a_ge (m + 1) (by omega)
  have h2 := a290835_a_ge m (by omega)
  rw [show m + 2 + 1 = (m + 1) + 2 by omega, pow_succ, pow_succ] at h0
  rw [show m + 1 + 1 = (m + 1) + 1 by omega, pow_succ] at h1
  generalize 10 ^ (m + 1) = X at h0 h1 h2
  omega

theorem a290835_gf :
    A = (1 - 10 * X + 100 * X ^ 2 + 10 * X ^ 3 - 11100 * X ^ 4 + 121000 * X ^ 5 - 110000 * X ^ 6) *
      ((1 - X) * (1 - 10 * X))⁻¹ := by
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  obtain ⟨h0, h1, h2, h3, h4⟩ := a290835_small
  have hz : ∀ n : ℕ, 5 ≤ n → (a n : ℚ) = (10 ^ (n + 1) - 1) / 9 := by
    intro n hn
    rw [a290835_closed n (by omega), add_comm 1 n]
  have e1 : A * ((1 - X) * (1 - 10 * X))
      = A - PowerSeries.C (11 : ℚ) * (A * X ^ 1) + PowerSeries.C (10 : ℚ) * (A * X ^ 2) := by
    simp only [map_ofNat]
    ring
  have e2 : (1 - 10 * X + 100 * X ^ 2 + 10 * X ^ 3 - 11100 * X ^ 4 + 121000 * X ^ 5
      - 110000 * X ^ 6 : ℚ⟦X⟧)
      = X ^ 0 - PowerSeries.C (10 : ℚ) * X ^ 1 + PowerSeries.C (100 : ℚ) * X ^ 2
        + PowerSeries.C (10 : ℚ) * X ^ 3 - PowerSeries.C (11100 : ℚ) * X ^ 4
        + PowerSeries.C (121000 : ℚ) * X ^ 5 - PowerSeries.C (110000 : ℚ) * X ^ 6 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', A, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  rcases Nat.lt_or_ge k 7 with hk | hk
  · interval_cases k
    · simp [h0]
    · simp [h0, h1]; norm_num
    · simp [h0, h1, h2]; norm_num
    · simp [h1, h2, h3]; norm_num
    · simp [h2, h3, h4]; norm_num
    · simp [h3, h4, hz 5 le_rfl]; norm_num
    · simp [h4, hz 5 le_rfl, hz 6 (by norm_num)]; norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 7 := ⟨k - 7, by omega⟩
    have c1 : 1 ≤ m + 7 := by omega
    have c2 : 2 ≤ m + 7 := by omega
    simp only [c1, c2, if_true, show m + 7 ≠ 0 by omega, show m + 7 ≠ 1 by omega,
      show m + 7 ≠ 2 by omega, show m + 7 ≠ 3 by omega, show m + 7 ≠ 4 by omega,
      show m + 7 ≠ 5 by omega, show m + 7 ≠ 6 by omega, if_false]
    rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega]
    rw [hz (m + 7) (by omega), hz (m + 6) (by omega), hz (m + 5) (by omega)]
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a290835.main :=
  ⟨OMA.Helpers.a290835_gf, OMA.Helpers.a290835_closed, OMA.Helpers.a290835_rec⟩
