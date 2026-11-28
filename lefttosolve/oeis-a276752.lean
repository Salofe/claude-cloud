import OMAStatements.S_oeis_a276752
import Mathlib

/-!
Upper bound: a list of positive integers with sum `n` and length `L` has product at most
`2 ^ (n - L)`, so every weight is at most `2 ^ (2 L (n - L)) <= sqrt 2 ^ (n ^ 2)`. Summing over the
`2 ^ (n - 1)` compositions twice gives `term n <= 4 ^ n * sqrt 2 ^ (n ^ 2)`.
Lower bound: `term n >= logCoeff n`, the summand of the one-block composition, and `logCoeff n` is
at least the summand of the composition into parts `2` (and one part `1` when `n` is odd), which
gives `term n >= sqrt 2 ^ (n ^ 2) / 4 ^ n`. Taking `1 / n ^ 2`-th powers, both bounds tend to
`sqrt 2`.
-/

namespace OMA.Helpers

open OMA.S_oeis_a276752 Filter Topology

theorem sqrt_two_ge_one : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr one_le_two

theorem sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

theorem card_comp_le (n : ℕ) : ((2 ^ (n - 1) : ℕ) : ℝ) ≤ 2 ^ n := by
  push_cast
  exact pow_le_pow_right₀ one_le_two (Nat.sub_le n 1)

theorem two_pow_le_four_pow (a b : ℕ) (h : a ≤ 2 * b) : (2 : ℝ) ^ a ≤ 4 ^ b := by
  calc (2 : ℝ) ^ a ≤ 2 ^ (2 * b) := pow_le_pow_right₀ one_le_two h
    _ = 4 ^ b := by rw [pow_mul]; norm_num

theorem double_le_two_pow : ∀ b : ℕ, 1 ≤ b → 2 * b ≤ 2 ^ b := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    rw [pow_succ]; omega

theorem prod_mul_two_pow_le : ∀ l : List ℕ, (∀ x ∈ l, 0 < x) →
    l.prod * 2 ^ l.length ≤ 2 ^ l.sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons b l ih =>
    intro h
    have hb : 0 < b := h b (by simp)
    have hl := ih (fun x hx => h x (by simp [hx]))
    have h2 := double_le_two_pow b hb
    simp only [List.prod_cons, List.length_cons, List.sum_cons, pow_succ, pow_add]
    calc b * l.prod * (2 ^ l.length * 2) = (2 * b) * (l.prod * 2 ^ l.length) := by ring
      _ ≤ 2 ^ b * 2 ^ l.sum := Nat.mul_le_mul h2 hl

theorem weight_sq_le {n : ℕ} (c : Composition n) : weight c ^ 2 ≤ 2 ^ (n ^ 2) := by
  have h1 : c.blocks.prod * 2 ^ c.length ≤ 2 ^ n := by
    have := prod_mul_two_pow_le c.blocks (fun x hx => c.blocks_pos hx)
    rwa [c.blocks_sum] at this
  set P := c.blocks.prod
  set L := c.length
  have h2 : (P * 2 ^ L) ^ (4 * L) ≤ (2 ^ n) ^ (4 * L) := Nat.pow_le_pow_left h1 _
  rw [mul_pow, ← pow_mul, ← pow_mul] at h2
  have h3 : n * (4 * L) ≤ n ^ 2 + L * (4 * L) := by
    have := sq_nonneg ((n : ℤ) - 2 * L)
    zify; nlinarith
  have h4 : 2 ^ (n * (4 * L)) ≤ 2 ^ (n ^ 2) * 2 ^ (L * (4 * L)) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) h3
  have h5 : P ^ (4 * L) * 2 ^ (L * (4 * L)) ≤ 2 ^ (n ^ 2) * 2 ^ (L * (4 * L)) := h2.trans h4
  have h6 : P ^ (4 * L) ≤ 2 ^ (n ^ 2) := Nat.le_of_mul_le_mul_right h5 (by positivity)
  have h7 : weight c ^ 2 = P ^ (4 * L) := by
    unfold weight; rw [← pow_mul]; congr 1; ring
  rw [h7]; exact h6

theorem weight_le {n : ℕ} (c : Composition n) :
    (weight c : ℝ) ≤ Real.sqrt 2 ^ (n ^ 2) := by
  have h := weight_sq_le c
  have h' : ((weight c : ℝ)) ^ 2 ≤ (Real.sqrt 2 ^ (n ^ 2)) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
    exact_mod_cast h
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h'

theorem logCoeff_nonneg (n : ℕ) : 0 ≤ logCoeff n := by
  unfold logCoeff
  exact Finset.sum_nonneg (fun c _ => by positivity)

theorem logCoeff_le (n : ℕ) : logCoeff n ≤ 2 ^ n * Real.sqrt 2 ^ (n ^ 2) := by
  unfold logCoeff
  calc ∑ c : Composition n, (weight c : ℝ) / (c.length : ℝ)
      ≤ ∑ c : Composition n, Real.sqrt 2 ^ (n ^ 2) := by
        apply Finset.sum_le_sum
        intro c _
        rcases Nat.eq_zero_or_pos c.length with h | h
        · rw [h]; simp
        · calc (weight c : ℝ) / (c.length : ℝ) ≤ (weight c : ℝ) :=
                div_le_self (by positivity) (by exact_mod_cast h)
            _ ≤ _ := weight_le c
    _ = (2 ^ (n - 1) : ℕ) * Real.sqrt 2 ^ (n ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, composition_card, nsmul_eq_mul]
    _ ≤ 2 ^ n * Real.sqrt 2 ^ (n ^ 2) :=
        mul_le_mul_of_nonneg_right (card_comp_le n) (by positivity)

theorem prod_logCoeff_le : ∀ l : List ℕ,
    0 ≤ (l.map logCoeff).prod ∧
      (l.map logCoeff).prod ≤ 2 ^ l.sum * Real.sqrt 2 ^ (l.sum ^ 2) := by
  intro l
  induction l with
  | nil => simp
  | cons b l ih =>
    obtain ⟨h0, h1⟩ := ih
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    refine ⟨mul_nonneg (logCoeff_nonneg b) h0, ?_⟩
    calc logCoeff b * (l.map logCoeff).prod
        ≤ (2 ^ b * Real.sqrt 2 ^ (b ^ 2)) * (2 ^ l.sum * Real.sqrt 2 ^ (l.sum ^ 2)) :=
          mul_le_mul (logCoeff_le b) h1 h0 (by positivity)
      _ = 2 ^ (b + l.sum) * Real.sqrt 2 ^ (b ^ 2 + l.sum ^ 2) := by
          rw [pow_add, pow_add]; ring
      _ ≤ 2 ^ (b + l.sum) * Real.sqrt 2 ^ ((b + l.sum) ^ 2) := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ sqrt_two_ge_one ?_) (by positivity)
          have e : (b + l.sum) ^ 2 = b ^ 2 + l.sum ^ 2 + 2 * b * l.sum := by ring
          rw [e]; exact Nat.le_add_right _ _

theorem term_le (n : ℕ) : term n ≤ 4 ^ n * Real.sqrt 2 ^ (n ^ 2) := by
  unfold term
  calc ∑ c : Composition n, (c.blocks.map logCoeff).prod / (c.length.factorial : ℝ)
      ≤ ∑ c : Composition n, 2 ^ n * Real.sqrt 2 ^ (n ^ 2) := by
        apply Finset.sum_le_sum
        intro c _
        obtain ⟨h0, h1⟩ := prod_logCoeff_le c.blocks
        rw [c.blocks_sum] at h1
        calc (c.blocks.map logCoeff).prod / (c.length.factorial : ℝ)
            ≤ (c.blocks.map logCoeff).prod :=
              div_le_self h0 (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
          _ ≤ _ := h1
    _ = (2 ^ (n - 1) : ℕ) * (2 ^ n * Real.sqrt 2 ^ (n ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, composition_card, nsmul_eq_mul]
    _ ≤ 2 ^ n * (2 ^ n * Real.sqrt 2 ^ (n ^ 2)) :=
        mul_le_mul_of_nonneg_right (card_comp_le n) (by positivity)
    _ = 4 ^ n * Real.sqrt 2 ^ (n ^ 2) := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]; ring

theorem term_ge_zero (n : ℕ) : 0 ≤ term n := by
  unfold term
  exact Finset.sum_nonneg (fun c _ => div_nonneg (prod_logCoeff_le c.blocks).1 (by positivity))

theorem term_ge_logCoeff (n : ℕ) (hn : 0 < n) : logCoeff n ≤ term n := by
  unfold term
  have := Finset.single_le_sum (f := fun c : Composition n =>
      (c.blocks.map logCoeff).prod / (c.length.factorial : ℝ))
    (fun c _ => div_nonneg (prod_logCoeff_le c.blocks).1 (by positivity))
    (Finset.mem_univ (Composition.single n hn))
  simpa using this

/-- The composition of `2 * m` into `m` parts equal to `2`. -/
def evenComp (m : ℕ) : Composition (2 * m) :=
  ⟨List.replicate m 2, by intro i hi; rw [List.eq_of_mem_replicate hi]; norm_num,
    by rw [List.sum_replicate]; simp [mul_comm]⟩

/-- The composition of `2 * m + 1` into one part `1` followed by `m` parts equal to `2`. -/
def oddComp (m : ℕ) : Composition (2 * m + 1) :=
  ⟨1 :: List.replicate m 2, by
    intro i hi
    rcases List.mem_cons.mp hi with h | h
    · rw [h]; norm_num
    · rw [List.eq_of_mem_replicate h]; norm_num,
    by rw [List.sum_cons, List.sum_replicate]; simp; ring⟩

theorem logCoeff_ge_aux {n : ℕ} (c : Composition n) :
    (weight c : ℝ) / (c.length : ℝ) ≤ logCoeff n := by
  unfold logCoeff
  have := Finset.single_le_sum (f := fun c : Composition n => (weight c : ℝ) / (c.length : ℝ))
    (fun c _ => by positivity) (Finset.mem_univ c)
  simpa using this

theorem term_ge (n : ℕ) (hn : 0 < n) : Real.sqrt 2 ^ (n ^ 2) / 4 ^ n ≤ term n := by
  refine le_trans ?_ (term_ge_logCoeff n hn)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsle : Real.sqrt 2 ≤ 2 := sqrt_two_le_two
  rcases Nat.even_or_odd' n with ⟨m, hm2 | hm2⟩ <;> subst hm2
  · have hm : 0 < m := by omega
    have hlen : (evenComp m).length = m := by simp [evenComp, Composition.length]
    have hw : (weight (evenComp m) : ℝ) = Real.sqrt 2 ^ ((2 * m) ^ 2) := by
      unfold weight
      rw [hlen]
      simp only [evenComp, List.prod_replicate]
      push_cast
      rw [show (2 * m) ^ 2 = 2 * (m * (2 * m)) by ring, pow_mul (Real.sqrt 2) 2, hs2]
      ring
    have := logCoeff_ge_aux (evenComp m)
    rw [hw, hlen] at this
    refine le_trans ?_ this
    apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hm)
    have : (m : ℝ) ≤ 2 ^ m := by exact_mod_cast (Nat.lt_two_pow_self).le
    calc (m : ℝ) ≤ 2 ^ m := this
      _ ≤ 4 ^ (2 * m) := two_pow_le_four_pow _ _ (by omega)
  · have hlen : (oddComp m).length = m + 1 := by simp [oddComp, Composition.length]
    have hw : (weight (oddComp m) : ℝ) * Real.sqrt 2 = Real.sqrt 2 ^ ((2 * m + 1) ^ 2) := by
      unfold weight
      rw [hlen]
      simp only [oddComp, List.prod_cons, List.prod_replicate, one_mul]
      push_cast
      rw [show (2 * m + 1) ^ 2 = 2 * (m * (2 * (m + 1))) + 1 by ring, pow_succ,
        pow_mul (Real.sqrt 2) 2, hs2]
      ring
    have := logCoeff_ge_aux (oddComp m)
    rw [hlen] at this
    refine le_trans ?_ this
    rw [← hw, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : ((m + 1 : ℕ) : ℝ) ≤ 2 ^ (m + 1) := by exact_mod_cast (Nat.lt_two_pow_self).le
    have h2 : (2 : ℝ) ^ (m + 1) * 2 ≤ 4 ^ (2 * m + 1) := by
      rw [← pow_succ]
      exact two_pow_le_four_pow _ _ (by omega)
    have hw0 : (0 : ℝ) ≤ weight (oddComp m) := by positivity
    calc (weight (oddComp m) : ℝ) * Real.sqrt 2 * ((m + 1 : ℕ) : ℝ)
        ≤ (weight (oddComp m) : ℝ) * (2 * 2 ^ (m + 1)) := by
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ hw0
          exact mul_le_mul hsle h1 (by positivity) (by norm_num)
      _ ≤ (weight (oddComp m) : ℝ) * 4 ^ (2 * m + 1) := by
          apply mul_le_mul_of_nonneg_left _ hw0
          linarith

end OMA.Helpers

open OMA.S_oeis_a276752 OMA.Helpers Filter Topology in
theorem OMA.solution : type_of% @OMA.S_oeis_a276752.main := by
  set s := Real.sqrt 2 with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 2
  -- `q n = 4 ^ (1 / n)` tends to `1`
  have hq : Tendsto (fun n : ℕ => (4 : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 1) := by
    have h0 := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    have := Filter.Tendsto.rpow (tendsto_const_nhds (x := (4 : ℝ))) h0 (Or.inl (by norm_num))
    simpa using this
  have key : ∀ n : ℕ, 0 < n →
      ((s ^ (n ^ 2)) ^ (1 / (n : ℝ) ^ 2) = s ∧
        ((4 : ℝ) ^ n) ^ (1 / (n : ℝ) ^ 2) = (4 : ℝ) ^ ((1 : ℝ) / n)) := by
    intro n hn
    have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
    constructor
    · rw [← Real.rpow_natCast, ← Real.rpow_mul hs0]
      push_cast
      rw [mul_one_div_cancel (pow_ne_zero 2 hnr), Real.rpow_one]
    · rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      field_simp
  have hup : ∀ᶠ n : ℕ in atTop, (term n) ^ (1 / (n : ℝ) ^ 2) ≤ s * (4 : ℝ) ^ ((1 : ℝ) / n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hn : 0 < n := hn1
    obtain ⟨k1, k2⟩ := key n hn
    calc (term n) ^ (1 / (n : ℝ) ^ 2) ≤ (4 ^ n * s ^ (n ^ 2)) ^ (1 / (n : ℝ) ^ 2) :=
          Real.rpow_le_rpow (term_ge_zero n) (term_le n) (by positivity)
      _ = s * (4 : ℝ) ^ ((1 : ℝ) / n) := by
          rw [Real.mul_rpow (by positivity) (by positivity), k1, k2, mul_comm]
  have hlo : ∀ᶠ n : ℕ in atTop, s / (4 : ℝ) ^ ((1 : ℝ) / n) ≤ (term n) ^ (1 / (n : ℝ) ^ 2) := by
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hn : 0 < n := hn1
    obtain ⟨k1, k2⟩ := key n hn
    calc s / (4 : ℝ) ^ ((1 : ℝ) / n) = (s ^ (n ^ 2) / 4 ^ n) ^ (1 / (n : ℝ) ^ 2) := by
          rw [Real.div_rpow (by positivity) (by positivity), k1, k2]
      _ ≤ (term n) ^ (1 / (n : ℝ) ^ 2) :=
          Real.rpow_le_rpow (by positivity) (term_ge n hn) (by positivity)
  have hU : Tendsto (fun n : ℕ => s * (4 : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 s) := by
    simpa using hq.const_mul s
  have hL : Tendsto (fun n : ℕ => s / (4 : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 s) := by
    have := (hq.inv₀ one_ne_zero).const_mul s
    simpa [div_eq_mul_inv] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU hlo hup
