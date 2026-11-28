import OMAStatements.S_oeis_a068598
import Mathlib

/-!
# A068598: the conjectured growth `a * exp (b * n ^ c)` with `c > 1` is impossible

The blocks of an admissible family are pairwise disjoint nonempty subsets of `Fin n`.
Sending each element to the least element of its block (or to `⊤` when it lies in no block)
determines the family, so `term n ≤ (n + 1) ^ n`. Hence `log (term n) = O(n log n)`, which is
`o(n ^ c)` for every `c > 1`, and the ratio `term n / (a * exp (b * n ^ c))` tends to `0`,
not to `1`.
-/

namespace OMA.Helpers

open OMA.S_oeis_a068598

/-- The block of `s` containing `i` (empty when there is none). -/
def blk {n : ℕ} (s : Family n) (i : Fin n) : Finset (Fin n) :=
  (s.filter (fun b => i ∈ b)).sup id

theorem blk_eq {n : ℕ} {s : Family n} (hs : admissible s) {b : Block n} (hb : b ∈ s)
    {i : Fin n} (hi : i ∈ b) : blk s i = b := by
  unfold blk
  have h : s.filter (fun b => i ∈ b) = {b} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hd, hid⟩
      exact hs.2 d hd b hb i hid hi
    · rintro rfl
      exact ⟨hb, hi⟩
  rw [h, Finset.sup_singleton]
  rfl

theorem blk_eq_empty {n : ℕ} {s : Family n} {i : Fin n} (h : ∀ b ∈ s, i ∉ b) :
    blk s i = ∅ := by
  unfold blk
  have h' : s.filter (fun b => i ∈ b) = ∅ := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hd, hid⟩
      exact absurd hid (h d hd)
    · intro hd
      simp at hd
  rw [h']
  rfl

/-- Each element is sent to the least element of its block. -/
def code {n : ℕ} (s : Family n) (i : Fin n) : WithTop (Fin n) := (blk s i).min

theorem code_of_mem {n : ℕ} {s : Family n} (hs : admissible s) {b : Block n} (hb : b ∈ s)
    {i : Fin n} (hi : i ∈ b) : code s i = b.min := by
  unfold code
  rw [blk_eq hs hb hi]

theorem exists_of_code {n : ℕ} {s : Family n} (hs : admissible s) {i m : Fin n}
    (h : code s i = (m : WithTop (Fin n))) : ∃ d ∈ s, i ∈ d ∧ m ∈ d := by
  by_cases hex : ∃ d ∈ s, i ∈ d
  · obtain ⟨d, hd, hid⟩ := hex
    refine ⟨d, hd, hid, ?_⟩
    rw [code_of_mem hs hd hid] at h
    exact Finset.mem_of_min h
  · simp only [not_exists, not_and] at hex
    unfold code at h
    rw [blk_eq_empty hex, Finset.min_empty] at h
    exact absurd h WithTop.top_ne_coe

theorem subset_of_code {n : ℕ} {s t : Family n} (hs : admissible s) (ht : admissible t)
    (h : code s = code t) : s ⊆ t := by
  intro b hb
  have hne : b.Nonempty := (hs.1 b hb).1
  obtain ⟨m, hbm⟩ := Finset.min_of_nonempty hne
  have hmb : m ∈ b := Finset.mem_of_min hbm
  have hcm : code t m = (m : WithTop (Fin n)) := by
    rw [← h, code_of_mem hs hb hmb, hbm]
  obtain ⟨c, hc, hmc, -⟩ := exists_of_code ht hcm
  have hcmin : c.min = (m : WithTop (Fin n)) := by
    rw [← code_of_mem ht hc hmc, hcm]
  have hbc : b = c := by
    ext j
    constructor
    · intro hj
      have hj' : code t j = (m : WithTop (Fin n)) := by
        rw [← h, code_of_mem hs hb hj, hbm]
      obtain ⟨d, hd, hjd, hmd⟩ := exists_of_code ht hj'
      rw [ht.2 c hc d hd m hmc hmd]
      exact hjd
    · intro hj
      have hj' : code s j = (m : WithTop (Fin n)) := by
        rw [h, code_of_mem ht hc hj, hcmin]
      obtain ⟨d, hd, hjd, hmd⟩ := exists_of_code hs hj'
      rw [hs.2 b hb d hd m hmb hmd]
      exact hjd
  rw [hbc]
  exact hc

theorem term_le_nat (n : ℕ) : term n ≤ (n + 1) ^ n := by
  unfold term
  split_ifs with hn
  · subst hn
    simp
  · calc _ ≤ (Finset.univ : Finset (Fin n → WithTop (Fin n))).card := by
          apply Finset.card_le_card_of_injOn code
          · intro s _
            exact Finset.mem_coe.2 (Finset.mem_univ _)
          · intro s hs t ht hst
            have hs' : admissible s := by
              simp only [Finset.mem_coe, Finset.mem_filter] at hs
              exact hs.2.1
            have ht' : admissible t := by
              simp only [Finset.mem_coe, Finset.mem_filter] at ht
              exact ht.2.1
            exact Finset.Subset.antisymm (subset_of_code hs' ht' hst)
              (subset_of_code ht' hs' hst.symm)
      _ = (n + 1) ^ n := by
          have hcard : Fintype.card (WithTop (Fin n)) = n + 1 :=
            (Fintype.card_option (α := Fin n)).trans (by simp)
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hcard]

theorem term_le (n : ℕ) : (term n : ℝ) ≤ ((n : ℝ) + 1) ^ n := by
  exact_mod_cast term_le_nat n

end OMA.Helpers

open OMA.S_oeis_a068598 OMA.Helpers Filter Topology in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a068598.main) := by
  rintro ⟨a, b, c, ha, hb, hc, hlim⟩
  have h1 : ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) < (term n : ℝ) / (a * Real.exp (b * (n : ℝ) ^ c)) :=
    hlim.eventually (lt_mem_nhds (by norm_num))
  have hr : 0 < c - 1 := by linarith
  have h2 : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ b / 4 * (n : ℝ) ^ (c - 1) := by
    have hbound := (isLittleO_log_rpow_atTop hr).bound (by positivity : (0 : ℝ) < b / 4)
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hbound] with n hn
    have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ (c - 1) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hn0] at hn
    exact (le_abs_self _).trans hn
  have h3 : ∀ᶠ n : ℕ in atTop, 2 * |Real.log (a / 2)| / b + 1 ≤ (n : ℝ) ^ c := by
    have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ c) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    exact ht.eventually_ge_atTop _
  obtain ⟨n, hn1, hn2, hn3, hn4⟩ :=
    (h1.and (h2.and (h3.and (eventually_ge_atTop 2)))).exists
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn4
  have hn0 : (0 : ℝ) < n := by linarith
  have hD : 0 < a * Real.exp (b * (n : ℝ) ^ c) := mul_pos ha (Real.exp_pos _)
  have hA : 1 / 2 * (a * Real.exp (b * (n : ℝ) ^ c)) < (term n : ℝ) :=
    (lt_div_iff₀ hD).1 hn1
  have hB : (a / 2) * Real.exp (b * (n : ℝ) ^ c) < ((n : ℝ) + 1) ^ n := by
    have := term_le n
    linarith
  have hC : Real.log (a / 2) + b * (n : ℝ) ^ c < (n : ℝ) * Real.log ((n : ℝ) + 1) := by
    have h := Real.log_lt_log (by positivity) hB
    rwa [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_pow] at h
  have hE : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log n := by
    have hsq : (n : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by nlinarith
    calc Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log (by positivity) hsq
      _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num
  have hF : (n : ℝ) * (n : ℝ) ^ (c - 1) = (n : ℝ) ^ c := by
    rw [Real.rpow_sub_one hn0.ne']
    field_simp
  have hG : (n : ℝ) * Real.log ((n : ℝ) + 1) ≤ b / 2 * (n : ℝ) ^ c := by
    calc (n : ℝ) * Real.log ((n : ℝ) + 1) ≤ (n : ℝ) * (2 * (b / 4 * (n : ℝ) ^ (c - 1))) := by
          apply mul_le_mul_of_nonneg_left _ hn0.le
          linarith
      _ = b / 2 * (n : ℝ) ^ c := by rw [← hF]; ring
  have hH : b / 2 * (n : ℝ) ^ c < |Real.log (a / 2)| := by
    have := neg_abs_le (Real.log (a / 2))
    linarith
  have hI : b / 2 * (2 * |Real.log (a / 2)| / b + 1) ≤ b / 2 * (n : ℝ) ^ c :=
    mul_le_mul_of_nonneg_left hn3 (by linarith)
  have hJ : b / 2 * (2 * |Real.log (a / 2)| / b + 1) = |Real.log (a / 2)| + b / 2 := by
    field_simp
  linarith
