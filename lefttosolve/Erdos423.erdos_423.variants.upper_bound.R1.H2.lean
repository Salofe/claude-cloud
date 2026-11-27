import OMAReductions.R_Erdos423_erdos_423_variants_upper_bound_R1

/-!
# Step H2 of the reduction Erdos423.erdos_423.variants.upper_bound.R1

Tang's transfer step. Every sum of at least two consecutive terms of the Hofstadter sequence is
itself a term of the sequence (the greedy rule cannot skip it), and every such block sum taken
from the first `m` terms is at most `m * a m`. Hence, if there are at least `n` distinct block sums
from the first `m` terms, then `a n ≤ m * a m`. Feeding in the counting hypothesis with
`m` of order `n ^ (1 / c')` gives `a n ≤ m * a m`, and a strong induction yields
`a n ≤ K * n ^ β` for every `β > 1 / (c' - 1)`.

Only the upstream definitions are used; all lemmas below are proved here.
-/

open Filter Asymptotics

namespace OMA.Helpers

theorem e423_step {a : ℕ → ℕ} (ha : Erdos423.IsHofstadterSeq a) (k : ℕ) (hk : 1 ≤ k) :
    a k < a (k + 1) := by
  obtain ⟨h1, h2, hrec⟩ := ha
  rcases Nat.lt_or_ge k 2 with h | h
  · obtain rfl : k = 1 := by omega
    rw [h1, h2]; omega
  · have := (hrec (k + 1) (by omega)).2.1
    simpa using this

theorem e423_lt {a : ℕ → ℕ} (ha : Erdos423.IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i)
    (hij : i < j) : a i < a j := by
  induction j, hij using Nat.le_induction with
  | base => exact e423_step ha i hi
  | succ j hj ih => exact ih.trans (e423_step ha j (by omega))

theorem e423_le {a : ℕ → ℕ} (ha : Erdos423.IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i)
    (hij : i ≤ j) : a i ≤ a j := by
  rcases eq_or_lt_of_le hij with rfl | h
  · exact le_rfl
  · exact (e423_lt ha hi h).le

theorem e423_ge {a : ℕ → ℕ} (ha : Erdos423.IsHofstadterSeq a) (n : ℕ) (hn : 1 ≤ n) :
    n ≤ a n := by
  induction n, hn using Nat.le_induction with
  | base => rw [ha.1]
  | succ k hk ih => have := e423_step ha k hk; omega

/-- Every block sum of at least two consecutive terms is a term of the sequence. -/
theorem e423_term {a : ℕ → ℕ} (ha : Erdos423.IsHofstadterSeq a) {i j : ℕ} (hi : 1 ≤ i)
    (hij : i + 1 ≤ j) : ∃ t, 1 ≤ t ∧ a t = ∑ l ∈ Finset.Icc i j, a l := by
  set s := ∑ l ∈ Finset.Icc i j, a l with hs
  have hpair : a i + a j ≤ s := by
    have hsub : ({i, j} : Finset ℕ) ⊆ Finset.Icc i j := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_Icc]; omega
    have := Finset.sum_le_sum_of_subset (f := a) hsub
    rwa [Finset.sum_pair (by omega)] at this
  have hai : 1 ≤ a i := le_trans hi (e423_ge ha i hi)
  have hjs : a j < s := by omega
  have hex : ∃ t, s ≤ a (j + t) := ⟨s, by have := e423_ge ha (j + s) (by omega); omega⟩
  classical
  set t0 := Nat.find hex with ht0
  have hspec : s ≤ a (j + t0) := Nat.find_spec hex
  have ht0pos : t0 ≠ 0 := by
    intro h
    rw [h, Nat.add_zero] at hspec
    omega
  have hmin : a (j + (t0 - 1)) < s := by
    have := Nat.find_min hex (show t0 - 1 < t0 by omega)
    omega
  refine ⟨j + t0, by omega, ?_⟩
  by_contra hne
  have hlt : s < a (j + t0) := lt_of_le_of_ne hspec (Ne.symm hne)
  have hrec := (ha.2.2 (j + t0) (by omega)).2.2 s
    (by rw [show j + t0 - 1 = j + (t0 - 1) by omega]; exact hmin) hlt
  exact hrec ⟨i, j, hi, hij, by omega, rfl⟩

/-- Block sums from the first `m` terms are at most `m * a m`. -/
theorem e423_bound {a : ℕ → ℕ} (ha : Erdos423.IsHofstadterSeq a) {i j m : ℕ} (hi : 1 ≤ i)
    (hjm : j ≤ m) : ∑ l ∈ Finset.Icc i j, a l ≤ m * a m := by
  calc ∑ l ∈ Finset.Icc i j, a l ≤ ∑ l ∈ Finset.Icc 1 m, a l := by
        apply Finset.sum_le_sum_of_subset
        intro x hx
        rw [Finset.mem_Icc] at hx ⊢
        omega
    _ ≤ ∑ l ∈ Finset.Icc 1 m, a m := by
        apply Finset.sum_le_sum
        intro l hl
        rw [Finset.mem_Icc] at hl
        exact e423_le ha hl.1 hl.2
    _ = m * a m := by rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]; congr 1

/-- If there are at least `n` distinct block sums from the first `m` terms, then
`a n ≤ m * a m`. -/
theorem e423_key {a : ℕ → ℕ} (ha : Erdos423.IsHofstadterSeq a) {n m : ℕ} (hn : 1 ≤ n)
    (hcard : n ≤ ({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard) :
    a n ≤ m * a m := by
  by_contra hcon
  have hlt : m * a m < a n := by omega
  have hsub : {s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s} ⊆
      ↑((Finset.Ico 1 n).image a) := by
    rintro s ⟨i, j, hi, hij, hjm, rfl⟩
    obtain ⟨t, ht1, hts⟩ := e423_term ha hi hij
    have hb := e423_bound ha hi (show j ≤ m by omega)
    have htn : t < n := by
      by_contra h
      have := e423_le ha hn (show n ≤ t by omega)
      omega
    rw [Finset.coe_image]
    exact ⟨t, by rw [Finset.coe_Ico]; exact ⟨ht1, htn⟩, hts⟩
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at h1
  have h2 := Finset.card_image_le (s := Finset.Ico 1 n) (f := a)
  rw [Nat.card_Ico] at h2
  omega

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos423_erdos_423_variants_upper_bound_R1.H2 := by
  intro a ha c hc hcount ε hε
  have hc1 : 0 < c - 1 := by linarith
  set β : ℝ := 1 / (c - 1) + ε with hβ
  have hinv : 0 < 1 / (c - 1) := by positivity
  have hβpos : 0 < β := by linarith
  have hβε : ε < β := by linarith
  set η : ℝ := ε * (c - 1) / (2 * β) with hη
  have hηpos : 0 < η := by positivity
  have hβc : β * (c - 1) = 1 + ε * (c - 1) := by
    rw [hβ, add_mul, one_div, inv_mul_cancel₀ hc1.ne']
  have hβη : β * η = ε * (c - 1) / 2 := by
    rw [hη]; field_simp
  have hηc : η < c - 1 := by
    rw [hη, div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨C, hCpos, hC⟩ := hcount η hηpos
  obtain ⟨M0, hM0⟩ := eventually_atTop.1 hC
  set c' : ℝ := c - η with hc'
  have hc'pos : 0 < c' := by linarith
  have hβc' : 1 + β < β * c' := by
    have : β * c' = β * (c - 1) - β * η + β := by rw [hc']; ring
    rw [this, hβc, hβη]
    nlinarith
  set γ : ℝ := c'⁻¹ * (1 + β) with hγ
  have hγβ : γ < β := by
    rw [hγ, inv_mul_lt_iff₀ hc'pos]
    linarith
  set δ : ℝ := β - γ with hδ
  have hδpos : 0 < δ := by linarith
  set D : ℝ := (2 : ℝ) ^ (1 + β) * C ^ γ with hD
  have htend : Tendsto (fun n : ℕ => (C * (n : ℝ)) ^ c'⁻¹) atTop atTop :=
    (tendsto_rpow_atTop (inv_pos.2 hc'pos)).comp
      (Tendsto.const_mul_atTop hCpos tendsto_natCast_atTop_atTop)
  have htend2 : Tendsto (fun n : ℕ => (n : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδpos).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ (C * (n : ℝ)) ^ c'⁻¹ ∧
      (M0 : ℝ) ≤ (C * (n : ℝ)) ^ c'⁻¹ ∧ D ≤ (n : ℝ) ^ δ ∧ 2 ≤ n :=
    (htend.eventually_ge_atTop 1).and ((htend.eventually_ge_atTop (M0 : ℝ)).and
      ((htend2.eventually_ge_atTop D).and (eventually_ge_atTop 2)))
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 hev
  set K : ℝ := (∑ i ∈ Finset.range N1, (a i : ℝ)) + 1 with hK
  have hKpos : 1 ≤ K := by
    have : 0 ≤ ∑ i ∈ Finset.range N1, (a i : ℝ) :=
      Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
    linarith
  have main : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) ≤ K * (n : ℝ) ^ β := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpow1 : 1 ≤ (n : ℝ) ^ β := Real.one_le_rpow hn1 hβpos.le
    rcases Nat.lt_or_ge n N1 with hlt | hge
    · have hle : (a n : ℝ) ≤ ∑ i ∈ Finset.range N1, (a i : ℝ) :=
        Finset.single_le_sum (f := fun i => (a i : ℝ)) (fun i _ => Nat.cast_nonneg _)
          (Finset.mem_range.2 hlt)
      calc (a n : ℝ) ≤ K := by linarith
        _ = K * 1 := (mul_one K).symm
        _ ≤ K * (n : ℝ) ^ β := mul_le_mul_of_nonneg_left hpow1 (by linarith)
    · obtain ⟨hx1, hxM, hDle, hn2⟩ := hN1 n hge
      set x : ℝ := (C * (n : ℝ)) ^ c'⁻¹ with hx
      set m : ℕ := ⌈x⌉₊ with hm
      have hxm : x ≤ m := Nat.le_ceil x
      have hmx : (m : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
      have hm1 : 1 ≤ m := by exact_mod_cast (show (1 : ℝ) ≤ m by linarith)
      have hmM : M0 ≤ m := by exact_mod_cast (show (M0 : ℝ) ≤ m by linarith)
      have hxc : x ^ c' = C * n := by
        rw [hx]; exact Real.rpow_inv_rpow (by positivity) hc'pos.ne'
      have hmc : C * n ≤ (m : ℝ) ^ c' := by
        rw [← hxc]; exact Real.rpow_le_rpow (by linarith) hxm hc'pos.le
      have hcard := hM0 m hmM
      have hnc : (n : ℝ) ≤
          (({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard : ℝ) := by
        have : C * n ≤ C * (({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard : ℝ) :=
          le_trans hmc hcard
        exact le_of_mul_le_mul_left this hCpos
      have hnc' : n ≤ ({s : ℕ | Erdos423.IsConsecutiveBlockSum a (m + 1) s}).ncard := by
        exact_mod_cast hnc
      have hkey := OMA.Helpers.e423_key ha hn hnc'
      have hmpow : (m : ℝ) ^ (1 + β) ≤ D * (n : ℝ) ^ γ := by
        have h2x : (m : ℝ) ≤ 2 * x := by linarith
        calc (m : ℝ) ^ (1 + β) ≤ (2 * x) ^ (1 + β) :=
              Real.rpow_le_rpow (Nat.cast_nonneg _) h2x (by linarith)
          _ = (2 : ℝ) ^ (1 + β) * x ^ (1 + β) := Real.mul_rpow (by norm_num) (by linarith)
          _ = (2 : ℝ) ^ (1 + β) * (C ^ γ * (n : ℝ) ^ γ) := by
              rw [hx, ← Real.rpow_mul (by positivity), Real.mul_rpow hCpos.le (Nat.cast_nonneg _)]
          _ = D * (n : ℝ) ^ γ := by rw [hD]; ring
      have hDn : D * (n : ℝ) ^ γ ≤ (n : ℝ) ^ β := by
        have : (n : ℝ) ^ β = (n : ℝ) ^ δ * (n : ℝ) ^ γ := by
          rw [← Real.rpow_add (by linarith)]; congr 1; rw [hδ]; ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hDle (by positivity)
      have hmn : m < n := by
        have hn1' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
        have h1 : (n : ℝ) ^ β < (n : ℝ) ^ (1 + β) :=
          Real.rpow_lt_rpow_of_exponent_lt hn1' (by linarith)
        have h2 : (m : ℝ) ^ (1 + β) < (n : ℝ) ^ (1 + β) := by linarith
        have h3 := (Real.rpow_lt_rpow_iff (Nat.cast_nonneg _) (Nat.cast_nonneg _)
          (by linarith : (0 : ℝ) < 1 + β)).1 h2
        exact_mod_cast h3
      have hih := ih m hmn hm1
      have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
      calc (a n : ℝ) ≤ (m : ℝ) * (a m : ℝ) := by exact_mod_cast hkey
        _ ≤ (m : ℝ) * (K * (m : ℝ) ^ β) := mul_le_mul_of_nonneg_left hih (Nat.cast_nonneg _)
        _ = K * (m : ℝ) ^ (1 + β) := by rw [Real.rpow_add hmpos 1 β, Real.rpow_one]; ring
        _ ≤ K * (n : ℝ) ^ β := mul_le_mul_of_nonneg_left (hmpow.trans hDn) (by linarith)
  refine Asymptotics.IsBigO.of_bound K ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (by positivity)]
  exact main n hn
