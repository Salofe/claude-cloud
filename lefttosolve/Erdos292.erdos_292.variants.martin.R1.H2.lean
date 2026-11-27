import OMAReductions.R_Erdos292_erdos_292_variants_martin_R1
import Mathlib

namespace OMA.Helpers

open Finset

theorem mul_prime_notMem (m p : ℕ) (hm : 1 ≤ m) (hp : p.Prime) (hlt : m * m.factorial < p) :
    m * p ∉ Erdos292.A := by
  classical
  rintro ⟨S, hS, hmem, hsum⟩
  have hpos : ∀ s ∈ S, 1 ≤ s := fun s hs => (mem_Icc.mp (hS hs)).1
  have hle : ∀ s ∈ S, s ≤ m * p := fun s hs => (mem_Icc.mp (hS hs)).2
  set T := S.filter (fun s => p ∣ s) with hT
  set U := S.filter (fun s => ¬ p ∣ s) with hU
  set M := ∏ s ∈ U, s with hM
  have hpM : ¬ p ∣ M := by
    intro h
    obtain ⟨s, hs, hd⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
    exact (mem_filter.mp hs).2 hd
  have hU_int : (M : ℚ) * ∑ s ∈ U, (1 : ℚ) / s = ((∑ s ∈ U, M / s : ℕ) : ℚ) := by
    rw [mul_sum, Nat.cast_sum]
    refine sum_congr rfl (fun s hs => ?_)
    have hsd : s ∣ M := dvd_prod_of_mem _ hs
    have hs1 := hpos s (mem_filter.mp hs).1
    have hs0 : (s : ℚ) ≠ 0 := by positivity
    rw [Nat.cast_div hsd hs0]
    field_simp
  set F := m.factorial with hF
  have hp0 : 0 < p := hp.pos
  have hT_int : ((p * F : ℕ) : ℚ) * ∑ s ∈ T, (1 : ℚ) / s =
      ((∑ s ∈ T, (p * F) / s : ℕ) : ℚ) := by
    rw [mul_sum, Nat.cast_sum]
    refine sum_congr rfl (fun s hs => ?_)
    obtain ⟨hsS, j, rfl⟩ := mem_filter.mp hs
    have h1 := hpos _ hsS
    have h2 := hle _ hsS
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · simp [h] at h1
      · exact h
    have hjm : j ≤ m := by
      have : p * j ≤ p * m := by rw [mul_comm p m]; exact h2
      exact Nat.le_of_mul_le_mul_left this hp0
    have hsd : p * j ∣ p * F := mul_dvd_mul_left p (Nat.dvd_factorial hj1 hjm)
    have hs0 : ((p * j : ℕ) : ℚ) ≠ 0 := by positivity
    rw [Nat.cast_div hsd hs0]
    field_simp
  set u := ∑ s ∈ U, M / s with hu
  set v := ∑ s ∈ T, (p * F) / s with hv
  have hmpT : m * p ∈ T := mem_filter.mpr ⟨hmem, dvd_mul_left p m⟩
  have hvpos : 0 < v := by
    have hF1 : m ≤ F := Nat.self_le_factorial m
    have : 0 < (p * F) / (m * p) := by
      apply Nat.div_pos
      · rw [mul_comm m p]; exact Nat.mul_le_mul_left p hF1
      · positivity
    exact lt_of_lt_of_le this (single_le_sum (fun _ _ => Nat.zero_le _) hmpT)
  have hvlt : v < p := by
    have hsub : T ⊆ (Icc 1 m).image (fun j => p * j) := by
      intro s hs
      obtain ⟨hsS, j, rfl⟩ := mem_filter.mp hs
      have h1 := hpos _ hsS
      have h2 := hle _ hsS
      refine mem_image.mpr ⟨j, mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos j with h | h
        · simp [h] at h1
        · exact h
      · have : p * j ≤ p * m := by rw [mul_comm p m]; exact h2
        exact Nat.le_of_mul_le_mul_left this hp0
    have hcard : T.card ≤ m := by
      calc T.card ≤ ((Icc 1 m).image (fun j => p * j)).card := card_le_card hsub
        _ ≤ (Icc 1 m).card := card_image_le
        _ = m := by simp
    have hterm : ∀ s ∈ T, (p * F) / s ≤ F := by
      intro s hs
      obtain ⟨hsS, j, rfl⟩ := mem_filter.mp hs
      rw [Nat.mul_div_mul_left _ _ hp0]
      exact Nat.div_le_self _ _
    calc v ≤ T.card • F := sum_le_card_nsmul _ _ _ hterm
      _ = T.card * F := smul_eq_mul _ _
      _ ≤ m * F := Nat.mul_le_mul_right _ hcard
      _ < p := hlt
  have hsplit := sum_filter_add_sum_filter_not S (fun s => p ∣ s) (fun s => (1 : ℚ) / s)
  rw [hsum] at hsplit
  have key : ((M * p * F : ℕ) : ℚ) = ((p * F * u + M * v : ℕ) : ℚ) := by
    have e1 : ((M * p * F : ℕ) : ℚ) = ((M * p * F : ℕ) : ℚ) * 1 := (mul_one _).symm
    rw [e1, ← hsplit]
    have e2 : ((M * p * F : ℕ) : ℚ) * (∑ s ∈ T, (1 : ℚ) / s + ∑ s ∈ U, (1 : ℚ) / s) =
        (M : ℚ) * (((p * F : ℕ) : ℚ) * ∑ s ∈ T, (1 : ℚ) / s) +
          ((p * F : ℕ) : ℚ) * ((M : ℚ) * ∑ s ∈ U, (1 : ℚ) / s) := by
      push_cast
      ring
    rw [e2, hT_int, hU_int]
    push_cast
    ring
  have keyN : M * p * F = p * F * u + M * v := by exact_mod_cast key
  have hdvd : p ∣ M * v := by
    have h1 : p ∣ M * p * F := Dvd.intro_left _ rfl |>.mul_right F
    rw [keyN] at h1
    exact (Nat.dvd_add_right (Dvd.intro (F * u) (by ring))).mp h1
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
  · exact hpM h
  · exact absurd (Nat.le_of_dvd hvpos h) (not_le.mpr hvlt)

theorem smallMultiples_card_le (x K : ℕ) :
    ∑ m ∈ Icc 1 K, ((Ioc (m * m.factorial) (x / m)).filter Nat.Prime).card ≤
      (Erdos292.Aᶜ ∩ Set.Icc 1 x).ncard := by
  classical
  set G := (Icc 1 K).sigma (fun m => (Ioc (m * m.factorial) (x / m)).filter Nat.Prime) with hG
  have hcardG : G.card = ∑ m ∈ Icc 1 K, ((Ioc (m * m.factorial) (x / m)).filter Nat.Prime).card :=
    card_sigma _ _
  rw [← hcardG]
  have hmem : ∀ q ∈ G, 1 ≤ q.1 ∧ q.1 * q.1.factorial < q.2 ∧ q.2 ≤ x / q.1 ∧ q.2.Prime := by
    intro q hq
    obtain ⟨h1, h2⟩ := mem_sigma.mp hq
    obtain ⟨h3, h4⟩ := mem_filter.mp h2
    exact ⟨(mem_Icc.mp h1).1, (mem_Ioc.mp h3).1, (mem_Ioc.mp h3).2, h4⟩
  have hinj : Set.InjOn (fun q : (Σ _ : ℕ, ℕ) => q.1 * q.2) (G : Set (Σ _ : ℕ, ℕ)) := by
    rintro ⟨m, p⟩ hq ⟨m', p'⟩ hq' he
    obtain ⟨hm1, hmp, -, hp⟩ := hmem _ hq
    obtain ⟨hm1', hmp', -, hp'⟩ := hmem _ hq'
    simp only at he hm1 hmp hp hm1' hmp' hp'
    have hmlt : m < p := lt_of_le_of_lt (Nat.le_mul_of_pos_right m (Nat.factorial_pos m)) hmp
    have hmlt' : m' < p' := lt_of_le_of_lt (Nat.le_mul_of_pos_right m' (Nat.factorial_pos m')) hmp'
    by_cases hpp : p = p'
    · subst hpp
      have : m = m' := Nat.eq_of_mul_eq_mul_right hp.pos he
      subst this
      rfl
    · exfalso
      have h1 : p ∣ m' * p' := he ▸ dvd_mul_left p m
      have h2 : p' ∣ m * p := he.symm ▸ dvd_mul_left p' m'
      have c1 : ¬ p ∣ p' := fun h => hpp ((Nat.prime_dvd_prime_iff_eq hp hp').mp h)
      have c2 : ¬ p' ∣ p := fun h => hpp ((Nat.prime_dvd_prime_iff_eq hp' hp).mp h).symm
      have d1 : p ∣ m' := ((Nat.Prime.dvd_mul hp).mp h1).resolve_right c1
      have d2 : p' ∣ m := ((Nat.Prime.dvd_mul hp').mp h2).resolve_right c2
      have e1 := Nat.le_of_dvd (by omega) d1
      have e2 := Nat.le_of_dvd (by omega) d2
      omega
  rw [← card_image_of_injOn hinj, ← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard _ ((Set.finite_Icc 1 x).subset Set.inter_subset_right)
  intro n hn
  obtain ⟨⟨m, p⟩, hq, rfl⟩ := mem_image.mp (mem_coe.mp hn)
  obtain ⟨hm1, hmp, hpx, hp⟩ := hmem _ hq
  simp only at hm1 hmp hpx hp ⊢
  refine ⟨mul_prime_notMem m p hm1 hp hmp, ?_, ?_⟩
  · exact Nat.mul_pos hm1 hp.pos
  · have := (Nat.le_div_iff_mul_le hm1).mp hpx
    rw [mul_comm]; exact this


theorem pi_le_card_add (a n : ℕ) :
    Nat.primeCounting n ≤ ((Ioc a n).filter Nat.Prime).card + a := by
  classical
  rw [← Nat.primesLE_card_eq_primeCounting]
  calc (Nat.primesLE n).card ≤ (((Ioc a n).filter Nat.Prime) ∪ Icc 1 a).card := by
        apply card_le_card
        intro p hp
        rw [Nat.mem_primesLE] at hp
        rcases le_or_gt p a with h | h
        · exact mem_union_right _ (mem_Icc.mpr ⟨hp.2.one_lt.le, h⟩)
        · exact mem_union_left _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨h, hp.1⟩, hp.2⟩)
    _ ≤ ((Ioc a n).filter Nat.Prime).card + (Icc 1 a).card := card_union_le _ _
    _ = ((Ioc a n).filter Nat.Prime).card + a := by simp

open Real Filter

theorem cheb_eventually :
    ∀ᶠ y : ℝ in atTop, y ≤ 4 * (Nat.primeCounting ⌊y⌋₊ : ℝ) * Real.log y := by
  have h1 : ∀ᶠ y : ℝ in atTop, Real.log (y + 2) ≤ (1 / 8) * (y + 2) := by
    have hb := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 8 by norm_num)
    have ht : Tendsto (fun y : ℝ => y + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_id
    filter_upwards [ht.eventually hb, eventually_ge_atTop (0 : ℝ)] with y hy hy0
    simp only [id, Real.norm_eq_abs] at hy
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ y + 2)] at hy
    exact le_trans (le_abs_self _) hy
  filter_upwards [h1, eventually_ge_atTop (4 : ℝ)] with y hy hy4
  have hlog := Real.log_two_gt_d9
  have hpi := Chebyshev.pi_ge' (by linarith : (1 : ℝ) < y)
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  rw [div_le_iff₀ hlogy] at hpi
  have hint := mul_le_mul_of_nonneg_left hlog.le (by linarith : (0 : ℝ) ≤ y - 1)
  linarith

theorem loglog_density_bound (Y0 : ℝ) (hY0 : 2 ≤ Y0)
    (hcheb : ∀ y ≥ Y0, y ≤ 4 * (Nat.primeCounting ⌊y⌋₊ : ℝ) * Real.log y) (x : ℕ)
    (e1 : Y0 ≤ √(x : ℝ)) (e2 : 1 ≤ Real.log (Real.log x)) (e3 : Real.log x ≤ √(x : ℝ) / 16)
    (e4 : (√(Real.log x) + 2) * Real.log (Real.log x) ≤ Real.log x) (e5 : 1 ≤ Real.log x) :
    Real.log (Real.log x) / Real.log x ≤
      16 * (((Erdos292.Aᶜ ∩ Set.Icc 1 x).ncard : ℝ) / x) := by
  classical
  set X : ℝ := (x : ℝ) with hXdef
  set L : ℝ := Real.log X with hLdef
  set K : ℕ := ⌊√L⌋₊ with hKdef
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg x
  have hsX2 : 2 ≤ √X := le_trans hY0 e1
  have hsXpos : 0 < √X := by linarith
  have hX4 : 4 ≤ X := by
    have := Real.sq_sqrt hX0
    nlinarith
  have hXpos : 0 < X := by linarith
  have hL0 : 0 < L := by linarith
  have hLX : L ≤ X := by
    have := Real.log_le_sub_one_of_pos hXpos
    linarith
  have hsL1 : 1 ≤ √L := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt e5
  have hK1 : 1 ≤ K := Nat.le_floor (by exact_mod_cast hsL1)
  have hKle : (K : ℝ) ≤ √L := Nat.floor_le (Real.sqrt_nonneg _)
  have hKlt : √L < (K : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsLsX : √L ≤ √X := Real.sqrt_le_sqrt hLX
  -- the counting bound
  have hcount := smallMultiples_card_le x K
  have hcountR : (∑ m ∈ Icc 1 K,
      (((Ioc (m * m.factorial) (x / m)).filter Nat.Prime).card : ℝ)) ≤
      ((Erdos292.Aᶜ ∩ Set.Icc 1 x).ncard : ℝ) := by
    exact_mod_cast hcount
  -- each term
  have hterm : ∀ m ∈ Icc 1 K,
      X / (4 * L) * (m : ℝ)⁻¹ - ((m * m.factorial : ℕ) : ℝ) ≤
        (((Ioc (m * m.factorial) (x / m)).filter Nat.Prime).card : ℝ) := by
    intro m hm
    obtain ⟨hm1, hmK⟩ := mem_Icc.mp hm
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hmpos : (0 : ℝ) < m := by linarith
    have hmK' : (m : ℝ) ≤ √X := le_trans (le_trans (by exact_mod_cast hmK) hKle) hsLsX
    set y : ℝ := X / m with hy
    have hyge : √X ≤ y := by
      rw [hy, le_div_iff₀ hmpos]
      calc √X * m ≤ √X * √X := mul_le_mul_of_nonneg_left hmK' hsXpos.le
        _ = X := Real.mul_self_sqrt hX0
    have hy0 : 0 < y := by linarith
    have hyX : y ≤ X := div_le_self hX0 hmR
    have hc := hcheb y (le_trans e1 hyge)
    have hfl : ⌊y⌋₊ = x / m := Nat.floor_div_eq_div x m
    rw [hfl] at hc
    have hlogy : Real.log y ≤ L := Real.log_le_log hy0 hyX
    have hpi0 : (0 : ℝ) ≤ (Nat.primeCounting (x / m) : ℝ) := Nat.cast_nonneg _
    have hA : y ≤ 4 * (Nat.primeCounting (x / m) : ℝ) * L := by
      calc y ≤ 4 * (Nat.primeCounting (x / m) : ℝ) * Real.log y := hc
        _ ≤ 4 * (Nat.primeCounting (x / m) : ℝ) * L := by
          apply mul_le_mul_of_nonneg_left hlogy; positivity
    have hB : X / (4 * L) * (m : ℝ)⁻¹ ≤ (Nat.primeCounting (x / m) : ℝ) := by
      have : X / (4 * L) * (m : ℝ)⁻¹ = y / (4 * L) := by
        rw [hy]; field_simp
      rw [this, div_le_iff₀ (by positivity)]
      linarith
    have hC := pi_le_card_add (m * m.factorial) (x / m)
    have hC' : (Nat.primeCounting (x / m) : ℝ) ≤
        (((Ioc (m * m.factorial) (x / m)).filter Nat.Prime).card : ℝ) +
          ((m * m.factorial : ℕ) : ℝ) := by exact_mod_cast hC
    linarith
  have hsum1 := sum_le_sum hterm
  rw [sum_sub_distrib, ← mul_sum] at hsum1
  -- harmonic part
  have hharm : Real.log L / 2 ≤ ∑ m ∈ Icc 1 K, ((m : ℝ))⁻¹ := by
    have h1 := log_add_one_le_harmonic K
    have h2 : ((harmonic K : ℚ) : ℝ) = ∑ m ∈ Icc 1 K, ((m : ℝ))⁻¹ := by
      rw [harmonic_eq_sum_Icc]; push_cast; rfl
    rw [h2] at h1
    have h3 : Real.log √L ≤ Real.log ((K + 1 : ℕ) : ℝ) := by
      apply Real.log_le_log (by positivity)
      push_cast; exact hKlt.le
    rw [Real.log_sqrt hL0.le] at h3
    linarith
  -- small part
  have hsmall : (∑ m ∈ Icc 1 K, ((m * m.factorial : ℕ) : ℝ)) ≤ √X := by
    have hN : ∑ m ∈ Icc 1 K, m * m.factorial ≤ K ^ (K + 2) := by
      calc ∑ m ∈ Icc 1 K, m * m.factorial ≤ (Icc 1 K).card • (K * K.factorial) := by
            apply sum_le_card_nsmul
            intro m hm
            obtain ⟨-, hmK⟩ := mem_Icc.mp hm
            exact Nat.mul_le_mul hmK (Nat.factorial_le hmK)
        _ = K * (K * K.factorial) := by simp
        _ ≤ K * (K * K ^ K) := by
            apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left; exact Nat.factorial_le_pow K
        _ = K ^ (K + 2) := by ring
    have hN' : (∑ m ∈ Icc 1 K, ((m * m.factorial : ℕ) : ℝ)) ≤ ((K : ℝ)) ^ (K + 2) := by
      exact_mod_cast hN
    refine le_trans hN' ?_
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
    rw [← Real.log_le_log_iff (by positivity) hsXpos, Real.log_pow, Real.log_sqrt hX0]
    have hlogK : Real.log K ≤ Real.log L / 2 := by
      rw [← Real.log_sqrt hL0.le]
      exact Real.log_le_log hKpos hKle
    have hlogK0 : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK1)
    push_cast
    have hb1 : ((K : ℝ) + 2) * Real.log K ≤ (√L + 2) * (Real.log L / 2) := by
      apply mul_le_mul (by linarith) hlogK hlogK0 (by positivity)
    have : (√L + 2) * Real.log L ≤ L := e4
    linarith
  -- final combination
  have hfin : X * Real.log L / (16 * L) ≤ ((Erdos292.Aᶜ ∩ Set.Icc 1 x).ncard : ℝ) := by
    have hq : √X ≤ X * Real.log L / (16 * L) := by
      rw [le_div_iff₀ (by positivity)]
      calc √X * (16 * L) ≤ √X * √X := by
            apply mul_le_mul_of_nonneg_left _ hsXpos.le; linarith
        _ = X := Real.mul_self_sqrt hX0
        _ ≤ X * Real.log L := le_mul_of_one_le_right hX0 e2
    have hmain : X * Real.log L / (8 * L) ≤ X / (4 * L) * ∑ m ∈ Icc 1 K, ((m : ℝ))⁻¹ := by
      have : X * Real.log L / (8 * L) = X / (4 * L) * (Real.log L / 2) := by
        field_simp; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hharm (by positivity)
    have e : X * Real.log L / (16 * L) = X * Real.log L / (8 * L) - X * Real.log L / (16 * L) := by
      field_simp; ring
    linarith
  rw [div_le_iff₀ hL0]
  rw [div_le_iff₀ (by positivity)] at hfin
  have : 16 * ((((Erdos292.Aᶜ ∩ Set.Icc 1 x).ncard : ℝ)) / X) * L =
      16 * L * ((Erdos292.Aᶜ ∩ Set.Icc 1 x).ncard : ℝ) / X := by ring
  rw [this, le_div_iff₀ hXpos]
  linarith

end OMA.Helpers

open Filter OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos292_erdos_292_variants_martin_R1.H2 := by
  obtain ⟨Y1, hY1⟩ := eventually_atTop.mp cheb_eventually
  set Y0 : ℝ := max Y1 2 with hY0def
  have hcheb : ∀ y ≥ Y0, y ≤ 4 * (Nat.primeCounting ⌊y⌋₊ : ℝ) * Real.log y :=
    fun y hy => hY1 y (le_trans (le_max_left _ _) hy)
  have hY02 : (2 : ℝ) ≤ Y0 := le_max_right _ _
  have ev1 : ∀ᶠ X : ℝ in atTop, Y0 ≤ √X := by
    filter_upwards [eventually_ge_atTop (Y0 ^ 2)] with X hX
    rw [show Y0 = √(Y0 ^ 2) by rw [Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_le_sqrt hX
  have ev2 : ∀ᶠ X : ℝ in atTop, 1 ≤ Real.log (Real.log X) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop 1)
  have ev5 : ∀ᶠ X : ℝ in atTop, 1 ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have sqbound : ∀ c : ℝ, 0 < c → ∀ᶠ X : ℝ in atTop, Real.log X ≤ c * √X := by
    intro c hc
    have hb := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).bound hc
    filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with X hX hX1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hX1),
      abs_of_nonneg (by positivity), ← Real.sqrt_eq_rpow] at hX
    exact hX
  have ev3 : ∀ᶠ X : ℝ in atTop, Real.log X ≤ √X / 16 := by
    filter_upwards [sqbound (1 / 16) (by norm_num)] with X hX
    linarith
  have ev4L : ∀ᶠ L : ℝ in atTop, (√L + 2) * Real.log L ≤ L := by
    filter_upwards [sqbound (1 / 4) (by norm_num), eventually_ge_atTop (1 : ℝ)] with L hL hL1
    have hs : √L * √L = L := Real.mul_self_sqrt (by linarith)
    have hs1 : √L ≤ L := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have hs0 : 0 ≤ √L := Real.sqrt_nonneg _
    nlinarith
  have ev4 : ∀ᶠ X : ℝ in atTop,
      (√(Real.log X) + 2) * Real.log (Real.log X) ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually ev4L
  have ev := ev1.and (ev2.and (ev3.and (ev4.and ev5)))
  unfold OMA.R_Erdos292_erdos_292_variants_martin_R1.H2
  apply Asymptotics.IsBigO.of_bound 16
  filter_upwards [tendsto_natCast_atTop_atTop.eventually ev] with x hx
  obtain ⟨e1, e2, e3, e4, e5⟩ := hx
  have hb := loglog_density_bound Y0 hY02 hcheb x e1 e2 e3 e4 e5
  have hL0 : 0 ≤ Real.log (Real.log (x : ℝ)) / Real.log x := by
    apply div_nonneg <;> linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL0, abs_of_nonneg (by positivity)]
  exact hb
