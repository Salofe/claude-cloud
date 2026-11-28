import OMAReductions.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1_H1_R1

/-!
# Step H2 of the reduction Erdos955.erdos_955.variants.pollack_pomerance_thompson_bound.R1.H1.R1

The three exceptional classes have density zero.

* (a) Integers with no prime factor up to log x.  Since the sum of 1 / p over the primes
  diverges, a finite set P of primes has product of (1 - 1 / p) below any given delta.  Once
  log x exceeds every prime of P, such an integer is coprime to the product Q of P, and the
  integers up to x coprime to Q number at most phi(Q) (x / Q + 1).
* (c) Integers with a squarefull divisor q above x ^ (2 eta).  Writing q = b ^ 2 a with a
  squarefree, every prime of a divides b, so a divides b and q is at most b ^ 3 while
  b ^ 2 divides n.  Hence n is divisible by d ^ 2 for some d above N, and there are at most
  x (1 / N) such n up to x.  Here x ^ (2 eta) tends to infinity because eta is at least
  1 / log log x.
* (d) Integers n with n ^ 2 at most x: at most sqrt x of them.
-/

namespace OMA.Helpers

open Filter Topology Finset
open scoped Classical

/-- Class (d): few `n` with `n ^ 2 ≤ x`. -/
theorem e955_small_bound (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ x : ℕ in atTop,
    ((((Icc 1 x).filter (fun n => n ^ 2 ≤ x)).card : ℕ) : ℝ) ≤ δ * x := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  filter_upwards [eventually_ge_atTop (N * N)] with x hx
  have hsub : (Icc 1 x).filter (fun n => n ^ 2 ≤ x) ⊆ Icc 1 (Nat.sqrt x) := by
    intro n hn
    rw [mem_filter, mem_Icc] at hn
    rw [mem_Icc]
    exact ⟨hn.1.1, Nat.le_sqrt'.mpr hn.2⟩
  have h1 := card_le_card hsub
  rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
  have hM : Nat.sqrt x * Nat.sqrt x ≤ x := Nat.sqrt_le x
  have hNM : N ≤ Nat.sqrt x := Nat.le_sqrt.mpr hx
  have hM' : ((Nat.sqrt x : ℕ) : ℝ) * (Nat.sqrt x : ℕ) ≤ x := by exact_mod_cast hM
  have hNM' : ((N : ℕ) : ℝ) ≤ (Nat.sqrt x : ℕ) := by exact_mod_cast hNM
  have h1' : ((((Icc 1 x).filter (fun n => n ^ 2 ≤ x)).card : ℕ) : ℝ) ≤ (Nat.sqrt x : ℕ) := by
    exact_mod_cast h1
  have hM0 : (0 : ℝ) ≤ (Nat.sqrt x : ℕ) := Nat.cast_nonneg _
  have key : ((Nat.sqrt x : ℕ) : ℝ) * (1 / δ) ≤ x := by
    have : ((Nat.sqrt x : ℕ) : ℝ) * (1 / δ) ≤ (Nat.sqrt x : ℕ) * (Nat.sqrt x : ℕ) :=
      mul_le_mul_of_nonneg_left (by linarith) hM0
    linarith
  have key2 : ((Nat.sqrt x : ℕ) : ℝ) = δ * (((Nat.sqrt x : ℕ) : ℝ) * (1 / δ)) := by
    field_simp
  have key3 : δ * (((Nat.sqrt x : ℕ) : ℝ) * (1 / δ)) ≤ δ * x :=
    mul_le_mul_of_nonneg_left key hδ.le
  linarith

/-- `x ^ (2 * max (ε x) (1 / log log x))` tends to infinity. -/
theorem e955_rpow_large (ε : ℕ → ℝ) (D : ℝ) : ∀ᶠ x : ℕ in atTop,
    D ≤ (x : ℝ) ^ (2 * max (ε x) (1 / Real.log (Real.log x))) := by
  set K : ℝ := max D 2 with hK
  have hK2 : 2 ≤ K := le_max_right _ _
  have hDK : D ≤ K := le_max_left _ _
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop (K ^ 2), eventually_ge_atTop 1] with x hx hx1
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx1
  set L := Real.log (x : ℝ) with hL
  have hL0 : 0 ≤ L := le_trans (by positivity) hx
  set s := Real.sqrt L with hs
  have hsK : K ≤ s := Real.le_sqrt_of_sq_le hx
  have hss : s * s = L := Real.mul_self_sqrt hL0
  have hlogs : Real.log L = 2 * Real.log s := by rw [hs, Real.log_sqrt hL0]; ring
  have hs1 : 1 < s := by linarith
  have hlogs_pos : 0 < Real.log s := Real.log_pos hs1
  have hlogs_le : Real.log s ≤ s := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < s)
    linarith
  have hexp : K ≤ L * (2 * max (ε x) (1 / Real.log L)) := by
    have h1 : L * (2 * (1 / Real.log L)) = s * s / Real.log s := by
      rw [hlogs, ← hss]
      field_simp
    have h2 : s ≤ s * s / Real.log s := by
      rw [le_div_iff₀ hlogs_pos]
      nlinarith
    have h3 : L * (2 * (1 / Real.log L)) ≤ L * (2 * max (ε x) (1 / Real.log L)) := by
      apply mul_le_mul_of_nonneg_left _ hL0
      have := le_max_right (ε x) (1 / Real.log L)
      linarith
    linarith
  rw [Real.rpow_def_of_pos hxpos]
  have := Real.add_one_le_exp (L * (2 * max (ε x) (1 / Real.log L)))
  linarith

/-- A positive squarefull number `q` has a `d` with `d ^ 2 ∣ q` and `q ≤ d ^ 3`. -/
theorem e955_sqfull_root (q : ℕ) (hq : 0 < q)
    (hsf : ∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q) :
    ∃ d : ℕ, d ^ 2 ∣ q ∧ q ≤ d ^ 3 := by
  obtain ⟨a, b, _ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos hq
  have hdiv : a ∣ b := by
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).prime
    · intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpa := Nat.dvd_of_mem_primeFactors hp
      by_contra hpb
      have hcop : Nat.Coprime (p ^ 2) (b ^ 2) :=
        Nat.Coprime.pow 2 2 ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hpb)
      have hpq : p ∣ q := hab ▸ dvd_mul_of_dvd_right hpa _
      have h2 : p ^ 2 ∣ b ^ 2 * a := hab ▸ hsf p hpp hpq
      have h3 : p ^ 2 ∣ a := hcop.dvd_of_dvd_mul_left h2
      have h4 := hsq p (by rw [← pow_two]; exact h3)
      exact hpp.one_lt.ne' (Nat.isUnit_iff.mp h4)
  refine ⟨b, ⟨a, hab.symm⟩, ?_⟩
  rw [← hab]
  have := Nat.le_of_dvd hb hdiv
  calc b ^ 2 * a ≤ b ^ 2 * b := Nat.mul_le_mul_left _ this
    _ = b ^ 3 := by ring

/-- Class (c): few `n` with a large squarefull divisor, uniformly in the threshold. -/
theorem e955_sqfull_bound (δ : ℝ) (hδ : 0 < δ) : ∃ D : ℝ, ∀ x : ℕ, ∀ T : ℝ, D ≤ T →
    ((((Icc 1 x).filter (fun n => ∃ q ∈ n.divisors, T < ((q : ℕ) : ℝ) ∧
      ∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q)).card : ℕ) : ℝ) ≤ δ * x := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hNpos
  refine ⟨(N : ℝ) ^ 3, fun x T hT => ?_⟩
  have hsub : (Icc 1 x).filter (fun n => ∃ q ∈ n.divisors, T < ((q : ℕ) : ℝ) ∧
      ∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q) ⊆
      (Ioc N x).biUnion (fun d => (Ioc 0 x).filter (fun n => d ^ 2 ∣ n)) := by
    intro n hn
    rw [mem_filter, mem_Icc] at hn
    obtain ⟨⟨hn1, hnx⟩, q, hqd, hTq, hsf⟩ := hn
    rw [Nat.mem_divisors] at hqd
    have hq0 : 0 < q := Nat.pos_of_dvd_of_pos hqd.1 (by omega)
    obtain ⟨d, hd2, hqd3⟩ := e955_sqfull_root q hq0 hsf
    have hNd : N < d := by
      have h1 : ((N : ℕ) : ℝ) ^ 3 < ((d : ℕ) : ℝ) ^ 3 := by
        have : ((q : ℕ) : ℝ) ≤ ((d : ℕ) : ℝ) ^ 3 := by exact_mod_cast hqd3
        linarith
      have h2 : N ^ 3 < d ^ 3 := by exact_mod_cast h1
      exact lt_of_pow_lt_pow_left₀ 3 (Nat.zero_le _) h2
    have hdn : d ^ 2 ∣ n := hd2.trans hqd.1
    have hdx : d ≤ x := by
      have h1 : d ^ 2 ≤ n := Nat.le_of_dvd (by omega) hdn
      have h2 : d ≤ d ^ 2 := by
        rw [pow_two]
        exact Nat.le_mul_of_pos_left d (by omega)
      omega
    rw [mem_biUnion]
    refine ⟨d, mem_Ioc.mpr ⟨hNd, hdx⟩, ?_⟩
    rw [mem_filter, mem_Ioc]
    exact ⟨⟨by omega, hnx⟩, hdn⟩
  have h1 := (card_le_card hsub).trans card_biUnion_le
  have h2 : ∀ d ∈ Ioc N x, ((Ioc 0 x).filter (fun n => d ^ 2 ∣ n)).card = x / d ^ 2 :=
    fun d _ => Nat.Ioc_filter_dvd_card_eq_div x (d ^ 2)
  rw [sum_congr rfl h2] at h1
  have h3 : ((((Icc 1 x).filter (fun n => ∃ q ∈ n.divisors, T < ((q : ℕ) : ℝ) ∧
      ∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q)).card : ℕ) : ℝ) ≤
      ∑ d ∈ Ioc N x, ((x / d ^ 2 : ℕ) : ℝ) := by exact_mod_cast h1
  have h4 : ∑ d ∈ Ioc N x, ((x / d ^ 2 : ℕ) : ℝ) ≤ ∑ d ∈ Ioc N x, (x : ℝ) * ((d : ℝ) ^ 2)⁻¹ := by
    apply sum_le_sum
    intro d _
    have := Nat.cast_div_le (α := ℝ) (m := x) (n := d ^ 2)
    rw [div_eq_mul_inv] at this
    push_cast at this
    exact this
  rw [← mul_sum] at h4
  have h5 : ∑ d ∈ Ioc N x, ((d : ℝ) ^ 2)⁻¹ ≤ (N : ℝ)⁻¹ := by
    by_cases hNx : N ≤ x
    · have := sum_Ioc_inv_sq_le_sub (α := ℝ) hN0 hNx
      have hx0 : (0 : ℝ) ≤ (x : ℝ)⁻¹ := by positivity
      linarith
    · rw [Ioc_eq_empty (by omega), sum_empty]
      positivity
  have h6 : (N : ℝ)⁻¹ ≤ δ := by
    rw [inv_le_comm₀ hNpos hδ]
    rw [one_div] at hN
    exact hN.le
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  have h7 : (x : ℝ) * ∑ d ∈ Ioc N x, ((d : ℝ) ^ 2)⁻¹ ≤ x * δ :=
    mul_le_mul_of_nonneg_left (h5.trans h6) hx0
  linarith

/-- A finite set of primes with `∏ (1 - 1 / p)` as small as we like. -/
theorem e955_small_prod (δ : ℝ) (hδ : 0 < δ) : ∃ N : ℕ,
    ∏ p ∈ (range N).filter Nat.Prime, (1 - ((p : ℕ) : ℝ)⁻¹) ≤ δ := by
  have hns := not_summable_one_div_on_primes
  have hex : ∃ N : ℕ, Real.log (1 / δ) <
      ∑ i ∈ range N, Set.indicator {p | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i := by
    by_contra hcon
    push Not at hcon
    apply hns
    refine summable_of_sum_range_le (c := Real.log (1 / δ)) (fun n => ?_) hcon
    apply Set.indicator_nonneg
    intro i _
    positivity
  obtain ⟨N, hN⟩ := hex
  refine ⟨N, ?_⟩
  have hsum : ∑ i ∈ range N, Set.indicator {p | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i =
      ∑ p ∈ (range N).filter Nat.Prime, ((p : ℕ) : ℝ)⁻¹ := by
    rw [sum_filter]
    apply sum_congr rfl
    intro i _
    by_cases hi : i.Prime
    · rw [Set.indicator_of_mem (by exact hi), if_pos hi, one_div]
    · rw [Set.indicator_of_notMem (by exact hi), if_neg hi]
  rw [hsum] at hN
  calc ∏ p ∈ (range N).filter Nat.Prime, (1 - ((p : ℕ) : ℝ)⁻¹)
      ≤ ∏ p ∈ (range N).filter Nat.Prime, Real.exp (-((p : ℕ) : ℝ)⁻¹) := by
        apply Finset.prod_le_prod
        · intro p hp
          have hp2 := (mem_filter.mp hp).2.two_le
          have : ((p : ℕ) : ℝ)⁻¹ ≤ 1 := by
            apply inv_le_one_of_one_le₀
            exact_mod_cast (by omega : 1 ≤ p)
          linarith
        · intro p _
          exact Real.one_sub_le_exp_neg _
    _ = Real.exp (-∑ p ∈ (range N).filter Nat.Prime, ((p : ℕ) : ℝ)⁻¹) := by
        rw [← Real.exp_sum, sum_neg_distrib]
    _ ≤ Real.exp (-Real.log (1 / δ)) := by
        apply Real.exp_le_exp.mpr
        linarith
    _ = δ := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp

/-- Class (a): few `n` without a prime factor up to `log x`. -/
theorem e955_rough_bound (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ x : ℕ in atTop,
    ((((Icc 1 x).filter (fun n => ¬ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧
      (p : ℝ) ≤ Real.log x)).card : ℕ) : ℝ) ≤ δ * x := by
  obtain ⟨N, hN⟩ := e955_small_prod (δ / 2) (by linarith)
  set P := (range N).filter Nat.Prime with hP
  set Q := ∏ p ∈ P, p with hQ
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => (mem_filter.mp hp).2
  have hQ0 : Q ≠ 0 := by
    rw [hQ]
    exact prod_ne_zero_iff.mpr (fun p hp => (hPprime p hp).ne_zero)
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero hQ0
  have hphi : ((Nat.totient Q : ℕ) : ℝ) = Q * ∏ p ∈ P, (1 - ((p : ℕ) : ℝ)⁻¹) := by
    have h := Nat.totient_eq_mul_prod_factors Q
    rw [hQ, Nat.primeFactors_prod hPprime] at h
    rw [← hQ] at h
    have h' := congrArg (fun r : ℚ => (r : ℝ)) h
    push_cast at h'
    exact h'
  have hphiQ : ((Nat.totient Q : ℕ) : ℝ) ≤ Q := by
    exact_mod_cast Nat.totient_le Q
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbig : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop (N : ℝ), hbig.eventually_ge_atTop (2 * Q / δ)]
    with x hx hxQ
  have hsub : (Icc 1 x).filter (fun n => ¬ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧
      (p : ℝ) ≤ Real.log x) ⊆ (Ico 1 (1 + x)).filter (fun n => Q.Coprime n) := by
    intro n hn
    rw [mem_filter, mem_Icc] at hn
    rw [mem_filter, mem_Ico]
    refine ⟨⟨hn.1.1, by omega⟩, ?_⟩
    apply Nat.coprime_of_dvd
    intro k hk hkQ hkn
    apply hn.2
    refine ⟨k, hk, hkn, ?_⟩
    rw [hQ] at hkQ
    obtain ⟨p, hp, hkp⟩ := (Prime.dvd_finsetProd_iff hk.prime _).mp hkQ
    have hkp' : k = p := (Nat.prime_dvd_prime_iff_eq hk (hPprime p hp)).mp hkp
    have hpN : p < N := mem_range.mp (mem_filter.mp hp).1
    have : (k : ℝ) < N := by exact_mod_cast (hkp' ▸ hpN)
    linarith
  have h1 := (card_le_card hsub).trans (Nat.Ico_filter_coprime_le 1 x hQ0)
  have h2 : ((((Icc 1 x).filter (fun n => ¬ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧
      (p : ℝ) ≤ Real.log x)).card : ℕ) : ℝ) ≤
      ((Nat.totient Q : ℕ) : ℝ) * (((x / Q : ℕ) : ℝ) + 1) := by exact_mod_cast h1
  have h3 : ((x / Q : ℕ) : ℝ) ≤ (x : ℝ) / Q := Nat.cast_div_le
  have hphi0 : (0 : ℝ) ≤ ((Nat.totient Q : ℕ) : ℝ) := Nat.cast_nonneg _
  have h4 : ((Nat.totient Q : ℕ) : ℝ) * (((x / Q : ℕ) : ℝ) + 1) ≤
      ((Nat.totient Q : ℕ) : ℝ) * ((x : ℝ) / Q) + Q := by
    have := mul_le_mul_of_nonneg_left h3 hphi0
    nlinarith
  have h5 : ((Nat.totient Q : ℕ) : ℝ) * ((x : ℝ) / Q) =
      (∏ p ∈ P, (1 - ((p : ℕ) : ℝ)⁻¹)) * x := by
    rw [hphi]
    field_simp
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  have h6 : (∏ p ∈ P, (1 - ((p : ℕ) : ℝ)⁻¹)) * x ≤ δ / 2 * x :=
    mul_le_mul_of_nonneg_right hN hx0
  have h7 : (Q : ℝ) ≤ δ / 2 * x := by
    have : 2 * (Q : ℝ) / δ ≤ x := hxQ
    rw [div_le_iff₀ hδ] at this
    linarith
  linarith

end OMA.Helpers

open Filter Topology Finset in
theorem OMA.solution :
    OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1_H1_R1.H2 := by
  intro ε _hε δ hδ
  obtain ⟨D, hD⟩ := OMA.Helpers.e955_sqfull_bound (δ / 3) (by linarith)
  filter_upwards [OMA.Helpers.e955_rough_bound (δ / 3) (by linarith),
    OMA.Helpers.e955_small_bound (δ / 3) (by linarith),
    OMA.Helpers.e955_rpow_large ε D] with x hA hC hT
  intro η other
  have hB := hD x ((x : ℝ) ^ (2 * η)) hT
  classical
  have hsub : (Icc 1 x).filter other ⊆
      ((Icc 1 x).filter (fun n => ¬ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : ℝ) ≤ Real.log x) ∪
        (Icc 1 x).filter (fun n => ∃ q ∈ n.divisors, (x : ℝ) ^ (2 * η) < ((q : ℕ) : ℝ) ∧
          ∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q)) ∪
        (Icc 1 x).filter (fun n => n ^ 2 ≤ x) := by
    intro n hn
    rw [mem_filter] at hn
    obtain ⟨hn1, h | h | h⟩ := hn
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hn1, h⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hn1, h⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨hn1, h⟩)
  have h1 := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))
  have h2 : (((Icc 1 x).filter other).card : ℝ) ≤
      ((((Icc 1 x).filter (fun n => ¬ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧
        (p : ℝ) ≤ Real.log x)).card : ℕ) : ℝ) +
      ((((Icc 1 x).filter (fun n => ∃ q ∈ n.divisors, (x : ℝ) ^ (2 * η) < ((q : ℕ) : ℝ) ∧
          ∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q)).card : ℕ) : ℝ) +
      ((((Icc 1 x).filter (fun n => n ^ 2 ≤ x)).card : ℕ) : ℝ) := by
    exact_mod_cast h1
  linarith
