import FormalConjectures.ErdosProblems.«1100»

/-!
Erdős–Tenenbaum bound for squarefree n: g(k) ≤ 3 (3 / 2^(2/3))^k.

Let n be squarefree with ω(n) = k, d_i the i-th divisor of n, and y = 2^(1/3), so y^3 = 2.
For a coprime consecutive pair (d_i, d_{i+1}) with a = ω(d_i), b = ω(d_{i+1}) we have
ω(d_i d_{i+1}) = a + b and
  1 ≤ y^k (1/2)^a + y^k (1/2)^b + 2^(a+b) / y^(2k)
(one of 3a ≤ k, 3b ≤ k, 3(a+b) ≥ 2k holds).  Summing over the coprime pairs, the three maps
i ↦ d_i, i ↦ d_{i+1}, i ↦ d_i d_{i+1} are injective into the divisors of n, and for squarefree n
the divisor sum of x^ω(d) is at most (1+x)^k (divisors inject into subsets of the prime factors).
Hence τ⊥(n) ≤ 2 y^k (3/2)^k + 3^k / y^(2k) = 3 (3y/2)^k = 3 (3/2^(2/3))^k.
-/

open scoped ArithmeticFunction.omega

namespace OMA.Helpers

theorem omega_eq_card (n : ℕ) : ω n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]
  rfl

theorem divisor_sum_le (n : ℕ) (hn : Squarefree n) (x : ℝ) (hx : 0 ≤ x) :
    ∑ d ∈ n.divisors, x ^ (ω d) ≤ (x + 1) ^ (ω n) := by
  classical
  have hn0 : n ≠ 0 := hn.ne_zero
  have hinj : Set.InjOn Nat.primeFactors (n.divisors : Set ℕ) := by
    intro a ha b hb hab
    have ha' : a ∣ n := Nat.dvd_of_mem_divisors ha
    have hb' : b ∣ n := Nat.dvd_of_mem_divisors hb
    have hsa : Squarefree a := hn.squarefree_of_dvd ha'
    have hsb : Squarefree b := hn.squarefree_of_dvd hb'
    rw [← Nat.prod_primeFactors_of_squarefree hsa, ← Nat.prod_primeFactors_of_squarefree hsb, hab]
  have h1 : ∑ d ∈ n.divisors, x ^ (ω d) = ∑ t ∈ n.divisors.image Nat.primeFactors, x ^ t.card := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [omega_eq_card]
  have h2 : n.divisors.image Nat.primeFactors ⊆ n.primeFactors.powerset := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_powerset.mpr (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hn0)
  have h3 : ∑ t ∈ n.primeFactors.powerset, x ^ t.card = (x + 1) ^ (ω n) := by
    rw [omega_eq_card, ← Finset.sum_pow_mul_eq_add_pow x 1 n.primeFactors]
    simp
  rw [h1, ← h3]
  exact Finset.sum_le_sum_of_subset_of_nonneg h2 (fun t _ _ => pow_nonneg hx _)

theorem sum_comp_le_of_injOn {ι : Type*} (S : Finset ι) (f : ι → ℕ) (T : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ d, 0 ≤ w d) (hmaps : ∀ i ∈ S, f i ∈ T) (hinj : Set.InjOn f S) :
    ∑ i ∈ S, w (f i) ≤ ∑ d ∈ T, w d := by
  classical
  rw [← Finset.sum_image hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
    exact hmaps i hi
  · intro d _ _
    exact hw d

theorem pair_ineq (y : ℝ) (hy1 : 1 ≤ y) (hy3 : y ^ 3 = 2) (a b k : ℕ) :
    1 ≤ y ^ k * (1/2 : ℝ) ^ a + y ^ k * (1/2 : ℝ) ^ b + (2 : ℝ) ^ (a + b) / y ^ (2 * k) := by
  have hy0 : 0 < y := by linarith
  have key : ∀ m : ℕ, 3 * m ≤ k → 1 ≤ y ^ k * (1/2 : ℝ) ^ m := by
    intro m hm
    have h1 : (2:ℝ) ^ m ≤ y ^ k := by
      calc (2:ℝ) ^ m = (y ^ 3) ^ m := by rw [hy3]
        _ = y ^ (3 * m) := by rw [← pow_mul]
        _ ≤ y ^ k := pow_le_pow_right₀ hy1 hm
    have h2 : (2:ℝ) ^ m * (1/2 : ℝ) ^ m = 1 := by
      rw [← mul_pow]; norm_num
    calc (1:ℝ) = (2:ℝ) ^ m * (1/2 : ℝ) ^ m := h2.symm
      _ ≤ y ^ k * (1/2 : ℝ) ^ m := by
        apply mul_le_mul_of_nonneg_right h1 (by positivity)
  have hA : 0 ≤ y ^ k * (1/2 : ℝ) ^ a := by positivity
  have hB : 0 ≤ y ^ k * (1/2 : ℝ) ^ b := by positivity
  have hC : 0 ≤ (2 : ℝ) ^ (a + b) / y ^ (2 * k) := by positivity
  by_cases ha : 3 * a ≤ k
  · have := key a ha; linarith
  by_cases hb : 3 * b ≤ k
  · have := key b hb; linarith
  · have hab : 2 * k ≤ 3 * (a + b) := by omega
    have h1 : y ^ (2 * k) ≤ (2:ℝ) ^ (a + b) := by
      calc y ^ (2 * k) ≤ y ^ (3 * (a + b)) := pow_le_pow_right₀ hy1 hab
        _ = (y ^ 3) ^ (a + b) := by rw [pow_mul]
        _ = (2:ℝ) ^ (a + b) := by rw [hy3]
    have h2 : 1 ≤ (2 : ℝ) ^ (a + b) / y ^ (2 * k) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith

theorem tauPerp_le (n : ℕ) (hn : Squarefree n) (y : ℝ) (hy1 : 1 ≤ y) (hy3 : y ^ 3 = 2) :
    (Erdos1100.tauPerp n : ℝ) ≤
      2 * (y ^ (ω n) * (3/2 : ℝ) ^ (ω n)) + (3 : ℝ) ^ (ω n) / y ^ (2 * ω n) := by
  classical
  set k := ω n with hk
  have hy0 : 0 < y := by linarith
  have hn0 : n ≠ 0 := hn.ne_zero
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hf : (Set.ofPred (· ∣ n)).Finite :=
    (Set.finite_Iic n).subset fun d hd => Nat.le_of_dvd hnpos hd
  have hcard : hf.toFinset.card = n.divisors.card := by
    congr 1
    ext d
    simp [hn0]
  set S := Finset.univ.filter fun i : Fin (n.divisors.card - 1) ↦
    Nat.Coprime (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) ((i : ℕ) + 1)) with hS
  have htau : Erdos1100.tauPerp n = S.card := rfl
  have hdvd : ∀ i, i < n.divisors.card → Nat.nth (· ∣ n) i ∣ n := fun i hi =>
    Nat.nth_mem_of_lt_card hf (by rw [hcard]; exact hi)
  have hmono : ∀ i j, i < j → j < n.divisors.card → Nat.nth (· ∣ n) i < Nat.nth (· ∣ n) j :=
    fun i j hij hj => Nat.nth_lt_nth_of_lt_card hf hij (by rw [hcard]; exact hj)
  -- weights
  set w1 : ℕ → ℝ := fun d => y ^ k * (1/2 : ℝ) ^ (ω d) with hw1
  set w3 : ℕ → ℝ := fun d => (2 : ℝ) ^ (ω d) / y ^ (2 * k) with hw3
  have hw1nn : ∀ d, 0 ≤ w1 d := fun d => by positivity
  have hw3nn : ∀ d, 0 ≤ w3 d := fun d => by positivity
  have hsum1 : ∑ d ∈ n.divisors, w1 d ≤ y ^ k * (3/2 : ℝ) ^ k := by
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := divisor_sum_le n hn (1/2 : ℝ) (by norm_num)
    rw [← hk] at this
    norm_num at this ⊢
    exact this
  have hsum3 : ∑ d ∈ n.divisors, w3 d ≤ (3 : ℝ) ^ k / y ^ (2 * k) := by
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := divisor_sum_le n hn (2 : ℝ) (by norm_num)
    rw [← hk] at this
    norm_num at this ⊢
    exact this
  -- the three maps
  have hT1 : ∑ i ∈ S, w1 (Nat.nth (· ∣ n) (i : ℕ)) ≤ ∑ d ∈ n.divisors, w1 d := by
    apply sum_comp_le_of_injOn S (fun i => Nat.nth (· ∣ n) (i : ℕ)) n.divisors w1 hw1nn
    · intro i _
      exact Nat.mem_divisors.mpr ⟨hdvd i (by omega), hn0⟩
    · intro i _ j _ hij
      have h := Nat.nth_injOn hf (by rw [Set.mem_Iio, hcard]; omega)
        (by rw [Set.mem_Iio, hcard]; omega) hij
      exact Fin.ext h
  have hT2 : ∑ i ∈ S, w1 (Nat.nth (· ∣ n) ((i : ℕ) + 1)) ≤ ∑ d ∈ n.divisors, w1 d := by
    apply sum_comp_le_of_injOn S (fun i => Nat.nth (· ∣ n) ((i : ℕ) + 1)) n.divisors w1 hw1nn
    · intro i _
      exact Nat.mem_divisors.mpr ⟨hdvd _ (by omega), hn0⟩
    · intro i _ j _ hij
      have h := Nat.nth_injOn hf (by rw [Set.mem_Iio, hcard]; omega)
        (by rw [Set.mem_Iio, hcard]; omega) hij
      exact Fin.ext (by simpa using h)
  have hT3 : ∑ i ∈ S, w3 (Nat.nth (· ∣ n) (i : ℕ) * Nat.nth (· ∣ n) ((i : ℕ) + 1)) ≤
      ∑ d ∈ n.divisors, w3 d := by
    apply sum_comp_le_of_injOn S
      (fun i => Nat.nth (· ∣ n) (i : ℕ) * Nat.nth (· ∣ n) ((i : ℕ) + 1)) n.divisors w3 hw3nn
    · intro i hi
      have hcop : Nat.Coprime (Nat.nth (· ∣ n) (i : ℕ)) (Nat.nth (· ∣ n) ((i : ℕ) + 1)) :=
        (Finset.mem_filter.mp hi).2
      exact Nat.mem_divisors.mpr
        ⟨hcop.mul_dvd_of_dvd_of_dvd (hdvd _ (by omega)) (hdvd _ (by omega)), hn0⟩
    · have hsm : StrictMonoOn
          (fun i : Fin (n.divisors.card - 1) =>
            Nat.nth (· ∣ n) (i : ℕ) * Nat.nth (· ∣ n) ((i : ℕ) + 1)) (S : Set _) := by
        intro i _ j _ hij
        have hij' : (i : ℕ) < (j : ℕ) := hij
        have hj := j.isLt
        exact mul_lt_mul'' (hmono _ _ hij' (by omega)) (hmono _ _ (by omega) (by omega))
          (Nat.zero_le _) (Nat.zero_le _)
      exact hsm.injOn
  -- pointwise inequality
  have hpt : ∀ i ∈ S, (1 : ℝ) ≤ w1 (Nat.nth (· ∣ n) (i : ℕ)) + w1 (Nat.nth (· ∣ n) ((i : ℕ) + 1))
      + w3 (Nat.nth (· ∣ n) (i : ℕ) * Nat.nth (· ∣ n) ((i : ℕ) + 1)) := by
    intro i hi
    have hcop : Nat.Coprime (Nat.nth (· ∣ n) (i : ℕ)) (Nat.nth (· ∣ n) ((i : ℕ) + 1)) :=
      (Finset.mem_filter.mp hi).2
    simp only [hw1, hw3]
    rw [ArithmeticFunction.cardDistinctFactors_mul hcop]
    exact pair_ineq y hy1 hy3 _ _ k
  have hcardS : (S.card : ℝ) = ∑ i ∈ S, (1 : ℝ) := by simp
  rw [htau, hcardS]
  calc ∑ i ∈ S, (1 : ℝ)
      ≤ ∑ i ∈ S, (w1 (Nat.nth (· ∣ n) (i : ℕ)) + w1 (Nat.nth (· ∣ n) ((i : ℕ) + 1))
      + w3 (Nat.nth (· ∣ n) (i : ℕ) * Nat.nth (· ∣ n) ((i : ℕ) + 1))) := Finset.sum_le_sum hpt
    _ = ∑ i ∈ S, w1 (Nat.nth (· ∣ n) (i : ℕ)) + ∑ i ∈ S, w1 (Nat.nth (· ∣ n) ((i : ℕ) + 1))
      + ∑ i ∈ S, w3 (Nat.nth (· ∣ n) (i : ℕ) * Nat.nth (· ∣ n) ((i : ℕ) + 1)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ y ^ k * (3/2 : ℝ) ^ k + y ^ k * (3/2 : ℝ) ^ k + (3 : ℝ) ^ k / y ^ (2 * k) := by
        linarith [hT1, hT2, hT3, hsum1, hsum3]
    _ = 2 * (y ^ k * (3/2 : ℝ) ^ k) + (3 : ℝ) ^ k / y ^ (2 * k) := by ring

theorem final_identity (k : ℕ) (y : ℝ) (hy : y = (2 : ℝ) ^ ((1 : ℝ) / 3)) :
    2 * (y ^ k * (3/2 : ℝ) ^ k) + (3 : ℝ) ^ k / y ^ (2 * k)
      = 3 * (3 / (2 : ℝ) ^ ((2 : ℝ) / 3)) ^ k := by
  have hy0 : 0 < y := by
    rw [hy]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hy3 : y ^ 3 = 2 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hy2 : (2 : ℝ) ^ ((2 : ℝ) / 3) = y ^ 2 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [hy2]
  have e1 : y ^ k * (3/2 : ℝ) ^ k = (3 * y / 2) ^ k := by
    rw [← mul_pow]
    ring_nf
  have e2 : (3 : ℝ) ^ k / y ^ (2 * k) = (3 / y ^ 2) ^ k := by
    rw [div_pow, pow_mul]
  have e3 : (3 / y ^ 2 : ℝ) = 3 * y / 2 := by
    rw [div_eq_div_iff (by positivity) (by norm_num)]
    nlinarith [hy3]
  rw [e1, e2, e3]
  ring

end OMA.Helpers

theorem OMA.solution : type_of% @Erdos1100.erdos_1100.variants.erdos_tenenbaum_g := by
  intro k
  set B : ℝ := 3 * (3 / (2 : ℝ) ^ ((2 : ℝ) / 3)) ^ k with hB
  set y : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 3) with hy
  have hy1 : 1 ≤ y := by
    rw [hy]
    exact Real.one_le_rpow (by norm_num) (by norm_num)
  have hy3 : y ^ 3 = 2 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hbound : ∀ n : ℕ, Squarefree n → ω n = k → (Erdos1100.tauPerp n : ℝ) ≤ B := by
    intro n hn hk
    have := OMA.Helpers.tauPerp_le n hn y hy1 hy3
    rw [hk] at this
    rw [hB, ← OMA.Helpers.final_identity k y hy]
    exact this
  have hB0 : 0 ≤ B := by positivity
  have hg : Erdos1100.g k ≤ ⌊B⌋₊ := by
    apply csSup_le'
    rintro t ⟨n, hn, hk, rfl⟩
    exact Nat.le_floor (hbound n hn hk)
  calc (Erdos1100.g k : ℝ) ≤ (⌊B⌋₊ : ℝ) := by exact_mod_cast hg
    _ ≤ B := Nat.floor_le hB0
