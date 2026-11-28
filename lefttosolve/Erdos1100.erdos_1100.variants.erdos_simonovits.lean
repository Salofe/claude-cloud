import FormalConjectures.ErdosProblems.«1100»

/-!
Erdős–Simonovits bounds for g(k) (squarefree n with ω(n) = k).

Upper bound: the Erdős–Tenenbaum argument gives τ⊥(n) ≤ 3 (3y/2)^k with y = 2^(1/3), and
3y/2 < 39/20 because y < 13/10; hence g(k) < (2 - 1/20)^k for large k.

Lower bound: call d good for n if its successor divisor d' is coprime to d. If N ≥ 1 and p < q are
primes with N < p and (q - p) N < p, then for N p q the good divisors of N stay good, N and p are
good (partners p and q), and q d is good with partner p d' for each good d of N (partner d').
These are pairwise distinct, so the count at least doubles plus two. Such p, q exist for every N:
otherwise all primes beyond N are spaced by the ratio (N+1)/N, so the reciprocal sum over primes at
least 2N+3 is at most (N+1)/(2N+3) < 1/2, contradicting `one_half_le_sum_primes_ge_one_div`.
Iterating (and one extra large prime for odd k) gives g(k) + 2 ≥ 2^(k/2+1) ≥ √2^k + 2 for k ≥ 4.
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


def Consec (n d d' : ℕ) : Prop :=
  d ∣ n ∧ d' ∣ n ∧ d < d' ∧ ∀ e, e ∣ n → d < e → e < d' → False

def Good (n d : ℕ) : Prop := ∃ d', Consec n d d' ∧ Nat.Coprime d d'

theorem card_le_tauPerp (n : ℕ) (hn : 0 < n) (S : Finset ℕ) (hS : ∀ d ∈ S, Good n d) :
    S.card ≤ Erdos1100.tauPerp n := by
  have hf : (Set.ofPred (· ∣ n)).Finite :=
    (Set.finite_Iic n).subset fun d hd => Nat.le_of_dvd hn hd
  have hcard : hf.toFinset.card = n.divisors.card := by
    congr 1
    ext d
    simp [hn.ne']
  set T := Finset.univ.filter fun i : Fin (n.divisors.card - 1) ↦
    Nat.Coprime (Nat.nth (· ∣ n) i) (Nat.nth (· ∣ n) ((i : ℕ) + 1)) with hT
  have htau : Erdos1100.tauPerp n = T.card := rfl
  have hsub : S ⊆ T.image (fun i : Fin (n.divisors.card - 1) => Nat.nth (· ∣ n) (i : ℕ)) := by
    intro d hd
    obtain ⟨d', ⟨hdn, hd'n, hlt, hnone⟩, hcop⟩ := hS d hd
    have hi : Nat.nth (· ∣ n) (Nat.count (· ∣ n) d) = d := Nat.nth_count hdn
    have hj : Nat.nth (· ∣ n) (Nat.count (· ∣ n) d') = d' := Nat.nth_count hd'n
    have hij : Nat.count (· ∣ n) d < Nat.count (· ∣ n) d' := Nat.count_strict_mono hdn hlt
    have hjc : Nat.count (· ∣ n) d' < hf.toFinset.card := Nat.count_lt_card hf hd'n
    have hj1 : Nat.count (· ∣ n) d' = Nat.count (· ∣ n) d + 1 := by
      by_contra hne
      have h1 : Nat.count (· ∣ n) d + 1 < Nat.count (· ∣ n) d' := by omega
      have hdiv := Nat.nth_mem_of_lt_card hf (lt_trans h1 hjc)
      have ha := Nat.nth_lt_nth_of_lt_card hf (Nat.lt_succ_self (Nat.count (· ∣ n) d))
        (lt_trans h1 hjc)
      have hb := Nat.nth_lt_nth_of_lt_card hf h1 hjc
      rw [hi] at ha
      rw [hj] at hb
      exact hnone _ hdiv ha hb
    refine Finset.mem_image.mpr ⟨⟨Nat.count (· ∣ n) d, by omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hi⟩
    show Nat.Coprime (Nat.nth (· ∣ n) (Nat.count (· ∣ n) d))
      (Nat.nth (· ∣ n) (Nat.count (· ∣ n) d + 1))
    rw [hi, ← hj1, hj]
    exact hcop
  calc S.card ≤ (T.image _).card := Finset.card_le_card hsub
    _ ≤ T.card := Finset.card_image_le
    _ = Erdos1100.tauPerp n := htau.symm

theorem dvd_mul_prime_cases {N P e : ℕ} (hP : P.Prime) (h : e ∣ N * P) :
    ∃ a, a ∣ N ∧ (e = a ∨ e = a * P) := by
  obtain ⟨a, f, ha, hf, rfl⟩ := dvd_mul.mp h
  rcases (Nat.dvd_prime hP).mp hf with rfl | rfl
  · exact ⟨a, ha, Or.inl (mul_one a)⟩
  · exact ⟨a, ha, Or.inr rfl⟩

theorem dvd_mul_two_primes_cases {N p q e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : e ∣ N * p * q) :
    ∃ a, a ∣ N ∧ (e = a ∨ e = a * p ∨ e = a * q ∨ e = a * p * q) := by
  obtain ⟨b, f, hb, hf, rfl⟩ := dvd_mul.mp h
  obtain ⟨a, ha, hb'⟩ := dvd_mul_prime_cases hp hb
  rcases (Nat.dvd_prime hq).mp hf with hf1 | hf1
  · rcases hb' with hb1 | hb1
    · exact ⟨a, ha, Or.inl (by rw [hf1, hb1, mul_one])⟩
    · exact ⟨a, ha, Or.inr (Or.inl (by rw [hf1, hb1, mul_one]))⟩
  · rcases hb' with hb1 | hb1
    · exact ⟨a, ha, Or.inr (Or.inr (Or.inl (by rw [hf1, hb1])))⟩
    · exact ⟨a, ha, Or.inr (Or.inr (Or.inr (by rw [hf1, hb1])))⟩

theorem good_lift_one {N P : ℕ} (hN : 0 < N) (hP : P.Prime) (hNP : N < P) {d : ℕ}
    (hd : Good N d) : Good (N * P) d := by
  obtain ⟨d', ⟨hdN, hd'N, hlt, hnone⟩, hcop⟩ := hd
  refine ⟨d', ⟨dvd_mul_of_dvd_left hdN P, dvd_mul_of_dvd_left hd'N P, hlt, ?_⟩, hcop⟩
  intro e he h1 h2
  have hd'le : d' ≤ N := Nat.le_of_dvd hN hd'N
  obtain ⟨a, ha, rfl | rfl⟩ := dvd_mul_prime_cases hP he
  · exact hnone _ ha h1 h2
  · have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha hN
    have : P ≤ a * P := Nat.le_mul_of_pos_left P ha0
    omega

theorem good_lift_two {N p q : ℕ} (hN : 0 < N) (hp : p.Prime) (hq : q.Prime) (hNp : N < p)
    (hpq : p < q) {d : ℕ} (hd : Good N d) : Good (N * p * q) d := by
  obtain ⟨d', ⟨hdN, hd'N, hlt, hnone⟩, hcop⟩ := hd
  refine ⟨d', ⟨dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdN p) q,
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd'N p) q, hlt, ?_⟩, hcop⟩
  intro e he h1 h2
  have hd'le : d' ≤ N := Nat.le_of_dvd hN hd'N
  obtain ⟨a, ha, rfl | rfl | rfl | rfl⟩ := dvd_mul_two_primes_cases hp hq he
  · exact hnone _ ha h1 h2
  · have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha hN
    have : p ≤ a * p := Nat.le_mul_of_pos_left p ha0
    omega
  · have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha hN
    have : q ≤ a * q := Nat.le_mul_of_pos_left q ha0
    omega
  · have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha hN
    have : q ≤ a * p * q := Nat.le_mul_of_pos_left q (Nat.mul_pos ha0 hp.pos)
    omega

theorem good_N {N p q : ℕ} (hN : 0 < N) (hp : p.Prime) (hq : q.Prime) (hNp : N < p)
    (hpq : p < q) : Good (N * p * q) N := by
  refine ⟨p, ⟨dvd_mul_of_dvd_left (dvd_mul_right N p) q,
    dvd_mul_of_dvd_left (dvd_mul_left p N) q, hNp, ?_⟩, ?_⟩
  · intro e he h1 h2
    obtain ⟨a, ha, rfl | rfl | rfl | rfl⟩ := dvd_mul_two_primes_cases hp hq he
    · have := Nat.le_of_dvd hN ha
      omega
    · have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha hN
      have : p ≤ a * p := Nat.le_mul_of_pos_left p ha0
      omega
    · have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha hN
      have : q ≤ a * q := Nat.le_mul_of_pos_left q ha0
      omega
    · have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha hN
      have : q ≤ a * p * q := Nat.le_mul_of_pos_left q (Nat.mul_pos ha0 hp.pos)
      omega
  · exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => by
      have := Nat.le_of_dvd hN h
      omega)

theorem good_p {N p q : ℕ} (hN : 0 < N) (hp : p.Prime) (hq : q.Prime) (hNp : N < p)
    (hpq : p < q) (hclose : (q - p) * N < p) : Good (N * p * q) p := by
  have hq2 : q < 2 * p := by
    have : q - p ≤ (q - p) * N := Nat.le_mul_of_pos_right _ hN
    omega
  refine ⟨q, ⟨dvd_mul_of_dvd_left (dvd_mul_left p N) q, dvd_mul_left q (N * p), hpq, ?_⟩,
    (Nat.coprime_primes hp hq).mpr (ne_of_lt hpq)⟩
  intro e he h1 h2
  obtain ⟨a, ha, rfl | rfl | rfl | rfl⟩ := dvd_mul_two_primes_cases hp hq he
  · have := Nat.le_of_dvd hN ha
    omega
  · have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha hN
    rcases Nat.lt_or_ge a 2 with ha2 | ha2
    · have : a = 1 := by omega
      subst this
      omega
    · have : 2 * p ≤ a * p := Nat.mul_le_mul_right p ha2
      omega
  · have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha hN
    have : q ≤ a * q := Nat.le_mul_of_pos_left q ha0
    omega
  · have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha hN
    have : q ≤ a * p * q := Nat.le_mul_of_pos_left q (Nat.mul_pos ha0 hp.pos)
    omega

theorem good_qd {N p q : ℕ} (hN : 0 < N) (hp : p.Prime) (hq : q.Prime) (hNp : N < p)
    (hpq : p < q) (hclose : (q - p) * N < p) {d : ℕ} (hd : Good N d) :
    Good (N * p * q) (q * d) := by
  obtain ⟨d', ⟨hdN, hd'N, hlt, hnone⟩, hcop⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdN hN
  have hd'le : d' ≤ N := Nat.le_of_dvd hN hd'N
  have hdle : d ≤ N := by omega
  have hlt' : q * d < p * d' := by
    have h1 : q * d = p * d + (q - p) * d := by
      rw [← Nat.add_mul]
      congr 1
      omega
    have h2 : (q - p) * d ≤ (q - p) * N := Nat.mul_le_mul_left _ hdle
    have h3 : p * (d + 1) ≤ p * d' := Nat.mul_le_mul_left _ hlt
    rw [Nat.mul_add, mul_one] at h3
    omega
  obtain ⟨c, hc⟩ := hdN
  obtain ⟨c', hc'⟩ := hd'N
  refine ⟨p * d', ⟨⟨c * p, by rw [hc]; ring⟩, ⟨c' * q, by rw [hc']; ring⟩, hlt', ?_⟩, ?_⟩
  · intro e he h1 h2
    obtain ⟨a, ha, rfl | rfl | rfl | rfl⟩ := dvd_mul_two_primes_cases hp hq he
    · have := Nat.le_of_dvd hN ha
      have : q ≤ q * d := Nat.le_mul_of_pos_right q hd0
      omega
    · have hda : d < a := by
        have : d * p ≤ q * d := by
          rw [mul_comm q d]
          exact Nat.mul_le_mul_left d hpq.le
        exact Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt this h1)
      have had' : a < d' := by
        rw [mul_comm p d'] at h2
        exact Nat.lt_of_mul_lt_mul_right h2
      exact hnone a ha hda had'
    · have hda : d < a := by
        rw [mul_comm q d] at h1
        exact Nat.lt_of_mul_lt_mul_right h1
      have had' : a < d' := by
        have : p * d' ≤ d' * q := by
          rw [mul_comm p d']
          exact Nat.mul_le_mul_left d' hpq.le
        exact Nat.lt_of_mul_lt_mul_right (lt_of_lt_of_le h2 this)
      exact hnone a ha hda had'
    · have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha hN
      have h3 : p * q ≤ a * p * q := by
        rw [mul_assoc]
        exact Nat.le_mul_of_pos_left _ ha0
      have h4 : p * d' < p * q := Nat.mul_lt_mul_of_pos_left (by omega) hp.pos
      omega
  · have hqp : Nat.Coprime q p := (Nat.coprime_primes hq hp).mpr (ne_of_gt hpq)
    have hqd' : Nat.Coprime q d' := (Nat.Prime.coprime_iff_not_dvd hq).mpr fun h => by
      have := Nat.le_of_dvd (by omega) h
      omega
    have hdp : Nat.Coprime d p :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => by
        have := Nat.le_of_dvd hd0 h
        omega)
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_right hqp hqd') (Nat.Coprime.mul_right hdp hcop)


theorem step {N p q : ℕ} (hN : 0 < N) (hp : p.Prime) (hq : q.Prime) (hNp : N < p) (hpq : p < q)
    (hclose : (q - p) * N < p) (S : Finset ℕ) (hS : ∀ d ∈ S, Good N d) :
    ∃ S' : Finset ℕ, (∀ d ∈ S', Good (N * p * q) d) ∧ 2 * S.card + 2 ≤ S'.card := by
  classical
  have hSlt : ∀ d ∈ S, 0 < d ∧ d < N := by
    intro d hd
    obtain ⟨d', ⟨hdN, hd'N, hlt, -⟩, -⟩ := hS d hd
    exact ⟨Nat.pos_of_dvd_of_pos hdN hN, lt_of_lt_of_le hlt (Nat.le_of_dvd hN hd'N)⟩
  set T := S.image (fun d => q * d) with hT
  have hTge : ∀ x ∈ T, q ≤ x := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    exact Nat.le_mul_of_pos_right q (hSlt d hd).1
  have hTcard : T.card = S.card :=
    Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hq.pos h)
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro a ha haT
    have := hTge a haT
    have := (hSlt a ha).2
    omega
  have hp_notin : p ∉ S ∪ T := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · have := (hSlt p h).2
      omega
    · have := hTge p h
      omega
  have hN_notin : N ∉ insert p (S ∪ T) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · omega
    rcases Finset.mem_union.mp h with h | h
    · have := (hSlt N h).2
      omega
    · have := hTge N h
      omega
  refine ⟨insert N (insert p (S ∪ T)), ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · rw [hx]
      exact good_N hN hp hq hNp hpq
    rcases Finset.mem_insert.mp hx with hx | hx
    · rw [hx]
      exact good_p hN hp hq hNp hpq hclose
    rcases Finset.mem_union.mp hx with hx | hx
    · exact good_lift_two hN hp hq hNp hpq (hS x hx)
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      exact good_qd hN hp hq hNp hpq hclose (hS d hd)
  · rw [Finset.card_insert_of_notMem hN_notin, Finset.card_insert_of_notMem hp_notin,
      Finset.card_union_of_disjoint hdisj, hTcard]
    omega

theorem coprime_of_lt_prime {N P : ℕ} (hN : 0 < N) (hP : P.Prime) (hNP : N < P) :
    Nat.Coprime N P :=
  Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hP).mpr fun h => by
    have := Nat.le_of_dvd hN h
    omega)

theorem sq_omega_one {N P : ℕ} (hN : 0 < N) (hsq : Squarefree N) (hP : P.Prime) (hNP : N < P) :
    Squarefree (N * P) ∧ ω (N * P) = ω N + 1 := by
  have hNP' : Nat.Coprime N P := coprime_of_lt_prime hN hP hNP
  constructor
  · rw [Nat.squarefree_mul_iff]
    exact ⟨hNP', hsq, hP.prime.squarefree⟩
  · rw [ArithmeticFunction.cardDistinctFactors_mul hNP',
      ArithmeticFunction.cardDistinctFactors_apply_prime hP]

theorem sq_omega_two {N p q : ℕ} (hN : 0 < N) (hsq : Squarefree N) (hp : p.Prime) (hq : q.Prime)
    (hNp : N < p) (hpq : p < q) : Squarefree (N * p * q) ∧ ω (N * p * q) = ω N + 2 := by
  have hNp' : Nat.Coprime N p := coprime_of_lt_prime hN hp hNp
  have hNq' : Nat.Coprime N q := coprime_of_lt_prime hN hq (by omega)
  have hpq' : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr (ne_of_lt hpq)
  have hNpq : Nat.Coprime (N * p) q := Nat.Coprime.mul_left hNq' hpq'
  constructor
  · rw [Nat.squarefree_mul_iff, Nat.squarefree_mul_iff]
    exact ⟨hNpq, ⟨hNp', hsq, hp.prime.squarefree⟩, hq.prime.squarefree⟩
  · rw [ArithmeticFunction.cardDistinctFactors_mul hNpq,
      ArithmeticFunction.cardDistinctFactors_mul hNp',
      ArithmeticFunction.cardDistinctFactors_apply_prime hp,
      ArithmeticFunction.cardDistinctFactors_apply_prime hq]

theorem sep_sum_le (N : ℕ) (hN : 0 < N) : ∀ (n : ℕ) (F : Finset ℕ), F.card = n → ∀ L : ℝ, 0 < L →
    (∀ x ∈ F, L ≤ (x : ℝ)) → (∀ x ∈ F, ∀ y ∈ F, x < y → (x : ℝ) * (N + 1) ≤ y * N) →
    ∑ x ∈ F, (1 : ℝ) / x ≤ (N + 1) / L := by
  intro n
  induction n with
  | zero =>
    intro F hF L hL _ _
    rw [Finset.card_eq_zero.mp hF, Finset.sum_empty]
    positivity
  | succ n ih =>
    intro F hF L hL hLF hsep
    have hne : F.Nonempty := Finset.card_pos.mp (by omega)
    have hmF : F.min' hne ∈ F := Finset.min'_mem F hne
    have hmle : ∀ x ∈ F, F.min' hne ≤ x := fun x hx => Finset.min'_le F x hx
    set m := F.min' hne with hm
    have hLm : L ≤ (m : ℝ) := hLF m hmF
    have hm0 : (0 : ℝ) < m := lt_of_lt_of_le hL hLm
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [← Finset.add_sum_erase F _ hmF]
    have hcard' : (F.erase m).card = n := by
      rw [Finset.card_erase_of_mem hmF]
      omega
    have hrest := ih (F.erase m) hcard' (m * (N + 1) / N) (by positivity) ?_ ?_
    · have e : ((N : ℝ) + 1) / (m * (N + 1) / N) = N / m := by
        field_simp
      have h3 : ((N : ℝ) + 1) / m ≤ (N + 1) / L :=
        div_le_div_of_nonneg_left (by positivity) hL hLm
      calc 1 / (m : ℝ) + ∑ x ∈ F.erase m, 1 / (x : ℝ) ≤ 1 / m + N / m := by
            rw [← e]
            linarith
        _ = (N + 1) / m := by ring
        _ ≤ (N + 1) / L := h3
    · intro x hx
      have hxF := Finset.mem_of_mem_erase hx
      have hxm : x ≠ m := Finset.ne_of_mem_erase hx
      have hlt : m < x := lt_of_le_of_ne (hmle x hxF) (Ne.symm hxm)
      have := hsep m hmF x hxF hlt
      rw [div_le_iff₀ hN0]
      linarith
    · intro x hx y hy hxy
      exact hsep x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy

theorem close_primes (N : ℕ) (hN : 0 < N) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ N < p ∧ p < q ∧ (q - p) * N < p := by
  by_contra h
  push Not at h
  have hsum := one_half_le_sum_primes_ge_one_div (2 * N + 3)
  set k := 2 * N + 3 with hk
  set F := (4 ^ (k.primesBelow.card + 1)).succ.primesBelow \ k.primesBelow with hF
  have hFmem : ∀ x ∈ F, x.Prime ∧ k ≤ x := by
    intro x hx
    rw [hF, Finset.mem_sdiff, Nat.mem_primesBelow, Nat.mem_primesBelow] at hx
    refine ⟨hx.1.2, ?_⟩
    by_contra h'
    exact hx.2 ⟨by omega, hx.1.2⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hle := sep_sum_le N hN F.card F rfl (k : ℝ) (by positivity)
    (fun x hx => by exact_mod_cast (hFmem x hx).2)
    (fun x hx y hy hxy => by
      have hx' := hFmem x hx
      have hy' := hFmem y hy
      have h1 := h x y hx'.1 hy'.1 (by omega) hxy
      have h2 : (x : ℝ) ≤ ((y - x : ℕ) : ℝ) * N := by exact_mod_cast h1
      rw [Nat.cast_sub hxy.le] at h2
      linarith)
  have hk' : ((N : ℝ) + 1) / k < 1 / 2 := by
    rw [div_lt_iff₀ (by positivity), hk]
    push_cast
    linarith
  linarith

theorem exists_good_even (m : ℕ) : ∃ n : ℕ, ∃ S : Finset ℕ, 0 < n ∧ Squarefree n ∧ ω n = 2 * m ∧
    (∀ d ∈ S, Good n d) ∧ 2 ^ (m + 1) ≤ S.card + 2 := by
  induction m with
  | zero => exact ⟨1, ∅, Nat.one_pos, squarefree_one, by simp, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨n, S, hn, hsq, hω, hS, hcard⟩ := ih
    obtain ⟨p, q, hp, hq, hnp, hpq, hclose⟩ := close_primes n hn
    obtain ⟨S', hS', hcard'⟩ := step hn hp hq hnp hpq hclose S hS
    obtain ⟨hsq', hω'⟩ := sq_omega_two hn hsq hp hq hnp hpq
    refine ⟨n * p * q, S', Nat.mul_pos (Nat.mul_pos hn hp.pos) hq.pos, hsq', ?_, hS', ?_⟩
    · rw [hω', hω]
      ring
    · rw [pow_succ]
      omega

theorem exists_good (k : ℕ) : ∃ n : ℕ, ∃ S : Finset ℕ, 0 < n ∧ Squarefree n ∧ ω n = k ∧
    (∀ d ∈ S, Good n d) ∧ 2 ^ (k / 2 + 1) ≤ S.card + 2 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · obtain ⟨n, S, hn, hsq, hω, hS, hcard⟩ := exists_good_even m
    refine ⟨n, S, hn, hsq, hω, hS, ?_⟩
    have : 2 * m / 2 = m := by omega
    rw [this]
    exact hcard
  · obtain ⟨n, S, hn, hsq, hω, hS, hcard⟩ := exists_good_even m
    obtain ⟨P, hP1, hP⟩ := Nat.exists_infinite_primes (n + 1)
    obtain ⟨hsq', hω'⟩ := sq_omega_one hn hsq hP (by omega)
    refine ⟨n * P, S, Nat.mul_pos hn hP.pos, hsq', by rw [hω', hω],
      fun d hd => good_lift_one hn hP (by omega) (hS d hd), ?_⟩
    have : (2 * m + 1) / 2 = m := by omega
    rw [this]
    exact hcard

theorem g_lower (k : ℕ) (M : ℕ) (hM : ∀ n, Squarefree n → ω n = k → Erdos1100.tauPerp n ≤ M) :
    2 ^ (k / 2 + 1) ≤ Erdos1100.g k + 2 := by
  obtain ⟨n, S, hn, hsq, hω, hS, hcard⟩ := exists_good k
  have h1 : S.card ≤ Erdos1100.tauPerp n := card_le_tauPerp n hn S hS
  have h2 : Erdos1100.tauPerp n ≤ Erdos1100.g k := by
    apply le_csSup
    · exact ⟨M, fun t ⟨n', hn', hk', ht'⟩ => ht' ▸ hM n' hn' hk'⟩
    · exact ⟨n, hsq, hω, rfl⟩
  omega

end OMA.Helpers

theorem OMA.solution : type_of% @Erdos1100.erdos_1100.variants.erdos_simonovits := by
  set y : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 3) with hy
  have hy1 : 1 ≤ y := by
    rw [hy]
    exact Real.one_le_rpow (by norm_num) (by norm_num)
  have hy3 : y ^ 3 = 2 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  set B : ℝ := 3 * y / 2 with hB
  have hB0 : 0 < B := by positivity
  have hylt : y < 13 / 10 := by
    by_contra h
    push Not at h
    have h2 : (13 / 10 : ℝ) ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ (by norm_num) h 3
    rw [hy3] at h2
    norm_num at h2
  have hBlt : B < 39 / 20 := by
    rw [hB]
    linarith
  have hbound : ∀ k n, Squarefree n → ω n = k → (Erdos1100.tauPerp n : ℝ) ≤ 3 * B ^ k := by
    intro k n hn hk
    have h := OMA.Helpers.tauPerp_le n hn y hy1 hy3
    rw [hk] at h
    have e1 : y ^ k * (3 / 2 : ℝ) ^ k = B ^ k := by
      rw [hB, ← mul_pow]
      congr 1
      ring
    have e2 : (3 : ℝ) ^ k / y ^ (2 * k) = B ^ k := by
      rw [pow_mul, ← div_pow]
      congr 1
      rw [hB, div_eq_div_iff (by positivity) (by norm_num)]
      linear_combination (-3 : ℝ) * hy3
    rw [e1, e2] at h
    linarith
  have hg_le : ∀ k, (Erdos1100.g k : ℝ) ≤ 3 * B ^ k := by
    intro k
    have hg : Erdos1100.g k ≤ ⌊3 * B ^ k⌋₊ := by
      apply csSup_le'
      rintro t ⟨n, hn, hk, rfl⟩
      exact Nat.le_floor (hbound k n hn hk)
    calc (Erdos1100.g k : ℝ) ≤ (⌊3 * B ^ k⌋₊ : ℝ) := by exact_mod_cast hg
      _ ≤ 3 * B ^ k := Nat.floor_le (by positivity)
  have hg_ge : ∀ k, (2 : ℝ) ^ (k / 2 + 1) ≤ Erdos1100.g k + 2 := by
    intro k
    have := OMA.Helpers.g_lower k ⌊3 * B ^ k⌋₊ (fun n hn hk => Nat.le_floor (hbound k n hn hk))
    exact_mod_cast this
  refine ⟨?_, 1 / 20, by norm_num, ?_⟩
  · intro r hr0 hr
    filter_upwards [Filter.eventually_ge_atTop 4] with k hk
    have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs15 : Real.sqrt 2 ≤ 3 / 2 := by nlinarith
    have h1 : r ^ k < Real.sqrt 2 ^ k := pow_lt_pow_left₀ hr hr0 (by omega)
    have h4 : (4 : ℝ) ≤ 2 ^ (k / 2) := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k / 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : Real.sqrt 2 ^ k ≤ (2 : ℝ) ^ (k / 2 + 1) - 2 := by
      obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' k
      · have hkm : k / 2 = m := by omega
        rw [hkm] at h4 ⊢
        rw [hm, pow_mul, hs2, pow_succ (2 : ℝ) m]
        linarith
      · have hkm : k / 2 = m := by omega
        rw [hkm] at h4 ⊢
        rw [hm, pow_succ (Real.sqrt 2), pow_mul, hs2, pow_succ (2 : ℝ) m]
        nlinarith [mul_nonneg (pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) m) (sub_nonneg.mpr hs15)]
    have h3 := hg_ge k
    linarith
  · have hρ : 1 < (39 / 20 : ℝ) / B := by
      rw [lt_div_iff₀ hB0]
      linarith
    have hev := (tendsto_pow_atTop_atTop_of_one_lt hρ).eventually_gt_atTop 3
    filter_upwards [hev] with k hk
    calc (Erdos1100.g k : ℝ) ≤ 3 * B ^ k := hg_le k
      _ < ((39 / 20) / B) ^ k * B ^ k := mul_lt_mul_of_pos_right hk (by positivity)
      _ = (39 / 20) ^ k := by rw [← mul_pow, div_mul_cancel₀ _ hB0.ne']
      _ = (2 - 1 / 20) ^ k := by norm_num
