import OMAReductions.R_Erdos389_erdos_389_R1

/-!
# Step H2 of Erdos389.erdos_389.R1

Compare p-adic valuations. For p at most B this is the second hypothesis. For p larger than B
every factor is below p^2, so each valuation counts the multiples of p in a block of k
consecutive integers; writing k = Q p + r, the only way the left block can have more multiples
is that p divides k + (p - r) with (n-1)/2 < p - r at most n - 1, which the first hypothesis
rules out. Divisibility then follows from the factorizations.
-/
namespace OMA.Helpers

theorem e389_count (a k p : ℕ) (ha : 1 ≤ a) :
    ((Finset.range k).filter (fun i => p ∣ a + i)).card = (a - 1 + k) / p - (a - 1) / p := by
  have h := Nat.card_multiples (a - 1 + k) p
  have h0 := Nat.card_multiples (a - 1) p
  rw [Finset.card_filter] at h h0
  rw [Finset.sum_range_add] at h
  rw [Finset.card_filter]
  have e : ∀ i, a - 1 + i + 1 = a + i := fun i => by omega
  simp only [e] at h
  omega

theorem e389_val (p x N : ℕ) (hp : p.Prime) (hx : x ≠ 0) (hxN : x ≤ N) (hN : N < p * p) :
    x.factorization p = if p ∣ x then 1 else 0 := by
  split_ifs with h
  · have h1 : 1 ≤ x.factorization p := (hp.dvd_iff_one_le_factorization hx).mp h
    have h2 : x.factorization p < 2 := by
      by_contra h2
      push Not at h2
      have h3 : p ^ 2 ∣ x := (hp.pow_dvd_iff_le_factorization hx).mpr h2
      have h4 := Nat.le_of_dvd (Nat.pos_of_ne_zero hx) h3
      rw [sq] at h4
      omega
    omega
  · exact Nat.factorization_eq_zero_of_not_dvd h

theorem e389_prod (a k p N : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hN : a + k - 1 ≤ N)
    (hNp : N < p * p) :
    (∏ i ∈ Finset.range k, (a + i)).factorization p =
      ((Finset.range k).filter (fun i => p ∣ a + i)).card := by
  rw [Nat.factorization_prod (fun i _ => by omega), Finsupp.finsetSum_apply, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  exact e389_val p (a + i) N hp (by omega) (by omega) hNp

theorem e389_main : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    (∀ s : ℕ, n - 1 < 2 * s → s ≤ n - 1 → ∀ p : ℕ, p.Prime → p ∣ k + s →
      p ≤ max (n - 1) (Nat.sqrt (n + 2 * k - 1))) →
    (∀ p : ℕ, p.Prime → p ≤ max (n - 1) (Nat.sqrt (n + 2 * k - 1)) →
      padicValNat p (∏ i ∈ Finset.range k, (n + i)) ≤
        padicValNat p (∏ i ∈ Finset.range k, (n + k + i))) →
    ∏ i ∈ Finset.range k, (n + i) ∣ ∏ i ∈ Finset.range k, (n + k + i) := by
  intro n k hn hk hsmooth hsmall
  have hL : ∏ i ∈ Finset.range k, (n + i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by omega)
  have hR : ∏ i ∈ Finset.range k, (n + k + i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by omega)
  apply (Nat.factorization_prime_le_iff_dvd hL hR).mp
  intro p hp
  by_cases hB : p ≤ max (n - 1) (Nat.sqrt (n + 2 * k - 1))
  · rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    exact hsmall p hp hB
  · push Not at hB
    have hpn : n - 1 < p := lt_of_le_of_lt (le_max_left _ _) hB
    have hps : Nat.sqrt (n + 2 * k - 1) < p := lt_of_le_of_lt (le_max_right _ _) hB
    have hpp : n + 2 * k - 1 < p * p := Nat.sqrt_lt.mp hps
    rw [e389_prod n k p (n + 2 * k - 1) hp hn (by omega) hpp,
      e389_prod (n + k) k p (n + 2 * k - 1) hp (by omega) (by omega) hpp,
      e389_count n k p hn, e389_count (n + k) k p (by omega)]
    have hp0 : 0 < p := hp.pos
    have h0 : (n - 1) / p = 0 := Nat.div_eq_of_lt hpn
    obtain ⟨Q, r, hr, hk'⟩ : ∃ Q r, r < p ∧ k = p * Q + r :=
      ⟨k / p, k % p, Nat.mod_lt _ hp0, (Nat.div_add_mod k p).symm⟩
    have hQ2 : p * (2 * Q) = 2 * (p * Q) := by ring
    have e1 : n - 1 + k = p * Q + (n - 1 + r) := by omega
    have e2 : n + k - 1 + k = p * (2 * Q) + (n - 1 + 2 * r) := by omega
    have e3 : n + k - 1 = p * Q + (n - 1 + r) := by omega
    rw [h0, e1, e2, e3, Nat.mul_add_div hp0, Nat.mul_add_div hp0]
    by_cases hc : n - 1 + r < p
    · rw [Nat.div_eq_of_lt hc]
      generalize (n - 1 + 2 * r) / p = D
      omega
    · push Not at hc
      have hd1 : (n - 1 + r) / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      have hs : ¬ (n - 1 < 2 * (p - r)) := by
        intro hlt
        have hdiv : p ∣ k + (p - r) := ⟨Q + 1, by rw [mul_add, mul_one]; omega⟩
        have := hsmooth (p - r) hlt (by omega) p hp hdiv
        omega
      have hd2 : 2 ≤ (n - 1 + 2 * r) / p := (Nat.le_div_iff_mul_le hp0).mpr (by omega)
      rw [hd1]
      generalize (n - 1 + 2 * r) / p = D at hd2 ⊢
      omega

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos389_erdos_389_R1.H2 :=
  OMA.Helpers.e389_main
