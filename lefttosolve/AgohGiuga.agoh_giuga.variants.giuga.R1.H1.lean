import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R1

/-!
# Step H1 of the reduction AgohGiuga.agoh_giuga.variants.giuga.R1

Every strong Giuga number is a Carmichael number (Giuga 1950).

For a prime p dividing n = p k, reduce the Giuga congruence modulo p.  The sum of i ^ (n - 1)
over 0 < i < n is k times the power sum over the residues modulo p, which is -1 if
p - 1 divides n - 1 and 0 otherwise.  The second case gives 1 = 0 modulo p, so p - 1 divides
n - 1, and then k = 1 modulo p, so p does not divide k.  Hence n is squarefree, and Fermat's
little theorem gives b ^ (n - 1) = 1 modulo each prime factor of n for b coprime to n.
-/

namespace OMA.Helpers

open Finset

theorem sum_range_zmod (p : ℕ) [NeZero p] (f : ZMod p → ZMod p) :
    ∑ i ∈ range p, f (i : ZMod p) = ∑ x : ZMod p, f x := by
  refine Finset.sum_nbij' (fun i => (i : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intro i _
    exact mem_univ _
  · intro x _
    exact mem_range.mpr (ZMod.val_lt x)
  · intro i hi
    exact ZMod.val_cast_of_lt (mem_range.mp hi)
  · intro x _
    exact ZMod.natCast_zmod_val x
  · intro i _
    rfl

theorem sum_pow_zmod (p : ℕ) [Fact p.Prime] (e : ℕ) (he : 1 ≤ e) :
    ∑ x : ZMod p, x ^ e = if p - 1 ∣ e then -1 else 0 := by
  classical
  have h0 : ∑ x : ZMod p, x ^ e = ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ e) := by
    let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ x, Units.val_injective⟩
    have hmap : univ.map φ = univ \ {0} := by
      ext x
      simp only [mem_map, mem_univ, true_and, mem_sdiff, mem_singleton, φ,
        Function.Embedding.coeFn_mk]
      exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
    rw [← sum_sdiff ({0} : Finset (ZMod p)).subset_univ, sum_singleton,
      zero_pow (by omega), add_zero, ← hmap, sum_map]
    rfl
  rw [h0, FiniteField.sum_pow_units, ZMod.card]

theorem sum_range_mul (p k e : ℕ) :
    ∑ i ∈ range (p * k), ((i : ℕ) : ZMod p) ^ e =
      (k : ZMod p) * ∑ i ∈ range p, ((i : ℕ) : ZMod p) ^ e := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    have h : ∀ x : ℕ, (((p * k + x : ℕ)) : ZMod p) = (x : ZMod p) := by
      intro x
      push_cast
      simp
    simp only [h]
    push_cast
    ring

theorem key (n : ℕ) (hn : 1 < n) (hdiv : n ∣ 1 + ∑ i ∈ Ioo 0 n, i ^ (n - 1)) (p : ℕ)
    (hp : p.Prime) (hpn : p ∣ n) : (p - 1) ∣ (n - 1) ∧ ¬ p * p ∣ n := by
  have := Fact.mk hp
  obtain ⟨k, rfl⟩ := hpn
  have h1 : ((1 + ∑ i ∈ Ioo 0 (p * k), i ^ (p * k - 1) : ℕ) : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact (dvd_mul_right p k).trans hdiv
  have he : 1 ≤ p * k - 1 := by omega
  have h2 : ∑ i ∈ Ioo 0 (p * k), ((i : ℕ) : ZMod p) ^ (p * k - 1) =
      ∑ i ∈ range (p * k), ((i : ℕ) : ZMod p) ^ (p * k - 1) := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (show 0 < p * k by omega),
      Finset.Ico_add_one_left_eq_Ioo]
    simp [zero_pow (show p * k - 1 ≠ 0 by omega)]
  push_cast at h1
  rw [h2, sum_range_mul, sum_range_zmod p (fun x => x ^ (p * k - 1)),
    sum_pow_zmod p _ he] at h1
  by_cases hd : p - 1 ∣ p * k - 1
  · rw [if_pos hd] at h1
    have hk1 : (k : ZMod p) = 1 := by linear_combination -h1
    refine ⟨hd, fun hpp => ?_⟩
    have hpk : p ∣ k := Nat.dvd_of_mul_dvd_mul_left hp.pos hpp
    rw [← ZMod.natCast_eq_zero_iff, hk1] at hpk
    exact one_ne_zero hpk
  · rw [if_neg hd, mul_zero, add_zero] at h1
    exact absurd h1 one_ne_zero

end OMA.Helpers

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1.H1 := by
  intro n hn
  obtain ⟨⟨hn1, hnp⟩, hdiv⟩ := hn
  have hkey := fun p hp hpn => OMA.Helpers.key n hn1 hdiv p hp hpn
  have hsq : Squarefree n := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro x hx hxx
    exact (hkey x hx ((dvd_mul_right x x).trans hxx)).2 hxx
  intro b hb hcop
  refine ⟨?_, hnp, hn1⟩
  unfold Nat.ProbablePrime
  rw [← Nat.prod_primeFactors_of_squarefree hsq]
  apply Finset.prod_primes_dvd
  · intro a ha
    exact (Nat.prime_of_mem_primeFactors ha).prime
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpn := Nat.dvd_of_mem_primeFactors hp
    have := Fact.mk hpp
    obtain ⟨c, hc⟩ := (hkey p hpp hpn).1
    have hb1 : 1 ≤ b ^ (n - 1) := Nat.one_le_pow _ _ hb
    rw [Nat.prod_primeFactors_of_squarefree hsq]
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hb1, sub_eq_zero]
    push_cast
    have hbp : (b : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      exact hpp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hpn h)
    rw [hc, pow_mul, ZMod.pow_card_sub_one_eq_one hbp, one_pow]
