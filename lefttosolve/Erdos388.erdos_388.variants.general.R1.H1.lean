import OMAReductions.R_Erdos388_erdos_388_variants_general_R1

/-!
# Step H1 of the reduction Erdos388.erdos_388.variants.general.R1

Small case: when the right start is below `a`, every left factor is below `a`, so the left side
is at most `a * a ^ a`, while the right side is at least its last factor, which is at least `k₂`.

Far case: a prime factor of the right block that exceeds `m₂` cannot divide `a` (as `a ≤ m₂`),
nor any left factor (all at most `m₂`). Bertrand's postulate then gives `k₂ < m₂`, since otherwise
the right block would contain a prime in `(m₂, 2 m₂]`.
-/

namespace OMA.Helpers

open Finset

theorem erdos388_le_prod (m k : ℕ) (hk : 0 < k) : k ≤ ∏ j ∈ Icc 1 k, (m + j) := by
  have hmem : k ∈ Icc 1 k := Finset.mem_Icc.mpr ⟨hk, le_rfl⟩
  have hdvd : (m + k) ∣ ∏ j ∈ Icc 1 k, (m + j) := Finset.dvd_prod_of_mem (fun j => m + j) hmem
  have hpos : 0 < ∏ j ∈ Icc 1 k, (m + j) := by
    apply Finset.prod_pos
    intro j hj
    have := (Finset.mem_Icc.mp hj).1
    omega
  exact (Nat.le_add_left k m).trans (Nat.le_of_dvd hpos hdvd)

theorem erdos388_prod_le (m k a : ℕ) (h : ∀ i ∈ Icc 1 k, m + i ≤ a) :
    ∏ i ∈ Icc 1 k, (m + i) ≤ a ^ k := by
  calc ∏ i ∈ Icc 1 k, (m + i) ≤ ∏ _i ∈ Icc 1 k, a :=
        Finset.prod_le_prod (fun i _ => Nat.zero_le _) h
    _ = a ^ k := by rw [Finset.prod_const, Nat.card_Icc]; congr 1

end OMA.Helpers

open Finset in
theorem OMA.solution : OMA.R_Erdos388_erdos_388_variants_general_R1.H1 := by
  intro a b m₁ k₁ m₂ k₂ ha hb hk₁ hk₂ hOrd hEq
  refine ⟨fun hlt => ?_, fun hle => ?_⟩
  · have h1 : k₂ ≤ ∏ j ∈ Icc 1 k₂, (m₂ + j) := OMA.Helpers.erdos388_le_prod m₂ k₂ (by omega)
    have h2 : ∏ j ∈ Icc 1 k₂, (m₂ + j) ≤ b * ∏ j ∈ Icc 1 k₂, (m₂ + j) :=
      Nat.le_mul_of_pos_left _ hb
    have h3 : ∏ i ∈ Icc 1 k₁, (m₁ + i) ≤ a ^ k₁ := by
      apply OMA.Helpers.erdos388_prod_le
      intro i hi
      have := (Finset.mem_Icc.mp hi).2
      omega
    have h4 : a ^ k₁ ≤ a ^ a := Nat.pow_le_pow_right ha (by omega)
    have h5 : a * ∏ i ∈ Icc 1 k₁, (m₁ + i) ≤ a * a ^ a :=
      Nat.mul_le_mul_left a (h3.trans h4)
    omega
  · have hfac : ∀ p ∈ (∏ j ∈ Icc 1 k₂, (m₂ + j)).primeFactors, p ≤ m₂ := by
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      obtain ⟨hpp, hpd, _⟩ := hp
      by_contra hlt
      push_neg at hlt
      have hdvd : p ∣ a * ∏ i ∈ Icc 1 k₁, (m₁ + i) := by
        rw [hEq]
        exact Dvd.dvd.mul_left hpd b
      rcases (Nat.Prime.dvd_mul hpp).mp hdvd with h | h
      · have := Nat.le_of_dvd ha h
        omega
      · obtain ⟨i, hi, hdi⟩ := (Prime.dvd_finsetProd_iff hpp.prime (fun i => m₁ + i)).mp h
        have hi' := Finset.mem_Icc.mp hi
        have := Nat.le_of_dvd (by omega) hdi
        omega
    refine ⟨?_, hfac⟩
    by_contra hge
    push_neg at hge
    obtain ⟨p, hpp, hlt, hle2⟩ := Nat.exists_prime_lt_and_le_two_mul m₂ (by omega)
    have hmem : p - m₂ ∈ Icc 1 k₂ := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hdvd : (m₂ + (p - m₂)) ∣ ∏ j ∈ Icc 1 k₂, (m₂ + j) :=
      Finset.dvd_prod_of_mem (fun j => m₂ + j) hmem
    have hpos : 0 < ∏ j ∈ Icc 1 k₂, (m₂ + j) := by
      apply Finset.prod_pos
      intro j hj
      have := (Finset.mem_Icc.mp hj).1
      omega
    have hp : p ∈ (∏ j ∈ Icc 1 k₂, (m₂ + j)).primeFactors := by
      rw [Nat.mem_primeFactors]
      refine ⟨hpp, ?_, by omega⟩
      have : m₂ + (p - m₂) = p := by omega
      rwa [this] at hdvd
    have := hfac p hp
    omega
