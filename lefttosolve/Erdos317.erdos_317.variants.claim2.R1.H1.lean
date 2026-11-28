import OMAReductions.R_Erdos317_erdos_317_variants_claim2_R1

/-!
# Step H1 of the reduction Erdos317.erdos_317.variants.claim2.R1

For every positive n, let u be the least prime power above n. No integer in the range from n + 1
to u - 1 is a prime power, and appending a non prime power m + 1 to the range 1..m does not change
the least common multiple: m + 1 splits as a product of two coprime factors, both at most m.
-/

open Finset

namespace OMA.Helpers

theorem dvd_lcm_of_not_primePow (m : ℕ) (hm : 1 ≤ m) (hpp : ¬ IsPrimePow (m + 1)) :
    m + 1 ∣ (Icc 1 m).lcm id := by
  set N := m + 1 with hN
  have hN0 : N ≠ 0 := by omega
  have hN1 : N ≠ 1 := by omega
  set p := N.minFac with hp
  have hpp' : p.Prime := Nat.minFac_prime hN1
  have hpd : p ∣ N := Nat.minFac_dvd N
  set a := p ^ N.factorization p with ha
  set b := N / a with hb
  have hab : a * b = N := Nat.ordProj_mul_ordCompl_eq_self N p
  have hcop : Nat.Coprime a b := (Nat.coprime_ordCompl hpp' hN0).pow_left _
  have he : 1 ≤ N.factorization p := (hpp'.dvd_iff_one_le_factorization hN0).1 hpd
  have ha2 : 2 ≤ a := by
    calc 2 ≤ p := hpp'.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ a := Nat.pow_le_pow_right hpp'.pos he
  have hb1 : b ≠ 1 := by
    intro h
    apply hpp
    rw [h, mul_one] at hab
    rw [← hab]
    exact ⟨p, N.factorization p, hpp'.prime, he, rfl⟩
  clear_value a b p
  have hb0 : b ≠ 0 := by
    rintro rfl
    omega
  have hb2 : 2 ≤ b := by omega
  have haN : a < N := by nlinarith
  have hbN : b < N := by nlinarith
  have hamem : a ∈ Icc 1 m := mem_Icc.2 ⟨by omega, by omega⟩
  have hbmem : b ∈ Icc 1 m := mem_Icc.2 ⟨by omega, by omega⟩
  rw [← hab]
  exact hcop.mul_dvd_of_dvd_of_dvd (Finset.dvd_lcm (f := id) hamem)
    (Finset.dvd_lcm (f := id) hbmem)

theorem lcm_succ_of_not_primePow (m : ℕ) (hm : 1 ≤ m) (hpp : ¬ IsPrimePow (m + 1)) :
    (Icc 1 (m + 1)).lcm id = (Icc 1 m).lcm id := by
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.lcm_insert]
  exact lcm_eq_right_iff _ _ (by simp) |>.2 (dvd_lcm_of_not_primePow m hm hpp)

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos317_erdos_317_variants_claim2_R1.H1 := by
  classical
  intro n hn
  have hex : ∃ u, n < u ∧ IsPrimePow u := by
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (n + 1)
    exact ⟨p, by omega, hp2.isPrimePow⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  have key : ∀ j, n + j < Nat.find hex → (Icc 1 n).lcm id = (Icc 1 (n + j)).lcm id := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have hnot : ¬ IsPrimePow (n + j + 1) := fun h =>
        Nat.find_min hex (show n + j + 1 < Nat.find hex by omega) ⟨by omega, h⟩
      rw [ih (by omega), ← add_assoc, OMA.Helpers.lcm_succ_of_not_primePow (n + j) (by omega) hnot]
  have h := key (Nat.find hex - 1 - n) (by have := (Nat.find_spec hex).1; omega)
  have h2 : n + (Nat.find hex - 1 - n) = Nat.find hex - 1 := by
    have := (Nat.find_spec hex).1; omega
  rw [h2] at h
  exact h
