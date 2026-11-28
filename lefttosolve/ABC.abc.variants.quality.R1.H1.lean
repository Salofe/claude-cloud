import OMAReductions.R_ABC_abc_variants_quality_R1

namespace OMA.Helpers

theorem rad_ge_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    ABC.radical m ≤ ABC.radical n := by
  unfold ABC.radical
  exact Finset.prod_le_prod_of_subset_of_one_le' (Nat.primeFactors_mono hmn hn)
    (fun p hp _ => (Nat.prime_of_mem_primeFactors hp).one_lt.le)

theorem rad_ge_two {c : ℕ} (hc : 2 ≤ c) : 2 ≤ ABC.radical c := by
  unfold ABC.radical
  have hmem : c.minFac ∈ c.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd c, by omega⟩
  have h1 : c.minFac ≤ ∏ p ∈ c.primeFactors, id p :=
    Finset.single_le_prod' (f := id)
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).one_lt.le) hmem
  have h2 : 2 ≤ c.minFac := (Nat.minFac_prime (by omega)).two_le
  exact le_trans h2 h1

theorem rad_of_squarefree {n : ℕ} (hn : Squarefree n) : ABC.radical n = n := by
  unfold ABC.radical
  simpa using Nat.prod_primeFactors_of_squarefree hn

theorem rad_mul_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    ABC.radical (m * n) = ABC.radical m * ABC.radical n := by
  unfold ABC.radical
  rw [h.primeFactors_mul, Finset.prod_union h.disjoint_primeFactors]

end OMA.Helpers

theorem OMA.solution : OMA.R_ABC_abc_variants_quality_R1.H1 := by
  intro a b c ha hb hcop hsum
  have hc2 : 2 ≤ c := by omega
  have hac : a ≠ c := by omega
  have hbc : b ≠ c := by omega
  have hcopac : Nat.Coprime a c :=
    hcop (by simp) (by simp) hac
  have hcopbc : Nat.Coprime b c :=
    hcop (by simp) (by simp) hbc
  have hcopab_c : Nat.Coprime (a * b) c := Nat.Coprime.mul hcopac hcopbc
  have habc0 : a * b * c ≠ 0 := by positivity
  have hradc : ABC.radical c ≤ ABC.radical (a * b * c) :=
    OMA.Helpers.rad_ge_of_dvd (Dvd.intro_left (a * b) rfl) habc0
  have hrc2 : 2 ≤ ABC.radical c := OMA.Helpers.rad_ge_two hc2
  refine ⟨by omega, ?_⟩
  rintro (hsq | hsq)
  · rw [OMA.Helpers.rad_of_squarefree hsq] at hradc
    exact hradc
  · rw [OMA.Helpers.rad_mul_coprime hcopab_c, OMA.Helpers.rad_of_squarefree hsq]
    have hab : c ≤ 2 * (a * b) := by
      have : (a - 1) * (b - 1) + a + b ≤ 2 * (a * b) + 1 := by
        rcases Nat.exists_eq_add_of_lt ha with ⟨a', rfl⟩
        rcases Nat.exists_eq_add_of_lt hb with ⟨b', rfl⟩
        simp only [zero_add, Nat.add_sub_cancel]
        nlinarith
      nlinarith [Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp ha),
        Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hb), Nat.mul_le_mul ha hb]
    calc c ≤ 2 * (a * b) := hab
      _ ≤ a * b * ABC.radical c := by rw [mul_comm 2]; exact Nat.mul_le_mul_left _ hrc2
