import OMAReductions.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1

/-!
# Step H2 of the reduction Erdos307.erdos_307.variants.coprime_one_notMem.R1

Write `D = M N - M' N'`. From `D p = M N' + N ^ 2` and `D q = M' N + M ^ 2` one gets the two
cross relations `p M' + M = N q` and `q N' + N = M p`. A common divisor `g` of `p` and some
`a ∈ P₀` divides `M` and is coprime to `N`; the first relation gives `g ∣ q`, and then the
second gives `g ∣ N`, so `g = 1`. The same argument with the roles exchanged handles `q`.
Coprimality with every member, together with `2 ≤ p`, also shows `p ∉ P₀`.
-/

namespace OMA.Helpers

theorem cross_eq {M M' N N' D p q : ℕ} (hlt : M' * N' < M * N)
    (hD : D = M * N - M' * N') (hp : D * p = M * N' + N ^ 2)
    (hq : D * q = M' * N + M ^ 2) :
    p * M' + M = N * q ∧ q * N' + N = M * p := by
  have hDz : (D : ℤ) = (M : ℤ) * N - (M' : ℤ) * N' := by
    rw [hD, Nat.cast_sub hlt.le]; push_cast; ring
  have hpz : (D : ℤ) * p = (M : ℤ) * N' + (N : ℤ) ^ 2 := by exact_mod_cast hp
  have hqz : (D : ℤ) * q = (M' : ℤ) * N + (M : ℤ) ^ 2 := by exact_mod_cast hq
  have hD0 : (D : ℤ) ≠ 0 := by
    have : 0 < D := by omega
    exact_mod_cast this.ne'
  constructor
  · have h : (D : ℤ) * ((p : ℤ) * M' + M) = (D : ℤ) * ((N : ℤ) * q) := by
      linear_combination (M' : ℤ) * hpz - (N : ℤ) * hqz + (M : ℤ) * hDz
    exact_mod_cast mul_left_cancel₀ hD0 h
  · have h : (D : ℤ) * ((q : ℤ) * N' + N) = (D : ℤ) * ((M : ℤ) * p) := by
      linear_combination (N' : ℤ) * hqz - (M : ℤ) * hpz + (N : ℤ) * hDz
    exact_mod_cast mul_left_cancel₀ hD0 h

/-- If `g` divides `M` and `p` and is coprime to `N`, the cross relations force `g = 1`. -/
theorem gcd_trap {M M' N N' p q g : ℕ} (c1 : p * M' + M = N * q) (c2 : q * N' + N = M * p)
    (hgM : g ∣ M) (hgN : Nat.Coprime g N) (hgp : g ∣ p) : g = 1 := by
  have h1 : g ∣ N * q := by
    rw [← c1]; exact dvd_add (dvd_mul_of_dvd_left hgp _) hgM
  have hgq : g ∣ q := hgN.dvd_of_dvd_mul_left h1
  have h2 : g ∣ q * N' + N := by
    rw [c2]; exact dvd_mul_of_dvd_right hgp _
  have hgN' : g ∣ N := (Nat.dvd_add_right (dvd_mul_of_dvd_left hgq _)).mp h2
  exact hgN.eq_one_of_dvd hgN'

theorem insert_pairwise {S : Finset ℕ} {p : ℕ} (hS : Set.Pairwise (S : Set ℕ) Nat.Coprime)
    (hp : ∀ a ∈ S, Nat.Coprime p a) :
    Set.Pairwise ((insert p S : Finset ℕ) : Set ℕ) Nat.Coprime := by
  rw [Finset.coe_insert, Set.pairwise_insert]
  exact ⟨hS, fun b hb _ => ⟨hp b hb, (hp b hb).symm⟩⟩

theorem not_mem_of_coprime {S : Finset ℕ} {p : ℕ} (h2 : 2 ≤ p)
    (hp : ∀ a ∈ S, Nat.Coprime p a) : p ∉ S := by
  intro hmem
  have := (Nat.coprime_self p).mp (hp p hmem)
  omega

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.H2 := by
  intro P₀ Q₀ _ _ _ _ hPc hQc hPQ M M' N N' hlt h2p h2q hdp hdq p q
  have hp : (M * N - M' * N') * p = M * N' + N ^ 2 := Nat.mul_div_cancel' hdp
  have hq : (M * N - M' * N') * q = M' * N + M ^ 2 := Nat.mul_div_cancel' hdq
  obtain ⟨c1, c2⟩ := cross_eq hlt rfl hp hq
  have hDpos : 0 < M * N - M' * N' := by omega
  have hp2 : 2 ≤ p := by
    refine Nat.le_of_mul_le_mul_left ?_ hDpos
    rw [hp]; linarith
  have hq2 : 2 ≤ q := by
    refine Nat.le_of_mul_le_mul_left ?_ hDpos
    rw [hq]; linarith
  have hpcop : ∀ a ∈ P₀, Nat.Coprime p a := by
    intro a ha
    have haN : Nat.Coprime a N := Nat.Coprime.prod_right fun b hb => hPQ a ha b hb
    exact gcd_trap c1 c2 ((Nat.gcd_dvd_right p a).trans (Finset.dvd_prod_of_mem _ ha))
      (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right p a) haN) (Nat.gcd_dvd_left p a)
  have hqcop : ∀ b ∈ Q₀, Nat.Coprime q b := by
    intro b hb
    have hbM : Nat.Coprime b M := Nat.Coprime.prod_right fun a ha => (hPQ a ha b hb).symm
    exact gcd_trap c2 c1 ((Nat.gcd_dvd_right q b).trans (Finset.dvd_prod_of_mem _ hb))
      (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right q b) hbM) (Nat.gcd_dvd_left q b)
  exact ⟨hp2, not_mem_of_coprime hp2 hpcop, hq2, not_mem_of_coprime hq2 hqcop,
    insert_pairwise hPc hpcop, insert_pairwise hQc hqcop⟩
