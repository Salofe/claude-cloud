import OMAReductions.R_Erdos821_erdos_821_variants_lichtman_R1
import Mathlib

/-!
# Step H2 of the reduction Erdos821.erdos_821.variants.lichtman.R1

Products of k distinct primes from P are pairwise distinct and at most X^k. Their totients
are products of the numbers p - 1, hence positive, at most X^k, and with every prime factor
at most B. Such a number is determined by its exponents at 1, ..., B, each at most
log_2 (X^k), so there are at most (log_2 (X^k) + 1)^B possible totient values. By the
pigeonhole principle some value n is hit more than z times, and every product hitting it
lies in the (finite) totient fibre of n.

Only the upstream definition `Erdos821.g` is used.
-/

namespace OMA.Helpers

open Finset

/-- The totient of a product of distinct primes. -/
theorem erdos821_totient_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Nat.totient (∏ p ∈ s, p) = ∏ p ∈ s, (p - 1) := by
  have h := Nat.totient_mul_prod_primeFactors (∏ p ∈ s, p)
  rw [Nat.primeFactors_prod hs] at h
  have hpos : 0 < ∏ p ∈ s, p := Finset.prod_pos fun p hp => (hs p hp).pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h.trans (Nat.mul_comm _ _))

/-- Totient fibres of positive numbers are finite. -/
theorem erdos821_totient_fiber_finite (y : ℕ) (hy : 0 < y) :
    {m : ℕ | Nat.totient m = y}.Finite := by
  apply (Set.finite_Iic (y * ∏ p ∈ Finset.Icc 1 (y + 1), p)).subset
  intro m hm
  simp only [Set.mem_setOf_eq] at hm
  simp only [Set.mem_Iic]
  have hsub : m.primeFactors ⊆ Finset.Icc 1 (y + 1) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    have h1 := Nat.totient_dvd_of_dvd hd
    rw [Nat.totient_prime hpp, hm] at h1
    have h2 := Nat.le_of_dvd hy h1
    have h3 := hpp.two_le
    simp only [Finset.mem_Icc]
    omega
  have h := Nat.totient_mul_prod_primeFactors m
  rw [hm] at h
  have hA : 0 < ∏ p ∈ m.primeFactors, (p - 1) := Finset.prod_pos fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hB : ∏ p ∈ m.primeFactors, p ≤ ∏ p ∈ Finset.Icc 1 (y + 1), p := by
    apply Nat.le_of_dvd
    · exact Finset.prod_pos fun p hp => by simp only [Finset.mem_Icc] at hp; omega
    · exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
  calc m ≤ m * ∏ p ∈ m.primeFactors, (p - 1) := Nat.le_mul_of_pos_right m hA
    _ = y * ∏ p ∈ m.primeFactors, p := h.symm
    _ ≤ y * ∏ p ∈ Finset.Icc 1 (y + 1), p := Nat.mul_le_mul_left y hB

/-- Exponents in the factorization of a positive number at most `N` are at most `log_2 N`. -/
theorem erdos821_factorization_le_log {n N : ℕ} (hn : n ≠ 0) (hN : n ≤ N) (p : ℕ) :
    n.factorization p ≤ Nat.log 2 N := by
  by_cases hp : p.Prime
  · apply Nat.le_log_of_pow_le (by norm_num)
    have h1 : p ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
    have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h1
    have h3 : 2 ^ n.factorization p ≤ p ^ n.factorization p :=
      Nat.pow_le_pow_left hp.two_le _
    omega
  · rw [Nat.factorization_eq_zero_of_not_prime n hp]
    exact Nat.zero_le _

/-- Counting `B`-smooth numbers in `[1, N]`. -/
theorem erdos821_card_smooth (N B : ℕ)
    [DecidablePred (fun n : ℕ => ∀ q : ℕ, q.Prime → q ∣ n → q ≤ B)] :
    ((Finset.Icc 1 N).filter (fun n => ∀ q : ℕ, q.Prime → q ∣ n → q ≤ B)).card ≤
      (Nat.log 2 N + 1) ^ B := by
  set T := (Finset.Icc 1 N).filter (fun n => ∀ q : ℕ, q.Prime → q ∣ n → q ≤ B) with hT
  let F : ℕ → (Fin B → ℕ) := fun n i => n.factorization (i.val + 1)
  have hmaps : Set.MapsTo F (T : Set ℕ)
      (Fintype.piFinset (fun _ : Fin B => Finset.range (Nat.log 2 N + 1)) : Set (Fin B → ℕ)) := by
    intro n hn
    rw [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    have := erdos821_factorization_le_log (n := n) (N := N) (by omega) hn.1.2 (i.val + 1)
    simp only [F]
    omega
  have hinj : Set.InjOn F (T : Set ℕ) := by
    intro n hn m hm hnm
    rw [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_Icc] at hn hm
    apply Nat.eq_of_factorization_eq (by omega) (by omega)
    intro p
    by_cases hpB : 1 ≤ p ∧ p ≤ B
    · have := congrFun hnm ⟨p - 1, by omega⟩
      simp only [F] at this
      rwa [Nat.sub_add_cancel hpB.1] at this
    · have zero : ∀ k : ℕ, (∀ q : ℕ, q.Prime → q ∣ k → q ≤ B) → k.factorization p = 0 := by
        intro k hk
        by_cases hp : p.Prime
        · apply Nat.factorization_eq_zero_of_not_dvd
          intro hd
          have := hk p hp hd
          have := hp.two_le
          omega
        · exact Nat.factorization_eq_zero_of_not_prime k hp
      rw [zero n hn.2, zero m hm.2]
  have h := Finset.card_le_card_of_injOn F hmaps hinj
  rw [Fintype.card_piFinset] at h
  simpa using h

end OMA.Helpers

open Finset in
theorem OMA.solution : OMA.R_Erdos821_erdos_821_variants_lichtman_R1.H2 := by
  classical
  intro P X B k z hprime hX hsmooth hz hbig
  set T := (Finset.Icc 1 (X ^ k)).filter (fun n => ∀ q : ℕ, q.Prime → q ∣ n → q ≤ B) with hT
  let S := P.powersetCard k
  let f : Finset ℕ → ℕ := fun s => ∏ p ∈ s, (p - 1)
  have hmaps : ∀ s ∈ S, f s ∈ T := by
    intro s hs
    obtain ⟨hsP, hsk⟩ := Finset.mem_powersetCard.mp hs
    have hpos : 0 < f s := Finset.prod_pos fun p hp => by
      have := (hprime p (hsP hp)).two_le
      omega
    have hle : f s ≤ X ^ k := by
      calc f s ≤ ∏ _p ∈ s, X := Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
              (fun p hp => (Nat.sub_le p 1).trans (hX p (hsP hp)))
        _ = X ^ k := by rw [Finset.prod_const, hsk]
    rw [hT, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hpos, hle⟩, ?_⟩
    intro q hq hqd
    obtain ⟨p, hp, hqp⟩ := (Nat.Prime.prime hq).dvd_finsetProd_iff _ |>.mp hqd
    exact hsmooth p (hsP hp) q hq hqp
  have hcardT := OMA.Helpers.erdos821_card_smooth (X ^ k) B
  rw [← hT] at hcardT
  have hlt : T.card • z < (S.card : ℝ) := by
    rw [Finset.card_powersetCard, nsmul_eq_mul]
    refine lt_of_le_of_lt ?_ hbig
    apply mul_le_mul_of_nonneg_right _ hz
    exact_mod_cast hcardT
  obtain ⟨y, hyT, hy⟩ := Finset.exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to hmaps hlt
  have hyI := (Finset.mem_filter.mp hyT).1
  rw [Finset.mem_Icc] at hyI
  refine ⟨y, hyI.1, hyI.2, lt_of_lt_of_le hy ?_⟩
  -- the fibre injects into the totient fibre of y
  set Fib := S.filter (fun x => f x = y) with hFib
  have hinj : Set.InjOn (fun s : Finset ℕ => ∏ p ∈ s, p) (Fib : Set (Finset ℕ)) := by
    intro s hs t ht hst
    have hs' := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hs).1).1
    have ht' := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp ht).1).1
    have e1 := Nat.primeFactors_prod (s := s) fun p hp => hprime p (hs' hp)
    have e2 := Nat.primeFactors_prod (s := t) fun p hp => hprime p (ht' hp)
    simp only at hst
    rw [← e1, ← e2, hst]
  have hcard : (Fib.image (fun s : Finset ℕ => ∏ p ∈ s, p)).card = Fib.card :=
    Finset.card_image_of_injOn hinj
  have hsubset : ((Fib.image (fun s : Finset ℕ => ∏ p ∈ s, p) : Finset ℕ) : Set ℕ) ⊆
      {m : ℕ | Nat.totient m = y} := by
    intro m hm
    rw [Finset.coe_image] at hm
    obtain ⟨s, hs, rfl⟩ := hm
    have hs1 := Finset.mem_filter.mp hs
    have hs' := (Finset.mem_powersetCard.mp hs1.1).1
    simp only [Set.mem_setOf_eq]
    rw [OMA.Helpers.erdos821_totient_prod_primes s fun p hp => hprime p (hs' hp)]
    exact hs1.2
  have hfin := OMA.Helpers.erdos821_totient_fiber_finite y hyI.1
  have hle := Set.ncard_le_ncard hsubset hfin
  rw [Set.ncard_coe_finset, hcard] at hle
  unfold Erdos821.g
  exact_mod_cast hle
