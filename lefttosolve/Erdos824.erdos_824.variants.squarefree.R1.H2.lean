import OMAReductions.R_Erdos824_erdos_824_variants_squarefree_R1

/-!
# Step H2 of the reduction Erdos824.erdos_824.variants.squarefree.R1

Let `T` be a `k`-element subset of `P`. The number `m = ∏ p ∈ T, (p + 1)` satisfies
`1 ≤ m ≤ (Y + 1) ^ k ≤ x`, and each prime factor of `m` divides some `p + 1`, so it is at most `s`.

Such an `m` equals `∏ i < s + 1, i ^ e i` where `e i` is the exponent of `i` in `m`, and every
exponent is at most `log₂ x` because `2 ^ e ≤ q ^ e ≤ m ≤ x` for a prime `q`. Hence every value is
in the image of the map `e ↦ ∏ i, i ^ e i` on functions `Fin (s + 1) → Fin (log₂ x + 1)`, a type
with `(log₂ x + 1) ^ (s + 1)` elements.
-/

namespace OMA.Helpers

/-- Every exponent in the factorization of a nonzero `m ≤ x` is at most `log₂ x`. -/
theorem erdos824_factorization_le_log {m x : ℕ} (hm : m ≠ 0) (hmx : m ≤ x) (q : ℕ) :
    m.factorization q ≤ Nat.log 2 x := by
  by_cases hq : q.Prime
  · apply Nat.le_log_of_pow_le (by norm_num)
    calc 2 ^ m.factorization q ≤ q ^ m.factorization q := Nat.pow_le_pow_left hq.two_le _
      _ ≤ m := Nat.ordProj_le q hm
      _ ≤ x := hmx
  · rw [Nat.factorization_eq_zero_of_not_prime m hq]
    exact Nat.zero_le _

/-- A nonzero `m` whose prime factors are all at most `s` is the product of `i ^ e i` over
`i < s + 1`, where `e i` is the exponent of `i` in `m`. -/
theorem erdos824_prod_fin_pow {m s : ℕ} (hm : m ≠ 0) (hs : ∀ q ∈ m.primeFactors, q ≤ s) :
    ∏ i : Fin (s + 1), (i : ℕ) ^ m.factorization i = m := by
  rw [Fin.prod_univ_eq_prod_range (fun i => i ^ m.factorization i) (s + 1)]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hm]
  rw [Finsupp.prod, Nat.support_factorization]
  symm
  apply Finset.prod_subset
  · intro q hq
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (hs q hq)
  · intro q _ hq
    rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hq
    rw [hq, pow_zero]

/-- A finite set of nonzero numbers at most `x`, all of whose prime factors are at most `s`,
has at most `(log₂ x + 1) ^ (s + 1)` elements. -/
theorem erdos824_card_smooth_le (S : Finset ℕ) (x s : ℕ)
    (hS : ∀ m ∈ S, m ≠ 0 ∧ m ≤ x ∧ ∀ q ∈ m.primeFactors, q ≤ s) :
    S.card ≤ (Nat.log 2 x + 1) ^ (s + 1) := by
  classical
  let g : (Fin (s + 1) → Fin (Nat.log 2 x + 1)) → ℕ :=
    fun e => ∏ i : Fin (s + 1), (i : ℕ) ^ (e i : ℕ)
  have hsub : S ⊆ Finset.univ.image g := by
    intro m hm
    obtain ⟨hm0, hmx, hms⟩ := hS m hm
    rw [Finset.mem_image]
    exact ⟨fun i => ⟨m.factorization i, Nat.lt_succ_of_le (erdos824_factorization_le_log hm0 hmx i)⟩,
      Finset.mem_univ _, erdos824_prod_fin_pow hm0 hms⟩
  calc S.card ≤ (Finset.univ.image g).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin (s + 1) → Fin (Nat.log 2 x + 1))).card := Finset.card_image_le
    _ = (Nat.log 2 x + 1) ^ (s + 1) := by simp

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos824_erdos_824_variants_squarefree_R1.H2 := by
  intro P Y s k x hY hs hx
  classical
  apply OMA.Helpers.erdos824_card_smooth_le
  intro m hm
  rw [Finset.mem_image] at hm
  obtain ⟨T, hT, rfl⟩ := hm
  rw [Finset.mem_powersetCard] at hT
  obtain ⟨hTP, hTk⟩ := hT
  refine ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => Nat.succ_ne_zero p), ?_, ?_⟩
  · calc ∏ p ∈ T, (p + 1) ≤ (Y + 1) ^ T.card :=
          Finset.prod_le_pow_card T _ _ (fun p hp => Nat.succ_le_succ (hY p (hTP hp)))
      _ = (Y + 1) ^ k := by rw [hTk]
      _ ≤ x := hx
  · intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    obtain ⟨p, hpT, hqp1⟩ :=
      (Prime.dvd_finsetProd_iff hqp.prime (fun p => p + 1)).mp (Nat.dvd_of_mem_primeFactors hq)
    exact hs p (hTP hpT) q (Nat.mem_primeFactors.mpr ⟨hqp, hqp1, Nat.succ_ne_zero p⟩)
