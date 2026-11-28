import OMAReductions.R_Erdos535_erdos_535_R1

/-!
# Step H2 of the reduction Erdos535.erdos_535.R1

Write each `a ∈ A` as `a = sm a * rf a`, where `sm a` collects the prime powers of `a` with
prime below `y` and `rf a` the others. Every prime factor of `rf a` is at least `y`, so
`y ^ Ω (rf a) ≤ rf a ≤ N < y ^ (K + 1)` and `Ω (rf a) ≤ K`. Every exponent of `a` is at most
`L` because `a ≤ N < 2 ^ L`. The map `a ↦ ((v_p(a))_{p < y}, Ω (rf a))` lands in a set of
`(L + 1) ^ y * (K + 1)` elements; a largest fiber `F` has `A.card ≤ (L + 1) ^ y * (K + 1) * F.card`.
On `F` the smooth part is a constant `s`, and `B = rf '' F` works, with `rf` injective on `F`.

Only the upstream definition `Erdos535.AllBigOmega` (through the step statement) is used.
-/

namespace OMA.Helpers

open ArithmeticFunction
open scoped ArithmeticFunction.Omega

/-- The part of `a` made of primes below `y`. -/
noncomputable def erdos535_sm (y a : ℕ) : ℕ := (a.factorization.filter (· < y)).prod (· ^ ·)
/-- The part of `a` made of primes at least `y`. -/
noncomputable def erdos535_rf (y a : ℕ) : ℕ := (a.factorization.filter (fun p => ¬ p < y)).prod (· ^ ·)

theorem erdos535_sm_mul_rf (y a : ℕ) (ha : a ≠ 0) : erdos535_sm y a * erdos535_rf y a = a := by
  unfold erdos535_sm erdos535_rf
  rw [Finsupp.prod_filter_mul_prod_filter_not]
  exact Nat.prod_factorization_pow_eq_self ha

theorem erdos535_sm_fact (y a : ℕ) : (erdos535_sm y a).factorization = a.factorization.filter (· < y) := by
  unfold erdos535_sm
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  rw [Finsupp.support_filter, Finset.mem_filter] at hp
  exact Nat.prime_of_mem_primeFactors hp.1

theorem erdos535_rf_fact (y a : ℕ) :
    (erdos535_rf y a).factorization = a.factorization.filter (fun p => ¬ p < y) := by
  unfold erdos535_rf
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  rw [Finsupp.support_filter, Finset.mem_filter] at hp
  exact Nat.prime_of_mem_primeFactors hp.1

theorem erdos535_rf_prime_ge (y a : ℕ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime) (hd : p ∣ erdos535_rf y a) : y ≤ p := by
  have hr : erdos535_rf y a ≠ 0 := by
    intro h0
    have := erdos535_sm_mul_rf y a ha
    rw [h0, mul_zero] at this
    exact ha this.symm
  have hpos := hp.factorization_pos_of_dvd hr hd
  rw [erdos535_rf_fact] at hpos
  by_contra hlt
  rw [Finsupp.filter_apply_neg (fun p => ¬ p < y) _ (not_not.mpr (not_le.mp hlt))] at hpos
  exact lt_irrefl 0 hpos

theorem erdos535_pow_omega_le (y n : ℕ) (hn : n ≠ 0) (h : ∀ p : ℕ, p.Prime → p ∣ n → y ≤ p) :
    y ^ Ω n ≤ n := by
  rw [cardFactors_apply]
  calc y ^ n.primeFactorsList.length ≤ n.primeFactorsList.prod :=
        List.pow_card_le_prod _ _ fun x hx =>
          h x (Nat.prime_of_mem_primeFactorsList hx) (Nat.dvd_of_mem_primeFactorsList hx)
    _ = n := Nat.prod_primeFactorsList hn

theorem erdos535_fact_le (a L : ℕ) (ha : a ≠ 0) (haL : a < 2 ^ L) (p : ℕ) : a.factorization p ≤ L := by
  by_cases h0 : a.factorization p = 0
  · omega
  have hp : p.Prime := Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr h0)
  have hd := Nat.le_of_dvd (Nat.pos_of_ne_zero ha) (Nat.ordProj_dvd a p)
  have h2 : 2 ^ a.factorization p ≤ p ^ a.factorization p := Nat.pow_le_pow_left hp.two_le _
  have : 2 ^ a.factorization p < 2 ^ L := by omega
  exact ((Nat.pow_lt_pow_iff_right (by norm_num)).mp this).le

end OMA.Helpers

open ArithmeticFunction
open scoped ArithmeticFunction.Omega

theorem OMA.solution : OMA.R_Erdos535_erdos_535_R1.H2 := by
  classical
  intro N y L K hy hNL hNK A hA
  have hmemA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ N := fun a ha => Finset.mem_Icc.mp (hA ha)
  let φ : ℕ → (Fin y → ℕ) × ℕ := fun a => (fun i => a.factorization i, Ω (OMA.Helpers.erdos535_rf y a))
  let t : Finset ((Fin y → ℕ) × ℕ) :=
    (Fintype.piFinset fun _ => Finset.range (L + 1)) ×ˢ Finset.range (K + 1)
  have hrf0 : ∀ a ∈ A, OMA.Helpers.erdos535_rf y a ≠ 0 := by
    intro a ha h0
    have := OMA.Helpers.erdos535_sm_mul_rf y a (by have := (hmemA a ha).1; omega)
    rw [h0, mul_zero] at this
    have := (hmemA a ha).1
    omega
  have hsm0 : ∀ a ∈ A, OMA.Helpers.erdos535_sm y a ≠ 0 := by
    intro a ha h0
    have := OMA.Helpers.erdos535_sm_mul_rf y a (by have := (hmemA a ha).1; omega)
    rw [h0, zero_mul] at this
    have := (hmemA a ha).1
    omega
  have hmaps : ∀ a ∈ A, φ a ∈ t := by
    intro a ha
    have ha0 : a ≠ 0 := by have := (hmemA a ha).1; omega
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (OMA.Helpers.erdos535_fact_le a L ha0 (by have := (hmemA a ha).2; omega) i))
    · refine Finset.mem_range.mpr ?_
      have h1 := OMA.Helpers.erdos535_pow_omega_le y (OMA.Helpers.erdos535_rf y a) (hrf0 a ha) (OMA.Helpers.erdos535_rf_prime_ge y a ha0)
      have h2 : OMA.Helpers.erdos535_rf y a ≤ a := Nat.le_of_dvd (by have := (hmemA a ha).1; omega)
        ⟨OMA.Helpers.erdos535_sm y a, by rw [mul_comm]; exact (OMA.Helpers.erdos535_sm_mul_rf y a ha0).symm⟩
      have h3 : y ^ Ω (OMA.Helpers.erdos535_rf y a) < y ^ (K + 1) := by
        have := (hmemA a ha).2
        omega
      exact (Nat.pow_lt_pow_iff_right (by omega)).mp h3
  have htcard : t.card = (L + 1) ^ y * (K + 1) := by
    simp [t, Finset.card_product, Fintype.card_piFinset]
  have htne : t.Nonempty := ⟨(fun _ => 0, 0), by simp [t]⟩
  obtain ⟨c, hct, hcmax⟩ := Finset.exists_max_image t (fun c => (A.filter fun a => φ a = c).card) htne
  set F := A.filter fun a => φ a = c with hF
  have hAF : A.card ≤ (L + 1) ^ y * (K + 1) * F.card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps, ← htcard]
    calc ∑ b ∈ t, (A.filter fun a => φ a = b).card ≤ ∑ _b ∈ t, F.card :=
          Finset.sum_le_sum fun b hb => hcmax b hb
      _ = t.card * F.card := by rw [Finset.sum_const, smul_eq_mul]
  rcases F.eq_empty_or_nonempty with hFe | ⟨a0, ha0F⟩
  · refine ⟨1, 0, ∅, one_pos, Nat.zero_le _, fun b hb => absurd hb (Finset.notMem_empty b), ?_,
      fun b hb => absurd hb (Finset.notMem_empty b)⟩
    rw [hFe, Finset.card_empty, mul_zero] at hAF
    simpa using hAF
  have hFA : ∀ a ∈ F, a ∈ A := fun a ha => (Finset.mem_filter.mp ha).1
  have hFφ : ∀ a ∈ F, φ a = c := fun a ha => (Finset.mem_filter.mp ha).2
  -- all elements of the fiber have the same smooth part
  have hsmeq : ∀ a ∈ F, OMA.Helpers.erdos535_sm y a = OMA.Helpers.erdos535_sm y a0 := by
    intro a ha
    apply Nat.eq_of_factorization_eq (hsm0 a (hFA a ha)) (hsm0 a0 (hFA a0 ha0F))
    intro p
    rw [OMA.Helpers.erdos535_sm_fact, OMA.Helpers.erdos535_sm_fact]
    by_cases hp : p < y
    · rw [Finsupp.filter_apply_pos (fun x => x < y) _ hp,
        Finsupp.filter_apply_pos (fun x => x < y) _ hp]
      have h := congrArg (fun z => z.1 ⟨p, hp⟩) ((hFφ a ha).trans (hFφ a0 ha0F).symm)
      exact h
    · rw [Finsupp.filter_apply_neg (fun x => x < y) _ hp,
        Finsupp.filter_apply_neg (fun x => x < y) _ hp]
  refine ⟨OMA.Helpers.erdos535_sm y a0, c.2, F.image (OMA.Helpers.erdos535_rf y), Nat.pos_of_ne_zero (hsm0 a0 (hFA a0 ha0F)), ?_, ?_, ?_, ?_⟩
  · exact Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hct).2)
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    refine ⟨Nat.pos_of_ne_zero (hrf0 a (hFA a ha)), ?_⟩
    have h := congrArg Prod.snd (hFφ a ha)
    exact h
  · rw [Finset.card_image_of_injOn]
    · exact hAF
    · intro a ha a' ha' heq
      have ha0 : a ≠ 0 := by have := (hmemA a (hFA a ha)).1; omega
      have ha0' : a' ≠ 0 := by have := (hmemA a' (hFA a' ha')).1; omega
      rw [← OMA.Helpers.erdos535_sm_mul_rf y a ha0, ← OMA.Helpers.erdos535_sm_mul_rf y a' ha0', hsmeq a ha, hsmeq a' ha']
      exact congrArg _ heq
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    have ha0 : a ≠ 0 := by have := (hmemA a (hFA a ha)).1; omega
    rw [← hsmeq a ha, OMA.Helpers.erdos535_sm_mul_rf y a ha0]
    exact hFA a ha
