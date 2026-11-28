import OMAReductions.R_Mills_exists_prime_R1

/-!
# Step H2 of the reduction Mills.exists-prime.R1

Mills' nested intervals. Put N n = 3^(n+1), a n = (q n)^(1/N n) and b n = (q n + 1)^(1/N n).
Raising to the power N (n+1) = 3 N n shows that a is monotone and b strictly decreasing, and
a n < b n. Hence A = sup a satisfies a n ≤ A ≤ b (n+1) < b n, so q n ≤ A^(N n) < q n + 1.
-/

namespace OMA.Helpers

/-- The real N-th root of a natural number, raised back to the N-th power. -/
theorem mills_root_pow (m N : ℕ) (hN : N ≠ 0) :
    (((m : ℝ) ^ ((N : ℝ)⁻¹)) ^ N) = (m : ℝ) :=
  Real.rpow_inv_natCast_pow (Nat.cast_nonneg m) hN

end OMA.Helpers

theorem OMA.solution : OMA.R_Mills_exists_prime_R1.H2 := by
  intro q hq2 hlow hup
  let N : ℕ → ℕ := fun n => 3 ^ (n + 1)
  have hNpos : ∀ n, N n ≠ 0 := fun n => by positivity
  have hNsucc : ∀ n, N (n + 1) = N n * 3 := fun n => by
    show 3 ^ (n + 1 + 1) = 3 ^ (n + 1) * 3
    rw [pow_succ]
  let a : ℕ → ℝ := fun n => ((q n : ℕ) : ℝ) ^ (((N n : ℕ) : ℝ)⁻¹)
  let b : ℕ → ℝ := fun n => ((q n + 1 : ℕ) : ℝ) ^ (((N n : ℕ) : ℝ)⁻¹)
  have ha0 : ∀ n, 0 ≤ a n := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hb0 : ∀ n, 0 ≤ b n := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hapow : ∀ n, a n ^ N n = ((q n : ℕ) : ℝ) := fun n =>
    OMA.Helpers.mills_root_pow (q n) (N n) (hNpos n)
  have hbpow : ∀ n, b n ^ N n = ((q n + 1 : ℕ) : ℝ) := fun n =>
    OMA.Helpers.mills_root_pow (q n + 1) (N n) (hNpos n)
  have hamono : ∀ n, a n ≤ a (n + 1) := by
    intro n
    have h : a n ^ N (n + 1) ≤ a (n + 1) ^ N (n + 1) := by
      rw [hapow (n + 1), hNsucc, pow_mul, hapow n]
      exact_mod_cast hlow n
    exact (pow_le_pow_iff_left₀ (ha0 n) (ha0 (n + 1)) (hNpos (n + 1))).mp h
  have hbanti : ∀ n, b (n + 1) < b n := by
    intro n
    have h : b (n + 1) ^ N (n + 1) < b n ^ N (n + 1) := by
      rw [hbpow (n + 1), hNsucc, pow_mul, hbpow n]
      exact_mod_cast hup n
    exact (pow_lt_pow_iff_left₀ (hb0 (n + 1)) (hb0 n) (hNpos (n + 1))).mp h
  have hab : ∀ n, a n < b n := by
    intro n
    have h : a n ^ N n < b n ^ N n := by
      rw [hapow n, hbpow n]
      exact_mod_cast Nat.lt_succ_self (q n)
    exact (pow_lt_pow_iff_left₀ (ha0 n) (hb0 n) (hNpos n)).mp h
  have amon : Monotone a := monotone_nat_of_le_succ hamono
  have banti : StrictAnti b := strictAnti_nat_of_succ_lt hbanti
  have hamb : ∀ m n, a m ≤ b n := by
    intro m n
    calc a m ≤ a (max m n) := amon (le_max_left _ _)
      _ ≤ b (max m n) := (hab _).le
      _ ≤ b n := banti.antitone (le_max_right _ _)
  have bdd : BddAbove (Set.range a) := ⟨b 0, by rintro _ ⟨m, rfl⟩; exact hamb m 0⟩
  have haA : ∀ n, a n ≤ ⨆ m, a m := fun n => le_ciSup bdd n
  have hAb : ∀ n, (⨆ m, a m) < b n := fun n =>
    lt_of_le_of_lt (ciSup_le fun m => hamb m (n + 1)) (hbanti n)
  refine ⟨⨆ m, a m, ?_, fun n => ?_⟩
  · have h1 : 1 < a 0 := by
      have h : (1 : ℝ) ^ N 0 < a 0 ^ N 0 := by
        rw [one_pow, hapow 0]
        have : 1 < q 0 := hq2 0
        exact_mod_cast this
      exact (pow_lt_pow_iff_left₀ zero_le_one (ha0 0) (hNpos 0)).mp h
    exact h1.trans_le (haA 0)
  · have hA0 : 0 ≤ ⨆ m, a m := (ha0 n).trans (haA n)
    show ⌊(⨆ m, a m) ^ N n⌋₊ = q n
    rw [Nat.floor_eq_iff (pow_nonneg hA0 _)]
    constructor
    · have h := pow_le_pow_left₀ (ha0 n) (haA n) (N n)
      rw [hapow n] at h
      exact h
    · have h := pow_lt_pow_left₀ (hAb n) hA0 (hNpos n)
      rw [hbpow n] at h
      push_cast at h
      exact h
