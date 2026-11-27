import OMAReductions.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1

/-!
# Step H1 of the reduction OeisA105751.conjecture.variants.moll_p_mod_4_eq_1.R1

For a prime `p ≡ 1 (mod 4)` and `e = ν_p(n!)`, `p ^ e` divides `a n`.

Write `∏_{k ≤ n} (1 + k i) = A_n + B_n i` with integers `A_n, B_n` (so `a n = B_n`). Since
`p ≡ 1 (mod 4)` there is `c` in `ZMod (p ^ e)` with `c ^ 2 = -1` (a square root of `-1` mod `p`,
lifted by Newton steps). The substitution `i ↦ c` is multiplicative, so
`A_n + c B_n = ∏_{k ≤ n} (1 + k c) = c ^ (n + 1) ∏_{k ≤ n} (-c + k)`, and the last product is the
image of a product of `n + 1` consecutive natural numbers, which `n!` and hence `p ^ e` divide.
So `A_n + c B_n = 0`, likewise `A_n - c B_n = 0`, hence `2 c B_n = 0` and `B_n = 0` in
`ZMod (p ^ e)` because `c` and `2` are units there.

Only upstream definitions are used.
-/

namespace OMA.Helpers

open Complex

/-- Real and imaginary parts of `∏_{k ≤ n} (1 + k i)`. -/
def a105751AB : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | k + 1 => ((a105751AB k).1 - ((k : ℤ) + 1) * (a105751AB k).2,
      (a105751AB k).2 + ((k : ℤ) + 1) * (a105751AB k).1)

theorem a105751_prod_eq (n : ℕ) :
    (∏ k ∈ Finset.range (n + 1), ((1 : ℂ) + (k : ℂ) * I)) =
      ((a105751AB n).1 : ℂ) + ((a105751AB n).2 : ℂ) * I := by
  induction n with
  | zero => simp [a105751AB]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    simp only [a105751AB]
    push_cast
    linear_combination (((n : ℂ) + 1) * ((a105751AB n).2 : ℂ)) * Complex.I_sq

theorem a105751_a_eq (n : ℕ) : OeisA105751.a n = (a105751AB n).2 := by
  show Int.floor ((∏ k ∈ Finset.range (n + 1), ((1 : ℂ) + (k : ℂ) * I)).im) = _
  rw [a105751_prod_eq]
  simp

theorem a105751_zmod_eq {N : ℕ} (c : ZMod N) (hc : c ^ 2 = -1) (n : ℕ) :
    ((a105751AB n).1 : ZMod N) + c * ((a105751AB n).2 : ZMod N) =
      ∏ k ∈ Finset.range (n + 1), ((1 : ZMod N) + (k : ZMod N) * c) := by
  induction n with
  | zero => simp [a105751AB]
  | succ n ih =>
    rw [Finset.prod_range_succ, ← ih]
    simp only [a105751AB]
    push_cast
    linear_combination (-((n : ZMod N) + 1) * ((a105751AB n).2 : ZMod N)) * hc

theorem a105751_prod_zero {N : ℕ} [NeZero N] (c : ZMod N) (hc : c ^ 2 = -1) (n : ℕ)
    (hN : N ∣ n.factorial) :
    ∏ k ∈ Finset.range (n + 1), ((1 : ZMod N) + (k : ZMod N) * c) = 0 := by
  have hfac : ∀ k : ℕ, (1 : ZMod N) + (k : ZMod N) * c =
      c * ((((-c).val : ℕ) : ZMod N) + (k : ZMod N)) := by
    intro k
    rw [ZMod.natCast_zmod_val]
    linear_combination hc
  simp_rw [hfac]
  rw [Finset.prod_mul_distrib]
  have hprod : ∏ k ∈ Finset.range (n + 1), ((((-c).val : ℕ) : ZMod N) + (k : ZMod N)) =
      (((-c).val.ascFactorial (n + 1) : ℕ) : ZMod N) := by
    rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    simp only [Nat.cast_add]
  rw [hprod]
  have hdvd : N ∣ (-c).val.ascFactorial (n + 1) :=
    hN.trans ((Nat.factorial_dvd_factorial (Nat.le_succ n)).trans
      (Nat.factorial_dvd_ascFactorial _ _))
  rw [(ZMod.natCast_eq_zero_iff _ _).mpr hdvd, mul_zero]

/-- A square root of `-1` modulo `p ^ (f + 1)` with `2 c` prime to `p`. -/
theorem a105751_lift (p : ℕ) (hp : p.Prime) (hmod : p % 4 = 1) :
    ∀ f : ℕ, ∃ c : ℤ, (p : ℤ) ^ (f + 1) ∣ c ^ 2 + 1 ∧ IsCoprime (2 * c) (p : ℤ) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  intro f
  induction f with
  | zero =>
    have := Fact.mk hp
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨y, hy⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3)
    refine ⟨(y.val : ℤ), ?_, ?_⟩
    · rw [zero_add, pow_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val, sq, ← hy]
      ring
    · rw [isCoprime_comm, hpZ.coprime_iff_not_dvd]
      intro h2
      rcases hpZ.dvd_or_dvd h2 with h | h
      · have : p ∣ 2 := by exact_mod_cast h
        have := Nat.le_of_dvd (by norm_num) this
        have := hp.two_le
        omega
      · have h1 : (p : ℤ) ∣ (y.val : ℤ) ^ 2 + 1 := by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
          push_cast
          rw [ZMod.natCast_zmod_val, sq, ← hy]
          ring
        have h3 : (p : ℤ) ∣ (y.val : ℤ) ^ 2 := dvd_pow h two_ne_zero
        have h4 : (p : ℤ) ∣ 1 := (dvd_add_right h3).mp h1
        exact hpZ.not_dvd_one h4
  | succ f ih =>
    obtain ⟨c, ⟨s, hs⟩, hcop⟩ := ih
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨c + (-s * u) * (p : ℤ) ^ (f + 1), ⟨s * v + s ^ 2 * u ^ 2 * (p : ℤ) ^ f, ?_⟩, ?_⟩
    · linear_combination hs - (p : ℤ) ^ (f + 1) * s * huv
    · have : 2 * (c + (-s * u) * (p : ℤ) ^ (f + 1)) =
          2 * c + (p : ℤ) * (2 * (-s * u) * (p : ℤ) ^ f) := by ring
      rw [this]
      exact IsCoprime.add_mul_left_left ⟨u, v, huv⟩ _

theorem a105751_sqrt (p : ℕ) (hp : p.Prime) (hmod : p % 4 = 1) (e : ℕ) :
    ∃ c : ZMod (p ^ e), c ^ 2 = -1 := by
  obtain ⟨c, hc, -⟩ := a105751_lift p hp hmod e
  refine ⟨(c : ZMod (p ^ e)), ?_⟩
  have h : (p : ℤ) ^ e ∣ c ^ 2 + 1 := (pow_dvd_pow _ (Nat.le_succ e)).trans hc
  have h' : (((c ^ 2 + 1 : ℤ)) : ZMod (p ^ e)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact h
  push_cast at h'
  linear_combination h'

end OMA.Helpers

theorem OMA.solution : OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1.H1 := by
  intro p hp hmod n
  set e := padicValNat p n.factorial with he
  set N := p ^ e with hN
  have : NeZero N := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨c, hc⟩ := OMA.Helpers.a105751_sqrt p hp hmod e
  have hdvd : N ∣ n.factorial := pow_padicValNat_dvd
  have hc' : (-c) ^ 2 = -1 := by rw [neg_sq]; exact hc
  have h1 := OMA.Helpers.a105751_zmod_eq c hc n
  rw [OMA.Helpers.a105751_prod_zero c hc n hdvd] at h1
  have h2 := OMA.Helpers.a105751_zmod_eq (-c) hc' n
  rw [OMA.Helpers.a105751_prod_zero (-c) hc' n hdvd] at h2
  have h2B : 2 * ((OMA.Helpers.a105751AB n).2 : ZMod N) = 0 := by
    linear_combination (-c) * h1 + c * h2 + 2 * ((OMA.Helpers.a105751AB n).2 : ZMod N) * hc
  have hodd : N % 2 = 1 := by
    rw [hN, Nat.pow_mod]
    have : p % 2 = 1 := by omega
    rw [this]
    simp
  have hk : ((N / 2 + 1 : ℕ) : ZMod N) * 2 = 1 := by
    have e1 : (N / 2 + 1) * 2 = N + 1 := by omega
    have e2 : (((N / 2 + 1) * 2 : ℕ) : ZMod N) = ((N + 1 : ℕ) : ZMod N) := by rw [e1]
    rw [Nat.cast_mul, Nat.cast_succ N, ZMod.natCast_self, zero_add, Nat.cast_ofNat] at e2
    exact e2
  have hB : (((OMA.Helpers.a105751AB n).2 : ℤ) : ZMod N) = 0 := by
    linear_combination ((N / 2 + 1 : ℕ) : ZMod N) * h2B -
      ((OMA.Helpers.a105751AB n).2 : ZMod N) * hk
  rw [OMA.Helpers.a105751_a_eq]
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hB
  rw [hN] at this
  push_cast at this
  exact this
