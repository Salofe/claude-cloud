import OMAStatements.S_oeis_a074882
import Mathlib

/-!
Proof of Robert Israel's conjecture on OEIS A074882: if n >= 1 is not a prime power, fewer than
n integers in {1, ..., sigma(n)} are coprime to n.

Write C(m, z) for the number of integers in {1, ..., z} coprime to m. Removing a prime p that does
not divide m gives C(p^k m, x) = C(m, x) - C(m, x / p). With R the product of the distinct primes
of m and Phi = phi(R), the scaled error G(m, z) = R C(m, z) - z Phi then satisfies
G(p^k m, x) = p G(m, x) - p G(m, x / p) + Phi (x mod p), so by induction over the prime-power
factors, -(K - 1) R <= G <= K R - 1 with K = 2^(r - 1) for r >= 1 distinct primes. On the other
side, the defect T(m) = m R - sigma(m) Phi satisfies T(p^k m) = m R + (p^(k+1) - 1) T(m), and one
checks T(n) >= K R as soon as n has at least two distinct prime factors. Then
R C(n, sigma(n)) = sigma(n) Phi + G <= sigma(n) Phi + K R - 1 <= n R - 1, so C(n, sigma(n)) < n.
-/

namespace OMA.Helpers

open Finset

/-- The number of integers in `{1, ..., z}` coprime to `m`. -/
def a074882_C (m z : ℕ) : ℕ := ((Icc 1 z).filter (fun k => Nat.Coprime k m)).card

theorem a074882_C_one (z : ℕ) : a074882_C 1 z = z := by
  unfold a074882_C
  rw [Finset.filter_true_of_mem (fun k _ => Nat.coprime_one_right k)]
  simp

/-- The multiples of `p` coprime to `m` in `{1, ..., x}` correspond to the integers coprime to
`m` in `{1, ..., x / p}`. -/
theorem a074882_mult (m p x : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    ((Icc 1 x).filter (fun j => Nat.Coprime j m ∧ p ∣ j)).card = a074882_C m (x / p) := by
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
  have hp0 : 0 < p := hp.pos
  unfold a074882_C
  apply Finset.card_bij' (fun j _ => j / p) (fun i _ => i * p)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
    obtain ⟨⟨h1, h2⟩, hc, t, rfl⟩ := hj
    rw [Nat.mul_div_cancel_left t hp0]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp at h1
      · exact ht
    · rw [Nat.le_div_iff_mul_le hp0]
      linarith
    · exact Nat.Coprime.coprime_mul_left hc
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_Icc] at hi ⊢
    obtain ⟨⟨h1, h2⟩, hc⟩ := hi
    refine ⟨⟨?_, ?_⟩, Nat.Coprime.mul_left hc hcop, dvd_mul_left p i⟩
    · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    · exact (Nat.le_div_iff_mul_le hp0).1 h2
  · intro j hj
    simp only [Finset.mem_filter] at hj
    exact Nat.div_mul_cancel hj.2.2
  · intro i _
    exact Nat.mul_div_cancel i hp0

/-- Removing the prime `p`: `C(p^k m, x) + C(m, x / p) = C(m, x)`. -/
theorem a074882_split (m p k x : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m) (hk : 0 < k) :
    a074882_C (p ^ k * m) x + a074882_C m (x / p) = a074882_C m x := by
  rw [← a074882_mult m p x hp hpm]
  have e1 : (Icc 1 x).filter (fun j => Nat.Coprime j (p ^ k * m))
      = ((Icc 1 x).filter (fun j => Nat.Coprime j m)).filter (fun j => ¬ p ∣ j) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr (fun j _ => ?_)
    rw [Nat.coprime_mul_iff_right, Nat.coprime_pow_right_iff hk, Nat.coprime_comm,
      Nat.Prime.coprime_iff_not_dvd hp]
    exact and_comm
  have e2 : (Icc 1 x).filter (fun j => Nat.Coprime j m ∧ p ∣ j)
      = ((Icc 1 x).filter (fun j => Nat.Coprime j m)).filter (fun j => ¬ ¬ p ∣ j) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr (fun j _ => ?_)
    rw [not_not]
  unfold a074882_C
  rw [e1, e2]
  exact Finset.card_filter_add_card_filter_not _

/-- The sum of divisors of a prime power times `p - 1`. -/
theorem a074882_sigma_pp (p k : ℕ) (hp : p.Prime) :
    (ArithmeticFunction.sigma 1 (p ^ k) : ℤ) * ((p : ℤ) - 1) = (p : ℤ) ^ (k + 1) - 1 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
  push_cast
  exact geom_sum_mul (p : ℤ) (k + 1)

/-- The scaled error term `R * C(m, z) - z * Φ`. -/
def a074882_G (m R Φ z : ℕ) : ℤ := (R : ℤ) * a074882_C m z - (z : ℤ) * Φ

theorem a074882_G_rec (m p k x R Φ : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m) (hk : 0 < k) :
    a074882_G (p ^ k * m) (p * R) ((p - 1) * Φ) x
      = p * a074882_G m R Φ x - p * a074882_G m R Φ (x / p) + Φ * ((x % p : ℕ) : ℤ) := by
  have hs := a074882_split m p k x hp hpm hk
  have hs' : (a074882_C (p ^ k * m) x : ℤ) + a074882_C m (x / p) = a074882_C m x := by
    exact_mod_cast hs
  have hd : ((x / p : ℕ) : ℤ) * p + ((x % p : ℕ) : ℤ) = x := by
    have := Nat.div_add_mod' x p
    exact_mod_cast this
  have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    have := hp.one_le
    push_cast [this]
    ring
  unfold a074882_G
  rw [Nat.cast_mul, Nat.cast_mul, hp1]
  linear_combination (p : ℤ) * R * hs' - (Φ : ℤ) * hd

/-- One step of the error bound: from bounds `[-(K-1)R, KR-1]` for the old error to bounds
`[-(2K-1)pR, 2KpR-1]` for the new one. -/
theorem a074882_G_bound (g1 g2 : ℤ) (p R Φ K s : ℕ) (hp : 1 ≤ p) (hΦ : Φ ≤ R) (hs : s < p)
    (g1u : g1 ≤ (K : ℤ) * R - 1) (g1l : -((K : ℤ) - 1) * R ≤ g1)
    (g2u : g2 ≤ (K : ℤ) * R - 1) (g2l : -((K : ℤ) - 1) * R ≤ g2) :
    (p : ℤ) * g1 - p * g2 + Φ * (s : ℤ) ≤ ((2 * K : ℕ) : ℤ) * ((p * R : ℕ) : ℤ) - 1 ∧
      -(((2 * K : ℕ) : ℤ) - 1) * ((p * R : ℕ) : ℤ) ≤ (p : ℤ) * g1 - p * g2 + Φ * (s : ℤ) := by
  have hp0 : (0 : ℤ) ≤ p := by positivity
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp
  have hΦR : (Φ : ℤ) ≤ R := by exact_mod_cast hΦ
  have hs1 : (s : ℤ) ≤ (p : ℤ) - 1 := by
    have : s + 1 ≤ p := hs
    have : ((s + 1 : ℕ) : ℤ) ≤ p := by exact_mod_cast this
    push_cast at this
    linarith
  have hs0 : (0 : ℤ) ≤ s := by positivity
  have hR0 : (0 : ℤ) ≤ R := by positivity
  have e1 : (Φ : ℤ) * s ≤ R * ((p : ℤ) - 1) := mul_le_mul hΦR hs1 hs0 hR0
  have e2 : (p : ℤ) * g1 ≤ p * ((K : ℤ) * R - 1) := mul_le_mul_of_nonneg_left g1u hp0
  have e3 : (p : ℤ) * (-((K : ℤ) - 1) * R) ≤ p * g2 := mul_le_mul_of_nonneg_left g2l hp0
  have e4 : (p : ℤ) * (-((K : ℤ) - 1) * R) ≤ p * g1 := mul_le_mul_of_nonneg_left g1l hp0
  have e5 : (p : ℤ) * g2 ≤ p * ((K : ℤ) * R - 1) := mul_le_mul_of_nonneg_left g2u hp0
  have e6 : (0 : ℤ) ≤ (Φ : ℤ) * s := mul_nonneg (by positivity) hs0
  push_cast
  constructor <;> nlinarith

/-- The invariant carried through the prime-power induction. -/
def a074882_Claim (m : ℕ) : Prop :=
  ∃ R Φ K : ℕ, 1 ≤ R ∧ Φ ≤ R ∧ 1 ≤ K ∧ K ≤ m ∧ R ∣ m ∧
    (∀ z : ℕ, a074882_G m R Φ z ≤ (K : ℤ) * R - 1 ∧ -((K : ℤ) - 1) * R ≤ a074882_G m R Φ z) ∧
    ((m = 1 ∧ R = 1 ∧ Φ = 1 ∧ K = 1) ∨
      (K = 1 ∧ 1 ≤ (m : ℤ) * R - (ArithmeticFunction.sigma 1 m : ℤ) * Φ ∧
        ∃ q k : ℕ, q.Prime ∧ 1 ≤ k ∧ m = q ^ k) ∨
      ((K : ℤ) * R ≤ (m : ℤ) * R - (ArithmeticFunction.sigma 1 m : ℤ) * Φ))

theorem a074882_claim_one : a074882_Claim 1 := by
  refine ⟨1, 1, 1, le_rfl, le_rfl, le_rfl, le_rfl, dvd_rfl, ?_, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
  intro z
  simp [a074882_G, a074882_C_one]

theorem a074882_claim_step (a p k : ℕ) (hp : p.Prime) (hpa : ¬ p ∣ a) (hk : 0 < k)
    (ha : 1 ≤ a) (ih : a074882_Claim a) : a074882_Claim (p ^ k * a) := by
  obtain ⟨R, Φ, K, hR, hΦ, hK, hKa, hRa, hG, hT⟩ := ih
  have hp2 : 2 ≤ p := hp.two_le
  have hpk : p ≤ p ^ k := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
  have hσ : (ArithmeticFunction.sigma 1 (p ^ k * a) : ℤ)
      = (ArithmeticFunction.sigma 1 (p ^ k) : ℤ) * ArithmeticFunction.sigma 1 a := by
    have hc : Nat.Coprime (p ^ k) a :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpa)
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc]
    push_cast
    ring
  have hsp := a074882_sigma_pp p k hp
  have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    push_cast [hp.one_le]
    ring
  -- the defect T(n) = n R' - σ(n) Φ' in terms of the defect of a
  have hTn : ((p ^ k * a : ℕ) : ℤ) * ((p * R : ℕ) : ℤ)
      - (ArithmeticFunction.sigma 1 (p ^ k * a) : ℤ) * (((p - 1) * Φ : ℕ) : ℤ)
      = (a : ℤ) * R + ((p : ℤ) ^ (k + 1) - 1) *
          ((a : ℤ) * R - (ArithmeticFunction.sigma 1 a : ℤ) * Φ) := by
    rw [hσ]
    push_cast
    rw [hp1]
    linear_combination (-(ArithmeticFunction.sigma 1 a : ℤ) * Φ) * hsp
  have hpow : (p : ℤ) * p ≤ (p : ℤ) ^ (k + 1) := by
    rw [← sq]
    exact_mod_cast Nat.pow_le_pow_right hp.pos (by omega : 2 ≤ k + 1)
  have hp4 : (4 : ℤ) ≤ (p : ℤ) * p := by
    have : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    nlinarith
  have hpk0 : (0 : ℤ) ≤ (p : ℤ) ^ (k + 1) - 1 := by linarith
  have hRle : R ≤ a := Nat.le_of_dvd (by omega) hRa
  have hRp : R ≠ p := by
    rintro rfl
    exact hpa hRa
  rcases hT with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, hT1, _⟩ | hT2
  · -- a = 1: the new number is a prime power
    refine ⟨p * 1, (p - 1) * 1, 1, by omega, by omega, le_rfl, by rw [mul_one]; omega,
      by rw [mul_one, mul_one]; exact dvd_pow_self p (by omega), ?_, ?_⟩
    · intro z
      have g1 : a074882_G 1 1 1 z = 0 := by simp [a074882_G, a074882_C_one]
      have g2 : a074882_G 1 1 1 (z / p) = 0 := by simp [a074882_G, a074882_C_one]
      rw [a074882_G_rec 1 p k z 1 1 hp hpa hk, g1, g2]
      have hlt := Nat.mod_lt z hp.pos
      generalize z % p = s at hlt ⊢
      simp only [Nat.cast_one, mul_zero, one_mul, zero_add, mul_one, sub_self, neg_zero,
        zero_mul]
      constructor <;> omega
    · right; left
      refine ⟨rfl, ?_, p, k, hp, hk, by rw [mul_one]⟩
      rw [hTn]
      simp
  · -- a is a prime power
    refine ⟨p * R, (p - 1) * Φ, 2 * 1, by simpa using Nat.mul_le_mul hp.one_le hR, ?_,
      by norm_num, ?_, ?_, ?_, ?_⟩
    · exact Nat.mul_le_mul (by omega) hΦ
    · nlinarith
    · exact mul_dvd_mul (dvd_pow_self p (by omega)) hRa
    · intro z
      obtain ⟨g1u, g1l⟩ := hG z
      obtain ⟨g2u, g2l⟩ := hG (z / p)
      rw [a074882_G_rec a p k z R Φ hp hpa hk]
      exact a074882_G_bound _ _ p R Φ 1 (z % p) hp.one_le hΦ (Nat.mod_lt z hp.pos)
        g1u g1l g2u g2l
    · right; right
      rw [hTn]
      set T := (a : ℤ) * R - (ArithmeticFunction.sigma 1 a : ℤ) * Φ with hTdef
      have hRp' : (R : ℤ) - p ≥ 1 ∨ (R : ℤ) - p ≤ -1 := by
        have : (R : ℤ) ≠ p := by exact_mod_cast hRp
        omega
      have hRa' : (R : ℤ) ≤ a := by exact_mod_cast hRle
      have hR0 : (0 : ℤ) ≤ R := by positivity
      have hp2' : (2 : ℤ) ≤ p := by exact_mod_cast hp2
      have f1 : ((p : ℤ) ^ (k + 1) - 1) * 1 ≤ ((p : ℤ) ^ (k + 1) - 1) * T :=
        mul_le_mul_of_nonneg_left hT1 hpk0
      have f2 : (R : ℤ) * R ≤ (a : ℤ) * R := mul_le_mul_of_nonneg_right hRa' hR0
      have f3 : 1 ≤ (R : ℤ) * R - 2 * p * R + p * p := by
        rcases hRp' with h | h <;> nlinarith
      have f4 : (p : ℤ) * p ≤ (p : ℤ) ^ (k + 1) := hpow
      push_cast
      linarith
  · -- a has at least two prime factors
    refine ⟨p * R, (p - 1) * Φ, 2 * K, by simpa using Nat.mul_le_mul hp.one_le hR, ?_,
      by omega, ?_, ?_, ?_, ?_⟩
    · exact Nat.mul_le_mul (by omega) hΦ
    · exact Nat.mul_le_mul (by omega) hKa
    · exact mul_dvd_mul (dvd_pow_self p (by omega)) hRa
    · intro z
      obtain ⟨g1u, g1l⟩ := hG z
      obtain ⟨g2u, g2l⟩ := hG (z / p)
      rw [a074882_G_rec a p k z R Φ hp hpa hk]
      exact a074882_G_bound _ _ p R Φ K (z % p) hp.one_le hΦ (Nat.mod_lt z hp.pos)
        g1u g1l g2u g2l
    · right; right
      rw [hTn]
      set T := (a : ℤ) * R - (ArithmeticFunction.sigma 1 a : ℤ) * Φ with hTdef
      have hKa' : (K : ℤ) ≤ a := by exact_mod_cast hKa
      have hR0 : (0 : ℤ) ≤ R := by positivity
      have hK0 : (1 : ℤ) ≤ K := by exact_mod_cast hK
      have hp2' : (2 : ℤ) ≤ p := by exact_mod_cast hp2
      have hKR : (0 : ℤ) ≤ (K : ℤ) * R := by positivity
      have f0 : (p : ℤ) * p - 1 ≤ (p : ℤ) ^ (k + 1) - 1 := by linarith
      have h1 : ((p : ℤ) * p - 1) * ((K : ℤ) * R) ≤ ((p : ℤ) ^ (k + 1) - 1) * T :=
        mul_le_mul f0 hT2 hKR hpk0
      have h2 : (K : ℤ) * R ≤ (a : ℤ) * R := mul_le_mul_of_nonneg_right hKa' hR0
      push_cast
      rcases Nat.lt_or_ge p 3 with h3 | h3
      · have hp_eq : (p : ℤ) = 2 := by
          have : p = 2 := by omega
          exact_mod_cast this
        rw [hp_eq] at h1 ⊢
        linarith
      · have h3' : (3 : ℤ) ≤ p := by exact_mod_cast h3
        have h4 : (2 * (p : ℤ)) * ((K : ℤ) * R) ≤ ((p : ℤ) * p - 1) * ((K : ℤ) * R) :=
          mul_le_mul_of_nonneg_right (by nlinarith) hKR
        have h5 : (0 : ℤ) ≤ (a : ℤ) * R := by positivity
        linarith

theorem a074882_claim : ∀ m : ℕ, 1 ≤ m → a074882_Claim m := by
  intro m
  induction m using Nat.recOnPrimePow with
  | zero => intro h; omega
  | one => intro _; exact a074882_claim_one
  | prime_pow_mul a p k hp hpa hk ih =>
    intro hm
    have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · simp at hm
      · exact h
    exact a074882_claim_step a p k hp hpa hk ha (ih ha)

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a074882.main := by
  intro n hn hnot
  obtain ⟨R, Φ, K, hR, hΦ, hK, hKn, hRn, hG, hT⟩ := a074882_claim n hn
  have hT' : (K : ℤ) * R ≤ (n : ℤ) * R - (ArithmeticFunction.sigma 1 n : ℤ) * Φ := by
    rcases hT with ⟨rfl, _⟩ | ⟨_, _, q, k, hq, hk, rfl⟩ | h
    · exact absurd (Or.inl rfl) hnot
    · exact absurd (Or.inr ⟨q, k, hq, hk, rfl⟩) hnot
    · exact h
  have hGn := (hG (ArithmeticFunction.sigma 1 n)).1
  unfold a074882_G at hGn
  have hR0 : (0 : ℤ) < R := by exact_mod_cast hR
  have hlt : (R : ℤ) * a074882_C n (ArithmeticFunction.sigma 1 n) < (R : ℤ) * n := by
    linarith
  have hlt' : (a074882_C n (ArithmeticFunction.sigma 1 n) : ℤ) < n :=
    lt_of_mul_lt_mul_left hlt hR0.le
  have : a074882_C n (ArithmeticFunction.sigma 1 n) < n := by exact_mod_cast hlt'
  exact this
