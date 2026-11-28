import OMAStatements.S_oeis_a365498
import Mathlib

namespace OMA.Helpers
open OMA.S_oeis_a365498 ArithmeticFunction

def F (h : ℕ → ℤ) (n : ℕ) : ℤ := n.factorization.prod fun _ k => h k

theorem F_eq (h : ℕ → ℤ) (n : ℕ) : F h n = ∏ p ∈ n.primeFactors, h (n.factorization p) := by
  unfold F Finsupp.prod
  rw [Nat.support_factorization]

theorem F_mul (h : ℕ → ℤ) {m n : ℕ} (hmn : m.Coprime n) : F h (m * n) = F h m * F h n := by
  rcases eq_or_ne m 0 with rfl | hm
  · have : n = 1 := by simpa using hmn
    subst this; simp [F]
  rcases eq_or_ne n 0 with rfl | hn
  · have : m = 1 := by simpa using hmn
    subst this; simp [F]
  unfold F
  rw [Nat.factorization_mul_of_coprime hmn, Finsupp.prod_add_index_of_disjoint]
  exact hmn.disjoint_primeFactors

theorem F_pp (h : ℕ → ℤ) (h0 : h 0 = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) : F h (p ^ k) = h k := by
  unfold F
  rw [hp.factorization_pow, Finsupp.prod_single_index h0]

def AF (h : ℕ → ℤ) : ArithmeticFunction ℤ := ⟨fun n => if n = 0 then 0 else F h n, by simp⟩

theorem AF_apply (h : ℕ → ℤ) {n : ℕ} (hn : n ≠ 0) : AF h n = F h n := by
  show (if n = 0 then 0 else F h n) = F h n
  rw [if_neg hn]

theorem AF_mult (h : ℕ → ℤ) : (AF h).IsMultiplicative := by
  apply IsMultiplicative.iff_ne_zero.mpr
  refine ⟨?_, fun {m n} hm hn hmn => ?_⟩
  · rw [AF_apply h one_ne_zero]; simp [F]
  · rw [AF_apply h (mul_ne_zero hm hn), AF_apply h hm, AF_apply h hn, F_mul h hmn]

def r (e : ℕ) : ℤ := (if e = 1 then 2 else 1) * (if e = 2 then 2 else 1)

theorem sum_c (i : ℕ) : ∑ k ∈ Finset.range (i + 1), c k = r i := by
  rcases i with _ | _ | _ | _ | i
  · decide
  · decide
  · decide
  · decide
  · induction i with
    | zero => decide
    | succ i ih =>
      rw [Finset.sum_range_succ, ih]
      simp [c, r]

theorem key : ∀ n : ℕ, 1 ≤ n → a n = a056671 n * a368885 n := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hL : a n = (AF c * (zeta : ArithmeticFunction ℤ)) n := by
    rw [coe_mul_zeta_apply]
    unfold a
    apply Finset.sum_congr rfl
    intro d hd
    rw [AF_apply c (Nat.pos_of_mem_divisors hd).ne', F_eq]
    rfl
  have hR : a056671 n * a368885 n = AF r n := by
    rw [AF_apply _ hn0, F_eq]
    unfold a056671 a368885 r
    rw [← Finset.prod_mul_distrib]
  have heq : AF c * (zeta : ArithmeticFunction ℤ) = AF r := by
    rw [IsMultiplicative.eq_iff_eq_on_prime_powers _
      ((AF_mult c).mul isMultiplicative_zeta.natCast) _ (AF_mult r)]
    intro p i hp
    have hpi : p ^ i ≠ 0 := pow_ne_zero _ hp.ne_zero
    rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, AF_apply _ hpi, F_pp _ rfl hp, ← sum_c]
    apply Finset.sum_congr rfl
    intro k _
    rw [AF_apply _ (pow_ne_zero _ hp.ne_zero), F_pp _ rfl hp]
  rw [hL, hR, heq]

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a365498.main := OMA.Helpers.key
