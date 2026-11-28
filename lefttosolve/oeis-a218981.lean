import OMAStatements.S_oeis_a218981
import Mathlib

namespace OMA.Helpers

theorem a218981_sigma_prime {p : ℕ} (hp : p.Prime) : ArithmeticFunction.sigma 1 p = p + 1 := by
  rw [ArithmeticFunction.sigma_one_apply, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  ring

theorem a218981_sigma_mul {c p : ℕ} (hp : p.Prime) (hc : 0 < c) (hcp : c < p) :
    ArithmeticFunction.sigma 1 (c * p) = ArithmeticFunction.sigma 1 c * (p + 1) := by
  have hcop : Nat.Coprime c p :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 (fun h => by
      have := Nat.le_of_dvd hc h
      omega))
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, a218981_sigma_prime hp]

theorem a218981_family {p : ℕ} (hp : p.Prime) (h5 : 5 < p) :
    ArithmeticFunction.sigma 1 (5 * p) = ArithmeticFunction.sigma 1 p + ArithmeticFunction.sigma 1 p
      + ArithmeticFunction.sigma 1 p + ArithmeticFunction.sigma 1 (2 * p) := by
  rw [a218981_sigma_mul hp (by norm_num) h5, a218981_sigma_mul hp (by norm_num) (by omega),
    a218981_sigma_prime hp]
  have h5' : ArithmeticFunction.sigma 1 5 = 6 := by decide
  have h2' : ArithmeticFunction.sigma 1 2 = 3 := by decide
  rw [h5', h2']
  ring

theorem a218981_isTerm {p : ℕ} (hp : p.Prime) (h5 : 5 < p) : OMA.S_oeis_a218981.IsTerm (5 * p) := by
  have hp0 : 0 < p := hp.pos
  refine ⟨p, p, p, 2 * p, hp0, hp0, hp0, by omega, by ring, ?_⟩
  exact a218981_family hp h5

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a218981.main := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 6)
  have hmem : 5 * p ∈ {n : ℕ | OMA.S_oeis_a218981.IsTerm n} :=
    OMA.Helpers.a218981_isTerm hp (by omega)
  have := hN hmem
  omega
