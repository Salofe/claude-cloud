import OMAReductions.R_OeisA1146_conjecture_R1_H2_R1
import Mathlib

/-!
Semiprime predecessors k-1 = p*q with p ≤ 61. The prime q divides 2^(p+1)-1,
so q lies in an explicit factor list. Every pair is then excluded by
4 ∤ k, a local test at q or at p, or a direct residue computation.
-/

namespace OMA.Helpers

open OMA.Hasler

/-- Boolean test certifying that a pair (p,q) cannot pass, unless p*q+1 = 16. -/
def goodPair (p q : ℕ) : Bool :=
  (p*q+1 == 16) || ((p*q+1) % 4 != 0) || ((2^((p*q+1).gcd (q-1)) - 1) % q != 0) ||
    ((2^((p*q+1).gcd (p-1)) - 1) % p != 0) || ((2^(p*q+1)-1) % ((p*q+1)^4-1) != 0)

lemma sub_one_dvd_pow_four (k : ℕ) : k - 1 ∣ k^4 - 1 := by
  simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow k 1 4

lemma q_dvd_mersenne (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h : (p*q+1)^4-1 ∣ 2^(p*q+1)-1) : q ∣ 2^(p+1)-1 := by
  have hk : 1 < p*q+1 := by
    have := Nat.mul_le_mul hp.two_le hq.two_le
    omega
  have hdvd : q^1 ∣ (p*q+1)^4-1 := by
    rw [pow_one]
    exact (dvd_mul_left q p).trans (by simpa using sub_one_dvd_pow_four (p*q+1))
  have hloc := (localIff hk).mp h q 1 hq hdvd
  rw [pow_one] at hloc
  have heq : p*q+1 = p*(q-1) + (p+1) := by
    have h1 := hq.one_le
    have : p*q = p*(q-1) + p := by
      rw [← Nat.mul_add_one, Nat.sub_add_cancel h1]
    omega
  have hg : (p*q+1).gcd (q-1) ∣ p+1 := by
    have h1 : (p*q+1).gcd (q-1) ∣ p*(q-1) + (p+1) := heq ▸ Nat.gcd_dvd_left _ _
    exact (Nat.dvd_add_right (dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) p)).mp h1
  exact hloc.trans ((mersenneIff _ _).mpr hg)

lemma pair_ok (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hgood : goodPair p q = true)
    (h : (p*q+1)^4-1 ∣ 2^(p*q+1)-1) : p*q+1 = 16 := by
  have hk : 1 < p*q+1 := by
    have := Nat.mul_le_mul hp.two_le hq.two_le
    omega
  simp only [goodPair, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hgood
  rcases hgood with (((h1 | h2) | h3) | h4) | h5
  · exact h1
  · exact absurd (Nat.mod_eq_zero_of_dvd (fourDvd hk h)) h2
  · have hdvd : q^1 ∣ (p*q+1)^4-1 := by
      rw [pow_one]
      exact (dvd_mul_left q p).trans (by simpa using sub_one_dvd_pow_four (p*q+1))
    have hloc := (localIff hk).mp h q 1 hq hdvd
    rw [pow_one] at hloc
    exact absurd (Nat.mod_eq_zero_of_dvd hloc) h3
  · have hdvd : p^1 ∣ (p*q+1)^4-1 := by
      rw [pow_one]
      exact (dvd_mul_right p q).trans (by simpa using sub_one_dvd_pow_four (p*q+1))
    have hloc := (localIff hk).mp h p 1 hp hdvd
    rw [pow_one] at hloc
    exact absurd (Nat.mod_eq_zero_of_dvd hloc) h4
  · exact absurd (Nat.mod_eq_zero_of_dvd h) h5

lemma by_list (p : ℕ) (hp : p.Prime) (L : List ℕ) (hL : ∀ x ∈ L, x.Prime)
    (hprod : L.prod = 2^(p+1)-1) (hg : L.all (goodPair p) = true) :
    ∀ q : ℕ, q.Prime → (p*q+1)^4-1 ∣ 2^(p*q+1)-1 → p*q+1 = 16 := by
  intro q hq h
  have hd := q_dvd_mersenne p q hp hq h
  rw [← hprod] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  have hxq := (Nat.prime_dvd_prime_iff_eq hq (hL x hx)).mp hqx
  subst hxq
  exact pair_ok p q hp hq (List.all_eq_true.mp hg q hx) h

end OMA.Helpers

set_option maxRecDepth 200000 in
theorem OMA.solution : OMA.R_OeisA1146_conjecture_R1_H2_R1.H1 := by
  intro p q hp hp61 hq h
  interval_cases p <;> try (exfalso; norm_num at hp; done)
  · exact OMA.Helpers.by_list 2 hp [7] (by norm_num) (by norm_num) (by decide +kernel) q hq h
  · exact OMA.Helpers.by_list 3 hp [3, 5] (by norm_num) (by norm_num) (by decide +kernel) q hq h
  · exact OMA.Helpers.by_list 5 hp [3, 3, 7] (by norm_num) (by norm_num) (by decide +kernel) q hq h
  · exact OMA.Helpers.by_list 7 hp [3, 5, 17] (by norm_num) (by norm_num) (by decide +kernel) q hq h
  · exact OMA.Helpers.by_list 11 hp [3, 3, 5, 7, 13] (by norm_num) (by norm_num)
      (by decide +kernel) q hq h
  · exact OMA.Helpers.by_list 13 hp [3, 43, 127] (by norm_num) (by norm_num)
      (by decide +kernel) q hq h
  · exact OMA.Helpers.by_list 17 hp [3, 3, 3, 7, 19, 73] (by norm_num) (by norm_num)
      (by decide +kernel) q hq h
  · exact OMA.Helpers.by_list 19 hp [3, 5, 5, 11, 31, 41] (by norm_num) (by norm_num)
      (by decide +kernel) q hq h
  · exact OMA.Helpers.by_list 23 hp [3, 3, 5, 7, 13, 17, 241] (by norm_num) (by norm_num)
      (by decide +kernel) q hq h
  · exact OMA.Helpers.by_list 29 hp [3, 3, 7, 11, 31, 151, 331] (by norm_num) (by norm_num)
      (by decide +kernel) q hq h
  · exact OMA.Helpers.by_list 31 hp [3, 5, 17, 257, 65537] (by norm_num) (by norm_num)
      (by decide +kernel) q hq h
  · exact OMA.Helpers.by_list 37 hp [3, 174763, 524287] (by norm_num) (by norm_num)
      (by decide +kernel) q hq h
  · exact OMA.Helpers.by_list 41 hp [3, 3, 7, 7, 43, 127, 337, 5419] (by norm_num) (by norm_num)
      (by decide +kernel) q hq h
  · exact OMA.Helpers.by_list 43 hp [3, 5, 23, 89, 397, 683, 2113] (by norm_num) (by norm_num)
      (by decide +kernel) q hq h
  · exact OMA.Helpers.by_list 47 hp [3, 3, 5, 7, 13, 17, 97, 241, 257, 673] (by norm_num)
      (by norm_num) (by decide +kernel) q hq h
  · exact OMA.Helpers.by_list 53 hp [3, 3, 3, 3, 7, 19, 73, 87211, 262657] (by norm_num)
      (by norm_num) (by decide +kernel) q hq h
  · exact OMA.Helpers.by_list 59 hp [3, 3, 5, 5, 7, 11, 13, 31, 41, 61, 151, 331, 1321]
      (by norm_num) (by norm_num) (by decide +kernel) q hq h
  · exact OMA.Helpers.by_list 61 hp [3, 715827883, 2147483647] (by norm_num) (by norm_num)
      (by decide +kernel) q hq h
