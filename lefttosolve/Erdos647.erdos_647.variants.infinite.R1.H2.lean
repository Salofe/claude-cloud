import OMAReductions.R_Erdos647_erdos_647_variants_infinite_R1
import Mathlib

/-!
# Step H2 of the reduction Erdos647.erdos_647.variants.infinite.R1

For `n > 24`, the six divisor bounds `d(n - j) <= j + 2` (for `j` in `1, 2, 3, 4, 6, 12`)
force `n` to be a multiple of `2520` whose six cofactors `n / j - 1` are prime, and conversely.

Main tool: if `a` divides `m` and `a * a < m`, then `m` has at least `2 d(a)` divisors
(the divisors of `a` together with their multiples by `m / a`). Small `n` are checked
by kernel computation; for larger `n` this tool gives `8 | n` and `9 | n`, after which
the coprime factorisation `n - j = j * (n / j - 1)` gives primality of the cofactors,
and then divisibility by `5` and `7`.
-/

namespace OMA.Helpers

theorem two_mul_card_le {a m : ℕ} (ha : a ∣ m) (h : a * a < m) :
    2 * a.divisors.card ≤ m.divisors.card := by
  obtain ⟨k, rfl⟩ := ha
  have hk : a < k := by
    by_contra hk
    push Not at hk
    have := Nat.mul_le_mul_left a hk
    omega
  have hk0 : 0 < k := by omega
  have hm0 : a * k ≠ 0 := by
    intro h0
    rw [h0] at h
    omega
  have hS : a.divisors ⊆ (a * k).divisors :=
    Nat.divisors_subset_of_dvd hm0 (dvd_mul_right a k)
  have hT : a.divisors.image (fun d => d * k) ⊆ (a * k).divisors := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    rw [Nat.mem_divisors] at hd ⊢
    exact ⟨Nat.mul_dvd_mul_right hd.1 k, hm0⟩
  have hdisj : Disjoint a.divisors (a.divisors.image (fun d => d * k)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx'
    have h1 := Nat.divisor_le hx
    have h2 : 0 < d := Nat.pos_of_mem_divisors hd
    have h3 : 1 * k ≤ d * k := Nat.mul_le_mul_right k h2
    omega
  have hcard : (a.divisors.image (fun d => d * k)).card = a.divisors.card :=
    Finset.card_image_of_injective _ (fun x y hxy => Nat.eq_of_mul_eq_mul_right hk0 hxy)
  calc 2 * a.divisors.card = (a.divisors ∪ a.divisors.image (fun d => d * k)).card := by
        rw [Finset.card_union_of_disjoint hdisj, hcard]
        ring
    _ ≤ (a * k).divisors.card := Finset.card_le_card (Finset.union_subset hS hT)

theorem three_le_card {m : ℕ} (hm : 2 ≤ m) (hp : ¬ m.Prime) : 3 ≤ m.divisors.card := by
  have hm1 : m ≠ 1 := by omega
  have hpr := Nat.minFac_prime hm1
  have hne : m.minFac ≠ m := fun h => hp (h ▸ hpr)
  have h1 : (1 : ℕ) ≠ m.minFac := fun h => hpr.ne_one h.symm
  have hsub : ({1, m.minFac, m} : Finset ℕ) ⊆ m.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Nat.mem_divisors]
    rcases hx with rfl | rfl | rfl
    · exact ⟨one_dvd _, by omega⟩
    · exact ⟨Nat.minFac_dvd _, by omega⟩
    · exact ⟨dvd_refl _, by omega⟩
  have hc : ({1, m.minFac, m} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hne]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1, by omega⟩
  rw [← hc]
  exact Finset.card_le_card hsub

theorem prime_of_card {q : ℕ} (hq : 2 ≤ q) (h : q.divisors.card ≤ 2) : q.Prime := by
  by_contra hp
  have := three_le_card hq hp
  omega

theorem coprime12 {q : ℕ} (hq : q % 6 = 5) : Nat.Coprime 12 q := by
  rw [Nat.Coprime, Nat.gcd_rec]
  have : q % 12 = 5 ∨ q % 12 = 11 := by omega
  rcases this with h | h <;> rw [h] <;> norm_num

theorem card_mul {j q : ℕ} (hj : j ∣ 12) (hq : q % 6 = 5) :
    (j * q).divisors.card = j.divisors.card * q.divisors.card :=
  Nat.Coprime.card_divisors_mul (Nat.Coprime.coprime_dvd_left hj (coprime12 hq))

theorem card_prime {p : ℕ} (hp : p.Prime) : p.divisors.card = 2 := by
  rw [hp.divisors, Finset.card_pair (fun h => hp.ne_one h.symm)]

theorem odd_sq_mod {p : ℕ} (hp : p % 2 = 1) : p * p % 8 = 1 := by
  have h := Nat.mul_mod p p 8
  have : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases this with h' | h' | h' | h' <;> rw [h'] at h <;> simpa using h

theorem small : ∀ n, n < 331 → 24 < n → ¬ ((n-1).divisors.card ≤ 3 ∧ (n-2).divisors.card ≤ 4 ∧
    (n-3).divisors.card ≤ 5 ∧ (n-4).divisors.card ≤ 6 ∧ (n-6).divisors.card ≤ 8 ∧
    (n-12).divisors.card ≤ 14) := by
  decide +kernel


theorem forward_mods (n : ℕ) (hn : 24 < n)
    (h1 : (n - 1).divisors.card ≤ 3) (h2 : (n - 2).divisors.card ≤ 4)
    (h3 : (n - 3).divisors.card ≤ 5) (h4 : (n - 4).divisors.card ≤ 6)
    (h6 : (n - 6).divisors.card ≤ 8) (h12 : (n - 12).divisors.card ≤ 14) :
    ∃ s : ℕ, 5 ≤ s ∧ n = 72 * s := by
  by_cases hs : n < 331
  · exact absurd ⟨h1, h2, h3, h4, h6, h12⟩ (small n hs hn)
  have d2 : (2 : ℕ).divisors.card = 2 := by decide
  have d3 : (3 : ℕ).divisors.card = 2 := by decide
  have d4 : (4 : ℕ).divisors.card = 3 := by decide
  have d6 : (6 : ℕ).divisors.card = 4 := by decide
  have d8 : (8 : ℕ).divisors.card = 4 := by decide
  have d9 : (9 : ℕ).divisors.card = 3 := by decide
  have d18 : (18 : ℕ).divisors.card = 6 := by decide
  have e2 : n % 2 = 0 := by
    by_contra hc
    have := two_mul_card_le (a := 2) (m := n - 1) (by omega) (by omega)
    omega
  have e4 : n % 4 = 0 := by
    by_contra hc
    have := two_mul_card_le (a := 4) (m := n - 2) (by omega) (by omega)
    omega
  have e3 : n % 3 = 0 := by
    by_contra hc
    rcases (by omega : n % 3 = 1 ∨ n % 3 = 2) with hr | hr
    · have := two_mul_card_le (a := 3) (m := n - 1) (by omega) (by omega)
      omega
    · have := two_mul_card_le (a := 6) (m := n - 2) (by omega) (by omega)
      omega
  have e8 : n % 8 = 0 := by
    by_contra hc
    have := two_mul_card_le (a := 8) (m := n - 4) (by omega) (by omega)
    omega
  have e9 : n % 9 = 0 := by
    by_contra hc
    rcases (by omega : n % 9 = 3 ∨ n % 9 = 6) with hr | hr
    · have := two_mul_card_le (a := 9) (m := n - 3) (by omega) (by omega)
      omega
    · have := two_mul_card_le (a := 18) (m := n - 6) (by omega) (by omega)
      omega
  exact ⟨n / 72, by omega, by omega⟩

theorem cofactor_prime (j q : ℕ) (hj : j ∣ 12) (hq : q % 6 = 5) (hq2 : 2 ≤ q)
    (hb : j.divisors.card * 3 > j + 2) (h : (j * q).divisors.card ≤ j + 2) : q.Prime := by
  rw [card_mul hj hq] at h
  apply prime_of_card hq2
  by_contra hc
  have : j.divisors.card * 3 ≤ j.divisors.card * q.divisors.card :=
    Nat.mul_le_mul_left _ (by omega)
  omega

theorem first_prime (q : ℕ) (hq : q % 8 = 7) (h : q.divisors.card ≤ 3) : q.Prime := by
  by_contra hp
  have hpos : 0 < q := by omega
  have hmp := Nat.minFac_prime (show q ≠ 1 by omega)
  have hsq := Nat.minFac_sq_le_self hpos hp
  rw [sq] at hsq
  rcases lt_or_eq_of_le hsq with hlt | heq
  · have := two_mul_card_le (Nat.minFac_dvd q) hlt
    rw [card_prime hmp] at this
    omega
  · have hodd : q.minFac % 2 = 1 := by
      by_contra hev
      have h2d : 2 ∣ q.minFac := by omega
      have := h2d.trans (Nat.minFac_dvd q)
      omega
    have := odd_sq_mod hodd
    omega

theorem not_dvd_prime {p q : ℕ} (hp : p.Prime) (hq : q ∣ p) (h1 : q ≠ 1) (h2 : q < p) : False := by
  rcases hp.eq_one_or_self_of_dvd q hq with h | h <;> omega

theorem forward (n : ℕ) (hn : 24 < n)
    (h : ∀ j ∈ ({1, 2, 3, 4, 6, 12} : Finset ℕ), (n - j).divisors.card ≤ j + 2) :
    ∃ t : ℕ, 0 < t ∧ n = 2520 * t ∧
      ∀ j ∈ ({1, 2, 3, 4, 6, 12} : Finset ℕ), ((2520 / j) * t - 1).Prime := by
  have h1 : (n - 1).divisors.card ≤ 3 := h 1 (by simp)
  have h2 : (n - 2).divisors.card ≤ 4 := h 2 (by simp)
  have h3 : (n - 3).divisors.card ≤ 5 := h 3 (by simp)
  have h4 : (n - 4).divisors.card ≤ 6 := h 4 (by simp)
  have h6 : (n - 6).divisors.card ≤ 8 := h 6 (by simp)
  have h12 : (n - 12).divisors.card ≤ 14 := h 12 (by simp)
  obtain ⟨s, hs5, rfl⟩ := forward_mods n hn h1 h2 h3 h4 h6 h12
  clear h hn
  have p1 : (72 * s - 1).Prime := first_prime _ (by omega) h1
  have p2 : (36 * s - 1).Prime := by
    rw [show 72 * s - 2 = 2 * (36 * s - 1) by omega] at h2
    exact cofactor_prime 2 _ (by norm_num) (by omega) (by omega) (by decide) h2
  have p3 : (24 * s - 1).Prime := by
    rw [show 72 * s - 3 = 3 * (24 * s - 1) by omega] at h3
    exact cofactor_prime 3 _ (by norm_num) (by omega) (by omega) (by decide) h3
  have p4 : (18 * s - 1).Prime := by
    rw [show 72 * s - 4 = 4 * (18 * s - 1) by omega] at h4
    exact cofactor_prime 4 _ (by norm_num) (by omega) (by omega) (by decide) h4
  have p6 : (12 * s - 1).Prime := by
    rw [show 72 * s - 6 = 6 * (12 * s - 1) by omega] at h6
    exact cofactor_prime 6 _ (by norm_num) (by omega) (by omega) (by decide) h6
  have p12 : (6 * s - 1).Prime := by
    rw [show 72 * s - 12 = 12 * (6 * s - 1) by omega] at h12
    exact cofactor_prime 12 _ (by norm_num) (by omega) (by omega) (by decide) h12
  clear h1 h2 h3 h4 h6 h12
  have e5 : s % 5 = 0 := by
    by_contra hc
    rcases (by omega : s % 5 = 1 ∨ s % 5 = 2 ∨ s % 5 = 3 ∨ s % 5 = 4) with hr | hr | hr | hr
    · exact not_dvd_prime p2 (q := 5) (by omega) (by omega) (by omega)
    · exact not_dvd_prime p4 (q := 5) (by omega) (by omega) (by omega)
    · exact not_dvd_prime p1 (q := 5) (by omega) (by omega) (by omega)
    · exact not_dvd_prime p3 (q := 5) (by omega) (by omega) (by omega)
  have e7 : s % 7 = 0 := by
    by_contra hc
    rcases (by omega : s % 7 = 1 ∨ s % 7 = 2 ∨ s % 7 = 3 ∨ s % 7 = 4 ∨ s % 7 = 5 ∨
      s % 7 = 6) with hr | hr | hr | hr | hr | hr
    · exact not_dvd_prime p2 (q := 7) (by omega) (by omega) (by omega)
    · exact not_dvd_prime p4 (q := 7) (by omega) (by omega) (by omega)
    · exact not_dvd_prime p6 (q := 7) (by omega) (by omega) (by omega)
    · exact not_dvd_prime p1 (q := 7) (by omega) (by omega) (by omega)
    · exact not_dvd_prime p3 (q := 7) (by omega) (by omega) (by omega)
    · exact not_dvd_prime p12 (q := 7) (by omega) (by omega) (by omega)
  obtain ⟨t, rfl⟩ : ∃ t, s = 35 * t := ⟨s / 35, by omega⟩
  refine ⟨t, by omega, by ring, ?_⟩
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show 2520 / 1 * t - 1 = 72 * (35 * t) - 1 by omega]; exact p1
  · rw [show 2520 / 2 * t - 1 = 36 * (35 * t) - 1 by omega]; exact p2
  · rw [show 2520 / 3 * t - 1 = 24 * (35 * t) - 1 by omega]; exact p3
  · rw [show 2520 / 4 * t - 1 = 18 * (35 * t) - 1 by omega]; exact p4
  · rw [show 2520 / 6 * t - 1 = 12 * (35 * t) - 1 by omega]; exact p6
  · rw [show 2520 / 12 * t - 1 = 6 * (35 * t) - 1 by omega]; exact p12

theorem backward (t : ℕ) (ht : 0 < t)
    (hp : ∀ j ∈ ({1, 2, 3, 4, 6, 12} : Finset ℕ), ((2520 / j) * t - 1).Prime) :
    ∀ j ∈ ({1, 2, 3, 4, 6, 12} : Finset ℕ), (2520 * t - j).divisors.card ≤ j + 2 := by
  intro j hj
  have hpj := hp j hj
  have hj12 : j ∣ 12 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hq : ((2520 / j) * t - 1) % 6 = 5 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have heq : 2520 * t - j = j * ((2520 / j) * t - 1) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  rw [heq, card_mul hj12 hq, card_prime hpj]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos647_erdos_647_variants_infinite_R1.H2 := by
  unfold OMA.R_Erdos647_erdos_647_variants_infinite_R1.H2
  intro n hn
  constructor
  · exact OMA.Helpers.forward n hn
  · rintro ⟨t, ht, rfl, hp⟩
    exact OMA.Helpers.backward t ht hp
