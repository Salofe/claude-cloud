import OMAStatements.S_oeis_a074915
import Mathlib

/-!
Proof that, for every n, the set of x whose reduced residue system contains exactly n nonprimes
is bounded (OEIS A074915).

Let p be the smallest prime not dividing x. The numbers 1, p^2, p^3, ..., p^N are N distinct
nonprimes coprime to x, so as soon as p^N <= x the count is at least N. If p^N > x, then every
prime below p divides x; choosing for each i < j a Bertrand prime in (2^i, 2^(i+1)], where
2^j <= p - 1 < 2^(j+1), gives a divisor of x of size at least 2^(j(j-1)/2), while
x < p^N <= 2^((j+1)N). This forces j <= 2N + 2, hence x < 2^((2N+3)N). So for
x > 2^((2N+3)N) the count is at least N, and with N = n + 1 every x with count n is at most
2^((2n+5)(n+1)).
-/

namespace OMA.Helpers
open OMA.S_oeis_a074915

/-- Powers `p ^ k` with `k = 0` or `2 ≤ k ≤ N` of a prime `p` not dividing `x`, with `p ^ N ≤ x`,
are `N` distinct nonprimes of the reduced residue system of `x`. -/
theorem q_count (x p N : ℕ) (hx : 0 < x) (hp : p.Prime) (hpx : ¬ p ∣ x) (hN : p ^ N ≤ x) :
    N ≤ nonprimeRRSCount x := by
  have hp2 := hp.two_le
  have hsub : (insert 0 (Finset.Icc 2 N)).image (fun k => p ^ k) ⊆
      (Finset.Icc 1 x).filter (fun k => Nat.Coprime k x ∧ ¬ Nat.Prime k) := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨k, hk, rfl⟩ := hm
    have hkN : k = 0 ∨ (2 ≤ k ∧ k ≤ N) := by
      rcases Finset.mem_insert.1 hk with h | h
      · left; exact h
      · right; exact Finset.mem_Icc.1 h
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.one_le_pow _ _ (by omega), ?_⟩, Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.2 hpx), ?_⟩
    · rcases hkN with h | h
      · rw [h, pow_zero]; omega
      · exact le_trans (Nat.pow_le_pow_right (by omega) h.2) hN
    · rcases hkN with h | h
      · rw [h, pow_zero]; exact Nat.not_prime_one
      · intro hq
        rcases hq.eq_one_or_self_of_dvd p (dvd_pow_self p (by omega)) with h1 | h1
        · omega
        · have : p ^ 1 < p ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
          rw [pow_one] at this; omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (Nat.pow_right_injective hp2)] at hcard
  have h0 : (0 : ℕ) ∉ Finset.Icc 2 N := by simp
  rw [Finset.card_insert_of_notMem h0, Nat.card_Icc] at hcard
  unfold nonprimeRRSCount
  omega

/-- If every prime `q ≤ 2 ^ j` divides `x`, then `x` has a divisor at least `2 ^ (0 + 1 + ... + (j-1))`
(a product of Bertrand primes, one in each interval `(2 ^ i, 2 ^ (i+1)]`). -/
theorem q_bertrand (x : ℕ) : ∀ j : ℕ, (∀ q : ℕ, q.Prime → q ≤ 2 ^ j → q ∣ x) →
    ∃ d, d ∣ x ∧ 2 ^ (∑ i ∈ Finset.range j, i) ≤ d ∧ ∀ q : ℕ, q.Prime → q ∣ d → q ≤ 2 ^ j := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨1, one_dvd _, by simp, ?_⟩
    intro q hq hd
    exact absurd (Nat.le_of_dvd one_pos hd) (by have := hq.two_le; omega)
  | succ j ih =>
    intro h
    obtain ⟨d, hdx, hdb, hdp⟩ := ih (fun q hq hle => h q hq (le_trans hle
      (Nat.pow_le_pow_right (by norm_num) (by omega))))
    obtain ⟨q, hq, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ j) (by positivity)
    have hle' : q ≤ 2 ^ (j + 1) := by rw [pow_succ]; omega
    have hqx := h q hq hle'
    have hco : Nat.Coprime d q := by
      rw [Nat.coprime_comm, hq.coprime_iff_not_dvd]
      intro hqd
      have := hdp q hq hqd
      omega
    refine ⟨d * q, Nat.Coprime.mul_dvd_of_dvd_of_dvd hco hdx hqx, ?_, ?_⟩
    · rw [Finset.sum_range_succ, pow_add]
      exact Nat.mul_le_mul hdb hlt.le
    · intro r hr hrd
      rcases (Nat.Prime.dvd_mul hr).1 hrd with h1 | h1
      · exact le_trans (hdp r hr h1) (Nat.pow_le_pow_right (by norm_num) (by omega))
      · rw [(Nat.prime_dvd_prime_iff_eq hr hq).1 h1]; exact hle'

/-- Main estimate: for `x > 2 ^ ((2N+3) N)` the count is at least `N`. -/
theorem q_main (N x : ℕ) (hN : 1 ≤ N) (hx : 2 ^ ((2 * N + 3) * N) < x) : N ≤ nonprimeRRSCount x := by
  have hx0 : 0 < x := lt_of_le_of_lt (Nat.zero_le _) hx
  have hex : ∃ p, p.Prime ∧ ¬ p ∣ x := by
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (x + 1)
    exact ⟨p, hp2, fun h => absurd (Nat.le_of_dvd hx0 h) (by omega)⟩
  classical
  set p := Nat.find hex with hpdef
  have hpspec : p.Prime ∧ ¬ p ∣ x := Nat.find_spec hex
  have hmin : ∀ q, q.Prime → q < p → q ∣ x := by
    intro q hq hlt
    have := Nat.find_min hex hlt
    by_contra hnd
    exact this ⟨hq, hnd⟩
  apply q_count x p N hx0 hpspec.1 hpspec.2
  by_contra hlt
  push Not at hlt
  -- p is large
  have hbig : 2 ^ (2 * N + 3) < p := by
    by_contra hle
    push Not at hle
    have : p ^ N ≤ (2 ^ (2 * N + 3)) ^ N := Nat.pow_le_pow_left hle N
    rw [← pow_mul] at this
    exact absurd (hx.trans (hlt.trans_le this)) (lt_irrefl _)
  have hpos : 0 < 2 ^ (2 * N + 3) := by positivity
  set j := Nat.log 2 (p - 1) with hj
  have hj1 : 2 ^ j ≤ p - 1 := Nat.pow_log_le_self 2 (by omega)
  have hj2 : p - 1 < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) (p - 1)
  obtain ⟨d, hdx, hdb, -⟩ := q_bertrand x j (fun q hq hle => hmin q hq (by omega))
  have hdle : d ≤ x := Nat.le_of_dvd hx0 hdx
  have hpj : p ≤ 2 ^ (j + 1) := by omega
  have hup : p ^ N ≤ 2 ^ ((j + 1) * N) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hpj N
  have hlt2 : 2 ^ (∑ i ∈ Finset.range j, i) < 2 ^ ((j + 1) * N) := by omega
  have hexp : (∑ i ∈ Finset.range j, i) < (j + 1) * N :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt2
  have hjb : 2 * N + 3 < j + 1 := by
    have : 2 ^ (2 * N + 3) < 2 ^ (j + 1) := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
  have hgauss := Finset.sum_range_id_mul_two j
  have h2 : j * (j - 1) < 2 * ((j + 1) * N) := by omega
  clear_value j
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [show k + 1 - 1 = k by omega] at h2
  nlinarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a074915.main := by
  intro n
  refine ⟨2 ^ ((2 * (n + 1) + 3) * (n + 1)), ?_⟩
  intro x hx
  obtain ⟨hx0, hc⟩ := hx
  by_contra h
  push Not at h
  have := OMA.Helpers.q_main (n + 1) x (by omega) h
  omega
