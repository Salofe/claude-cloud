import OMAStatements.S_oeis_a067567
import Mathlib

namespace OMA.Helpers

open Finset OMA.S_oeis_a067567

theorem b_eq_range (m N : ℕ) :
    b m N = ∑ k ∈ range (N + 1), k ^ (2 * m + 1) * p k * p (N - k) := by
  unfold b
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega),
    Finset.Ico_add_one_right_eq_Icc]
  simp

theorem two_mul_b (m N : ℕ) :
    2 * b m N = ∑ k ∈ range (N + 1),
      (k ^ (2 * m + 1) + (N - k) ^ (2 * m + 1)) * (p k * p (N - k)) := by
  rw [b_eq_range, two_mul]
  conv_lhs => arg 2; rw [← Finset.sum_range_reflect]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ N := by simpa [Nat.lt_succ_iff] using hk
  have h1 : N + 1 - 1 - k = N - k := by omega
  have h2 : N - (N - k) = k := by omega
  rw [h1, h2]
  ring

theorem dvd_term (m N k : ℕ) (hk : k ≤ N) :
    N ∣ k ^ (2 * m + 1) + (N - k) ^ (2 * m + 1) := by
  have h : k + (N - k) ∣ k ^ (2 * m + 1) + (N - k) ^ (2 * m + 1) :=
    Odd.nat_add_dvd_pow_add_pow k (N - k) ⟨m, rfl⟩
  have e : k + (N - k) = N := by omega
  rwa [e] at h

theorem part1 (m N : ℕ) (hN : Odd N) : N ∣ b m N := by
  have h : N ∣ 2 * b m N := by
    rw [two_mul_b]
    refine Finset.dvd_sum fun k hk => ?_
    have hk' : k ≤ N := by simpa [Nat.lt_succ_iff] using hk
    exact Dvd.dvd.mul_right (dvd_term m N k hk') _
  have hc : Nat.Coprime N 2 := by
    exact Nat.coprime_two_right.mpr hN
  exact hc.dvd_of_dvd_mul_left h

theorem split_even (m n : ℕ) :
    b m (2 * n) = n ^ (2 * m + 1) * p n * p n + ∑ k ∈ range n,
      (k ^ (2 * m + 1) + (2 * n - k) ^ (2 * m + 1)) * (p k * p (2 * n - k)) := by
  rw [b_eq_range]
  have e : 2 * n + 1 = (n + 1) + n := by omega
  rw [e, Finset.sum_range_add, Finset.sum_range_succ]
  rw [← Finset.sum_range_reflect (fun x => (n + 1 + x) ^ (2 * m + 1) * p (n + 1 + x) *
    p (2 * n - (n + 1 + x))) n]
  have h3 : 2 * n - n = n := by omega
  rw [h3, add_comm (∑ x ∈ range n, _) _, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < n := by simpa using hk
  have h1 : n + 1 + (n - 1 - k) = 2 * n - k := by omega
  have h2 : 2 * n - (2 * n - k) = k := by omega
  simp only [h1, h2]
  ring

theorem key_eq (m n : ℕ) (hn : 1 ≤ n) :
    b m (2 * n) = n * (n ^ (2 * m) * p n * p n + 2 * ∑ k ∈ range n,
      (k ^ (2 * m + 1) + (2 * n - k) ^ (2 * m + 1)) / (2 * n) * (p k * p (2 * n - k))) := by
  rw [split_even, mul_add, Finset.mul_sum, Finset.mul_sum]
  have hs : ∀ k ∈ range n, (k ^ (2 * m + 1) + (2 * n - k) ^ (2 * m + 1)) * (p k * p (2 * n - k)) =
      n * (2 * ((k ^ (2 * m + 1) + (2 * n - k) ^ (2 * m + 1)) / (2 * n) *
        (p k * p (2 * n - k)))) := by
    intro k hk
    have hk' : k ≤ 2 * n := by have := Finset.mem_range.mp hk; omega
    obtain ⟨c, hc⟩ := dvd_term m (2 * n) k hk'
    rw [hc, Nat.mul_div_cancel_left _ (by omega)]
    ring
  rw [Finset.sum_congr rfl hs]
  have hp : n ^ (2 * m + 1) * p n * p n = n * (n ^ (2 * m) * p n * p n) := by ring
  rw [hp]

theorem part2 (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    n ∣ b m (2 * n) ∧ (Odd (b m (2 * n) / n) ↔ Odd n ∧ Odd (p n)) := by
  have key := key_eq m n hn
  generalize hQ : (∑ k ∈ range n, (k ^ (2 * m + 1) + (2 * n - k) ^ (2 * m + 1)) / (2 * n) *
      (p k * p (2 * n - k))) = Q at key
  generalize hP : p n = P at key ⊢
  generalize hB : b m (2 * n) = B at key ⊢
  refine ⟨⟨_, key⟩, ?_⟩
  rw [key, Nat.mul_div_cancel_left _ (by omega)]
  have hm2 : 2 * m ≠ 0 := by omega
  rw [Nat.odd_add, Nat.odd_mul, Nat.odd_mul, Nat.odd_pow_iff hm2]
  simp only [even_two_mul Q, iff_true, and_assoc, and_self]

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a067567.main := by
  intro m hm
  exact ⟨fun n _ hodd => part1 m n hodd, fun n hn => part2 m n hm hn⟩
