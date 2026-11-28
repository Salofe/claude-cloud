import OMAStatements.S_oeis_a309291
import Mathlib

namespace OMA.Helpers

theorem a309291_fact_gt (k : ℕ) (hk : 5 ≤ k) : k ^ 2 + k < Nat.factorial k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    rw [Nat.factorial_succ]
    nlinarith

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a309291.main := by
  intro k hk q hq hlo hhi
  have hf := OMA.Helpers.a309291_fact_gt k hk
  have hqk : k < q := by omega
  have hpk : k ≤ Nat.factorial k - q := by omega
  have hpk2 : Nat.factorial k - q ≤ k ^ 2 := by omega
  by_contra hnp
  set p := Nat.factorial k - q with hp
  have hp0 : 0 < p := by omega
  have hp1 : p ≠ 1 := by omega
  have hr := Nat.minFac_prime hp1
  have hsq := Nat.minFac_sq_le_self hp0 hnp
  have hrk : Nat.minFac p ≤ k := by
    by_contra h
    push_neg at h
    have : k ^ 2 < Nat.minFac p ^ 2 := Nat.pow_lt_pow_left h (by norm_num)
    omega
  have h1 : Nat.minFac p ∣ Nat.factorial k := Nat.dvd_factorial hr.pos hrk
  have h2 : Nat.minFac p ∣ p := Nat.minFac_dvd p
  have h3 : Nat.minFac p ∣ q := by
    have hq' : q = Nat.factorial k - p := by omega
    rw [hq']
    exact Nat.dvd_sub h1 h2
  have h4 : Nat.minFac p = q := ((Nat.prime_dvd_prime_iff_eq hr hq).mp h3)
  omega
