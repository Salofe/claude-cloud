import OMAReductions.R_Erdos408_erdos_408_parts_ii_R1

/-!
# Step H1 of the reduction Erdos408.erdos_408.parts.ii.R1

Write `f n` for the least `k ≥ 1` with `φ^[k] n = 1` (the upstream `Erdos408.f`), and give each
prime `p` the weight `w p = 1` if `p = 2` and `w p = f p - 1` otherwise. The additive height is
`F n = ∑ p ∣ n, v_p(n) * w p`, the function `F` in the statement of H1. We prove the exact
identity `f n = F n + n % 2` for every `n ≥ 1`, which gives `|f n - F n| ≤ 1`.

Proof sketch.
* For `n ≥ 1` some iterate of `φ` reaches `1` (since `φ n < n` for `n > 1`), so `f n ≥ 1` and
  `φ^[f n] n = 1`; for `n ≥ 3` this gives the recursion `f n = f (φ n) + 1`, because `φ n ≠ 1`.
* `F` is completely additive on positive integers (`F (a * b) = F a + F b`), `F (p ^ k) = k * w p`
  and `F 1 = 0`.
* Euler's product `φ n = ∏ p ^ (v_p(n) - 1) * (p - 1)` then gives
  `F (φ n) + [2 ∣ n] = F n` as soon as `F (p - 1) = w p` for every odd prime `p ∣ n`.
* By strong induction on `n`: for `n ≥ 3`, `φ n` is even, smaller than `n`, and positive, so
  `f (φ n) = F (φ n)`; for an odd prime `p ∣ n`, the induction hypothesis at the even number
  `p - 1 < n` and the recursion at `p` give `F (p - 1) = f (p - 1) = f p - 1 = w p`.

Only the upstream definition `Erdos408.f`, Mathlib, and the helper lemmas below are used.
-/

namespace OMA.Helpers

open Erdos408

/-- The weight of a prime `p` in the additive height: `1` for `p = 2`, else `f p - 1`. -/
noncomputable def wt408 (p : ℕ) : ℕ := if p = 2 then 1 else f p - 1

/-- The additive height of `n`. -/
noncomputable def ht408 (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, n.factorization p * wt408 p

theorem ht408_eq_sum (n : ℕ) : ht408 n = n.factorization.sum (fun p k => k * wt408 p) := rfl

theorem ht408_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : ht408 (a * b) = ht408 a + ht408 b := by
  rw [ht408_eq_sum, ht408_eq_sum, ht408_eq_sum, Nat.factorization_mul ha hb]
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem ht408_one : ht408 1 = 0 := by simp [ht408]

theorem ht408_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : ht408 (p ^ k) = k * wt408 p := by
  rw [ht408_eq_sum, hp.factorization_pow, Finsupp.sum_single_index (zero_mul _)]

theorem ht408_prod {ι : Type*} (s : Finset ι) (g : ι → ℕ) (hg : ∀ i ∈ s, g i ≠ 0) :
    ht408 (∏ i ∈ s, g i) = ∑ i ∈ s, ht408 (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ht408_one]
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, g i ≠ 0 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ht408_mul (hg a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.mpr hs), ih hs]

theorem ht408_totient {n : ℕ} (hn : n ≠ 0)
    (hw : ∀ p, p.Prime → p ∣ n → p ≠ 2 → ht408 (p - 1) = wt408 p) :
    ht408 (Nat.totient n) + (if 2 ∣ n then 1 else 0) = ht408 n := by
  have hne : ∀ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p - 1) ≠ 0 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    exact mul_ne_zero (pow_ne_zero _ hpp.ne_zero) (by have := hpp.two_le; omega)
  rw [Nat.totient_eq_prod_factorization hn, Finsupp.prod, Nat.support_factorization,
    ht408_prod _ _ hne]
  have h2 : (if 2 ∣ n then 1 else 0) = ∑ p ∈ n.primeFactors, (if p = 2 then 1 else 0) := by
    rw [Finset.sum_ite_eq']
    simp [Nat.mem_primeFactors, Nat.prime_two, hn]
  rw [h2, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have ha : 1 ≤ n.factorization p := hpp.factorization_pos_of_dvd hn hpn
  have hp1 : p - 1 ≠ 0 := by have := hpp.two_le; omega
  rw [ht408_mul (pow_ne_zero _ hpp.ne_zero) hp1, ht408_prime_pow hpp]
  obtain ⟨b, hb⟩ : ∃ b, n.factorization p = b + 1 := ⟨n.factorization p - 1, by omega⟩
  rw [hb, Nat.add_sub_cancel]
  by_cases hp2 : p = 2
  · subst hp2
    simp [wt408, ht408_one]
  · rw [hw p hpp hpn hp2, if_neg hp2]
    ring

theorem totient_iterate_exists (n : ℕ) (hn : 1 ≤ n) : ∃ k, 1 ≤ k ∧ Nat.totient^[k] n = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      exact ⟨1, le_rfl, by simp⟩
    · obtain ⟨k, hk1, hk⟩ := ih (Nat.totient n) (Nat.totient_lt n (by omega))
        (Nat.totient_pos.mpr (by omega))
      exact ⟨k + 1, by omega, by rw [Function.iterate_succ_apply]; exact hk⟩

theorem f_spec (n : ℕ) (hn : 1 ≤ n) : 1 ≤ f n ∧ Nat.totient^[f n] n = 1 :=
  Nat.sInf_mem (s := {k : ℕ | 1 ≤ k ∧ Nat.totient^[k] n = 1}) (totient_iterate_exists n hn)

theorem f_le_of {n k : ℕ} (hk : 1 ≤ k) (h : Nat.totient^[k] n = 1) : f n ≤ k :=
  Nat.sInf_le ⟨hk, h⟩

theorem f_one_eq : f 1 = 1 :=
  le_antisymm (f_le_of le_rfl (by simp)) (f_spec 1 le_rfl).1

theorem f_two_eq : f 2 = 1 :=
  le_antisymm (f_le_of le_rfl (by simp)) (f_spec 2 (by norm_num)).1

theorem f_rec {n : ℕ} (hn : 3 ≤ n) : f n = f (Nat.totient n) + 1 := by
  have hφ : 1 ≤ Nat.totient n := Nat.totient_pos.mpr (by omega)
  obtain ⟨h1, h2⟩ := f_spec (Nat.totient n) hφ
  obtain ⟨h3, h4⟩ := f_spec n (by omega)
  apply le_antisymm
  · apply f_le_of (by omega)
    rw [Function.iterate_succ_apply]
    exact h2
  · have hne : f n ≠ 1 := by
      intro h
      rw [h, Function.iterate_one, Nat.totient_eq_one_iff] at h4
      omega
    have h5 : Nat.totient^[f n - 1] (Nat.totient n) = 1 := by
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel h3]
      exact h4
    have := f_le_of (n := Nat.totient n) (by omega) h5
    omega

theorem ht408_two : ht408 2 = 1 := by
  have h := ht408_prime_pow Nat.prime_two 1
  simpa [wt408] using h

theorem f_eq_ht408 (n : ℕ) (hn : 1 ≤ n) : f n = ht408 n + n % 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | h3
    · rw [f_one_eq, ht408_one]
    · rw [f_two_eq, ht408_two]
    · have hlt : Nat.totient n < n := Nat.totient_lt n (by omega)
      have hev : Even (Nat.totient n) := Nat.totient_even (by omega)
      have hpos : 1 ≤ Nat.totient n := Nat.totient_pos.mpr (by omega)
      have ihφ := ih _ hlt hpos
      have hmod : Nat.totient n % 2 = 0 := Nat.even_iff.mp hev
      have hw : ∀ p, p.Prime → p ∣ n → p ≠ 2 → ht408 (p - 1) = wt408 p := by
        intro p hp hpn hp2
        have hp3 : 3 ≤ p := by have := hp.two_le; omega
        have hple : p ≤ n := Nat.le_of_dvd (by omega) hpn
        have hodd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
        have ihp := ih (p - 1) (by omega) (by omega)
        have hfp := f_rec hp3
        rw [Nat.totient_prime hp] at hfp
        simp only [wt408, if_neg hp2]
        omega
      have key := ht408_totient (by omega : n ≠ 0) hw
      rw [f_rec h3, ihφ, hmod]
      split_ifs at key with h2 <;> omega

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos408_erdos_408_parts_ii_R1.H1 := by
  show ∀ n : ℕ, 1 ≤ n → |(Erdos408.f n : ℝ) - (ht408 n : ℝ)| ≤ 1
  intro n hn
  rw [f_eq_ht408 n hn, Nat.cast_add, add_sub_cancel_left,
    abs_of_nonneg (Nat.cast_nonneg _)]
  have h : n % 2 ≤ 1 := by omega
  exact_mod_cast h
