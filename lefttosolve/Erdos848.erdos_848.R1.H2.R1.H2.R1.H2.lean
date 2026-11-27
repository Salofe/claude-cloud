import OMAReductions.R_Erdos848_erdos_848_R1_H2_R1_H2_R1
import Mathlib

/-!
# Step H2 of the reduction Erdos848.erdos_848.R1.H2.R1.H2.R1

For `N ≥ 2 ^ 2300`, `b ≡ 7` and `b' ≡ 18 (mod 25)`, the classes `a ≡ 18` and `a ≡ 7 (mod 25)`
give `a * b + 1 ≡ 2 (mod 5)`, so a non-squarefree value `a * b + 1 ≤ N ^ 2 + 1` is divisible by
`p ^ 2` for a prime `p ≤ N` with `p ≠ 5` and `p` coprime to `b`. Those `a` lie in one class
modulo `25 * p ^ 2`, hence there are at most `N / (25 * p ^ 2) + 1` of them. Summing,
`sum 1 / p ^ 2 < 11 / 25` (explicit small primes plus a telescoping tail), and the number of
primes up to `N` is controlled by `primorial N ≤ 4 ^ N`. Both sides together stay below
`N / 25`, which is at most the size of the class of 7 modulo 25 in `[1, N]`.
-/

namespace OMA.Helpers
open Finset

/-- Naturals in `[0, N]` that are pairwise congruent modulo `m` are at most `N / m + 1`. -/
theorem card_le_of_modEq (N m : ℕ) (s : Finset ℕ) (hs : ∀ a ∈ s, a ≤ N)
    (hc : ∀ a ∈ s, ∀ a' ∈ s, a % m = a' % m) : s.card ≤ N / m + 1 := by
  have h := Finset.card_le_card_of_injOn (fun a => a / m) (s := s) (t := range (N / m + 1)) ?_ ?_
  · simpa using h
  · intro a ha
    have h1 := Nat.div_le_div_right (c := m) (hs a (Finset.mem_coe.1 ha))
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  · intro a ha a' ha' he
    have h1 := hc a (Finset.mem_coe.1 ha) a' (Finset.mem_coe.1 ha')
    simp only at he
    rw [← Nat.div_add_mod a m, ← Nat.div_add_mod a' m, he, h1]

/-- For a prime `p ≠ 5`, the elements `a` of a residue class modulo 25 with
`p ^ 2 ∣ a * b + 1` are pairwise congruent modulo `25 * p ^ 2`. -/
theorem card_primeSq_le (N b r p : ℕ) (hp : p.Prime) (hp5 : p ≠ 5) :
    ((Icc 1 N).filter (fun a => a % 25 = r ∧ p ^ 2 ∣ a * b + 1)).card ≤
      N / (25 * p ^ 2) + 1 := by
  apply card_le_of_modEq N (25 * p ^ 2)
  · intro a ha
    simp only [mem_filter, mem_Icc] at ha
    exact ha.1.2
  · intro a ha a' ha'
    simp only [mem_filter, mem_Icc] at ha ha'
    have hpb : ¬ p ∣ b := by
      intro h
      have h1 : p ∣ a * b + 1 := (dvd_pow_self p two_ne_zero).trans ha.2.2
      have h2 : p ∣ a * b := dvd_mul_of_dvd_right h a
      exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h2).1 h1))
    have hcop : Nat.gcd (p ^ 2) b = 1 :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpb)
    have hmod : a * b ≡ a' * b [MOD p ^ 2] := by
      have : a * b + 1 ≡ a' * b + 1 [MOD p ^ 2] :=
        (Nat.modEq_zero_iff_dvd.2 ha.2.2).trans (Nat.modEq_zero_iff_dvd.2 ha'.2.2).symm
      exact Nat.ModEq.add_right_cancel' 1 this
    have hp2 : a ≡ a' [MOD p ^ 2] := Nat.ModEq.cancel_right_of_coprime hcop hmod
    have h25 : a ≡ a' [MOD 25] := (ha.2.1.trans ha'.2.1.symm : a % 25 = a' % 25)
    have hc : Nat.Coprime 25 (p ^ 2) := by
      have : Nat.Coprime 5 p := (Nat.coprime_primes (by norm_num) hp).2 (Ne.symm hp5)
      simpa using Nat.Coprime.pow 2 2 this
    exact (Nat.modEq_and_modEq_iff_modEq_mul hc).1 ⟨h25, hp2⟩

/-- Union bound over the prime squares dividing `a * b + 1`. -/
theorem side_bound (N b r : ℕ) (hbN : b ≤ N) (h5 : ∀ a, a % 25 = r → ¬ 5 ∣ a * b + 1)
    (s : Finset ℕ) (hs : ∀ a ∈ s, a ∈ Icc 1 N ∧ a % 25 = r ∧ ¬ Squarefree (a * b + 1)) :
    s.card ≤ ∑ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 5),
      (N / (25 * p ^ 2) + 1) := by
  have hsub : s ⊆ ((range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 5)).biUnion
      (fun p => (Icc 1 N).filter (fun a => a % 25 = r ∧ p ^ 2 ∣ a * b + 1)) := by
    intro a ha
    obtain ⟨hI, hr, hsq⟩ := hs a ha
    rw [Nat.squarefree_iff_prime_squarefree] at hsq
    push Not at hsq
    obtain ⟨p, hp, hpd⟩ := hsq
    rw [mem_biUnion]
    refine ⟨p, ?_, ?_⟩
    · rw [mem_filter, mem_range]
      refine ⟨?_, hp, ?_⟩
      · have hle := Nat.le_of_dvd (Nat.succ_pos _) hpd
        have ha' := (mem_Icc.1 hI).2
        have : a * b ≤ N * N := Nat.mul_le_mul ha' hbN
        have ha1 := (mem_Icc.1 hI).1
        by_contra hc
        push Not at hc
        have h2 := Nat.mul_le_mul hc hc
        simp only [Nat.succ_eq_add_one] at hle
        nlinarith
      · rintro rfl
        exact h5 a hr ((dvd_mul_right 5 5).trans hpd)
    · rw [mem_filter]
      exact ⟨hI, hr, by rw [pow_two]; exact hpd⟩
  calc s.card ≤ _ := card_le_card hsub
    _ ≤ ∑ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 5),
          ((Icc 1 N).filter (fun a => a % 25 = r ∧ p ^ 2 ∣ a * b + 1)).card := card_biUnion_le
    _ ≤ _ := sum_le_sum (fun p hp =>
          card_primeSq_le N b r p (mem_filter.1 hp).2.1 (mem_filter.1 hp).2.2)

/-- Chebyshev-type count from `primorial N ≤ 4 ^ N`: at most `2 ^ k` primes lie below `2 ^ k`
and at most `2 N / k` primes in `[2 ^ k, N]`. -/
theorem card_primes_le (N k : ℕ) :
    ((range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 5)).card * k ≤ 2 ^ k * k + 2 * N := by
  set P := (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 5) with hP
  have hsplit := card_filter_add_card_filter_not (s := P) (fun p => p < 2 ^ k)
  have hsmall : (P.filter (fun p => p < 2 ^ k)).card ≤ 2 ^ k := by
    calc _ ≤ (range (2 ^ k)).card := card_le_card (fun p hp => by
            simp only [mem_filter, mem_range] at hp ⊢; exact hp.2)
      _ = 2 ^ k := card_range _
  have hlarge : (P.filter (fun p => ¬ p < 2 ^ k)).card * k ≤ 2 * N := by
    set L := P.filter (fun p => ¬ p < 2 ^ k) with hL
    have h1 : (2 ^ k) ^ L.card ≤ ∏ p ∈ L, p :=
      Finset.pow_card_le_prod L (fun p => p) (2 ^ k) (fun p hp => by
        simp only [hL, hP, mem_filter] at hp; omega)
    have h2 : ∏ p ∈ L, p ≤ primorial N := by
      unfold primorial
      apply Finset.prod_le_prod_of_subset_of_one_le'
      · intro p hp
        simp only [hL, hP, mem_filter] at hp
        simp only [mem_filter]
        exact ⟨hp.1.1, hp.1.2.1⟩
      · intro p hp _
        simp only [mem_filter] at hp
        exact hp.2.one_lt.le
    have h3 := primorial_le_four_pow N
    have h4 : 2 ^ (k * L.card) ≤ 2 ^ (2 * N) := by
      rw [pow_mul, pow_mul]
      calc (2 ^ k) ^ L.card ≤ _ := h1
        _ ≤ _ := h2
        _ ≤ 4 ^ N := h3
        _ = (2 ^ 2) ^ N := by norm_num
    have := (pow_le_pow_iff_right₀ (by norm_num : (1:ℕ) < 2)).1 h4
    rw [mul_comm] at this
    exact this
  have : P.card * k = (P.filter (fun p => p < 2 ^ k)).card * k +
      (P.filter (fun p => ¬ p < 2 ^ k)).card * k := by rw [← add_mul, hsplit]
  rw [this]
  have := Nat.mul_le_mul_right k hsmall
  omega

/-- Telescoping bound for the tail of the series of inverse squares. -/
theorem tail_inv_sq (k M : ℕ) (hk : 2 ≤ k) (hkM : k ≤ M) :
    ∑ n ∈ Ico k M, (1:ℝ) / (n:ℝ) ^ 2 ≤ 1 / ((k:ℝ) - 1) - 1 / ((M:ℝ) - 1) := by
  induction M, hkM using Nat.le_induction with
  | base => simp
  | succ M hkM ih =>
    rw [Finset.sum_Ico_succ_top hkM]
    have hM : (2:ℝ) ≤ M := by exact_mod_cast hk.trans hkM
    have e : ((M + 1 : ℕ) : ℝ) - 1 = M := by push_cast; ring
    rw [e]
    have key : (1:ℝ) / (M:ℝ) ^ 2 ≤ 1 / ((M:ℝ) - 1) - 1 / (M:ℝ) := by
      rw [div_sub_div _ _ (by linarith) (by linarith),
        div_le_div_iff₀ (by positivity) (by nlinarith)]
      nlinarith
    linarith

/-- The sum of `1 / p ^ 2` over primes `p ≠ 5` is below `11 / 25`. -/
theorem sum_inv_sq_primes (N : ℕ) :
    ∑ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 5), (1:ℝ) / (p:ℝ) ^ 2 ≤ 11 / 25 := by
  have hsub : (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 5) ⊆
      ({2, 3, 7, 11, 13, 17, 19, 23} : Finset ℕ) ∪ Ico 29 (N + 30) := by
    intro p hp
    simp only [mem_filter, mem_range] at hp
    obtain ⟨hpN, hp, hp5⟩ := hp
    rw [mem_union, mem_Ico]
    by_cases h : 29 ≤ p
    · right; omega
    · left
      push Not at h
      interval_cases p <;> first | exact absurd rfl hp5 | decide | (exfalso; norm_num at hp)
  have hdisj : Disjoint ({2, 3, 7, 11, 13, 17, 19, 23} : Finset ℕ) (Ico 29 (N + 30)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [mem_insert, mem_singleton] at hx
    rw [mem_Ico] at hx'
    omega
  calc _ ≤ ∑ p ∈ ({2, 3, 7, 11, 13, 17, 19, 23} : Finset ℕ) ∪ Ico 29 (N + 30),
        (1:ℝ) / (p:ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ p ∈ ({2, 3, 7, 11, 13, 17, 19, 23} : Finset ℕ), (1:ℝ) / (p:ℝ) ^ 2 +
        ∑ p ∈ Ico 29 (N + 30), (1:ℝ) / (p:ℝ) ^ 2 := sum_union hdisj
    _ ≤ ∑ p ∈ ({2, 3, 7, 11, 13, 17, 19, 23} : Finset ℕ), (1:ℝ) / (p:ℝ) ^ 2 +
        (1 / (((29:ℕ):ℝ) - 1) - 1 / (((N + 30 : ℕ):ℝ) - 1)) :=
        add_le_add le_rfl (tail_inv_sq 29 (N + 30) (by norm_num) (by omega))
    _ ≤ 11 / 25 := by
      norm_num [Finset.sum_insert, Finset.sum_singleton]
      have : (0:ℝ) ≤ ((N:ℝ) + 30 - 1)⁻¹ :=
        inv_nonneg.2 (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])
      linarith

/-- The total bound for both sides is at most `N / 25` once `N ≥ 2 ^ 2300`. -/
theorem two_T_le (N : ℕ) (hN : 2 ^ 2300 ≤ N) :
    2 * ∑ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 5), (N / (25 * p ^ 2) + 1) ≤
      N / 25 := by
  have hcard := card_primes_le N 2000
  have hinv := sum_inv_sq_primes N
  set P := (range (N + 1)).filter (fun p => p.Prime ∧ p ≠ 5) with hP
  rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one]
  have hS : ((∑ p ∈ P, N / (25 * p ^ 2) : ℕ) : ℝ) ≤ (N:ℝ) * (11 / 625) := by
    push_cast
    calc ∑ p ∈ P, ((N / (25 * p ^ 2) : ℕ) : ℝ)
        ≤ ∑ p ∈ P, (N:ℝ) * (1 / 25) * (1 / (p:ℝ) ^ 2) := by
          apply sum_le_sum
          intro p _
          calc ((N / (25 * p ^ 2) : ℕ) : ℝ) ≤ (N:ℝ) / ((25 * p ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
            _ = _ := by push_cast; ring
      _ = (N:ℝ) * (1 / 25) * ∑ p ∈ P, (1:ℝ) / (p:ℝ) ^ 2 := by rw [mul_sum]
      _ ≤ (N:ℝ) * (1 / 25) * (11 / 25) := by gcongr
      _ = _ := by ring
  set S := ∑ p ∈ P, N / (25 * p ^ 2) with hSdef
  have hq : N < 25 * (N / 25) + 25 := by omega
  set q := N / 25 with hqdef
  have hN' : (2:ℝ) ^ 2300 ≤ N := by exact_mod_cast hN
  have hc' : (P.card : ℝ) * 2000 ≤ 2 ^ 2000 * 2000 + 2 * N := by exact_mod_cast hcard
  have hq' : (N:ℝ) < 25 * q + 25 := by exact_mod_cast hq
  have hbig : (2:ℝ) ^ 2000 * 1000000 ≤ 2 ^ 2300 := by
    have h1 : (2:ℝ) ^ 2300 = 2 ^ 2000 * 2 ^ 300 := by rw [← pow_add]
    have h2 : (1000000:ℝ) ≤ 2 ^ 300 :=
      calc (1000000:ℝ) ≤ 2 ^ 20 := by norm_num
        _ ≤ 2 ^ 300 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hY : (1:ℝ) ≤ 2 ^ 2000 := one_le_pow₀ (by norm_num)
  generalize (2:ℝ) ^ 2000 = Y at hc' hbig hY
  generalize (2:ℝ) ^ 2300 = Z at hN' hbig
  have : (2 * (S + P.card) : ℝ) ≤ q := by linarith
  exact_mod_cast this

end OMA.Helpers

open Finset in
theorem OMA.solution : OMA.R_Erdos848_erdos_848_R1_H2_R1_H2_R1.H2 := by
  intro N hN badCount Witness c7 b b' hb h7 hb' h18
  obtain ⟨hbI, -⟩ := hb
  obtain ⟨hbI', -⟩ := hb'
  have hbN : b ≤ N := (mem_Icc.1 hbI).2
  have hbN' : b' ≤ N := (mem_Icc.1 hbI').2
  have hc7 : N / 25 ≤ c7 := by
    have h := card_le_card_of_injOn (fun k => 25 * k + 7) (s := range (N / 25))
      (t := (Icc 1 N).filter (fun a => a % 25 = 7)) ?_ ?_
    · simpa using h
    · intro k hk
      simp only [coe_range, Set.mem_Iio] at hk
      simp only [Finset.mem_coe, mem_filter, mem_Icc]
      omega
    · intro x _ y _ h
      simp only at h
      omega
  have h3 := OMA.Helpers.two_T_le N hN
  dsimp only [badCount]
  refine le_trans (add_le_add (OMA.Helpers.side_bound N b 18 hbN ?_ _ ?_)
    (OMA.Helpers.side_bound N b' 7 hbN' ?_ _ ?_)) (by omega)
  · intro a ha hd
    have e1 : a % 5 = 3 := by omega
    have e2 : b % 5 = 2 := by omega
    have e3 : (a * b + 1) % 5 = 2 := by rw [Nat.add_mod, Nat.mul_mod, e1, e2]
    omega
  · intro a ha
    simpa only [mem_filter] using ha
  · intro a ha hd
    have e1 : a % 5 = 2 := by omega
    have e2 : b' % 5 = 3 := by omega
    have e3 : (a * b' + 1) % 5 = 2 := by rw [Nat.add_mod, Nat.mul_mod, e1, e2]
    omega
  · intro a ha
    simpa only [mem_filter] using ha
