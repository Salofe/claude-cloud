import OMAStatements.S_erdos_684
import Mathlib

-- Problem: Erdos Problem 684 (upper bound f(n) <= n^(30/43+o(1)))
-- Elementary argument: for Y with 2n < Y^3 and 2Y^2 <= n, some k < 2Y^2 has at least six
-- primes p in (Y, k] with n % p < k % p; each divides C(n,k) by Lucas, so the k-smooth
-- part of C(n,k) is at least Y^6 > n^2.

namespace OMA.Helpers

open Finset

lemma dvd_choose_of_mod_lt {n k p : ℕ} (hp : p.Prime) (h : n % p < k % p) :
    p ∣ n.choose k := by
  have : Fact p.Prime := Fact.mk hp
  have h1 := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := p)
  rw [Nat.choose_eq_zero_of_lt h, zero_mul] at h1
  exact (Nat.modEq_zero_iff_dvd).1 h1

lemma smooth_ge {k m : ℕ} (H : Finset ℕ) (hH : ∀ p ∈ H, p.Prime ∧ p ≤ k ∧ p ∣ m)
    (hm : m ≠ 0) : ∏ p ∈ H, p ≤ OMA.S_erdos_684.smoothPart k m := by
  unfold OMA.S_erdos_684.smoothPart
  have hsub : H ⊆ m.primeFactors.filter (· ≤ k) := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hH p hp
    simp only [mem_filter, Nat.mem_primeFactors]
    exact ⟨⟨h1, h3, hm⟩, h2⟩
  calc ∏ p ∈ H, p ≤ ∏ p ∈ H, p ^ (m.factorization p) := by
        apply Finset.prod_le_prod
        · intro i _; exact Nat.zero_le _
        · intro p hp
          obtain ⟨h1, h2, h3⟩ := hH p hp
          exact Nat.le_self_pow (h1.factorization_pos_of_dvd hm h3).ne' p
    _ ≤ _ := by
        apply Finset.prod_le_prod_of_subset_of_one_le hsub
        · intro i _; exact Nat.zero_le _
        · intro p hp _
          simp only [mem_filter, Nat.mem_primeFactors] at hp
          exact Nat.one_le_pow _ _ hp.1.1.pos

lemma log_bound (L : ℕ) (hL : 9 ≤ L) : 24 * L + 1 ≤ 2 ^ (L - 1) := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    have : L + 1 - 1 = (L - 1) + 1 := by omega
    rw [this, pow_succ]
    omega

lemma primes_many (Y : ℕ) (hY : 256 ≤ Y) :
    12 * Y ≤ ((range (Y ^ 2 + 1)).filter Nat.Prime).card := by
  by_contra hcon
  push Not at hcon
  set m := Y ^ 2 / 2 with hm
  have hYY : 256 * 256 ≤ Y ^ 2 := by nlinarith
  have hm4 : 4 ≤ m := by omega
  have h2m : 2 * m ≤ Y ^ 2 := by omega
  have h2m' : Y ^ 2 ≤ 2 * m + 1 := by omega
  have h1 := Nat.four_pow_lt_mul_centralBinom m hm4
  have h2 : Nat.centralBinom m ≤ (2 * m) ^ ((range (2 * m + 1)).filter Nat.Prime).card := by
    rw [← Finset.prod_const]
    conv_lhs => rw [← Nat.prod_pow_factorization_centralBinom m]
    rw [← Finset.prod_subset (Finset.filter_subset Nat.Prime (range (2 * m + 1)))]
    · apply Finset.prod_le_prod
      · intro i _; exact Nat.zero_le _
      · intro p _
        rw [Nat.centralBinom_eq_two_mul_choose]
        exact Nat.pow_factorization_choose_le (by omega)
    · intro p hp hp2
      have : ¬ p.Prime := fun h => hp2 (mem_filter.2 ⟨hp, h⟩)
      rw [Nat.factorization_eq_zero_of_not_prime _ this, pow_zero]
  have hcard : ((range (2 * m + 1)).filter Nat.Prime).card + 1 ≤ 12 * Y := by
    have : ((range (2 * m + 1)).filter Nat.Prime).card
        ≤ ((range (Y ^ 2 + 1)).filter Nat.Prime).card := by
      apply Finset.card_le_card
      apply Finset.filter_subset_filter
      intro x hx
      simp only [mem_range] at hx ⊢
      omega
    omega
  have hYpos : 0 < Y := by omega
  have h3 : 4 ^ m < (Y ^ 2) ^ (12 * Y) := by
    calc 4 ^ m < m * Nat.centralBinom m := h1
      _ ≤ Y ^ 2 * (Y ^ 2) ^ ((range (2 * m + 1)).filter Nat.Prime).card := by
          apply Nat.mul_le_mul (by omega)
          exact h2.trans (Nat.pow_le_pow_left h2m _)
      _ = (Y ^ 2) ^ (((range (2 * m + 1)).filter Nat.Prime).card + 1) := by
          exact (pow_succ' (Y ^ 2) _).symm
      _ ≤ (Y ^ 2) ^ (12 * Y) := Nat.pow_le_pow_right (by positivity) hcard
  set L := Nat.log 2 Y + 1 with hL
  have hYL : Y < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) Y
  have hLY : 2 ^ (L - 1) ≤ Y := by
    have : L - 1 = Nat.log 2 Y := by omega
    rw [this]
    exact Nat.pow_log_le_self 2 (by omega)
  have hL9 : 9 ≤ L := by
    by_contra h
    push Not at h
    have : 2 ^ L ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hLb := log_bound L hL9
  have h4 : (Y ^ 2) ^ (12 * Y) ≤ 2 ^ (L * (24 * Y)) := by
    calc (Y ^ 2) ^ (12 * Y) = Y ^ (24 * Y) := by rw [← pow_mul]; congr 1; ring
      _ ≤ (2 ^ L) ^ (24 * Y) := Nat.pow_le_pow_left hYL.le _
      _ = 2 ^ (L * (24 * Y)) := by rw [← pow_mul]
  have h5 : L * (24 * Y) ≤ 2 * m := by
    have h6 : 24 * L + 1 ≤ Y := hLb.trans hLY
    have h7 : (24 * L + 1) * Y ≤ Y * Y := Nat.mul_le_mul_right Y h6
    have h8 : Y * Y = Y ^ 2 := by ring
    have h9 : (24 * L + 1) * Y = L * (24 * Y) + Y := by ring
    omega
  have h6 : (4 : ℕ) ^ m = 2 ^ (2 * m) := by
    rw [pow_mul]; norm_num
  have h7 : 2 ^ (L * (24 * Y)) ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) h5
  omega

lemma bad_card (n Y A : ℕ) (hA : A ≤ n) (h1 : 2 * n < Y ^ 3) (B : Finset ℕ)
    (hB : ∀ p ∈ B, p.Prime ∧ Y < p ∧ p ≤ n % p + A) : B.card ≤ 2 * A := by
  have himg : (B.image (fun p => p - n % p)) ⊆ Finset.Icc 1 A := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hc
    obtain ⟨hpp, hYp, hpA⟩ := hB p hp
    have := Nat.mod_lt n hpp.pos
    simp only [mem_Icc]
    omega
  have hfib : ∀ c ∈ B.image (fun p => p - n % p),
      (B.filter (fun p => p - n % p = c)).card ≤ 2 := by
    intro c hc
    by_contra hcon
    push Not at hcon
    have hcA := mem_Icc.1 (himg hc)
    obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card.1 hcon
    have key : ∀ x ∈ B.filter (fun p => p - n % p = c), x.Prime ∧ Y < x ∧ x ∣ n + c := by
      intro x hx
      obtain ⟨hxB, hxc⟩ := mem_filter.1 hx
      obtain ⟨hxp, hYx, hxA⟩ := hB x hxB
      refine ⟨hxp, hYx, ?_⟩
      have hlt := Nat.mod_lt n hxp.pos
      have e : n + c = x + x * (n / x) := by
        have := Nat.mod_add_div n x
        omega
      rw [e]
      exact Dvd.intro (1 + n / x) (by ring)
    obtain ⟨hp1, hp2, hp3⟩ := key p hp
    obtain ⟨hq1, hq2, hq3⟩ := key q hq
    obtain ⟨hr1, hr2, hr3⟩ := key r hr
    have cpq : Nat.Coprime p q := (Nat.coprime_primes hp1 hq1).2 hpq
    have cpr : Nat.Coprime p r := (Nat.coprime_primes hp1 hr1).2 hpr
    have cqr : Nat.Coprime q r := (Nat.coprime_primes hq1 hr1).2 hqr
    have d1 : p * q ∣ n + c := Nat.Coprime.mul_dvd_of_dvd_of_dvd cpq hp3 hq3
    have d2 : p * q * r ∣ n + c :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.mul_left cpr cqr) d1 hr3
    have hle : p * q * r ≤ n + c := Nat.le_of_dvd (by omega) d2
    have hbig : Y ^ 3 ≤ p * q * r := by
      have e : Y ^ 3 = Y * Y * Y := by ring
      rw [e]
      exact Nat.mul_le_mul (Nat.mul_le_mul hp2.le hq2.le) hr2.le
    omega
  have h := Finset.card_le_mul_card_image B 2 hfib
  have h2 := Finset.card_le_card himg
  rw [Nat.card_Icc] at h2
  have : 2 * (B.image (fun p => p - n % p)).card ≤ 2 * A := by omega
  omega

lemma good_hits (n p A M : ℕ) (hlt : n % p + A < p) (hM : 2 * p ≤ M) :
    A ≤ ((range M).filter (fun k => p ≤ k ∧ n % p < k % p)).card := by
  have hinj : Set.InjOn (fun c => p + n % p + c) (Finset.Icc 1 A : Set ℕ) := by
    intro a _ b _ hab
    simp only at hab
    omega
  have := Finset.card_le_card_of_injOn (s := Finset.Icc 1 A)
    (t := (range M).filter (fun k => p ≤ k ∧ n % p < k % p))
    (fun c => p + n % p + c) ?_ hinj
  · rwa [Nat.card_Icc, Nat.add_sub_cancel] at this
  · intro c hc
    have hc' := mem_Icc.1 hc
    simp only [Finset.coe_filter, mem_range, Set.mem_ofPred_eq]
    have e : (p + n % p + c) % p = n % p + c := by
      rw [add_assoc, Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e]
    omega

lemma core (n Y : ℕ) (hY : 256 ≤ Y) (h1 : 2 * n < Y ^ 3) (h2 : 2 * Y ^ 2 ≤ n) :
    ∃ k, k < 2 * Y ^ 2 ∧ n ^ 2 < OMA.S_erdos_684.smoothPart k (n.choose k) := by
  classical
  have hYY : 256 * Y ≤ Y ^ 2 := by nlinarith
  set S := (range (Y ^ 2 + 1)).filter Nat.Prime with hS
  have hScard : 12 * Y ≤ S.card := primes_many Y hY
  set Sm := S.filter (fun p => p ≤ Y) with hSm
  set B := S.filter (fun p => Y < p ∧ p ≤ n % p + 4 * Y) with hBdef
  set G := S.filter (fun p => Y < p ∧ n % p + 4 * Y < p) with hGdef
  have hcov : S ⊆ Sm ∪ B ∪ G := by
    intro p hp
    simp only [hSm, hBdef, hGdef, mem_union, mem_filter]
    by_cases h : p ≤ Y
    · exact Or.inl (Or.inl ⟨hp, h⟩)
    · by_cases h' : p ≤ n % p + 4 * Y
      · exact Or.inl (Or.inr ⟨hp, by omega, h'⟩)
      · exact Or.inr ⟨hp, by omega, by omega⟩
  have hSmc : Sm.card ≤ Y := by
    have : Sm ⊆ Finset.Icc 1 Y := by
      intro p hp
      obtain ⟨hpS, hpY⟩ := mem_filter.1 hp
      have := (mem_filter.1 hpS).2.pos
      simp only [mem_Icc]
      omega
    have h := Finset.card_le_card this
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at h
  have hBc : B.card ≤ 2 * (4 * Y) := by
    apply bad_card n Y (4 * Y) (by omega) h1
    intro p hp
    obtain ⟨hpS, hp1, hp2⟩ := mem_filter.1 hp
    exact ⟨(mem_filter.1 hpS).2, hp1, hp2⟩
  have hGc : 3 * Y ≤ G.card := by
    have h := Finset.card_le_card hcov
    have h' := (Finset.card_union_le (Sm ∪ B) G).trans
      (Nat.add_le_add_right (Finset.card_union_le Sm B) _)
    omega
  set R := range (2 * Y ^ 2) with hR
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := G) (t := R) (r := fun p k => p ≤ k ∧ n % p < k % p)
  have hlow : G.card * (4 * Y) ≤ ∑ p ∈ G, (R.bipartiteAbove (fun p k => p ≤ k ∧ n % p < k % p) p).card := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hpS, hp1, hp2⟩ := mem_filter.1 hp
    have hpr := mem_range.1 (mem_filter.1 hpS).1
    exact good_hits n p (4 * Y) (2 * Y ^ 2) hp2 (by omega)
  have hex : ∃ k ∈ R, 6 ≤ (G.bipartiteBelow (fun p k => p ≤ k ∧ n % p < k % p) k).card := by
    by_contra hcon
    push Not at hcon
    have hup : ∑ k ∈ R, (G.bipartiteBelow (fun p k => p ≤ k ∧ n % p < k % p) k).card
        ≤ ∑ _k ∈ R, 5 := Finset.sum_le_sum (fun k hk => by have := hcon k hk; omega)
    have hRc : R.card = 2 * Y ^ 2 := Finset.card_range _
    rw [Finset.sum_const, smul_eq_mul, hRc] at hup
    rw [hdc] at hlow
    have h3 : 3 * Y * (4 * Y) ≤ G.card * (4 * Y) := Nat.mul_le_mul_right _ hGc
    have h4 : 3 * Y * (4 * Y) = 12 * Y ^ 2 := by ring
    have h5 : 0 < Y ^ 2 := by positivity
    omega
  obtain ⟨k, hkR, hk6⟩ := hex
  have hk : k < 2 * Y ^ 2 := mem_range.1 hkR
  refine ⟨k, hk, ?_⟩
  set H := G.bipartiteBelow (fun p k => p ≤ k ∧ n % p < k % p) k with hH
  have hHmem : ∀ p ∈ H, p.Prime ∧ Y < p ∧ p ≤ k ∧ n % p < k % p := by
    intro p hp
    rw [hH, Finset.mem_bipartiteBelow] at hp
    obtain ⟨hpG, hpk, hpm⟩ := hp
    obtain ⟨hpS, hp1, hp2⟩ := mem_filter.1 hpG
    exact ⟨(mem_filter.1 hpS).2, hp1, hpk, hpm⟩
  have hsm := smooth_ge (k := k) (m := n.choose k) H
    (fun p hp => ⟨(hHmem p hp).1, (hHmem p hp).2.2.1,
      dvd_choose_of_mod_lt (hHmem p hp).1 (hHmem p hp).2.2.2⟩)
    (Nat.choose_pos (by omega)).ne'
  have hprod : Y ^ H.card ≤ ∏ p ∈ H, p :=
    Finset.pow_card_le_prod H (fun p => p) Y (fun p hp => (hHmem p hp).2.1.le)
  have hY6 : Y ^ 6 ≤ Y ^ H.card := Nat.pow_le_pow_right (by omega) hk6
  have hn : n ^ 2 < Y ^ 6 := by
    have e : Y ^ 6 = Y ^ 3 * Y ^ 3 := by ring
    rw [e]
    nlinarith
  omega

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_erdos_684.main := by
  intro ε hε
  filter_upwards [Filter.eventually_ge_atTop (2 ^ 158)] with n hn
  have hex : ∃ Y, 2 * n < Y ^ 3 := by
    refine ⟨2 * n + 1, ?_⟩
    have : (2 * n + 1) ^ 1 ≤ (2 * n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    rw [pow_one] at this
    omega
  classical
  set Y := Nat.find hex with hYdef
  have hY1 : 2 * n < Y ^ 3 := Nat.find_spec hex
  have hYpos : Y ≠ 0 := by
    intro h
    rw [h] at hY1
    simp at hY1
  obtain ⟨Z, hZ⟩ : ∃ Z, Y = Z + 1 := ⟨Y - 1, by omega⟩
  have hZ3 : Z ^ 3 ≤ 2 * n := by
    have := Nat.find_min hex (m := Z) (by omega)
    omega
  have hY256 : 256 ≤ Y := by
    by_contra h
    push Not at h
    have : Y ^ 3 ≤ 255 ^ 3 := Nat.pow_le_pow_left (by omega) 3
    norm_num at this
    have h158 : (2 : ℕ) ^ 24 ≤ 2 ^ 158 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    norm_num at h158
    omega
  have hZ1 : 1 ≤ Z := by omega
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hpow : (2 * Y ^ 2) ^ 43 ≤ n ^ 30 := by
    have a1 : 2 * Y ^ 2 ≤ 8 * Z ^ 2 := by
      rw [hZ]; nlinarith
    have a2 : Z ^ 86 ≤ Z ^ 87 := Nat.pow_le_pow_right hZ1 (by norm_num)
    have a3 : Z ^ 87 ≤ (2 * n) ^ 29 := by
      have : Z ^ 87 = (Z ^ 3) ^ 29 := by rw [← pow_mul]
      rw [this]
      exact Nat.pow_le_pow_left hZ3 29
    calc (2 * Y ^ 2) ^ 43 ≤ (8 * Z ^ 2) ^ 43 := Nat.pow_le_pow_left a1 43
      _ = 2 ^ 129 * Z ^ 86 := by rw [mul_pow, ← pow_mul]; norm_num
      _ ≤ 2 ^ 129 * (2 * n) ^ 29 := Nat.mul_le_mul_left _ (a2.trans a3)
      _ = 2 ^ 158 * n ^ 29 := by rw [mul_pow, ← mul_assoc, ← pow_add]
      _ ≤ n * n ^ 29 := Nat.mul_le_mul_right _ hn
      _ = n ^ 30 := by rw [← pow_succ']
  have h2 : 2 * Y ^ 2 ≤ n := by
    by_contra h
    push Not at h
    have b1 : n ^ 43 < (2 * Y ^ 2) ^ 43 := Nat.pow_lt_pow_left h (by norm_num)
    have b2 : n ^ 30 ≤ n ^ 43 := Nat.pow_le_pow_right hnpos (by norm_num)
    omega
  obtain ⟨k, hk, hsm⟩ := core n Y hY256 hY1 h2
  have hf : OMA.S_erdos_684.f n ≤ k := by
    unfold OMA.S_erdos_684.f
    exact Nat.sInf_le ⟨by omega, hsm⟩
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
  have hreal : ((2 * Y ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ ((30 : ℝ) / 43) := by
    have c1 : (((2 * Y ^ 2 : ℕ) : ℝ)) ^ 43 ≤ (n : ℝ) ^ 30 := by exact_mod_cast hpow
    have c2 : ((n : ℝ) ^ ((30 : ℝ) / 43)) ^ 43 = (n : ℝ) ^ 30 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
      have : ((30 : ℝ) / 43) * ((43 : ℕ) : ℝ) = ((30 : ℕ) : ℝ) := by norm_num
      rw [this, Real.rpow_natCast]
    rw [← c2] at c1
    exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (Real.rpow_nonneg hn0 _) (by norm_num)).1 c1
  calc (OMA.S_erdos_684.f n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hf
    _ ≤ ((2 * Y ^ 2 : ℕ) : ℝ) := by exact_mod_cast hk.le
    _ ≤ (n : ℝ) ^ ((30 : ℝ) / 43) := hreal
    _ ≤ (n : ℝ) ^ ((30 : ℝ) / 43 + ε) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
