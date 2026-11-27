import OMAReductions.R_Erdos69_erdos_69_R2
import Mathlib

/-!
# Step H2 of the reduction Erdos69.erdos_69.R2

The finite moment estimate for the small-prime model
W i = sum over r in J of w r times the number of p in P dividing D i + b + r.

Write N for the product of the primes of P, S for the sum of their reciprocals and
m_a for the sum of (w r)^a over J.

* Every condition p divides D i + b + r (p coprime to D) holds on one residue class modulo p,
  and a conjunction of such conditions holds on no i or on one residue class modulo a divisor
  of N. Expanding W i ^ k as a sum over k-tuples of pairs (r, p) therefore shows that the sum of
  W i ^ k over i below M differs from M / N times the sum over one full period of length N by
  at most (card P * sum of |w r|) ^ k.
* Over a full period the Chinese remainder theorem makes the prime contributions independent:
  inserting one prime p into P, the sums over i below p N' of Y ^ a V ^ c factor, and over one
  period of p the contribution Y of p has a-th power sum m_a (a at least one), since by the
  injectivity hypothesis at most one r is hit for each i. By induction on P the period sums are
  0, N m_2 S and at most N (m_4 S + 3 (m_2 S)^2).
* The hypotheses on m_2 S, m_4 S and the size of M then give the three bounds.
-/

open Finset

namespace OMA.Helpers

/-- A predicate on the naturals that is empty or one residue class modulo a divisor of `N`. -/
def ResClass (N : ℕ) (Q : ℕ → Prop) : Prop :=
  ∃ L : ℕ, 0 < L ∧ L ∣ N ∧ ∀ i j : ℕ, Q i → (Q j ↔ j ≡ i [MOD L])

theorem dvd_affine_iff {p D b r i j : ℕ} (hp : p.Coprime D) (hi : p ∣ D * i + b + r) :
    (p ∣ D * j + b + r ↔ j ≡ i [MOD p]) := by
  constructor
  · intro hj
    have h1 : D * j + b + r ≡ D * i + b + r [MOD p] :=
      (Nat.modEq_zero_iff_dvd.mpr hj).trans (Nat.modEq_zero_iff_dvd.mpr hi).symm
    have h2 : D * j ≡ D * i [MOD p] :=
      Nat.ModEq.add_right_cancel' b (Nat.ModEq.add_right_cancel' r h1)
    exact Nat.ModEq.cancel_left_of_coprime hp h2
  · intro hji
    have h1 : D * j + b + r ≡ D * i + b + r [MOD p] := ((hji.mul_left D).add_right b).add_right r
    exact (h1.dvd_iff dvd_rfl).mpr hi

theorem resClass_dvd {N p D b r : ℕ} (hp : p.Coprime D) (hpN : p ∣ N) (hp0 : 0 < p) :
    ResClass N (fun i => p ∣ D * i + b + r) :=
  ⟨p, hp0, hpN, fun _ _ hi => dvd_affine_iff hp hi⟩

theorem resClass_and {N : ℕ} {Q1 Q2 : ℕ → Prop} (h1 : ResClass N Q1) (h2 : ResClass N Q2) :
    ResClass N (fun i => Q1 i ∧ Q2 i) := by
  obtain ⟨L1, hL1, hL1N, hQ1⟩ := h1
  obtain ⟨L2, hL2, hL2N, hQ2⟩ := h2
  refine ⟨Nat.lcm L1 L2, Nat.lcm_pos hL1 hL2, Nat.lcm_dvd hL1N hL2N, fun i j hi => ?_⟩
  have hi' : Q1 i ∧ Q2 i := hi
  show Q1 j ∧ Q2 j ↔ _
  rw [hQ1 i j hi'.1, hQ2 i j hi'.2]
  exact ⟨fun h => Nat.mod_lcm h.1 h.2, fun h =>
    ⟨Nat.ModEq.of_dvd (Nat.dvd_lcm_left L1 L2) h, Nat.ModEq.of_dvd (Nat.dvd_lcm_right L1 L2) h⟩⟩

theorem resClass_forall {α : Type*} [DecidableEq α] {N : ℕ} (R : α → ℕ → Prop) (s : Finset α)
    (h : ∀ a ∈ s, ResClass N (R a)) : ResClass N (fun i => ∀ a ∈ s, R a i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, one_dvd N, fun i j _ => by simp [Nat.modEq_one]⟩
  | insert x s hx ih =>
    have h' := resClass_and (h x (mem_insert_self x s))
      (ih (fun a ha => h a (mem_insert_of_mem ha)))
    simpa only [forall_mem_insert] using h'

theorem count_approx {N : ℕ} (hN : 0 < N) (Q : ℕ → Prop) [DecidablePred Q] (hQ : ResClass N Q)
    (M : ℕ) :
    |((#{i ∈ range M | Q i} : ℕ) : ℝ) - (M : ℝ) * ((#{i ∈ range N | Q i} : ℕ) : ℝ) / N| ≤ 1 := by
  by_cases hex : ∃ i0, Q i0
  · obtain ⟨i0, hi0⟩ := hex
    obtain ⟨L, hL, hLN, hQL⟩ := hQ
    have hf : ∀ K, #{i ∈ range K | Q i} = #{i ∈ range K | i ≡ i0 [MOD L]} := fun K => by
      congr 1
      exact Finset.filter_congr (fun j _ => hQL i0 j hi0)
    rw [hf M, hf N, ← Nat.count_eq_card_filter_range, ← Nat.count_eq_card_filter_range,
      Nat.count_modEq_card M hL, Nat.count_modEq_card N hL]
    have hNL : N % L = 0 := Nat.mod_eq_zero_of_dvd hLN
    rw [hNL, if_neg (Nat.not_lt_zero _), add_zero]
    have hLr : (0:ℝ) < L := by exact_mod_cast hL
    have hNr : (0:ℝ) < N := by exact_mod_cast hN
    rw [Nat.cast_div hLN hLr.ne']
    have e : (M:ℝ) * (N / L) / N = M / L := by field_simp
    have hMdec : (M : ℝ) = L * ((M / L : ℕ) : ℝ) + ((M % L : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod M L).symm
    have hmodlt : ((M % L : ℕ) : ℝ) < L := by exact_mod_cast Nat.mod_lt M hL
    have e2 : (M : ℝ) / L = ((M / L : ℕ) : ℝ) + ((M % L : ℕ) : ℝ) / L := by
      rw [hMdec]; field_simp
    have h0 : (0:ℝ) ≤ ((M % L : ℕ) : ℝ) / L := by positivity
    have h1 : ((M % L : ℕ) : ℝ) / L < 1 := (div_lt_one hLr).mpr hmodlt
    rw [e, e2]
    split_ifs <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith
  · push Not at hex
    have h0 : ∀ K, #{i ∈ range K | Q i} = 0 := fun K => by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun x _ => hex x
    simp [h0]

theorem pow_sum_ite {ι : Type*} (T : Finset ι) (c : ι → ℝ) (Q : ι → ℕ → Prop)
    [∀ t, DecidablePred (Q t)] (k i : ℕ) :
    (∑ t ∈ T, c t * (if Q t i then (1:ℝ) else 0)) ^ k =
      ∑ f ∈ Fintype.piFinset (fun _ : Fin k => T),
        (∏ l, c (f l)) * (if ∀ l, Q (f l) i then (1:ℝ) else 0) := by
  rw [← Fin.prod_const, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  rw [Finset.prod_mul_distrib, Fintype.prod_boole]
  by_cases h : ∀ l, Q (f l) i <;> simp [h]

theorem moment_approx {ι : Type*} [DecidableEq ι] (T : Finset ι) (c : ι → ℝ) (Q : ι → ℕ → Prop)
    [∀ t, DecidablePred (Q t)] {N : ℕ} (hN : 0 < N) (hQ : ∀ t ∈ T, ResClass N (Q t)) (k M : ℕ) :
    |∑ i ∈ range M, (∑ t ∈ T, c t * (if Q t i then (1:ℝ) else 0)) ^ k
      - (M:ℝ) / N * ∑ i ∈ range N, (∑ t ∈ T, c t * (if Q t i then (1:ℝ) else 0)) ^ k|
      ≤ (∑ t ∈ T, |c t|) ^ k := by
  have hsum : ∀ K, ∑ i ∈ range K, (∑ t ∈ T, c t * (if Q t i then (1:ℝ) else 0)) ^ k =
      ∑ f ∈ Fintype.piFinset (fun _ : Fin k => T),
        (∏ l, c (f l)) * ((#{i ∈ range K | ∀ l, Q (f l) i} : ℕ) : ℝ) := by
    intro K
    simp_rw [pow_sum_ite T c Q k]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [← Finset.mul_sum, Finset.sum_boole]
  rw [hsum M, hsum N, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ f ∈ Fintype.piFinset (fun _ : Fin k => T), |(∏ l, c (f l)) *
        ((#{i ∈ range M | ∀ l, Q (f l) i} : ℕ) : ℝ) - (M:ℝ) / N * ((∏ l, c (f l)) *
        ((#{i ∈ range N | ∀ l, Q (f l) i} : ℕ) : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ f ∈ Fintype.piFinset (fun _ : Fin k => T), ∏ l, |c (f l)| := by
        refine Finset.sum_le_sum (fun f hf => ?_)
        have hres : ResClass N (fun i => ∀ l, Q (f l) i) := by
          have := resClass_forall (fun l i => Q (f l) i) Finset.univ
            (fun l _ => hQ (f l) (Fintype.mem_piFinset.mp hf l))
          simpa only [Finset.mem_univ, true_imp_iff] using this
        have hc := count_approx hN (fun i => ∀ l, Q (f l) i) hres M
        rw [show (∏ l, c (f l)) * ((#{i ∈ range M | ∀ l, Q (f l) i} : ℕ) : ℝ) - (M:ℝ) / N *
            ((∏ l, c (f l)) * ((#{i ∈ range N | ∀ l, Q (f l) i} : ℕ) : ℝ)) =
            (∏ l, c (f l)) * (((#{i ∈ range M | ∀ l, Q (f l) i} : ℕ) : ℝ) - (M:ℝ) *
            ((#{i ∈ range N | ∀ l, Q (f l) i} : ℕ) : ℝ) / N) by ring, abs_mul,
            Finset.abs_prod]
        exact mul_le_of_le_one_right (Finset.prod_nonneg (fun l _ => abs_nonneg _)) hc
    _ = (∑ t ∈ T, |c t|) ^ k := by
        rw [Finset.sum_prod_piFinset T (fun _ t => |c t|), Fin.prod_const]

theorem sum_range_mul_crt {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) (f g : ℕ → ℝ)
    (hf : ∀ i, f i = f (i % m)) (hg : ∀ i, g i = g (i % n)) :
    ∑ i ∈ range (m * n), f i * g i = (∑ i ∈ range m, f i) * (∑ j ∈ range n, g j) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product' (f := fun a c => f a * g c)]
  refine Finset.sum_nbij (fun i => (i % m, i % n)) ?_ ?_ ?_ ?_
  · intro i _
    simp [Finset.mem_product, Nat.mod_lt _ hm, Nat.mod_lt _ hn]
  · intro i hi j hj hij
    simp only [Prod.mk.injEq] at hij
    have h := (Nat.modEq_and_modEq_iff_modEq_mul hmn).mp ⟨hij.1, hij.2⟩
    exact Nat.ModEq.eq_of_lt_of_lt h (by simpa using hi) (by simpa using hj)
  · rintro ⟨a, c⟩ hac
    simp only [coe_product, Set.mem_prod, mem_coe, mem_range] at hac
    refine ⟨(Nat.chineseRemainder hmn a c).val, ?_, ?_⟩
    · simpa using Nat.chineseRemainder_lt_mul hmn a c hm.ne' hn.ne'
    · have h1 : (Nat.chineseRemainder hmn a c).val % m = a % m := (Nat.chineseRemainder hmn a c).prop.1
      have h2 : (Nat.chineseRemainder hmn a c).val % n = c % n := (Nat.chineseRemainder hmn a c).prop.2
      simp only [Prod.mk.injEq]
      rw [h1, h2, Nat.mod_eq_of_lt hac.1, Nat.mod_eq_of_lt hac.2]
      exact ⟨rfl, rfl⟩
  · intro i _
    simp only
    rw [← hf, ← hg]


/-- The contribution of one prime `p`. -/
def Yf (J : Finset ℕ) (D b : ℕ) (w : ℕ → ℝ) (p i : ℕ) : ℝ :=
  ∑ r ∈ J, w r * (if p ∣ D * i + b + r then (1:ℝ) else 0)

theorem dvd_mod_iff {q L D b r i : ℕ} (hq : q ∣ L) :
    (q ∣ D * i + b + r ↔ q ∣ D * (i % L) + b + r) := by
  have h : D * (i % L) + b + r ≡ D * i + b + r [MOD L] :=
    (((Nat.mod_modEq i L).mul_left D).add_right b).add_right r
  exact (h.dvd_iff hq).symm

theorem Yf_mod {J : Finset ℕ} {D b : ℕ} (w : ℕ → ℝ) {p L : ℕ} (hpL : p ∣ L) (i : ℕ) :
    Yf J D b w p i = Yf J D b w p (i % L) := by
  unfold Yf
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [if_congr (dvd_mod_iff (D := D) (b := b) (r := r) (i := i) hpL) rfl rfl]

theorem period_card_one {p D b r : ℕ} (hp : p.Prime) (hpD : p.Coprime D) :
    #{i ∈ range p | p ∣ D * i + b + r} = 1 := by
  obtain ⟨i0, hi0lt, hi0⟩ :=
    Nat.exists_mul_mod_eq_of_coprime ((p - 1) * (b + r)) (Nat.Coprime.symm hpD) hp.ne_zero
  have hdiv : p ∣ D * i0 + b + r := by
    have hm : D * i0 ≡ (p - 1) * (b + r) [MOD p] := hi0
    have h1 : D * i0 + (b + r) ≡ (p - 1) * (b + r) + (b + r) [MOD p] := Nat.ModEq.add_right _ hm
    have h2 : (p - 1) * (b + r) + (b + r) = p * (b + r) := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    rw [h2] at h1
    rw [add_assoc]
    exact Nat.modEq_zero_iff_dvd.mp (h1.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right p _)))
  rw [Finset.card_eq_one]
  refine ⟨i0, ?_⟩
  ext j
  simp only [mem_filter, mem_range, mem_singleton]
  constructor
  · rintro ⟨hj, hjd⟩
    exact Nat.ModEq.eq_of_lt_of_lt ((dvd_affine_iff hpD hdiv).mp hjd) hj hi0lt
  · rintro rfl
    exact ⟨hi0lt, hdiv⟩

theorem Yf_pow {J : Finset ℕ} {p D b : ℕ} (w : ℕ → ℝ)
    (hinj : Set.InjOn (fun r : ℕ => r % p) (J : Set ℕ)) {a : ℕ} (ha : a ≠ 0) (i : ℕ) :
    Yf J D b w p i ^ a = ∑ r ∈ J, w r ^ a * (if p ∣ D * i + b + r then (1:ℝ) else 0) := by
  unfold Yf
  by_cases hex : ∃ r0 ∈ J, p ∣ D * i + b + r0
  · obtain ⟨r0, hr0, hd0⟩ := hex
    have hother : ∀ r ∈ J, r ≠ r0 → ¬ p ∣ D * i + b + r := by
      intro r hr hne hd
      apply hne
      apply hinj hr hr0
      have h1 : D * i + b + r ≡ D * i + b + r0 [MOD p] :=
        (Nat.modEq_zero_iff_dvd.mpr hd).trans (Nat.modEq_zero_iff_dvd.mpr hd0).symm
      exact Nat.ModEq.add_left_cancel' (D * i + b) h1
    rw [Finset.sum_eq_single_of_mem r0 hr0, Finset.sum_eq_single_of_mem r0 hr0]
    · simp [hd0]
    · intro r hr hne
      simp [hother r hr hne]
    · intro r hr hne
      simp [hother r hr hne]
  · push Not at hex
    have e1 : ∑ r ∈ J, w r * (if p ∣ D * i + b + r then (1:ℝ) else 0) = 0 :=
      Finset.sum_eq_zero (fun r hr => by simp [hex r hr])
    have e2 : ∑ r ∈ J, w r ^ a * (if p ∣ D * i + b + r then (1:ℝ) else 0) = 0 :=
      Finset.sum_eq_zero (fun r hr => by simp [hex r hr])
    rw [e1, e2, zero_pow ha]

theorem Yf_period_sum {J : Finset ℕ} {p D b : ℕ} (w : ℕ → ℝ) (hp : p.Prime) (hpD : p.Coprime D)
    (hinj : Set.InjOn (fun r : ℕ => r % p) (J : Set ℕ)) {a : ℕ} (ha : a ≠ 0) :
    ∑ i ∈ range p, Yf J D b w p i ^ a = ∑ r ∈ J, w r ^ a := by
  rw [Finset.sum_congr rfl (fun i _ => Yf_pow w hinj ha i), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [← Finset.mul_sum, Finset.sum_boole, period_card_one hp hpD]
  simp

theorem full_moments (J : Finset ℕ) (D b : ℕ) (w : ℕ → ℝ) (hw : ∑ r ∈ J, w r = 0)
    (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p.Coprime D ∧ Set.InjOn (fun r : ℕ => r % p) (J : Set ℕ)) :
    ∑ i ∈ range (∏ p ∈ P, p), (∑ p ∈ P, Yf J D b w p i) = 0 ∧
    ∑ i ∈ range (∏ p ∈ P, p), (∑ p ∈ P, Yf J D b w p i) ^ 2 =
      (∏ p ∈ P, p : ℕ) * ((∑ r ∈ J, w r ^ 2) * ∑ p ∈ P, 1 / (p:ℝ)) ∧
    ∑ i ∈ range (∏ p ∈ P, p), (∑ p ∈ P, Yf J D b w p i) ^ 4 ≤
      (∏ p ∈ P, p : ℕ) * ((∑ r ∈ J, w r ^ 4) * (∑ p ∈ P, 1 / (p:ℝ)) +
        3 * ((∑ r ∈ J, w r ^ 2) * ∑ p ∈ P, 1 / (p:ℝ)) ^ 2) := by
  induction P using Finset.induction_on with
  | empty => simp
  | insert p P hpP ih =>
    obtain ⟨hp, hpD, hpinj⟩ := hP p (mem_insert_self p P)
    obtain ⟨ih1, ih2, ih4⟩ := ih (fun q hq => hP q (mem_insert_of_mem hq))
    have hN'pos : 0 < ∏ q ∈ P, q :=
      Finset.prod_pos (fun q hq => (hP q (mem_insert_of_mem hq)).1.pos)
    have hcop : p.Coprime (∏ q ∈ P, q) := Nat.Coprime.prod_right (fun q hq =>
      (Nat.coprime_primes hp (hP q (mem_insert_of_mem hq)).1).mpr (fun h => hpP (h ▸ hq)))
    have mix : ∀ a c : ℕ, ∑ i ∈ range (p * ∏ q ∈ P, q),
        Yf J D b w p i ^ a * (∑ q ∈ P, Yf J D b w q i) ^ c =
        (∑ i ∈ range p, Yf J D b w p i ^ a) *
          (∑ i ∈ range (∏ q ∈ P, q), (∑ q ∈ P, Yf J D b w q i) ^ c) := by
      intro a c
      refine sum_range_mul_crt hp.pos hN'pos hcop (fun i => Yf J D b w p i ^ a)
        (fun i => (∑ q ∈ P, Yf J D b w q i) ^ c) (fun i => ?_) (fun i => ?_)
      · rw [Yf_mod w (dvd_refl p) i]
      · congr 1
        exact Finset.sum_congr rfl (fun q hq => Yf_mod (J := J) (D := D) (b := b) w
          (Finset.dvd_prod_of_mem (fun q : ℕ => q) hq : q ∣ ∏ q ∈ P, q) i)
    have y0 : ∑ i ∈ range p, Yf J D b w p i ^ 0 = p := by simp
    have v0 : ∑ i ∈ range (∏ q ∈ P, q), (∑ q ∈ P, Yf J D b w q i) ^ 0 = (∏ q ∈ P, q : ℕ) := by
      simp
    have ya : ∀ a ≠ 0, ∑ i ∈ range p, Yf J D b w p i ^ a = ∑ r ∈ J, w r ^ a :=
      fun a ha => Yf_period_sum w hp hpD hpinj ha
    have hw1 : ∑ r ∈ J, w r ^ 1 = 0 := by simpa using hw
    have ih1' : ∑ i ∈ range (∏ q ∈ P, q), (∑ q ∈ P, Yf J D b w q i) ^ 1 = 0 := by simpa using ih1
    have hpr : (0:ℝ) < p := by exact_mod_cast hp.pos
    have hps : (p:ℝ) * (1 / p) = 1 := by field_simp
    simp only [prod_insert hpP, sum_insert hpP]
    refine ⟨?_, ?_, ?_⟩
    · have e : ∀ i, Yf J D b w p i + ∑ q ∈ P, Yf J D b w q i =
          Yf J D b w p i ^ 1 * (∑ q ∈ P, Yf J D b w q i) ^ 0 +
          Yf J D b w p i ^ 0 * (∑ q ∈ P, Yf J D b w q i) ^ 1 := by intro i; ring
      rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib, mix, mix, v0, ih1',
        ya 1 one_ne_zero, hw1]
      ring
    · have e : ∀ i, (Yf J D b w p i + ∑ q ∈ P, Yf J D b w q i) ^ 2 =
          Yf J D b w p i ^ 2 * (∑ q ∈ P, Yf J D b w q i) ^ 0 +
          2 * (Yf J D b w p i ^ 1 * (∑ q ∈ P, Yf J D b w q i) ^ 1) +
          Yf J D b w p i ^ 0 * (∑ q ∈ P, Yf J D b w q i) ^ 2 := by intro i; ring
      rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, mix, mix, mix, v0, ih1', ya 1 one_ne_zero, ya 2 two_ne_zero, hw1, y0,
        ih2]
      rw [Nat.cast_mul]
      generalize ((∏ q ∈ P, q : ℕ) : ℝ) = N' at *
      generalize ∑ r ∈ J, w r ^ 2 = m2 at *
      generalize ∑ q ∈ P, 1 / (q:ℝ) = S at *
      linear_combination (-(N' * m2)) * hps
    · have e : ∀ i, (Yf J D b w p i + ∑ q ∈ P, Yf J D b w q i) ^ 4 =
          Yf J D b w p i ^ 4 * (∑ q ∈ P, Yf J D b w q i) ^ 0 +
          4 * (Yf J D b w p i ^ 3 * (∑ q ∈ P, Yf J D b w q i) ^ 1) +
          6 * (Yf J D b w p i ^ 2 * (∑ q ∈ P, Yf J D b w q i) ^ 2) +
          4 * (Yf J D b w p i ^ 1 * (∑ q ∈ P, Yf J D b w q i) ^ 3) +
          Yf J D b w p i ^ 0 * (∑ q ∈ P, Yf J D b w q i) ^ 4 := by intro i; ring
      rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, mix, mix, mix, mix, mix, v0, ih1', ya 1 one_ne_zero, ya 2 two_ne_zero,
        ya 3 three_ne_zero, ya 4 four_ne_zero, hw1, y0, ih2]
      rw [Nat.cast_mul]
      have hN'r : (0:ℝ) ≤ ((∏ q ∈ P, q : ℕ) : ℝ) := Nat.cast_nonneg _
      generalize ((∏ q ∈ P, q : ℕ) : ℝ) = N' at *
      generalize ∑ r ∈ J, w r ^ 2 = m2 at *
      generalize ∑ r ∈ J, w r ^ 4 = m4 at *
      generalize ∑ q ∈ P, 1 / (q:ℝ) = S at *
      generalize ∑ i ∈ range (∏ q ∈ P, q), (∑ q ∈ P, Yf J D b w q i) ^ 4 = A4 at *
      have key : (p:ℝ) * N' * (m4 * (1 / p + S) + 3 * (m2 * (1 / p + S)) ^ 2) =
          N' * m4 + 3 * N' * m2 ^ 2 * (1 / p) + 6 * N' * m2 ^ 2 * S +
            p * (N' * (m4 * S + 3 * (m2 * S) ^ 2)) := by
        linear_combination (N' * m4 + 3 * N' * m2 ^ 2 * (1 / p) + 6 * N' * m2 ^ 2 * S) * hps
      rw [key]
      have h4' := mul_le_mul_of_nonneg_left ih4 hpr.le
      have hnn : (0:ℝ) ≤ 3 * N' * m2 ^ 2 * (1 / p) := by positivity
      nlinarith [h4', hnn]

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos69_erdos_69_R2.H2 := by
  intro P J D b M w hyp
  obtain ⟨hP, hw, hlo, hhi, h4, hM⟩ := hyp
  intro W
  have hWF : ∀ i, W i = ∑ t ∈ J ×ˢ P, w t.1 * (if t.2 ∣ D * i + b + t.1 then (1:ℝ) else 0) := by
    intro i
    simp only [W]
    rw [Finset.sum_product]
    simp_rw [Finset.mul_sum]
  have hWV : ∀ i, W i = ∑ p ∈ P, OMA.Helpers.Yf J D b w p i := by
    intro i
    simp only [W, OMA.Helpers.Yf]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  have hNpos : 0 < ∏ p ∈ P, p := Finset.prod_pos (fun p hp => (hP p hp).1.pos)
  have hres : ∀ t ∈ J ×ˢ P, OMA.Helpers.ResClass (∏ p ∈ P, p) (fun i => t.2 ∣ D * i + b + t.1) := by
    intro t ht
    have ht2 : t.2 ∈ P := (Finset.mem_product.mp ht).2
    exact OMA.Helpers.resClass_dvd (hP t.2 ht2).2.1 (Finset.dvd_prod_of_mem (fun q : ℕ => q) ht2)
      (hP t.2 ht2).1.pos
  have happrox := fun k => OMA.Helpers.moment_approx (J ×ˢ P) (fun t => w t.1)
    (fun t i => t.2 ∣ D * i + b + t.1) hNpos hres k M
  have hE : ∑ t ∈ J ×ˢ P, |w t.1| = (P.card : ℝ) * ∑ r ∈ J, |w r| := by
    rw [Finset.sum_product]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.mul_sum]
  simp only [← hWF, hE] at happrox
  obtain ⟨m1, m2, m4⟩ := OMA.Helpers.full_moments J D b w hw P hP
  simp only [← hWV] at m1 m2 m4
  have a1 := happrox 1
  have a2 := happrox 2
  have a4 := happrox 4
  simp only [pow_one] at a1
  rw [m1] at a1
  rw [m2] at a2
  have hNr : (0:ℝ) < ((∏ p ∈ P, p : ℕ) : ℝ) := by exact_mod_cast hNpos
  have hMr : (0:ℝ) ≤ M := Nat.cast_nonneg M
  have hMN : (M:ℝ) / ((∏ p ∈ P, p : ℕ) : ℝ) * ((∏ p ∈ P, p : ℕ) : ℝ) = M := by field_simp
  have b4 := mul_le_mul_of_nonneg_left m4 (div_nonneg hMr hNr.le)
  rw [← mul_assoc, hMN] at b4
  rw [← mul_assoc, hMN] at a2
  generalize ((∏ p ∈ P, p : ℕ) : ℝ) = N at *
  generalize hE' : (P.card : ℝ) * ∑ r ∈ J, |w r| = E at *
  have hE0 : 0 ≤ E := by rw [← hE']; positivity
  generalize (∑ r ∈ J, w r ^ 2) * ∑ p ∈ P, 1 / (p:ℝ) = s2 at *
  generalize (∑ r ∈ J, w r ^ 4) * ∑ p ∈ P, 1 / (p:ℝ) = s4 at *
  have hK1 : E ≤ (1 + E) ^ 4 := by nlinarith [pow_le_pow_left₀ hE0 (show E ≤ 1 + E by linarith) 4]
  have hK2 : E ^ 2 ≤ (1 + E) ^ 4 := by nlinarith [pow_le_pow_left₀ hE0 (show E ≤ 1 + E by linarith) 4]
  have hK4 : E ^ 4 ≤ (1 + E) ^ 4 := pow_le_pow_left₀ hE0 (show E ≤ 1 + E by linarith) 4
  have hs2 : 0 ≤ s2 := by linarith
  have hsq : s2 ^ 2 ≤ (11/10000) ^ 2 := pow_le_pow_left₀ hs2 hhi 2
  rw [abs_le] at a1 a2 a4
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_le]
    constructor <;> nlinarith
  · nlinarith
  · nlinarith
