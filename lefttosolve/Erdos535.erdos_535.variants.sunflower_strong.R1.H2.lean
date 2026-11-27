import OMAReductions.R_Erdos535_erdos_535_variants_sunflower_strong_R1

/-!
# Step H2 of the reduction Erdos535.erdos_535.variants.sunflower_strong.R1

Transfer from integers with exactly `k` prime factors (with multiplicity) to `k`-sets.

* Encoding. The cells of `n` are the pairs `(p, j)` with `p` a prime factor of `n` and
  `j < v_p(n)`; they are coded into naturals with `Nat.pair`. The code set `e535Enc n` has
  `Ω n` elements, satisfies `e535Enc (gcd a b) = e535Enc a ∩ e535Enc b` (by
  `Nat.factorization_gcd`) and determines `n` when `n ≠ 0` (by `Nat.eq_of_factorization_eq`).
* Thinning. Let `D` be the union of all codes of elements of `A`. For a subset `U` of `D`
  (a choice of coins), keep `n` when `U` meets the cells of `n` exactly in the top cells
  `(p, v_p(n) - 1)`. For each `n` exactly `2 ^ (#D - k)` subsets keep it, so double
  counting gives some `U` with `#A ≤ 2 ^ k * #B`, where `B` is the kept set. Inside `B`
  two elements sharing a prime `p` have the same exponent at `p` (look at the top cell of
  the smaller exponent).
* Lifting. A sunflower of codes with kernel `K` forces a constant pairwise gcd `d` (the gcds
  have equal code sets), and the equal-exponent property makes `a / d` coprime to `d`.
  When `S` has at most one element, `d = 1` works.

Only upstream definitions are used, together with Mathlib.
-/

open scoped ArithmeticFunction.Omega

namespace OMA.Helpers

/-- The cells of `n`: pairs `(p, j)` with `p` a prime factor of `n` and `j < v_p(n)`. -/
def e535Cells (n : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  n.primeFactors.sigma fun p => Finset.range (n.factorization p)

/-- The encoding of `n` as a finite set of naturals (cells coded by `Nat.pair`). -/
def e535Enc (n : ℕ) : Finset ℕ :=
  (e535Cells n).image fun x => Nat.pair x.1 x.2

/-- The top cell of each prime factor of `n`. -/
def e535Top (n : ℕ) : Finset ℕ :=
  n.primeFactors.image fun p => Nat.pair p (n.factorization p - 1)

theorem e535_mem_enc (n m : ℕ) :
    m ∈ e535Enc n ↔ (Nat.unpair m).2 < n.factorization (Nat.unpair m).1 := by
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
    rw [e535Cells, Finset.mem_sigma, Finset.mem_range] at hx
    rw [Nat.unpair_pair]
    exact hx.2
  · intro h
    refine Finset.mem_image.mpr ⟨⟨(Nat.unpair m).1, (Nat.unpair m).2⟩, ?_, Nat.pair_unpair m⟩
    rw [e535Cells, Finset.mem_sigma, Finset.mem_range]
    refine ⟨?_, h⟩
    show (Nat.unpair m).1 ∈ n.primeFactors
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    omega

theorem e535_pair_mem_enc (n p j : ℕ) :
    Nat.pair p j ∈ e535Enc n ↔ j < n.factorization p := by
  rw [e535_mem_enc, Nat.unpair_pair]

theorem e535_card_enc (n : ℕ) : (e535Enc n).card = Ω n := by
  rw [e535Enc, Finset.card_image_of_injective, e535Cells, Finset.card_sigma,
    ArithmeticFunction.cardFactors_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  · simp
  · rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Nat.pair_eq_pair] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

theorem e535_enc_gcd {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    e535Enc (Nat.gcd a b) = e535Enc a ∩ e535Enc b := by
  ext m
  rw [Finset.mem_inter, e535_mem_enc, e535_mem_enc, e535_mem_enc, Nat.factorization_gcd ha hb,
    Finsupp.inf_apply, lt_inf_iff]

theorem e535_enc_inj {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : e535Enc a = e535Enc b) :
    a = b := by
  apply Nat.eq_of_factorization_eq ha hb
  intro p
  have key : ∀ j, j < a.factorization p ↔ j < b.factorization p := by
    intro j
    rw [← e535_pair_mem_enc, ← e535_pair_mem_enc, h]
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd ((key _).mpr hlt) (lt_irrefl _)
  · exact absurd ((key _).mp hlt) (lt_irrefl _)

theorem e535_top_subset (n : ℕ) : e535Top n ⊆ e535Enc n := by
  intro m hm
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
  rw [e535_pair_mem_enc]
  have : 0 < n.factorization p := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff] at hp
    omega
  omega

/-- The number of subsets `U` of `D` with a prescribed trace `M` on `T ⊆ D`. -/
theorem e535_count {α : Type*} [DecidableEq α] (D T M : Finset α) (hMT : M ⊆ T)
    (hTD : T ⊆ D) :
    (D.powerset.filter (fun U => U ∩ T = M)).card = 2 ^ (D.card - T.card) := by
  have hEq : D.powerset.filter (fun U => U ∩ T = M) =
      (D \ T).powerset.image (fun V => V ∪ M) := by
    ext U
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hUD, hUT⟩
      refine ⟨U \ T, Finset.sdiff_subset_sdiff hUD le_rfl, ?_⟩
      rw [← hUT, Finset.sdiff_union_inter]
    · rintro ⟨V, hV, rfl⟩
      refine ⟨Finset.union_subset (hV.trans Finset.sdiff_subset) (hMT.trans hTD), ?_⟩
      rw [Finset.union_inter_distrib_right]
      have h1 : V ∩ T = ∅ :=
        Finset.disjoint_iff_inter_eq_empty.mp (Finset.sdiff_disjoint.mono_left hV)
      have h2 : M ∩ T = M := Finset.inter_eq_left.mpr hMT
      rw [h1, h2, Finset.empty_union]
  rw [hEq, Finset.card_image_of_injOn, Finset.card_powerset, Finset.card_sdiff_of_subset hTD]
  intro V1 hV1 V2 hV2 h
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
    Finset.coe_subset] at hV1 hV2
  have d1 : Disjoint V1 M := Finset.sdiff_disjoint.mono hV1 hMT
  have d2 : Disjoint V2 M := Finset.sdiff_disjoint.mono hV2 hMT
  have h' : (V1 ∪ M) \ M = (V2 ∪ M) \ M := by
    simp only at h
    rw [h]
  rwa [Finset.union_sdiff_cancel_right d1, Finset.union_sdiff_cancel_right d2] at h'

/-- Consistency of exponents inside one selected class (one inequality). -/
theorem e535_consistent_le {U : Finset ℕ} {a b p : ℕ} (ha : a ≠ 0)
    (hUa : U ∩ e535Enc a = e535Top a) (hUb : U ∩ e535Enc b = e535Top b) (hp : p.Prime)
    (hpa : p ∣ a) (hle : a.factorization p ≤ b.factorization p) :
    a.factorization p = b.factorization p := by
  have hpos : 0 < a.factorization p := hp.factorization_pos_of_dvd ha hpa
  have hmem : Nat.pair p (a.factorization p - 1) ∈ e535Top a :=
    Finset.mem_image.mpr ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpa, ha⟩, rfl⟩
  have hU : Nat.pair p (a.factorization p - 1) ∈ U := by
    rw [← hUa] at hmem
    exact (Finset.mem_inter.mp hmem).1
  have hEb : Nat.pair p (a.factorization p - 1) ∈ e535Enc b := by
    rw [e535_pair_mem_enc]
    omega
  have hTb : Nat.pair p (a.factorization p - 1) ∈ e535Top b := by
    rw [← hUb]
    exact Finset.mem_inter.mpr ⟨hU, hEb⟩
  obtain ⟨q, _, hqe⟩ := Finset.mem_image.mp hTb
  rw [Nat.pair_eq_pair] at hqe
  obtain ⟨rfl, h2⟩ := hqe
  omega

/-- Consistency of exponents inside one selected class. -/
theorem e535_consistent {U : Finset ℕ} {a b p : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hUa : U ∩ e535Enc a = e535Top a) (hUb : U ∩ e535Enc b = e535Top b) (hp : p.Prime)
    (hpa : p ∣ a) (hpb : p ∣ b) : a.factorization p = b.factorization p := by
  rcases le_total (a.factorization p) (b.factorization p) with h | h
  · exact e535_consistent_le ha hUa hUb hp hpa h
  · exact (e535_consistent_le hb hUb hUa hp hpb h).symm

/-- With consistent exponents, `a / gcd a b` is coprime to `gcd a b`. -/
theorem e535_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcons : ∀ p, p.Prime → p ∣ a → p ∣ b → a.factorization p = b.factorization p) :
    Nat.gcd (a / Nat.gcd a b) (Nat.gcd a b) = 1 := by
  apply Nat.Coprime.gcd_eq_one
  apply Nat.coprime_of_dvd
  intro p hp hpq hpd
  have hd0 : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha)
  have hpa : p ∣ a := hpd.trans (Nat.gcd_dvd_left a b)
  have hpb : p ∣ b := hpd.trans (Nat.gcd_dvd_right a b)
  have heq := hcons p hp hpa hpb
  have hq0 : a / Nat.gcd a b ≠ 0 := by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero ha) (Nat.gcd_dvd_left a b)
    exact (Nat.div_pos this hd0).ne'
  have hpos := hp.factorization_pos_of_dvd hq0 hpq
  rw [Nat.factorization_div (Nat.gcd_dvd_left a b), Nat.factorization_gcd ha hb] at hpos
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.inf_apply] at hpos
  rw [heq, inf_idem] at hpos
  omega

/-- A sunflower of encodings inside one selected class lifts to a constant gcd. -/
theorem e535_lift (U S : Finset ℕ)
    (hS : ∀ a ∈ S, a ≠ 0 ∧ U ∩ e535Enc a = e535Top a) (K : Finset ℕ)
    (hK : (S : Set ℕ).Pairwise (fun a b => e535Enc a ∩ e535Enc b = K)) :
    ∃ d, 0 < d ∧ (S : Set ℕ).Pairwise (fun a b => Nat.gcd a b = d) ∧
      ∀ a ∈ S, ∃ b, a = d * b ∧ Nat.gcd b d = 1 := by
  by_cases h : ∃ a0 ∈ S, ∃ b0 ∈ S, a0 ≠ b0
  · obtain ⟨a0, ha0, b0, hb0, hne⟩ := h
    have hgcd : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.gcd a b = Nat.gcd a0 b0 := by
      intro a ha b hb hab
      apply e535_enc_inj (Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero (hS a ha).1)).ne'
        (Nat.gcd_pos_of_pos_left b0 (Nat.pos_of_ne_zero (hS a0 ha0).1)).ne'
      rw [e535_enc_gcd (hS a ha).1 (hS b hb).1, e535_enc_gcd (hS a0 ha0).1 (hS b0 hb0).1,
        hK ha hb hab, hK ha0 hb0 hne]
    refine ⟨Nat.gcd a0 b0, Nat.gcd_pos_of_pos_left b0 (Nat.pos_of_ne_zero (hS a0 ha0).1),
      ?_, ?_⟩
    · intro a ha b hb hab
      exact hgcd a ha b hb hab
    · intro a ha
      obtain ⟨b, hb, hab⟩ : ∃ b ∈ S, a ≠ b := by
        by_cases h1 : a = a0
        · refine ⟨b0, hb0, ?_⟩
          rintro rfl
          exact hne h1.symm
        · exact ⟨a0, ha0, h1⟩
      rw [← hgcd a ha b hb hab]
      refine ⟨a / Nat.gcd a b, (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm, ?_⟩
      exact e535_coprime (hS a ha).1 (hS b hb).1 (fun p hp hpa hpb =>
        e535_consistent (hS a ha).1 (hS b hb).1 (hS a ha).2 (hS b hb).2 hp hpa hpb)
  · refine ⟨1, Nat.one_pos, ?_, ?_⟩
    · intro a ha b hb hab
      exact absurd ⟨a, ha, b, hb, hab⟩ h
    · intro a ha
      exact ⟨a, (one_mul a).symm, Nat.gcd_one_right a⟩

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1.H2 := by
  intro r k A hA
  classical
  set D : Finset ℕ := A.biUnion OMA.Helpers.e535Enc with hD
  have hcount : ∀ n ∈ A, 2 ^ k * (D.powerset.filter
      (fun U => U ∩ OMA.Helpers.e535Enc n = OMA.Helpers.e535Top n)).card = 2 ^ D.card := by
    intro n hn
    have hsub : OMA.Helpers.e535Enc n ⊆ D := Finset.subset_biUnion_of_mem _ hn
    have hcard : (OMA.Helpers.e535Enc n).card = k := by
      rw [OMA.Helpers.e535_card_enc]
      exact (hA n hn).2
    rw [OMA.Helpers.e535_count D _ _ (OMA.Helpers.e535_top_subset n) hsub, hcard, ← pow_add]
    congr 1
    have := Finset.card_le_card hsub
    omega
  have hsum : ∑ U ∈ D.powerset, A.card = ∑ U ∈ D.powerset, 2 ^ k *
      (A.filter (fun n => U ∩ OMA.Helpers.e535Enc n = OMA.Helpers.e535Top n)).card := by
    calc ∑ U ∈ D.powerset, A.card = ∑ n ∈ A, 2 ^ D.card := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_powerset, smul_eq_mul,
            smul_eq_mul, mul_comm]
      _ = ∑ n ∈ A, 2 ^ k * (D.powerset.filter
            (fun U => U ∩ OMA.Helpers.e535Enc n = OMA.Helpers.e535Top n)).card :=
          (Finset.sum_congr rfl hcount).symm
      _ = 2 ^ k * ∑ n ∈ A, (D.powerset.filter
            (fun U => U ∩ OMA.Helpers.e535Enc n = OMA.Helpers.e535Top n)).card := by
          rw [Finset.mul_sum]
      _ = 2 ^ k * ∑ U ∈ D.powerset,
            (A.filter (fun n => U ∩ OMA.Helpers.e535Enc n = OMA.Helpers.e535Top n)).card := by
          congr 1
          simp only [Finset.card_filter]
          exact Finset.sum_comm
      _ = ∑ U ∈ D.powerset, 2 ^ k *
            (A.filter (fun n => U ∩ OMA.Helpers.e535Enc n = OMA.Helpers.e535Top n)).card := by
          rw [Finset.mul_sum]
  obtain ⟨U, -, hle⟩ := Finset.exists_le_of_sum_le ⟨∅, Finset.empty_mem_powerset D⟩ hsum.le
  refine ⟨A.filter (fun n => U ∩ OMA.Helpers.e535Enc n = OMA.Helpers.e535Top n),
    Finset.filter_subset _ _, hle, OMA.Helpers.e535Enc, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).1
    have hb' := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).1
    have ha1 := (hA a ha').1
    have hb1 := (hA b hb').1
    exact OMA.Helpers.e535_enc_inj (by omega) (by omega) hab
  · intro n hn
    rw [OMA.Helpers.e535_card_enc]
    exact (hA n (Finset.mem_filter.mp hn).1).2
  · rintro S hS - ⟨K, hK⟩
    apply OMA.Helpers.e535_lift U S _ K hK
    intro a ha
    have h1 := Finset.mem_filter.mp (hS ha)
    have h2 := (hA a h1.1).1
    exact ⟨by omega, h1.2⟩
