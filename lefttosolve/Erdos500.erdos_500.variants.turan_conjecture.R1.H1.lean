import OMAReductions.R_Erdos500_erdos_500_variants_turan_conjecture_R1
import Mathlib

/-!
# Step H1 of the reduction Erdos500.erdos_500.variants.turan_conjecture.R1

Turan's construction. Colour the vertex v of Fin n by v mod 3. A triple is an edge when the sum
of its three colours is not 2 mod 3 and the triple is not monochromatic; equivalently, its
colours are all distinct, or two equal colours i and the third colour i + 1. A finite check on
the colours of four vertices shows that no four vertices span all four triples.

With m = n / 3, the vertices 3a, 3b + 1, 3c + 2 (a, b, c below m) give m^3 transversal edges, and
for each class t the vertices 3b + t, 3c + t, 3a + (t + 1) mod 3 (b below c below m) give
m * m (m - 1) / 2 further edges. These are counted by an injection from an explicit index set,
so the extremal number is at least (5/2) m^3 - (3/2) m^2, which beats (5/9 - eps) (n choose 3)
once eps m is at least 3.

Only upstream definitions are used, together with Mathlib.
-/

namespace OMA.Helpers

open Finset

/-- Turan's edge rule on residues mod three. -/
def turQ (x y z : ℕ) : Prop :=
  (x % 3 + y % 3 + z % 3) % 3 ≠ 2 ∧ ¬ (x % 3 = y % 3 ∧ y % 3 = z % 3)

theorem turQ_noK4 (a b c d : ℕ) (h1 : turQ a b c) (h2 : turQ a b d) (h3 : turQ a c d)
    (h4 : turQ b c d) : False := by
  have key : ∀ x y z w : Fin 3,
      ¬ (((x.val + y.val + z.val) % 3 ≠ 2 ∧ ¬ (x.val = y.val ∧ y.val = z.val)) ∧
        ((x.val + y.val + w.val) % 3 ≠ 2 ∧ ¬ (x.val = y.val ∧ y.val = w.val)) ∧
        ((x.val + z.val + w.val) % 3 ≠ 2 ∧ ¬ (x.val = z.val ∧ z.val = w.val)) ∧
        ((y.val + z.val + w.val) % 3 ≠ 2 ∧ ¬ (y.val = z.val ∧ z.val = w.val))) := by
    decide
  exact key ⟨a % 3, Nat.mod_lt _ (by norm_num)⟩ ⟨b % 3, Nat.mod_lt _ (by norm_num)⟩
    ⟨c % 3, Nat.mod_lt _ (by norm_num)⟩ ⟨d % 3, Nat.mod_lt _ (by norm_num)⟩ ⟨h1, h2, h3, h4⟩

/-- The edge predicate on a set of vertices. -/
def turP {n : ℕ} (e : Finset (Fin n)) : Prop :=
  ∀ x ∈ e, ∀ y ∈ e, ∀ z ∈ e, x ≠ y → y ≠ z → x ≠ z → turQ x.val y.val z.val

theorem turan_free (n : ℕ) (H : Finset (Finset (Fin n))) (hH : ∀ e ∈ H, turP e) :
    ¬ H.ContainsCompleteHypergraph 3 4 := by
  rintro ⟨S, hS, hsub⟩
  obtain ⟨a, ha⟩ : S.Nonempty := by
    rw [← Finset.card_pos, hS]; norm_num
  have h3 : (S.erase a).card = 3 := by rw [Finset.card_erase_of_mem ha, hS]
  obtain ⟨b, c, d, hbc, hbd, hcd, hE⟩ := Finset.card_eq_three.1 h3
  have hb : b ∈ S.erase a := by rw [hE]; simp
  have hc : c ∈ S.erase a := by rw [hE]; simp
  have hd : d ∈ S.erase a := by rw [hE]; simp
  rw [Finset.mem_erase] at hb hc hd
  have mem : ∀ x y z : Fin n, x ∈ S → y ∈ S → z ∈ S → x ≠ y → x ≠ z → y ≠ z →
      turQ x.val y.val z.val := by
    intro x y z hx hy hz hxy hxz hyz
    have hm : ({x, y, z} : Finset (Fin n)) ∈ S.powersetCard 3 := by
      rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_eq_three.2 ⟨x, y, z, hxy, hxz, hyz, rfl⟩⟩
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    exact hH _ (hsub hm) x (by simp) y (by simp) z (by simp) hxy hyz hxz
  exact turQ_noK4 a.val b.val c.val d.val
    (mem a b c ha hb.2 hc.2 (Ne.symm hb.1) (Ne.symm hc.1) hbc)
    (mem a b d ha hb.2 hd.2 (Ne.symm hb.1) (Ne.symm hd.1) hbd)
    (mem a c d ha hc.2 hd.2 (Ne.symm hc.1) (Ne.symm hd.1) hcd)
    (mem b c d hb.2 hc.2 hd.2 hbc hbd hcd)

theorem le_extremal (n r : ℕ) (P : Finset (Finset (Fin n)) → Prop) (H : Finset (Finset (Fin n)))
    (h1 : H ⊆ (Finset.univ : Finset (Fin n)).powersetCard r) (h2 : P H) :
    H.card ≤ Hypergraph.extremalNumber n r P := by
  classical
  unfold Hypergraph.extremalNumber
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 h1, h2⟩)

/-- A vertex given by a natural number, clamped into range. -/
def tvtx (n : ℕ) (hn : 0 < n) (k : ℕ) : Fin n := ⟨min k (n - 1), by omega⟩

theorem tvtx_val (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n) : (tvtx n hn k).val = k := by
  simp only [tvtx]
  omega

/-- Pairs `(c, b)` with `b < c < m`. -/
def tL (m : ℕ) : Finset (ℕ × ℕ) :=
  ((range m).sigma fun c => range c).image fun x => (x.1, x.2)

theorem mem_tL (m : ℕ) (p : ℕ × ℕ) : p ∈ tL m ↔ p.1 < m ∧ p.2 < p.1 := by
  constructor
  · intro h
    obtain ⟨⟨c, b⟩, hcb, rfl⟩ := Finset.mem_image.1 h
    simpa using hcb
  · rintro ⟨h1, h2⟩
    exact Finset.mem_image.2 ⟨⟨p.1, p.2⟩, by simp [h1, h2], rfl⟩

theorem card_tL (m : ℕ) : (tL m).card = ∑ c ∈ range m, c := by
  rw [tL, Finset.card_image_of_injective, Finset.card_sigma]
  · simp
  · rintro ⟨c, b⟩ ⟨c', b'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- The index set of the construction. -/
def tDom (m : ℕ) : Finset ((ℕ × ℕ × ℕ) ⊕ (ℕ × ℕ × (ℕ × ℕ))) :=
  (range m ×ˢ range m ×ˢ range m).disjSum (range 3 ×ˢ range m ×ˢ tL m)

theorem card_tDom (m : ℕ) : (tDom m).card = m ^ 3 + 3 * m * ∑ c ∈ range m, c := by
  rw [tDom, Finset.card_disjSum, Finset.card_product, Finset.card_product, Finset.card_product,
    Finset.card_product, card_tL]
  simp only [Finset.card_range]
  ring

/-- The edges of Turan's construction indexed by `tDom`. -/
def tMap (n : ℕ) (hn : 0 < n) : (ℕ × ℕ × ℕ) ⊕ (ℕ × ℕ × (ℕ × ℕ)) → Finset (Fin n) :=
  Sum.elim (fun p => {tvtx n hn (3 * p.1), tvtx n hn (3 * p.2.1 + 1), tvtx n hn (3 * p.2.2 + 2)})
    (fun q => {tvtx n hn (3 * q.2.2.2 + q.1), tvtx n hn (3 * q.2.2.1 + q.1),
      tvtx n hn (3 * q.2.1 + (q.1 + 1) % 3)})

theorem turan_count (n : ℕ) (hn : 0 < n) :
    (n / 3) ^ 3 + 3 * (n / 3) * (∑ c ∈ range (n / 3), c) ≤ Hypergraph.cliqueExtremalNumber n 3 4 := by
  classical
  have h3m : 3 * (n / 3) ≤ n := by omega
  set m := n / 3 with hm
  let H : Finset (Finset (Fin n)) := (univ.powersetCard 3).filter turP
  have maps : Set.MapsTo (tMap n hn) (tDom m) H := by
    intro x hx
    simp only [Finset.mem_coe] at hx ⊢
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    rcases x with ⟨a, b, c⟩ | ⟨t, a, c, b⟩
    · simp only [tDom, Finset.inl_mem_disjSum, Finset.mem_product, Finset.mem_range] at hx
      simp only [tMap, Sum.elim_inl]
      refine ⟨⟨Finset.subset_univ _, Finset.card_eq_three.2 ⟨_, _, _, ?_, ?_, ?_, rfl⟩⟩, ?_⟩
      · simp only [ne_eq, Fin.ext_iff]
        rw [tvtx_val _ _ _ (by omega), tvtx_val _ _ _ (by omega)]
        omega
      · simp only [ne_eq, Fin.ext_iff]
        rw [tvtx_val _ _ _ (by omega), tvtx_val _ _ _ (by omega)]
        omega
      · simp only [ne_eq, Fin.ext_iff]
        rw [tvtx_val _ _ _ (by omega), tvtx_val _ _ _ (by omega)]
        omega
      · intro x hx y hy z hz hxy hyz hxz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
          rcases hz with rfl | rfl | rfl <;>
          simp (disch := omega) only [turQ, ne_eq, Fin.ext_iff, tvtx_val, not_true_eq_false]
            at hxy hyz hxz ⊢ <;>
          omega
    · simp only [tDom, Finset.inr_mem_disjSum, Finset.mem_product, Finset.mem_range,
        mem_tL] at hx
      simp only [tMap, Sum.elim_inr]
      refine ⟨⟨Finset.subset_univ _, Finset.card_eq_three.2 ⟨_, _, _, ?_, ?_, ?_, rfl⟩⟩, ?_⟩
      · simp only [ne_eq, Fin.ext_iff]
        rw [tvtx_val _ _ _ (by omega), tvtx_val _ _ _ (by omega)]
        omega
      · simp only [ne_eq, Fin.ext_iff]
        rw [tvtx_val _ _ _ (by omega), tvtx_val _ _ _ (by omega)]
        omega
      · simp only [ne_eq, Fin.ext_iff]
        rw [tvtx_val _ _ _ (by omega), tvtx_val _ _ _ (by omega)]
        omega
      · intro x hx y hy z hz hxy hyz hxz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
          rcases hz with rfl | rfl | rfl <;>
          simp (disch := omega) only [turQ, ne_eq, Fin.ext_iff, tvtx_val, not_true_eq_false]
            at hxy hyz hxz ⊢ <;>
          omega
  have inj : Set.InjOn (tMap n hn) (tDom m) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    rcases x with ⟨a, b, c⟩ | ⟨t, a, c, b⟩ <;> rcases y with ⟨a', b', c'⟩ | ⟨t', a', c', b'⟩ <;>
      simp only [tDom, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, Finset.mem_product,
        Finset.mem_range, mem_tL] at hx hy <;>
      simp only [tMap, Sum.elim_inl, Sum.elim_inr] at hxy <;>
      have h1 := (Finset.ext_iff.1 hxy _).1 (Finset.mem_insert_self _ _) <;>
      have h2 := (Finset.ext_iff.1 hxy _).1 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) <;>
      have h3 := (Finset.ext_iff.1 hxy _).1 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _))) <;>
      simp (disch := omega) only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff,
        tvtx_val] at h1 h2 h3 <;>
      simp only [Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq] <;>
      omega
  calc m ^ 3 + 3 * m * (∑ c ∈ range m, c) = (tDom m).card := (card_tDom m).symm
    _ ≤ H.card := Finset.card_le_card_of_injOn _ maps inj
    _ ≤ Hypergraph.cliqueExtremalNumber n 3 4 := by
      unfold Hypergraph.cliqueExtremalNumber
      exact le_extremal n 3 _ H (Finset.filter_subset _ _)
        (turan_free n H (fun e he => (Finset.mem_filter.1 he).2))

theorem six_choose_three_le (n : ℕ) : 6 * n.choose 3 ≤ n ^ 3 := by
  have h := Nat.descFactorial_le_pow n 3
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  simpa [Nat.factorial] using h

theorem turan_poly (ε x : ℝ) (hε : 0 < ε) (hx : 1 ≤ x) (hεx : 3 ≤ ε * x) :
    (5 / 9 - ε) * ((3 * x + 2) ^ 3 / 6) ≤ x ^ 3 + 3 / 2 * (x * (x * (x - 1))) := by
  have h3 : 3 * x ^ 2 ≤ ε * x * x ^ 2 := mul_le_mul_of_nonneg_right hεx (sq_nonneg x)
  have hxx : x ≤ x ^ 2 := by nlinarith
  have e1 : 0 ≤ ε * x ^ 2 := by positivity
  have e2 : 0 ≤ ε * x := by positivity
  nlinarith

end OMA.Helpers

open Filter in
theorem OMA.solution : OMA.R_Erdos500_erdos_500_variants_turan_conjecture_R1.H1 := by
  unfold OMA.R_Erdos500_erdos_500_variants_turan_conjecture_R1.H1
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_ge (3 / ε)
  rw [Filter.eventually_atTop]
  refine ⟨3 * N + 3, fun n hn => ?_⟩
  have hn0 : 0 < n := by omega
  have hc := OMA.Helpers.turan_count n hn0
  have hC := OMA.Helpers.six_choose_three_le n
  have hnm : n ≤ 3 * (n / 3) + 2 := by omega
  have hmN : N + 1 ≤ n / 3 := by omega
  have hS := Finset.sum_range_id_mul_two (n / 3)
  set m := n / 3 with hm
  set S := ∑ c ∈ Finset.range m, c with hSdef
  have h1m : 1 ≤ m := by omega
  have hcR : ((m ^ 3 + 3 * m * S : ℕ) : ℝ) ≤ (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) := by
    exact_mod_cast hc
  push_cast at hcR
  have hCR : 6 * (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 := by exact_mod_cast hC
  have hnmR : (n : ℝ) ≤ 3 * m + 2 := by exact_mod_cast hnm
  have hSR : (S : ℝ) * 2 = m * (m - 1) := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) hS
    simp only [Nat.cast_mul, Nat.cast_sub h1m, Nat.cast_one, Nat.cast_ofNat] at h
    exact h
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast h1m
  have hNR : (N : ℝ) + 1 ≤ m := by exact_mod_cast hmN
  have hεm : 3 ≤ ε * m := by
    have h1 : 3 ≤ ε * N := by
      have := mul_le_mul_of_nonneg_left hN hε.le
      rwa [mul_div_cancel₀ _ hε.ne'] at this
    nlinarith
  have hC0 : (0 : ℝ) ≤ (n.choose 3 : ℝ) := Nat.cast_nonneg _
  have hpoly := OMA.Helpers.turan_poly ε m hε hmR hεm
  have hRHS : (m : ℝ) ^ 3 + 3 / 2 * (m * (m * (m - 1))) = (m : ℝ) ^ 3 + 3 * m * S := by
    rw [← hSR]
    ring
  refine le_trans ?_ hcR
  rw [← hRHS]
  rcases le_or_gt (5 / 9) ε with h | h
  · have h0 : (5 / 9 - ε) * (n.choose 3 : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hC0
    have h1 : (0 : ℝ) ≤ (m : ℝ) ^ 3 + 3 / 2 * (m * (m * (m - 1))) := by
      have : (0 : ℝ) ≤ m - 1 := by linarith
      positivity
    linarith
  · refine le_trans ?_ hpoly
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    have hn3 : (n : ℝ) ^ 3 ≤ (3 * m + 2) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hnmR 3
    linarith
