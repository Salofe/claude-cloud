import OMAReductions.R_Erdos560_erdos_560_variants_conlon_fox_wigderson_R1
import Mathlib

/-!
# Step H1 of the reduction Erdos560.erdos_560.variants.conlon_fox_wigderson.R1

The size Ramsey number of K_{n,n} is O(n^3 2^n). Host graph: K_{2m,b} with m = n^2 and
b = n 2^(n+2). For a red/blue colouring, every vertex v of the b-side has a colour class
M v of size at least m among its 2m neighbours. Counting pairs (v, S) with S an n-subset of
M v against the 2 C(2m,n) pairs (colour, S) gives, by pigeonhole, n vertices sharing the
same colour and the same n-set S, i.e. a monochromatic K_{n,n}. The counting condition
2 C(2m,n) (n-1) < b C(m,n) follows from the descending-factorial comparison
(2n)^n (2m)_n <= (2(2n+1))^n (m)_n and Bernoulli's inequality (2n+1)^n <= 2 (2n)^n.
The host has 2m b = 8 n^3 2^n edges.
-/

namespace OMA.Helpers

open SimpleGraph Finset

/-- A graph on any finite type with the Ramsey property bounds the size Ramsey number. -/
theorem sizeRamsey_le_ncard {V α : Type*} [Fintype V] [Fintype α] (G : SimpleGraph α)
    (F : SimpleGraph V)
    (hF : ∀ R : SimpleGraph V, R ≤ F → G.IsContained R ∨ G.IsContained (F \ R)) :
    sizeRamsey G G ≤ F.edgeSet.ncard := by
  classical
  let e := Fintype.equivFin V
  let F' : SimpleGraph (Fin (Fintype.card V)) := F.map e
  apply Nat.sInf_le
  refine ⟨Fintype.card V, F', ?_, ?_⟩
  · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact (Nat.card_congr (Iso.map e F).mapEdgeSet).symm
  · intro R' hR'
    let R : SimpleGraph V := R'.comap e
    have hmap : ∀ x y : V, F'.Adj (e x) (e y) ↔ F.Adj x y := by
      intro x y
      exact (Iso.map e F).map_rel_iff
    have hRF : R ≤ F := by
      intro x y h
      exact (hmap x y).mp (hR' h)
    have hblue : F \ R ≤ (F' \ R').comap e := by
      intro x y h
      exact ⟨(hmap x y).mpr h.1, h.2⟩
    rcases hF R hRF with h | h
    · left
      exact h.trans ⟨(Iso.comap e R').toEmbedding.toCopy⟩
    · right
      exact (h.mono_right hblue).trans ⟨(Iso.comap e (F' \ R')).toEmbedding.toCopy⟩

/-- Edges of the complete bipartite graph `K_{a,b}`. -/
theorem kbip_ncard_le (a b : ℕ) :
    (completeBipartiteGraph (Fin a) (Fin b)).edgeSet.ncard ≤ a * b := by
  have hsub : (completeBipartiteGraph (Fin a) (Fin b)).edgeSet ⊆
      (fun p : Fin a × Fin b => s(Sum.inl p.1, Sum.inr p.2)) '' Set.univ := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [mem_edgeSet] at he
      rcases x with x | x <;> rcases y with y | y <;> simp [completeBipartiteGraph] at he
      · exact ⟨(x, y), trivial, rfl⟩
      · exact ⟨(y, x), trivial, Sym2.eq_swap⟩
  calc _ ≤ ((fun p : Fin a × Fin b => s(Sum.inl p.1, Sum.inr p.2)) '' Set.univ).ncard :=
        Set.ncard_le_ncard hsub
    _ ≤ (Set.univ : Set (Fin a × Fin b)).ncard := Set.ncard_image_le
    _ = a * b := by simp

/-- A copy of `K_{n,n}` from two `n`-sets joined completely. -/
theorem kbip_copy {a b n : ℕ} (H : SimpleGraph (Fin a ⊕ Fin b)) (S : Finset (Fin a))
    (T : Finset (Fin b)) (hS : S.card = n) (hT : T.card = n)
    (h : ∀ i ∈ S, ∀ j ∈ T, H.Adj (Sum.inl i) (Sum.inr j)) :
    (completeBipartiteGraph (Fin n) (Fin n)).IsContained H := by
  refine ⟨⟨⟨Sum.map (S.orderEmbOfFin hS) (T.orderEmbOfFin hT), ?_⟩, ?_⟩⟩
  · intro x y hxy
    rcases x with x | x <;> rcases y with y | y <;> simp [completeBipartiteGraph] at hxy ⊢
    · exact h _ (S.orderEmbOfFin_mem hS x) _ (T.orderEmbOfFin_mem hT y)
    · exact (h _ (S.orderEmbOfFin_mem hS y) _ (T.orderEmbOfFin_mem hT x)).symm
  · exact Sum.map_injective.mpr ⟨(S.orderEmbOfFin hS).injective, (T.orderEmbOfFin hT).injective⟩

/-- Ramsey property of `K_{2m,b}` for `K_{n,n}` under a counting condition. -/
theorem kbip_ramsey (n m b : ℕ)
    (hcount : 2 * Nat.choose (2 * m) n * (n - 1) < b * Nat.choose m n)
    (R : SimpleGraph (Fin (2 * m) ⊕ Fin b))
    (_hR : R ≤ completeBipartiteGraph (Fin (2 * m)) (Fin b)) :
    (completeBipartiteGraph (Fin n) (Fin n)).IsContained R ∨
    (completeBipartiteGraph (Fin n) (Fin n)).IsContained
      (completeBipartiteGraph (Fin (2 * m)) (Fin b) \ R) := by
  classical
  let red : Fin b → Finset (Fin (2 * m)) := fun v =>
    univ.filter (fun i => R.Adj (Sum.inl i) (Sum.inr v))
  let blue : Fin b → Finset (Fin (2 * m)) := fun v =>
    univ.filter (fun i => ¬ R.Adj (Sum.inl i) (Sum.inr v))
  let c : Fin b → Bool := fun v => decide (m ≤ (red v).card)
  let M : Fin b → Finset (Fin (2 * m)) := fun v => if c v then red v else blue v
  have hM : ∀ v, m ≤ (M v).card := by
    intro v
    have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * m))))
      (fun i => R.Adj (Sum.inl i) (Sum.inr v))
    simp only [card_univ, Fintype.card_fin] at h
    by_cases hc : m ≤ (red v).card
    · simp only [M, c, hc, decide_true, if_true]
    · simp only [M, c, hc, decide_false, if_false, Bool.false_eq_true]
      simp only [red, blue] at hc ⊢
      omega
  let s : Finset (Σ _ : Fin b, Finset (Fin (2 * m))) := univ.sigma (fun v => powersetCard n (M v))
  let t : Finset (Bool × Finset (Fin (2 * m))) := univ ×ˢ powersetCard n univ
  let f : (Σ _ : Fin b, Finset (Fin (2 * m))) → Bool × Finset (Fin (2 * m)) :=
    fun x => (c x.1, x.2)
  have hf : ∀ x ∈ s, f x ∈ t := by
    intro x hx
    simp only [s, mem_sigma, mem_univ, true_and, mem_powersetCard] at hx
    simp only [t, f, mem_product, mem_univ, true_and, mem_powersetCard, subset_univ]
    exact hx.2
  have hs : b * Nat.choose m n ≤ s.card := by
    rw [card_sigma]
    calc b * Nat.choose m n = ∑ _v : Fin b, Nat.choose m n := by simp
      _ ≤ ∑ v : Fin b, (powersetCard n (M v)).card := by
        apply sum_le_sum
        intro v _
        rw [card_powersetCard]
        exact Nat.choose_le_choose n (hM v)
  have ht : t.card = 2 * Nat.choose (2 * m) n := by
    simp [t, card_product, card_powersetCard]
  obtain ⟨y, hy, hlt⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf (n := n - 1)
    (by rw [ht]; omega)
  have hSy : y.2.card = n := by
    simp only [t, mem_product, mem_univ, true_and, mem_powersetCard] at hy
    exact hy.2
  let Fb := s.filter (fun x => f x = y)
  have hFb : ∀ x ∈ Fb, c x.1 = y.1 ∧ x.2 = y.2 ∧ y.2 ⊆ M x.1 := by
    intro x hx
    simp only [Fb, s, f, mem_filter, mem_sigma, mem_univ, true_and, mem_powersetCard] at hx
    obtain ⟨⟨hsub, _⟩, hxy⟩ := hx
    rw [← hxy]
    exact ⟨rfl, rfl, hsub⟩
  let T := Fb.image Sigma.fst
  have hTcard : n ≤ T.card := by
    rw [card_image_of_injOn]
    · change n - 1 < Fb.card at hlt
      omega
    · intro x hx x' hx' hxx
      obtain ⟨v, S⟩ := x
      obtain ⟨v', S'⟩ := x'
      have h1 := hFb _ hx
      have h2 := hFb _ hx'
      simp only at hxx h1 h2
      subst hxx
      rw [h1.2.1, h2.2.1]
  have hT : ∀ v ∈ T, c v = y.1 ∧ y.2 ⊆ M v := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hv
    exact ⟨(hFb x hx).1, (hFb x hx).2.2⟩
  obtain ⟨T', hT'T, hT'card⟩ := exists_subset_card_eq hTcard
  rcases hy1 : y.1 with _ | _
  · right
    refine kbip_copy _ y.2 T' hSy hT'card ?_
    intro i hi j hj
    have hj' := hT j (hT'T hj)
    rw [hy1] at hj'
    have hMj : M j = blue j := by simp [M, hj'.1]
    have hi' := hj'.2 hi
    rw [hMj] at hi'
    simp only [blue, mem_filter, mem_univ, true_and] at hi'
    refine ⟨?_, hi'⟩
    simp [completeBipartiteGraph]
  · left
    refine kbip_copy _ y.2 T' hSy hT'card ?_
    intro i hi j hj
    have hj' := hT j (hT'T hj)
    rw [hy1] at hj'
    have hMj : M j = red j := by simp [M, hj'.1]
    have hi' := hj'.2 hi
    rw [hMj] at hi'
    simp only [red, mem_filter, mem_univ, true_and] at hi'
    exact hi'

/-- One factor of the descending product. -/
theorem desc_step (n k : ℕ) (hk : k < n) :
    2 * n * (2 * n ^ 2 - k) ≤ 2 * (2 * n + 1) * (n ^ 2 - k) := by
  have h1 : k ≤ n ^ 2 := by nlinarith
  have h2 : k ≤ 2 * n ^ 2 := by nlinarith
  zify [h1, h2]
  have h3 : (k : ℤ) + 1 ≤ n := by exact_mod_cast hk
  have h4 : (0 : ℤ) ≤ k := by positivity
  nlinarith

theorem desc_bound (n : ℕ) : ∀ k, k ≤ n →
    (2 * n) ^ k * (2 * n ^ 2).descFactorial k ≤ (2 * (2 * n + 1)) ^ k * (n ^ 2).descFactorial k
  | 0, _ => by simp
  | k + 1, hk => by
    have ih := desc_bound n k (by omega)
    have hs := desc_step n k (by omega)
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ (2 * n) k, pow_succ (2 * (2 * n + 1)) k]
    calc (2 * n) ^ k * (2 * n) * ((2 * n ^ 2 - k) * (2 * n ^ 2).descFactorial k)
        = ((2 * n) ^ k * (2 * n ^ 2).descFactorial k) * (2 * n * (2 * n ^ 2 - k)) := by ring
      _ ≤ ((2 * (2 * n + 1)) ^ k * (n ^ 2).descFactorial k) * (2 * (2 * n + 1) * (n ^ 2 - k)) :=
        Nat.mul_le_mul ih hs
      _ = _ := by ring

theorem pow_bound (n : ℕ) : (2 * n + 1) ^ n ≤ 2 * (2 * n) ^ n := by
  have hx : (0 : ℝ) < 2 * n + 1 := by positivity
  have ha : (-2 : ℝ) ≤ -1 / (2 * n + 1) := by
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ hx]
    have : (0 : ℝ) ≤ n := by positivity
    linarith
  have h := one_add_mul_le_pow ha n
  have e : (1 : ℝ) + -1 / (2 * n + 1) = (2 * n) / (2 * n + 1) := by
    field_simp
    ring
  rw [e, div_pow] at h
  have hp : (0 : ℝ) < (2 * n + 1) ^ n := by positivity
  have hl : (1 : ℝ) / 2 ≤ 1 + n * (-1 / (2 * n + 1)) := by
    rw [mul_div_assoc', div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    rw [show (1 : ℝ) + n * -1 / (2 * n + 1) = (n + 1) / (2 * n + 1) by field_simp; ring]
    rw [div_mul_eq_mul_div, le_div_iff₀ hx]
    linarith
  have key := hl.trans h
  rw [le_div_iff₀ hp] at key
  have key' : ((2 * n + 1 : ℕ) : ℝ) ^ n ≤ ((2 * (2 * n) ^ n : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast key'

theorem count_bound (n : ℕ) (hn : 1 ≤ n) :
    2 * Nat.choose (2 * n ^ 2) n * (n - 1) < n * 2 ^ (n + 2) * Nat.choose (n ^ 2) n := by
  have hd := desc_bound n n le_rfl
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at hd
  have hfac : 0 < n.factorial := Nat.factorial_pos n
  have hd' : (2 * n) ^ n * Nat.choose (2 * n ^ 2) n ≤
      (2 * (2 * n + 1)) ^ n * Nat.choose (n ^ 2) n := by
    have : ((2 * n) ^ n * Nat.choose (2 * n ^ 2) n) * n.factorial ≤
        ((2 * (2 * n + 1)) ^ n * Nat.choose (n ^ 2) n) * n.factorial := by
      calc _ = (2 * n) ^ n * (n.factorial * Nat.choose (2 * n ^ 2) n) := by ring
        _ ≤ (2 * (2 * n + 1)) ^ n * (n.factorial * Nat.choose (n ^ 2) n) := hd
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right this hfac
  have hpb := pow_bound n
  have hC : 0 < Nat.choose (n ^ 2) n := Nat.choose_pos (by nlinarith)
  have hP : 0 < (2 * n) ^ n := by positivity
  have h3 : (2 * n) ^ n * (2 * Nat.choose (2 * n ^ 2) n * (n - 1)) <
      (2 * n) ^ n * (n * 2 ^ (n + 2) * Nat.choose (n ^ 2) n) := by
    have e1 : (2 * (2 * n + 1)) ^ n = 2 ^ n * (2 * n + 1) ^ n := by rw [mul_pow]
    rw [e1] at hd'
    calc (2 * n) ^ n * (2 * Nat.choose (2 * n ^ 2) n * (n - 1))
        = 2 * (n - 1) * ((2 * n) ^ n * Nat.choose (2 * n ^ 2) n) := by ring
      _ ≤ 2 * (n - 1) * (2 ^ n * (2 * n + 1) ^ n * Nat.choose (n ^ 2) n) :=
        Nat.mul_le_mul_left _ hd'
      _ ≤ 2 * (n - 1) * (2 ^ n * (2 * (2 * n) ^ n) * Nat.choose (n ^ 2) n) := by
        apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul_right
        exact Nat.mul_le_mul_left _ hpb
      _ = (n - 1) * (2 ^ (n + 2) * (2 * n) ^ n * Nat.choose (n ^ 2) n) := by ring
      _ < n * (2 ^ (n + 2) * (2 * n) ^ n * Nat.choose (n ^ 2) n) := by
        apply Nat.mul_lt_mul_of_pos_right (by omega)
        positivity
      _ = (2 * n) ^ n * (n * 2 ^ (n + 2) * Nat.choose (n ^ 2) n) := by ring
  exact Nat.lt_of_mul_lt_mul_left h3

theorem sizeRamsey_bound (n : ℕ) (hn : 1 ≤ n) :
    sizeRamsey (completeBipartiteGraph (Fin n) (Fin n))
      (completeBipartiteGraph (Fin n) (Fin n)) ≤ 8 * n ^ 3 * 2 ^ n := by
  have h := sizeRamsey_le_ncard (completeBipartiteGraph (Fin n) (Fin n))
    (completeBipartiteGraph (Fin (2 * n ^ 2)) (Fin (n * 2 ^ (n + 2))))
    (kbip_ramsey n (n ^ 2) (n * 2 ^ (n + 2)) (count_bound n hn))
  have h2 := kbip_ncard_le (2 * n ^ 2) (n * 2 ^ (n + 2))
  calc _ ≤ _ := h
    _ ≤ _ := h2
    _ = 8 * n ^ 3 * 2 ^ n := by ring

end OMA.Helpers

open Filter Asymptotics in
theorem OMA.solution : OMA.R_Erdos560_erdos_560_variants_conlon_fox_wigderson_R1.H1 := by
  unfold OMA.R_Erdos560_erdos_560_variants_conlon_fox_wigderson_R1.H1
  apply Asymptotics.IsBigO.of_bound 8
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have h := OMA.Helpers.sizeRamsey_bound n hn
  have h' : ((SimpleGraph.sizeRamsey (completeBipartiteGraph (Fin n) (Fin n))
      (completeBipartiteGraph (Fin n) (Fin n)) : ℕ) : ℝ) ≤ ((8 * n ^ 3 * 2 ^ n : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  linarith
