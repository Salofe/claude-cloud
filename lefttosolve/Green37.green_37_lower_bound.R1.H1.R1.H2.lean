import OMAReductions.R_Green37_green_37_lower_bound_R1_H1_R1

/-!
# Step H2 of the reduction Green37.green_37_lower_bound.R1.H1.R1

Gap compression. Take an optimal cover `A` (it exists since covers exist). Let `U` be the union
of the windows `[a, a + N)` over `a ∈ A` and let `f y` count the elements of `U` below `y`.
Then `f (x + j) = f x + j` for `x ∈ A` and `j ≤ N`, so `f` keeps every progression with
difference `d ≤ N` inside `A` (consecutive terms differ by `d`), and `f` is strictly increasing
on `A` (as `N ≥ 1`). Hence `f '' A` is a cover of the same size, and all its elements are at most
`|U| ≤ |A| N`.
-/

namespace OMA.Helpers

theorem g37c_ap_set_eq (a d k : ℕ) :
    {x | ∃ n : ℕ, ∃ _ : (n : ℕ∞) < (k : ℕ∞), a + n • d = x} =
      (((Finset.range k).image (fun n => a + n * d) : Finset ℕ) : Set ℕ) := by
  ext x
  simp only [Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_range, Set.mem_image,
    Set.mem_Iio, smul_eq_mul, Nat.cast_lt, exists_prop]

theorem g37c_ap_card (a d k : ℕ) (hd : 1 ≤ d) :
    ENat.card {x | ∃ n : ℕ, ∃ _ : (n : ℕ∞) < (k : ℕ∞), a + n • d = x} = (k : ℕ∞) := by
  rw [g37c_ap_set_eq, ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
    Finset.card_image_of_injective _ (fun m n h => by
      have h' : m * d = n * d := by simpa using h
      exact Nat.eq_of_mul_eq_mul_right hd h'), Finset.card_range]

theorem g37c_cover_exists (N k : ℕ) :
    ∃ A : Finset ℕ, Green37.IsAPCover (A : Set ℕ) N k := by
  refine ⟨Finset.range (k * N + 1), ?_⟩
  intro d hd
  refine ⟨0, {x | ∃ n : ℕ, ∃ _ : (n : ℕ∞) < (k : ℕ∞), 0 + n • d = x}, ?_,
    g37c_ap_card 0 d k hd.1, rfl⟩
  intro x hx
  obtain ⟨n, hn, rfl⟩ := hx
  have hn' : n < k := by exact_mod_cast hn
  simp only [Finset.coe_range, Set.mem_Iio, zero_add, smul_eq_mul]
  exact Nat.lt_succ_of_le (Nat.mul_le_mul hn'.le hd.2)

/-- The union of the windows `[a, a + N)`. -/
def g37U (A : Finset ℕ) (N : ℕ) : Finset ℕ := A.biUnion (fun a => Finset.Ico a (a + N))

/-- The compression map. -/
def g37f (A : Finset ℕ) (N : ℕ) (y : ℕ) : ℕ :=
  ((Finset.range y).filter (fun t => t ∈ g37U A N)).card

theorem g37f_succ (A : Finset ℕ) (N y : ℕ) (hy : y ∈ g37U A N) :
    g37f A N (y + 1) = g37f A N y + 1 := by
  unfold g37f
  rw [Finset.range_add_one, Finset.filter_insert, if_pos hy,
    Finset.card_insert_of_notMem (by simp)]

theorem g37f_mono (A : Finset ℕ) (N : ℕ) {y z : ℕ} (h : y ≤ z) :
    g37f A N y ≤ g37f A N z := by
  unfold g37f
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 h))

theorem g37f_shift (A : Finset ℕ) (N : ℕ) {x : ℕ} (hx : x ∈ A) :
    ∀ j : ℕ, j ≤ N → g37f A N (x + j) = g37f A N x + j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hmem : x + j ∈ g37U A N := by
      unfold g37U
      exact Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_Ico.2 ⟨by omega, by omega⟩⟩
    rw [← Nat.add_assoc, g37f_succ A N _ hmem, ih (by omega), Nat.add_assoc]

theorem g37f_bound (A : Finset ℕ) (N y : ℕ) : g37f A N y ≤ A.card * N := by
  have h1 : g37f A N y ≤ (g37U A N).card := by
    unfold g37f
    exact Finset.card_le_card (fun t ht => (Finset.mem_filter.1 ht).2)
  have h2 : (g37U A N).card ≤ ∑ a ∈ A, (Finset.Ico a (a + N)).card := Finset.card_biUnion_le
  have h3 : ∑ a ∈ A, (Finset.Ico a (a + N)).card = A.card * N := by
    simp [Nat.card_Ico]
  omega

theorem g37f_strict (A : Finset ℕ) (N : ℕ) (hN : 1 ≤ N) {x y : ℕ} (hx : x ∈ A)
    (hxy : x < y) : g37f A N x < g37f A N y := by
  have h1 := g37f_shift A N hx 1 hN
  have h2 := g37f_mono A N (show x + 1 ≤ y by omega)
  omega

theorem g37f_ap (A : Finset ℕ) (N : ℕ) {a d k : ℕ} (hdN : d ≤ N)
    (hA : ∀ n : ℕ, n < k → a + n * d ∈ A) :
    ∀ n : ℕ, n < k → g37f A N (a + n * d) = g37f A N a + n * d := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hmem := hA n (by omega)
    have e1 : a + (n + 1) * d = (a + n * d) + d := by ring
    rw [e1, g37f_shift A N hmem d hdN, ih (by omega)]
    ring

theorem g37_image_cover (A : Finset ℕ) (N k : ℕ)
    (hA : Green37.IsAPCover (A : Set ℕ) N k) :
    Green37.IsAPCover ((A.image (g37f A N) : Finset ℕ) : Set ℕ) N k := by
  intro d hd
  obtain ⟨a, s, hsA, -, hs⟩ := hA d hd
  have hmem : ∀ n : ℕ, n < k → a + n * d ∈ A := by
    intro n hn
    have : a + n • d ∈ s := by
      rw [hs]
      exact ⟨n, by exact_mod_cast hn, rfl⟩
    have h' := hsA this
    simpa [smul_eq_mul] using h'
  refine ⟨g37f A N a, {x | ∃ n : ℕ, ∃ _ : (n : ℕ∞) < (k : ℕ∞), g37f A N a + n • d = x}, ?_,
    g37c_ap_card _ d k hd.1, rfl⟩
  intro x hx
  obtain ⟨n, hn, rfl⟩ := hx
  have hn' : n < k := by exact_mod_cast hn
  rw [Finset.coe_image]
  refine ⟨a + n * d, hmem n hn', ?_⟩
  rw [g37f_ap A N hd.2 hmem n hn', smul_eq_mul]

end OMA.Helpers

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1_H1_R1.H2 := by
  intro N k hN _hk
  have hne : { m | ∃ A : Finset ℕ, A.card = m ∧
      Green37.IsAPCover (A : Set ℕ) N k }.Nonempty := by
    obtain ⟨A, hA⟩ := OMA.Helpers.g37c_cover_exists N k
    exact ⟨A.card, A, rfl, hA⟩
  obtain ⟨A, hAc, hA⟩ := Nat.sInf_mem hne
  have hm : Green37.m N k = A.card := by
    unfold Green37.m
    exact hAc.symm
  refine ⟨A.image (OMA.Helpers.g37f A N), ?_, OMA.Helpers.g37_image_cover A N k hA, ?_⟩
  · rw [hm]
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with h | h
    · have := OMA.Helpers.g37f_strict A N hN hx h
      exact absurd hxy (by omega)
    · have := OMA.Helpers.g37f_strict A N hN hy h
      exact absurd hxy (by omega)
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
    rw [hm]
    exact OMA.Helpers.g37f_bound A N y
