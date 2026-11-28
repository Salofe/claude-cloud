import OMAReductions.R_Erdos835_johnson_chromaticNumber_R1

/-!
# Step H1 of Erdos835.johnson_chromaticNumber.R1: the composite case

If `k + 1` is composite then `J(2k, k)` has no proper colouring with `k + 1` colours.

Self-contained argument.  Let `p` be the least prime factor of `k + 1`, so `p ≤ k`.
Fix a set `I` of size `k - p` and let `W` be its complement (size `k + p`).  For a
`(p - 1)`-subset `T'` of `W`, the `k + 1` vertices `I ∪ insert x T'` (`x ∈ W \ T'`) are
pairwise adjacent, so a colouring with at most `k + 1` colours gives each colour to exactly
one of them.  Fixing a colour `b` and double counting the pairs `T' ⊆ T` (`T` a `p`-subset of
`W` with `I ∪ T` coloured `b`) gives `C(k + p, p - 1) = p * N`.  But by Lucas' theorem
`C(k + p, p - 1) ≡ C(p - 1, p - 1) * C((k + 1) / p, 0) = 1 [MOD p]`, a contradiction.
-/

open Finset

namespace OMA.Helpers

theorem inter_insert_insert_eq {α : Type*} [DecidableEq α] (T : Finset α) {x y : α}
    (hxy : x ≠ y) : insert x T ∩ insert y T = T := by
  ext z
  simp only [mem_inter, mem_insert]
  constructor
  · rintro ⟨h1 | h1, h2 | h2⟩
    · exact absurd (h1.symm.trans h2) hxy
    · exact h2
    · exact h1
    · exact h1
  · intro h
    exact ⟨Or.inr h, Or.inr h⟩

theorem key_count {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (W : Finset α) (q : ℕ) (f : Finset α → β)
    (hβ : Fintype.card β ≤ #W - q)
    (hf : ∀ T₁ ⊆ W, ∀ T₂ ⊆ W, #T₁ = q + 1 → #T₂ = q + 1 → T₁ ≠ T₂ →
      #(T₁ ∩ T₂) = q → f T₁ ≠ f T₂)
    (b : β) :
    #(powersetCard q W) * 1 = #({T ∈ powersetCard (q + 1) W | f T = b}) * (q + 1) := by
  apply card_mul_eq_card_mul (fun T' T => T' ⊆ T)
  · intro T' hT'
    rw [mem_powersetCard] at hT'
    obtain ⟨hT'W, hT'card⟩ := hT'
    have hinj : ∀ x ∈ W \ T', ∀ y ∈ W \ T', f (insert x T') = f (insert y T') → x = y := by
      intro x hx y hy hxy
      rw [mem_sdiff] at hx hy
      by_contra hne
      apply hf (insert x T') (insert_subset hx.1 hT'W) (insert y T') (insert_subset hy.1 hT'W)
        (by rw [card_insert_of_notMem hx.2, hT'card]) (by rw [card_insert_of_notMem hy.2, hT'card])
        ?_ ?_ hxy
      · intro h
        apply hne
        have : x ∈ insert y T' := h ▸ mem_insert_self x T'
        rcases mem_insert.1 this with h1 | h1
        · exact h1
        · exact absurd h1 hx.2
      · rw [inter_insert_insert_eq T' hne, hT'card]
    have hsurj : ∃ x ∈ W \ T', f (insert x T') = b := by
      have hcard : #(univ : Finset β) ≤ #(W \ T') := by
        rw [card_univ, card_sdiff_of_subset hT'W, hT'card]
        exact hβ
      obtain ⟨x, hx, hxb⟩ := surj_on_of_inj_on_of_card_le (s := W \ T') (t := (univ : Finset β))
        (fun x _ => f (insert x T')) (fun _ _ => mem_univ _)
        (fun a₁ a₂ ha₁ ha₂ h => hinj a₁ ha₁ a₂ ha₂ h) hcard b (mem_univ b)
      exact ⟨x, hx, hxb.symm⟩
    obtain ⟨x, hx, hxb⟩ := hsurj
    rw [card_eq_one]
    refine ⟨insert x T', ?_⟩
    rw [eq_singleton_iff_unique_mem]
    have hx' := mem_sdiff.1 hx
    constructor
    · rw [mem_bipartiteAbove, mem_filter, mem_powersetCard]
      exact ⟨⟨⟨insert_subset hx'.1 hT'W, by rw [card_insert_of_notMem hx'.2, hT'card]⟩, hxb⟩,
        subset_insert x T'⟩
    · intro T hT
      rw [mem_bipartiteAbove, mem_filter, mem_powersetCard] at hT
      obtain ⟨⟨⟨hTW, hTcard⟩, hTb⟩, hT'T⟩ := hT
      have hcd : #(T \ T') = 1 := by
        rw [card_sdiff_of_subset hT'T, hTcard, hT'card]; simp
      obtain ⟨y, hy⟩ := card_eq_one.1 hcd
      have hyTT : y ∈ T \ T' := by rw [hy]; exact mem_singleton_self y
      have hyT : y ∈ T := (mem_sdiff.1 hyTT).1
      have hyT' : y ∉ T' := (mem_sdiff.1 hyTT).2
      have hTeq : T = insert y T' := by
        ext z
        constructor
        · intro hz
          by_cases hzT' : z ∈ T'
          · exact mem_insert_of_mem hzT'
          · have : z ∈ T \ T' := mem_sdiff.2 ⟨hz, hzT'⟩
            rw [hy, mem_singleton] at this
            rw [this]; exact mem_insert_self y T'
        · intro hz
          rcases mem_insert.1 hz with h | h
          · rw [h]; exact hyT
          · exact hT'T h
      have hyx : y = x := by
        apply hinj y (mem_sdiff.2 ⟨hTW hyT, hyT'⟩) x hx
        rw [← hTeq, hTb, hxb]
      rw [hTeq, hyx]
  · intro T hT
    rw [mem_filter, mem_powersetCard] at hT
    obtain ⟨⟨hTW, hTcard⟩, -⟩ := hT
    have : bipartiteBelow (fun T' T => T' ⊆ T) (powersetCard q W) T = powersetCard q T := by
      ext T'
      rw [mem_bipartiteBelow, mem_powersetCard, mem_powersetCard]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1.trans hTW, h2⟩, h1⟩
    rw [this, card_powersetCard, hTcard, Nat.choose_succ_self_right]

end OMA.Helpers

open Finset SimpleGraph in
theorem OMA.solution : OMA.R_Erdos835_johnson_chromaticNumber_R1.H1 := by
  intro k hk hcomp
  obtain ⟨hk1, hnp⟩ := hcomp
  have hcast : ((k + 2 : ℕ) : ℕ∞) = (k : ℕ∞) + 2 := by push_cast; rfl
  rw [← hcast, le_chromaticNumber_iff_coloring]
  intro m C
  by_contra hlt
  replace hlt : m < k + 2 := by omega
  set p := (k + 1).minFac with hp_def
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpdvd : p ∣ k + 1 := Nat.minFac_dvd _
  have hp2 : 2 ≤ p := hp.two_le
  have hpk : p ≤ k := by
    have h1 : p ≤ k + 1 := Nat.minFac_le (by omega)
    have h2 : p ≠ k + 1 := fun h => hnp (h ▸ hp)
    omega
  obtain ⟨I, -, hI⟩ := exists_subset_card_eq (s := (univ : Finset (Fin (2 * k)))) (n := k - p)
    (by rw [card_univ, Fintype.card_fin]; omega)
  have hWcard : #Iᶜ = k + p := by rw [card_compl, Fintype.card_fin, hI]; omega
  obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset (Fin (2 * k)))) (n := k)
    (by rw [card_univ, Fintype.card_fin]; omega)
  let b0 : Fin m := C ⟨S, hS⟩
  let f : Finset (Fin (2 * k)) → Fin m := fun T =>
    if h : #(I ∪ T) = k then C ⟨I ∪ T, h⟩ else b0
  have hdisj : ∀ T ⊆ Iᶜ, Disjoint I T := by
    intro T hT
    rw [Finset.disjoint_left]
    intro a ha haT
    exact (mem_compl.1 (hT haT)) ha
  have hkey := OMA.Helpers.key_count Iᶜ (p - 1) f ?_ ?_ b0
  · rw [card_powersetCard, hWcard, mul_one, Nat.sub_add_cancel (by omega : 1 ≤ p)] at hkey
    have hdvd : p ∣ (k + p).choose (p - 1) := ⟨_, hkey.trans (mul_comm _ _)⟩
    have := Fact.mk hp
    have hluc := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := k + p) (k := p - 1) (p := p)
    obtain ⟨c, hc⟩ := hpdvd
    have hkp : k + p = p * c + (p - 1) := by omega
    rw [hkp, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega : p - 1 < p),
      Nat.mul_add_div (by omega : p > 0), Nat.div_eq_of_lt (by omega : p - 1 < p),
      Nat.choose_self, Nat.choose_zero_right, mul_one] at hluc
    rw [hkp] at hdvd
    have h0 := (Nat.modEq_zero_iff_dvd.2 hdvd)
    have h01 := h0.symm.trans hluc
    unfold Nat.ModEq at h01
    rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 1 < p)] at h01
    exact absurd h01 (by norm_num)
  · rw [Fintype.card_fin, hWcard]; omega
  · intro T₁ h₁ T₂ h₂ c₁ c₂ hne hint
    have hc₁ : #(I ∪ T₁) = k := by rw [card_union_of_disjoint (hdisj T₁ h₁), hI, c₁]; omega
    have hc₂ : #(I ∪ T₂) = k := by rw [card_union_of_disjoint (hdisj T₂ h₂), hI, c₂]; omega
    simp only [f, dif_pos hc₁, dif_pos hc₂]
    apply C.valid
    show #((I ∪ T₁) ∩ (I ∪ T₂)) + 1 = k
    rw [← union_inter_distrib_left, card_union_of_disjoint (hdisj _ (inter_subset_left.trans h₁)),
      hI, hint]
    omega
