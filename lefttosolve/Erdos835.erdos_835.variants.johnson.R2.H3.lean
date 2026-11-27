import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R2

/-!
# Step H3 of the reduction Erdos835.erdos_835.variants.johnson.R2

Let `p ≥ 5` be prime, `t = p - 3`, and let `c` separate `(p - 2)`-sets meeting in `p - 3` points.
Suppose `A`, `B` are disjoint `(p - 2)`-sets with `c A = c B`, and let `𝓑` be the colour class of
`A`. The `p` sets `insert y T` (`y ∉ T`) containing a `(p - 3)`-set `T` pairwise meet in `T`, so
they get all `p` colours once: each `(p - 3)`-set lies in exactly one member of `𝓑`, and in
exactly `p` sets of size `p - 2`.

Double counting the pairs `J ⊆ T ⊆ C` with `#T = p - 3` then gives, for every proper subset
`J` of `A`, `M_J = p * N_J`, where `N_J` and `M_J` count the members of `𝓑`, respectively all
`(p - 2)`-sets, containing `J`. Inclusion–exclusion over the subsets of `A` counts the members
disjoint from `A`: there are `p - 1` such `(p - 2)`-sets, hence, since `#A = p - 2` is odd,
`p * #{C ∈ 𝓑 | Disjoint A C} = (p - 1) - (p - 1) = 0`. This contradicts `B ∈ 𝓑`.
-/

open Finset

namespace OMA.Helpers

theorem eq_insert_of_card_succ {α : Type*} [DecidableEq α] (A T : Finset α) (hT : T ⊆ A)
    (h : #A = #T + 1) : ∃ a, a ∉ T ∧ A = insert a T := by
  have hc : #(A \ T) = 1 := by rw [card_sdiff_of_subset hT]; omega
  obtain ⟨a, ha⟩ := card_eq_one.mp hc
  have haA : a ∈ A \ T := by rw [ha]; exact mem_singleton_self a
  refine ⟨a, (mem_sdiff.mp haA).2, ?_⟩
  rw [insert_eq, ← ha, sdiff_union_of_subset hT]

/-- The `(#C - 1)`-subsets of `C` containing `J` are the sets `C.erase x` with `x ∈ C \ J`. -/
theorem card_erase_family {α : Type*} [DecidableEq α] (C J : Finset α) (hJ : J ⊆ C)
    (hpos : 0 < #C) :
    #((powersetCard (#C - 1) C).filter (fun T => J ⊆ T)) = #C - #J := by
  have hC : (powersetCard (#C - 1) C).filter (fun T => J ⊆ T) =
      (C \ J).image (fun x => C.erase x) := by
    ext T
    simp only [mem_filter, mem_powersetCard, mem_image, mem_sdiff]
    constructor
    · rintro ⟨⟨hTC, hTc⟩, hJT⟩
      obtain ⟨x, hxT, hCeq⟩ := eq_insert_of_card_succ C T hTC (by omega)
      refine ⟨x, ⟨?_, fun hxJ => hxT (hJT hxJ)⟩, ?_⟩
      · rw [hCeq]; exact mem_insert_self x T
      · rw [hCeq, erase_insert hxT]
    · rintro ⟨x, ⟨hxC, hxJ⟩, rfl⟩
      refine ⟨⟨erase_subset x C, by rw [card_erase_of_mem hxC]⟩, ?_⟩
      intro y hy
      exact mem_erase.mpr ⟨fun h => hxJ (h ▸ hy), hJ hy⟩
  rw [hC, card_image_of_injOn, card_sdiff_of_subset hJ]
  intro x hx y hy hxy
  by_contra hne
  have hmem : x ∈ C.erase y := mem_erase.mpr ⟨hne, (mem_sdiff.mp hx).1⟩
  have hxy' : C.erase x = C.erase y := hxy
  rw [← hxy'] at hmem
  simp at hmem

/-- Double counting of pairs `(T, C)` with `J ⊆ T ⊆ C`, `#T = k - 1`, `C ∈ F`. -/
theorem double_count {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (Finset α)) (k r : ℕ)
    (hk : 0 < k) (hF : ∀ C ∈ F, #C = k) (J : Finset α)
    (hr : ∀ T : Finset α, #T = k - 1 → J ⊆ T → #(F.filter (fun C => T ⊆ C)) = r) :
    (k - #J) * #(F.filter (fun C => J ⊆ C)) =
      r * #((powersetCard (k - 1) (univ : Finset α)).filter (fun T => J ⊆ T)) := by
  set s := F.filter (fun C => J ⊆ C) with hs
  set u := (powersetCard (k - 1) (univ : Finset α)).filter (fun T => J ⊆ T) with hu
  have key := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := s) (t := u) (r := fun C T => T ⊆ C)
  have h1 : ∀ C ∈ s, #(u.bipartiteAbove (fun C T => T ⊆ C) C) = k - #J := by
    intro C hC
    obtain ⟨hCF, hJC⟩ := mem_filter.mp hC
    have hCk := hF C hCF
    have heq : u.bipartiteAbove (fun C T => T ⊆ C) C =
        (powersetCard (#C - 1) C).filter (fun T => J ⊆ T) := by
      ext T
      simp only [mem_bipartiteAbove, hu, mem_filter, mem_powersetCard, subset_univ, true_and,
        hCk]
      tauto
    rw [heq, card_erase_family C J hJC (by rw [hCk]; exact hk), hCk]
  have h2 : ∀ T ∈ u, #(s.bipartiteBelow (fun C T => T ⊆ C) T) = r := by
    intro T hT
    obtain ⟨hTp, hJT⟩ := mem_filter.mp hT
    have hTc := (mem_powersetCard.mp hTp).2
    have heq : s.bipartiteBelow (fun C T => T ⊆ C) T = F.filter (fun C => T ⊆ C) := by
      ext C
      simp only [mem_bipartiteBelow, hs, mem_filter]
      constructor
      · rintro ⟨⟨hCF, _⟩, hTC⟩
        exact ⟨hCF, hTC⟩
      · rintro ⟨hCF, hTC⟩
        exact ⟨⟨hCF, hJT.trans hTC⟩, hTC⟩
    rw [heq, hr T hTc hJT]
  rw [sum_congr rfl h1, sum_congr rfl h2, sum_const, sum_const, smul_eq_mul, smul_eq_mul] at key
  rw [mul_comm, key, mul_comm]

/-- Inclusion–exclusion for the members of `F` disjoint from `A`. -/
theorem incl_excl {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (A : Finset α) :
    (#(F.filter (fun C => Disjoint A C)) : ℤ) =
      ∑ J ∈ A.powerset, (-1 : ℤ) ^ #J * #(F.filter (fun C => J ⊆ C)) := by
  have h1 : ∀ C : Finset α, (∑ J ∈ A.powerset, if J ⊆ C then (-1 : ℤ) ^ #J else 0) =
      if Disjoint A C then 1 else 0 := by
    intro C
    rw [← sum_filter]
    have hpow : A.powerset.filter (fun J => J ⊆ C) = (A ∩ C).powerset := by
      ext J
      rw [mem_filter, mem_powerset, mem_powerset, subset_inter_iff]
    rw [hpow, sum_powerset_neg_one_pow_card]
    by_cases hd : Disjoint A C
    · rw [if_pos (disjoint_iff_inter_eq_empty.mp hd), if_pos hd]
    · rw [if_neg (fun h => hd (disjoint_iff_inter_eq_empty.mpr h)), if_neg hd]
  calc (#(F.filter (fun C => Disjoint A C)) : ℤ)
        = ∑ C ∈ F, (if Disjoint A C then (1 : ℤ) else 0) := by
          rw [sum_boole]
    _ = ∑ C ∈ F, ∑ J ∈ A.powerset, if J ⊆ C then (-1 : ℤ) ^ #J else 0 := by
          apply sum_congr rfl
          intro C _
          rw [h1]
    _ = ∑ J ∈ A.powerset, ∑ C ∈ F, if J ⊆ C then (-1 : ℤ) ^ #J else 0 := sum_comm
    _ = _ := by
          apply sum_congr rfl
          intro J _
          rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos835_erdos_835_variants_johnson_R2.H3 := by
  intro p hp hp5 c hsep A B hA hB hAB hc
  classical
  have hcardU : Fintype.card (Fin (2 * p - 3)) = 2 * p - 3 := Fintype.card_fin _
  -- the colour class of `A`
  set 𝓚 : Finset (Finset (Fin (2 * p - 3))) := powersetCard (p - 2) (univ : Finset (Fin (2 * p - 3))) with h𝓚
  set 𝓑 : Finset (Finset (Fin (2 * p - 3))) := 𝓚.filter (fun C => c C = c A) with h𝓑
  have h𝓑card : ∀ C ∈ 𝓑, #C = p - 2 := fun C hC =>
    (mem_powersetCard.mp (mem_filter.mp hC).1).2
  have h𝓚card : ∀ C ∈ 𝓚, #C = p - 2 := fun C hC => (mem_powersetCard.mp hC).2
  -- every `(p - 3)`-set lies in exactly one member of the colour class
  have hsteiner : ∀ T : Finset (Fin (2 * p - 3)), #T = p - 3 → #(𝓑.filter (fun C => T ⊆ C)) = 1 := by
    intro T hT
    let g : {y : Fin (2 * p - 3) // y ∉ T} → Fin p := fun y => c (insert y.1 T)
    have hinj : Function.Injective g := by
      intro y y' hyy
      by_contra hne
      have hne' : y.1 ≠ y'.1 := fun h => hne (Subtype.ext h)
      have hi : insert y.1 T ∩ insert y'.1 T = T := by
        ext z
        simp only [mem_inter, mem_insert]
        constructor
        · rintro ⟨h1 | h1, h2 | h2⟩
          · exact absurd (h1.symm.trans h2) hne'
          · exact h2
          · exact h1
          · exact h1
        · intro hz
          exact ⟨Or.inr hz, Or.inr hz⟩
      apply hsep (insert y.1 T) (insert y'.1 T)
        (by rw [card_insert_of_notMem y.2, hT]; omega)
        (by rw [card_insert_of_notMem y'.2, hT]; omega)
        (by rw [hi, hT]) (show c (insert y.1 T) = c (insert y'.1 T) from hyy)
    have hcard : Fintype.card {y : Fin (2 * p - 3) // y ∉ T} = Fintype.card (Fin p) := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_fin, Fintype.card_coe, hT]
      omega
    have hbij : Function.Bijective g :=
      (Fintype.bijective_iff_injective_and_card g).mpr ⟨hinj, hcard⟩
    obtain ⟨y₀, hy₀⟩ := hbij.2 (c A)
    rw [card_eq_one]
    refine ⟨insert y₀.1 T, ?_⟩
    ext C
    simp only [h𝓑, h𝓚, mem_filter, mem_powersetCard, subset_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨⟨hC, hcC⟩, hTC⟩
      obtain ⟨y, hyT, hCeq⟩ := eq_insert_of_card_succ C T hTC (by omega)
      have : g ⟨y, hyT⟩ = g y₀ := by
        simp only [g]
        rw [← hCeq, hcC]
        exact hy₀.symm
      have := hinj this
      rw [hCeq, show y = y₀.1 from congrArg Subtype.val this]
    · rintro rfl
      refine ⟨⟨by rw [card_insert_of_notMem y₀.2, hT]; omega, hy₀⟩, subset_insert _ _⟩
  -- every `(p - 3)`-set lies in exactly `p` sets of size `p - 2`
  have hall : ∀ T : Finset (Fin (2 * p - 3)), #T = p - 3 → #(𝓚.filter (fun C => T ⊆ C)) = p := by
    intro T hT
    have heq : 𝓚.filter (fun C => T ⊆ C) = Tᶜ.image (fun y => insert y T) := by
      ext C
      simp only [h𝓚, mem_filter, mem_powersetCard, subset_univ, true_and, mem_image,
        mem_compl]
      constructor
      · rintro ⟨hC, hTC⟩
        obtain ⟨y, hyT, hCeq⟩ := eq_insert_of_card_succ C T hTC (by omega)
        exact ⟨y, hyT, hCeq.symm⟩
      · rintro ⟨y, hyT, rfl⟩
        exact ⟨by rw [card_insert_of_notMem hyT, hT]; omega, subset_insert _ _⟩
    rw [heq, card_image_of_injOn, card_compl, hcardU, hT]
    · omega
    · intro y hy y' hy' hyy
      have hyy' : insert y T = insert y' T := hyy
      have hyT : y ∉ T := mem_compl.mp hy
      by_contra hne
      have : y ∈ insert y' T := by rw [← hyy']; exact mem_insert_self y T
      rcases mem_insert.mp this with h | h
      · exact hne h
      · exact hyT h
  -- comparison of the two counts on proper subsets of `A`
  have hcmp : ∀ J ∈ A.powerset.erase A,
      #(𝓚.filter (fun C => J ⊆ C)) = p * #(𝓑.filter (fun C => J ⊆ C)) := by
    intro J hJ
    obtain ⟨hJA, hJA'⟩ := mem_erase.mp hJ
    have hJsub : J ⊆ A := mem_powerset.mp hJA'
    have hJlt : #J < #A := card_lt_card (ssubset_of_subset_of_ne hJsub hJA)
    have hk : 0 < p - 2 := by omega
    have d1 := double_count 𝓑 (p - 2) 1 hk h𝓑card J (fun T hT _ => hsteiner T (by omega))
    have d2 := double_count 𝓚 (p - 2) p hk h𝓚card J (fun T hT _ => hall T (by omega))
    have hpos : 0 < p - 2 - #J := by omega
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [d2, mul_left_comm, d1, one_mul]
  have hA𝓑 : A ∈ 𝓑 := mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, hA⟩, rfl⟩
  have hB𝓑 : B ∈ 𝓑 := mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, hB⟩, hc.symm⟩
  have hNA : #(𝓑.filter (fun C => A ⊆ C)) = 1 := by
    rw [card_eq_one]
    refine ⟨A, ?_⟩
    ext C
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hC, hAC⟩
      exact (eq_of_subset_of_card_le hAC (by rw [h𝓑card C hC, hA])).symm
    · rintro rfl
      exact ⟨hA𝓑, subset_refl _⟩
  have hMA : #(𝓚.filter (fun C => A ⊆ C)) = 1 := by
    rw [card_eq_one]
    refine ⟨A, ?_⟩
    ext C
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hC, hAC⟩
      exact (eq_of_subset_of_card_le hAC (by rw [h𝓚card C hC, hA])).symm
    · rintro rfl
      exact ⟨mem_powersetCard.mpr ⟨subset_univ _, hA⟩, subset_refl _⟩
  have hm0 : #(𝓚.filter (fun C => Disjoint A C)) = p - 1 := by
    have heq : 𝓚.filter (fun C => Disjoint A C) = powersetCard (p - 2) Aᶜ := by
      ext C
      simp only [h𝓚, mem_filter, mem_powersetCard, subset_univ, true_and]
      constructor
      · rintro ⟨hC, hd⟩
        exact ⟨fun x hx => mem_compl.mpr (fun hxA => disjoint_left.mp hd hxA hx), hC⟩
      · rintro ⟨hCA, hC⟩
        exact ⟨hC, disjoint_left.mpr (fun x hxA hxC => mem_compl.mp (hCA hxC) hxA)⟩
    rw [heq, card_powersetCard, card_compl, hcardU, hA]
    have h' : 2 * p - 3 - (p - 2) = (p - 2) + 1 := by omega
    rw [h', Nat.choose_succ_self_right]
    omega
  have ie1 := incl_excl 𝓑 A
  have ie2 := incl_excl 𝓚 A
  rw [← add_sum_erase _ _ (mem_powerset_self A)] at ie1 ie2
  rw [hNA] at ie1
  rw [hMA, hm0] at ie2
  have hsum : ∑ J ∈ A.powerset.erase A, (-1 : ℤ) ^ #J * (#(𝓚.filter (fun C => J ⊆ C)) : ℤ) =
      (p : ℤ) * ∑ J ∈ A.powerset.erase A, (-1 : ℤ) ^ #J * (#(𝓑.filter (fun C => J ⊆ C)) : ℤ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro J hJ
    rw [hcmp J hJ]
    push_cast
    ring
  have hodd : (-1 : ℤ) ^ #A = -1 := by
    rw [hA]
    apply Odd.neg_one_pow
    rcases hp.eq_two_or_odd' with h | h
    · omega
    · obtain ⟨m, hm⟩ := h
      exact ⟨m - 1, by omega⟩
  rw [hodd] at ie1 ie2
  have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  rw [hp1] at ie2
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hn0 : (#(𝓑.filter (fun C => Disjoint A C)) : ℤ) = 0 := by
    apply mul_left_cancel₀ hp0
    linear_combination (p : ℤ) * ie1 - hsum - ie2
  have hpos : 0 < #(𝓑.filter (fun C => Disjoint A C)) :=
    card_pos.mpr ⟨B, mem_filter.mpr ⟨hB𝓑, hAB⟩⟩
  omega
