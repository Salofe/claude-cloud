import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1

/-!
# Step H2 of the reduction Erdos835.erdos_835.variants.johnson.R1.H1.R1

`Q` has `k + 1` points with `k` even, and `e` colours the pairs of distinct points of `Q` with
`k + 1` colours, symmetrically and properly at every point. Claim: two different points of `Q`
cannot miss the same colour.

Proof by counting the incidences between points of `Q` and the colours occurring at them.
* At a point `x ∈ Q` the `k` edges towards the rest of `Q` get `k` different colours, so exactly
  `k` colours occur at `x`. Summed over `Q` this gives `(k + 1) * k` incidences.
* Fix a colour `c`. Sending a point where `c` occurs to the other end of its `c`-coloured edge
  is a fixed-point-free involution of the set of such points, so that set has even size. It sits
  inside `Q`, of odd size `k + 1`, hence `c` occurs at no more than `k` points.
* If one colour were missing at two different points, it would occur at no more than `k - 1`
  points, and the incidences would number at most `(k - 1) + k * k < (k + 1) * k`.
-/

namespace OMA.Helpers

/-- A finite set with an irreflexive, symmetric, functional pairing relation in which every
element has a partner has even cardinality: the partner map is a fixed-point-free involution,
so the elements cancel in pairs in `ZMod 2`. -/
theorem even_card_of_pairing {V : Type*} (T : Finset V) (p : V → V → Prop)
    (hex : ∀ x ∈ T, ∃ y ∈ T, p x y) (hirr : ∀ x ∈ T, ¬ p x x)
    (hsymm : ∀ x ∈ T, ∀ y ∈ T, p x y → p y x)
    (huniq : ∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ T, p x y → p x z → y = z) : Even T.card := by
  let g : ∀ x ∈ T, V := fun x hx => (hex x hx).choose
  have hg : ∀ x (hx : x ∈ T), g x hx ∈ T ∧ p x (g x hx) := fun x hx => (hex x hx).choose_spec
  have hsum : ∑ x ∈ T, (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution g (fun _ _ => by decide) (fun x hx _ hfix => ?_)
      (fun x hx => (hg x hx).1) (fun x hx => ?_)
    · have h := (hg x hx).2
      rw [hfix] at h
      exact hirr x hx h
    · have h1 := hg x hx
      have h2 := hg (g x hx) h1.1
      exact huniq (g x hx) h1.1 _ h2.1 x hx h2.2 (hsymm x hx _ h1.1 h1.2)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact ZMod.natCast_eq_zero_iff_even.mp hsum

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1.H2 := by
  classical
  intro k hk Q hQ e hsym hprop a ha b hb hab i j hi hj hij
  rw [← hij] at hj
  -- `P x`: the colours occurring at `x`; `R x c`: the colour `c` occurs at `x`
  let P : Fin (2 * k) → Finset (Fin (k + 1)) := fun x => (Q.erase x).image (e x)
  let R : Fin (2 * k) → Fin (k + 1) → Prop := fun x c => c ∈ P x
  -- exactly `k` colours occur at each point of `Q`
  have hP : ∀ x ∈ Q, (P x).card = k := by
    intro x hx
    have hinj : Set.InjOn (e x) (Q.erase x : Set (Fin (2 * k))) := by
      intro y hy z hz hyz
      by_contra hne
      have hy' := Finset.mem_erase.mp (Finset.mem_coe.mp hy)
      have hz' := Finset.mem_erase.mp (Finset.mem_coe.mp hz)
      exact hprop x hx y hy'.2 z hz'.2 hy'.1 hz'.1 hne hyz
    show ((Q.erase x).image (e x)).card = k
    rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hx, hQ, Nat.add_sub_cancel]
  have habove : ∀ x ∈ Q, (Finset.univ.bipartiteAbove R x).card = k := by
    intro x hx
    have heq : Finset.univ.bipartiteAbove R x = P x := by
      ext c
      simp [Finset.mem_bipartiteAbove, R]
    rw [heq, hP x hx]
  -- each colour occurs at an even number of points
  have heven : ∀ c, Even (Q.bipartiteBelow R c).card := by
    intro c
    apply OMA.Helpers.even_card_of_pairing _ (fun x y => x ≠ y ∧ e x y = c)
    · intro x hx
      obtain ⟨hxQ, hxc⟩ := (Finset.mem_bipartiteBelow R).mp hx
      obtain ⟨t, ht, htc⟩ := Finset.mem_image.mp hxc
      obtain ⟨htx, htQ⟩ := Finset.mem_erase.mp ht
      refine ⟨t, (Finset.mem_bipartiteBelow R).mpr ⟨htQ, ?_⟩, htx.symm, htc⟩
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_erase.mpr ⟨htx.symm, hxQ⟩, (hsym t htQ x hxQ).trans htc⟩
    · intro x _ h
      exact h.1 rfl
    · intro x hx y hy h
      exact ⟨h.1.symm, (hsym y ((Finset.mem_bipartiteBelow R).mp hy).1 x
        ((Finset.mem_bipartiteBelow R).mp hx).1).trans h.2⟩
    · intro x hx y hy z hz hxy hxz
      by_contra hyz
      exact hprop x ((Finset.mem_bipartiteBelow R).mp hx).1 y
        ((Finset.mem_bipartiteBelow R).mp hy).1 z ((Finset.mem_bipartiteBelow R).mp hz).1
        hxy.1.symm hxz.1.symm hyz (hxy.2.trans hxz.2.symm)
  -- hence, `Q` being odd, each colour occurs at no more than `k` points
  have hbelow : ∀ c, (Q.bipartiteBelow R c).card ≤ k := by
    intro c
    have hle : (Q.bipartiteBelow R c).card ≤ Q.card :=
      Finset.card_le_card fun x hx => ((Finset.mem_bipartiteBelow R).mp hx).1
    obtain ⟨l, hl⟩ := hk
    obtain ⟨m, hm⟩ := heven c
    omega
  -- the colour `i` is missing at `a` and at `b`, so it occurs at no more than `k - 1` points
  have hmiss : ∀ x ∈ Q, (∀ t ∈ Q, t ≠ x → i ≠ e x t) → i ∉ P x := by
    intro x _ hx hiP
    obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp hiP
    obtain ⟨htx, htQ⟩ := Finset.mem_erase.mp ht
    exact hx t htQ htx hti.symm
  have hbelow_i : (Q.bipartiteBelow R i).card + 1 ≤ k := by
    have hsub : Q.bipartiteBelow R i ⊆ (Q.erase a).erase b := by
      intro x hx
      obtain ⟨hxQ, hxi⟩ := (Finset.mem_bipartiteBelow R).mp hx
      have hxa : x ≠ a := fun h => hmiss a ha hi (by rw [← h]; exact hxi)
      have hxb : x ≠ b := fun h => hmiss b hb hj (by rw [← h]; exact hxi)
      exact Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨hxa, hxQ⟩⟩
    have hbQa : b ∈ Q.erase a := Finset.mem_erase.mpr ⟨fun h => hab h.symm, hb⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_erase_of_mem hbQa
    have h3 := Finset.card_erase_of_mem ha
    have h4 := Finset.card_pos.mpr ⟨b, hbQa⟩
    omega
  -- double counting the incidences gives `(k + 1) * k ≤ (k - 1) + k * k`, a contradiction
  have hcount := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := Q)
    (t := (Finset.univ : Finset (Fin (k + 1)))) R
  rw [Finset.sum_congr rfl habove, Finset.sum_const, hQ, smul_eq_mul,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hcount
  have hrest : ∑ c ∈ Finset.univ.erase i, (Q.bipartiteBelow R c).card ≤ k * k := by
    calc ∑ c ∈ Finset.univ.erase i, (Q.bipartiteBelow R c).card
        ≤ ∑ _c ∈ (Finset.univ : Finset (Fin (k + 1))).erase i, k :=
          Finset.sum_le_sum fun c _ => hbelow c
      _ = k * k := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
            Fintype.card_fin, smul_eq_mul, Nat.add_sub_cancel]
  have hsq : (k + 1) * k = k * k + k := by ring
  omega
