import OMAReductions.R_Green72_no_k_in_line_big_R1

/-!
# Step H2 of the reduction Green72.no_k_in_line_big.R1

Let t be a subset of s with k points (k at least 2) whose real images are collinear. Pick two
distinct points p and q of t. The integer line a x + b y = c with a = q.2 - p.2, b = p.1 - q.1 and
c = a p.1 + b p.2 has coefficients strictly between -N and N, not both zero, and it contains every
point of t: writing each point as p + r v along the common direction v, the quantity a x + b y - c
is a multiple of the cross product of v with itself, hence zero. So that line meets s in at least
k points, contradicting the bound k - 1.
-/

theorem OMA.solution : OMA.R_Green72_no_k_in_line_big_R1.H2 := by
  intro k N s hk hs hl
  refine ⟨fun i hi => ?_, ?_⟩
  · have h := hs hi
    simp only [Finset.mem_product, Finset.mem_range] at h
    exact h
  · intro t hts htc hcol
    have h1 : 1 < t.card := by omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h1
    have hpS : ((p.1 : ℝ), (p.2 : ℝ)) ∈
        ({r | ∃ i ∈ t, r = ((↑i.1 : ℝ), (↑i.2 : ℝ))} : Set (ℝ × ℝ)) := ⟨p, hp, rfl⟩
    rw [collinear_iff_of_mem hpS] at hcol
    obtain ⟨v, hv⟩ := hcol
    have hpN := hs (hts hp)
    have hqN := hs (hts hq)
    simp only [Finset.mem_product, Finset.mem_range] at hpN hqN
    obtain ⟨a, ha⟩ : ∃ a : ℤ, a = (q.2 : ℤ) - p.2 := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : ℤ, b = (p.1 : ℤ) - q.1 := ⟨_, rfl⟩
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push Not at h
      obtain ⟨ha0, hb0⟩ := h
      apply hpq
      ext <;> omega
    have hcoord (x : ℕ × ℕ) (hx : x ∈ t) :
        ∃ r : ℝ, (x.1 : ℝ) = r * v.1 + p.1 ∧ (x.2 : ℝ) = r * v.2 + p.2 := by
      obtain ⟨r, hr⟩ := hv _ ⟨x, hx, rfl⟩
      refine ⟨r, ?_, ?_⟩
      · have h := congrArg Prod.fst hr
        simpa [vadd_eq_add] using h
      · have h := congrArg Prod.snd hr
        simpa [vadd_eq_add] using h
    obtain ⟨rq, hq1, hq2⟩ := hcoord q hq
    have hline : ∀ x ∈ t, a * x.1 + b * x.2 = a * p.1 + b * p.2 := by
      intro x hx
      obtain ⟨rx, hx1, hx2⟩ := hcoord x hx
      have hR : ((a * x.1 + b * x.2 : ℤ) : ℝ) = ((a * p.1 + b * p.2 : ℤ) : ℝ) := by
        rw [ha, hb]
        push_cast
        rw [hx1, hx2, hq1, hq2]
        ring
      exact_mod_cast hR
    have hsub : t ⊆ s.filter (fun i => a * i.1 + b * i.2 = a * p.1 + b * p.2) := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨hts hx, hline x hx⟩
    have hcard := Finset.card_le_card hsub
    have hbound := hl a b (a * p.1 + b * p.2) hab (by omega) (by omega) (by omega) (by omega)
    omega
