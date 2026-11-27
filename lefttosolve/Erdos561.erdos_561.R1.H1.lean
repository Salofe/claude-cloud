import OMAReductions.R_Erdos561_erdos_561_R1

/-!
# Step H1 of the reduction Erdos561.erdos_561.R1

Suppose neither colour admits a matching. By Hall's theorem there is a set A of red demands whose
admissible slots are fewer than the size of A, and similarly a set B of blue demands. Let i be the
largest index in A and j the largest index in B. The slots k with n i at most r k are admissible for
A, so there are at most i of them (A has at most i + 1 elements); likewise there are at most j slots
with m j at most b k. Hence among the i + j + 1 slots with index at most i + j some slot k has
r k below n i and b k below m j, which contradicts the hypothesis n i + m j - 1 at most r k + b k.
-/

namespace OMA.Helpers

/-- A Hall violator for threshold demands: if no injective assignment exists, then there is an index
`i` such that at most `i` slots can carry the demand of `i`. -/
theorem hall_threshold_violator {s N : ℕ} (n : Fin s → ℕ) (r : Fin N → ℕ)
    (hno : ¬ ∃ f : Fin s ↪ Fin N, ∀ i, n i ≤ r (f i)) :
    ∃ i : Fin s, (Finset.univ.filter (fun k : Fin N => n i ≤ r k)).card ≤ i.val := by
  classical
  have hA : ¬ ∀ A : Finset (Fin s),
      A.card ≤ (Finset.univ.filter (fun k : Fin N => ∃ i ∈ A, n i ≤ r k)).card := by
    intro hall
    obtain ⟨f, hf, hfr⟩ :=
      (Fintype.all_card_le_filter_rel_iff_exists_injective (fun i k => n i ≤ r k)).mp
        (fun A => by convert hall A)
    exact hno ⟨⟨f, hf⟩, hfr⟩
  push Not at hA
  obtain ⟨A, hAc⟩ := hA
  have hAne : A.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at hAc
  refine ⟨A.max' hAne, ?_⟩
  have hAle : A.card ≤ (A.max' hAne).val + 1 := by
    calc A.card ≤ (Finset.Iic (A.max' hAne)).card :=
          Finset.card_le_card (fun x hx => Finset.mem_Iic.mpr (A.le_max' x hx))
      _ = (A.max' hAne).val + 1 := Fin.card_Iic _
  have hsub : (Finset.univ.filter (fun k : Fin N => n (A.max' hAne) ≤ r k)).card ≤
      (Finset.univ.filter (fun k : Fin N => ∃ i ∈ A, n i ≤ r k)).card := by
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact ⟨A.max' hAne, A.max'_mem hAne, hk⟩
  omega

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos561_erdos_561_R1.H1 := by
  intro s t n m r b h
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hr, hb⟩ := hcon
  obtain ⟨i, hi⟩ := OMA.Helpers.hall_threshold_violator n r hr
  obtain ⟨j, hj⟩ := OMA.Helpers.hall_threshold_violator m b hb
  have hc : i.val + j.val < s + t - 1 := by
    have := i.isLt
    have := j.isLt
    omega
  let c : Fin (s + t - 1) := ⟨i.val + j.val, hc⟩
  have hT : ∃ k ∈ Finset.Iic c, k ∉ (Finset.univ.filter (fun k => n i ≤ r k)) ∪
      (Finset.univ.filter (fun k => m j ≤ b k)) := by
    by_contra hall
    push Not at hall
    have h1 := Finset.card_le_card (show Finset.Iic c ⊆ _ from hall)
    have h2 := Finset.card_union_le (Finset.univ.filter (fun k => n i ≤ r k))
      (Finset.univ.filter (fun k => m j ≤ b k))
    rw [Fin.card_Iic] at h1
    have hcv : c.val = i.val + j.val := rfl
    omega
  obtain ⟨k, hk, hkn⟩ := hT
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or,
    not_le] at hkn
  have hk' : k.val ≤ i.val + j.val := Fin.le_iff_val_le_val.mp (Finset.mem_Iic.mp hk)
  have := h i j k hk'
  omega
