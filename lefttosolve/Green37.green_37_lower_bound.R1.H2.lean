import OMAReductions.R_Green37_green_37_lower_bound_R1

/-!
# Step H2 of the reduction Green37.green_37_lower_bound.R1

Monotonicity of the minimum AP-cover size in the progression length: a progression of length
k2 with difference d contains its initial segment of length k1, which is again a progression
with difference d (for d at least 1), so every cover for k2 is a cover for k1.
-/

namespace OMA.Helpers

/-- The arithmetic progression of length `k`, first term `a` and difference `d`, written as a
coerced finset. -/
theorem ap_set_eq (a d k : ℕ) :
    {x | ∃ n : ℕ, ∃ _ : (n : ℕ∞) < (k : ℕ∞), a + n • d = x} =
      (((Finset.range k).image (fun n => a + n * d) : Finset ℕ) : Set ℕ) := by
  ext x
  simp only [Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_range, Set.mem_image,
    Set.mem_Iio, smul_eq_mul, Nat.cast_lt, exists_prop]

theorem ap_card (a d k : ℕ) (hd : 1 ≤ d) :
    ENat.card {x | ∃ n : ℕ, ∃ _ : (n : ℕ∞) < (k : ℕ∞), a + n • d = x} = (k : ℕ∞) := by
  rw [ap_set_eq, ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
    Finset.card_image_of_injective _ (fun m n h => by
      have h' : m * d = n * d := by simpa using h
      exact Nat.eq_of_mul_eq_mul_right hd h'), Finset.card_range]

theorem containsAP_mono {A : Set ℕ} {k₁ k₂ d : ℕ} (hd : 1 ≤ d) (hk : k₁ ≤ k₂)
    (h : A.ContainsAP k₂ d) : A.ContainsAP k₁ d := by
  obtain ⟨a, s, hsA, -, hs⟩ := h
  refine ⟨a, {x | ∃ n : ℕ, ∃ _ : (n : ℕ∞) < (k₁ : ℕ∞), a + n • d = x}, ?_, ap_card a d k₁ hd, rfl⟩
  intro x hx
  obtain ⟨n, hn, rfl⟩ := hx
  apply hsA
  rw [hs]
  refine ⟨n, lt_of_lt_of_le hn (by exact_mod_cast hk), rfl⟩

theorem cover_exists (N k : ℕ) :
    ∃ A : Finset ℕ, Green37.IsAPCover (A : Set ℕ) N k := by
  refine ⟨Finset.range (k * N + 1), ?_⟩
  intro d hd
  refine ⟨0, {x | ∃ n : ℕ, ∃ _ : (n : ℕ∞) < (k : ℕ∞), 0 + n • d = x}, ?_, ap_card 0 d k hd.1, rfl⟩
  intro x hx
  obtain ⟨n, hn, rfl⟩ := hx
  have hn' : n < k := by exact_mod_cast hn
  simp only [Finset.coe_range, Set.mem_Iio, zero_add, smul_eq_mul]
  exact Nat.lt_succ_of_le (Nat.mul_le_mul hn'.le hd.2)

end OMA.Helpers

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1.H2 := by
  intro N k₁ k₂ hk
  have hne : { m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N k₂ }.Nonempty := by
    obtain ⟨A, hA⟩ := OMA.Helpers.cover_exists N k₂
    exact ⟨A.card, A, rfl, hA⟩
  obtain ⟨A, hAc, hA⟩ := Nat.sInf_mem hne
  unfold Green37.m
  apply Nat.sInf_le
  refine ⟨A, hAc, ?_⟩
  intro d hd
  exact OMA.Helpers.containsAP_mono hd.1 hk (hA d hd)
