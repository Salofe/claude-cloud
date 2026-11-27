import OMAReductions.R_Green37_green_37_lower_bound_R1_H1_R1

/-!
# Step H3 of the reduction Green37.green_37_lower_bound.R1.H1.R1

Two independent facts.

* `Green37.m N k` is monotone in `N`. For every `N` the initial segment `{0, 1, ..., k N}`
  contains the progression `{0, d, ..., (k - 1) d}` for each `1 ≤ d ≤ N`, so the set whose
  infimum defines `Green37.m N₂ k` is nonempty and its infimum is attained by some finset `A`.
  That `A` covers every difference `d ≤ N₁ ≤ N₂` as well, hence `Green37.m N₁ k ≤ A.card`.
* For `N ≥ 2`, Bertrand's postulate applied to `N / 2` gives a prime `p` with
  `N / 2 < p ≤ 2 (N / 2)`, so `N ≤ 2 p` and `p ≤ N`.

Only definitions of formal-conjectures (`Green37.m`, `Green37.IsAPCover`, `Set.ContainsAP`,
`Set.IsAPOfLengthWith`) and Mathlib lemmas are used.
-/

namespace OMA.Helpers

/-- The set used in `Set.IsAPOfLengthWith` for a finite length `k`, rewritten as an image of
`Finset.range k`. -/
theorem green37H3_apSet_eq (a d k : ℕ) :
    {x | ∃ n : ℕ, ∃ _ : (n : ℕ∞) < (k : ℕ∞), a + n • d = x} =
      (fun n : ℕ => a + n * d) '' ((Finset.range k : Finset ℕ) : Set ℕ) := by
  ext x
  simp only [smul_eq_mul, Nat.cast_lt, exists_prop, Set.mem_ofPred_eq, Finset.coe_range,
    Set.mem_image, Set.mem_Iio]

/-- For a positive difference `d`, the image of `range k` under `n ↦ a + n d` is an arithmetic
progression of length `k`, first term `a` and difference `d`. -/
theorem green37H3_isAP (a d k : ℕ) (hd : 0 < d) :
    Set.IsAPOfLengthWith ((fun n : ℕ => a + n * d) '' ((Finset.range k : Finset ℕ) : Set ℕ))
      (k : ℕ∞) a d := by
  refine ⟨?_, (green37H3_apSet_eq a d k).symm⟩
  have hinj : Set.InjOn (fun n : ℕ => a + n * d) ((Finset.range k : Finset ℕ) : Set ℕ) := by
    intro m _ n _ hmn
    have h1 : m * d = n * d := Nat.add_left_cancel hmn
    exact Nat.eq_of_mul_eq_mul_right hd h1
  rw [ENat.card_coe_set_eq, hinj.encard_image, Set.encard_coe_eq_coe_finsetCard,
    Finset.card_range]

/-- The initial segment `{0, 1, ..., k N}` contains, for every `d` with `1 ≤ d ≤ N`, the
progression `{0, d, ..., (k - 1) d}`. -/
theorem green37H3_cover (N k : ℕ) :
    Green37.IsAPCover ((Finset.range (k * N + 1) : Finset ℕ) : Set ℕ) N k := by
  intro d hd
  refine ⟨0, (fun n : ℕ => 0 + n * d) '' ((Finset.range k : Finset ℕ) : Set ℕ), ?_,
    green37H3_isAP 0 d k hd.1⟩
  rintro x ⟨n, hn, rfl⟩
  have hn' : n < k := by simpa only [Finset.coe_range, Set.mem_Iio] using hn
  have hle : n * d ≤ k * N := Nat.mul_le_mul hn'.le hd.2
  simp only [Finset.coe_range, Set.mem_Iio]
  omega

/-- A cover for the differences `1, ..., N₂` is a cover for the differences `1, ..., N₁` when
`N₁ ≤ N₂`. -/
theorem green37H3_cover_mono {A : Set ℕ} {N₁ N₂ k : ℕ} (hN : N₁ ≤ N₂)
    (hA : Green37.IsAPCover A N₂ k) : Green37.IsAPCover A N₁ k :=
  fun d hd => hA d ⟨hd.1, hd.2.trans hN⟩

/-- `Green37.m` is monotone in `N`. -/
theorem green37H3_m_mono {N₁ N₂ k : ℕ} (hN : N₁ ≤ N₂) : Green37.m N₁ k ≤ Green37.m N₂ k := by
  have hne : {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N₂ k}.Nonempty :=
    ⟨_, Finset.range (k * N₂ + 1), rfl, green37H3_cover N₂ k⟩
  obtain ⟨A, hAcard, hAcov⟩ := Nat.sInf_mem hne
  exact Nat.sInf_le ⟨A, hAcard, green37H3_cover_mono hN hAcov⟩

/-- Bertrand's postulate at the scale `N / 2`. -/
theorem green37H3_bertrand {N : ℕ} (hN : 2 ≤ N) : ∃ p : ℕ, Nat.Prime p ∧ N ≤ 2 * p ∧ p ≤ N := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (N / 2) (by omega)
  exact ⟨p, hp, by omega, by omega⟩

end OMA.Helpers

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1_H1_R1.H3 :=
  ⟨fun _ _ _ hN => OMA.Helpers.green37H3_m_mono hN,
    fun _ hN => OMA.Helpers.green37H3_bertrand hN⟩
