import OMAReductions.R_Erdos261_erdos_261_parts_ii_R1

/-!
# Step H2 of Erdos261.erdos_261.parts.ii.R1

Along the canonical orbit the state (l, r) after j steps has l = n + 1 + j and keeps the invariant
n / 2^n = (sum of a / 2^a over the levels a taken so far) + r / 2^l,
where every level taken so far lies in [n + 1, n + 1 + j).
A take step needs r > l + 1, so the natural-number subtraction r - l is exact.
A hit r = l adds the final level l; the taken set is nonempty because
n / 2^n is strictly larger than m / 2^m for m at least n + 2.
-/
namespace OMA.Helpers

/-- The first coordinate of the orbit just counts the steps. -/
theorem e261_fst (F : ℕ × ℕ → ℕ × ℕ) (hF : ∀ p, (F p).1 = p.1 + 1) (x : ℕ × ℕ) (j : ℕ) :
    (F^[j] x).1 = x.1 + j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', hF, ih]; ring

/-- The residual invariant along the canonical orbit. -/
theorem e261_inv (n : ℕ) (F : ℕ × ℕ → ℕ × ℕ)
    (hF : ∀ p, F p = (p.1 + 1, if p.1 + 1 < p.2 then 2 * (p.2 - p.1) else 2 * p.2)) (j : ℕ) :
    ∃ S : Finset ℕ, (∀ a ∈ S, n + 1 ≤ a ∧ a < n + 1 + j) ∧
      (n : ℚ) / 2 ^ n = ∑ a ∈ S, (a : ℚ) / 2 ^ a +
        ((F^[j] (n + 1, 2 * n)).2 : ℚ) / 2 ^ (n + 1 + j) := by
  have hfst : ∀ j, (F^[j] (n + 1, 2 * n)).1 = n + 1 + j := fun j =>
    e261_fst F (fun p => by rw [hF]) _ j
  induction j with
  | zero =>
    refine ⟨∅, by simp, ?_⟩
    simp only [Finset.sum_empty, zero_add, Function.iterate_zero, id, add_zero]
    push_cast
    rw [pow_succ]
    field_simp
  | succ j ih =>
    obtain ⟨S, hS, hsum⟩ := ih
    have h1 := hfst j
    set q := F^[j] (n + 1, 2 * n) with hq
    rw [Function.iterate_succ_apply', ← hq, hF]
    have hexp : n + 1 + (j + 1) = (n + 1 + j) + 1 := by ring
    rw [hexp, pow_succ]
    by_cases hc : q.1 + 1 < q.2
    · -- take the level n + 1 + j
      refine ⟨insert (n + 1 + j) S, ?_, ?_⟩
      · intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · omega
        · have := hS a ha; omega
      · have hnot : n + 1 + j ∉ S := fun h => by have := hS _ h; omega
        rw [Finset.sum_insert hnot, if_pos hc, hsum]
        have hle : q.1 ≤ q.2 := by omega
        simp only
        rw [Nat.cast_mul, Nat.cast_sub hle, h1]
        push_cast
        field_simp
        ring
    · -- skip the level n + 1 + j
      refine ⟨S, fun a ha => by have := hS a ha; omega, ?_⟩
      rw [if_neg hc, hsum]
      simp only
      push_cast
      field_simp

/-- A hit of the canonical orbit gives a representation with at least two distinct terms. -/
theorem e261_main : ∀ n j : ℕ, 0 < n → 0 < j →
    ((fun p : ℕ × ℕ => (p.1 + 1, if p.1 + 1 < p.2 then 2 * (p.2 - p.1) else 2 * p.2))^[j]
      (n + 1, 2 * n)).2 = n + 1 + j → Erdos261.Erdos261Prop n := by
  intro n j hn hj h
  obtain ⟨S, hS, hsum⟩ := e261_inv n _ (fun p => rfl) j
  rw [h] at hsum
  have hm : n + 1 + j ∉ S := fun hmS => by have := hS _ hmS; omega
  have hsum' : (n : ℚ) / 2 ^ n = ∑ a ∈ insert (n + 1 + j) S, (a : ℚ) / 2 ^ a := by
    rw [Finset.sum_insert hm, hsum]; push_cast; ring
  -- the taken set is nonempty: otherwise n / 2^n = m / 2^m with m = n + 1 + j and j at least 1
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hSe
    rw [hSe, Finset.sum_empty, zero_add] at hsum
    have h2 : j + 1 ≤ 2 ^ j := j.lt_two_pow_self
    have keyN : (n + 1 + j) * 2 ^ n < n * 2 ^ (n + 1 + j) := by
      have e : 2 ^ (n + 1 + j) = 2 ^ n * 2 * 2 ^ j := by rw [pow_add, pow_succ]
      rw [e]
      have hp : 0 < 2 ^ n := by positivity
      have a1 : n + 1 + j < 2 * n * (j + 1) := by nlinarith
      have a2 : 2 * n * (j + 1) ≤ 2 * n * 2 ^ j := Nat.mul_le_mul_left _ h2
      have a3 : (n + 1 + j) * 2 ^ n < (2 * n * 2 ^ j) * 2 ^ n :=
        Nat.mul_lt_mul_of_pos_right (by omega) hp
      calc (n + 1 + j) * 2 ^ n < (2 * n * 2 ^ j) * 2 ^ n := a3
        _ = n * (2 ^ n * 2 * 2 ^ j) := by ring
    have keyQ : ((n + 1 + j : ℕ) : ℚ) * 2 ^ n < (n : ℚ) * 2 ^ (n + 1 + j) := by
      exact_mod_cast keyN
    rw [div_eq_div_iff (by positivity) (by positivity)] at hsum
    push_cast at keyQ hsum
    linarith
  have hcard : 2 ≤ (insert (n + 1 + j) S).card := by
    rw [Finset.card_insert_of_notMem hm]
    have := hne.card_pos
    omega
  -- list the finite set through its canonical enumeration
  set S' := insert (n + 1 + j) S with hS'
  refine ⟨S'.card, hcard, fun i => (S'.equivFin.symm i).val, ?_, ?_, ?_⟩
  · intro i i' hii
    exact S'.equivFin.symm.injective (Subtype.ext hii)
  · intro i
    have hmem := (S'.equivFin.symm i).property
    show 1 ≤ ((S'.equivFin.symm i) : ℕ)
    rcases Finset.mem_insert.mp hmem with h' | h'
    · rw [h']; omega
    · have := hS _ h'; omega
  · rw [hsum', ← Finset.sum_coe_sort S']
    exact (Equiv.sum_comp S'.equivFin.symm (fun x : S' => ((x : ℕ) : ℚ) / 2 ^ (x : ℕ))).symm

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos261_erdos_261_parts_ii_R1.H2 :=
  OMA.Helpers.e261_main
