import OMAStatements.S_oeis_a078128
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a078128

/-- The partition of `n` with `x` parts equal to 8 and `y` parts equal to 27. -/
def cubePart (n x y : ℕ) (h : 8 * x + 27 * y = n) : Nat.Partition n where
  parts := Multiset.replicate x 8 + Multiset.replicate y 27
  parts_pos := by
    intro i hi
    rw [Multiset.mem_add] at hi
    rcases hi with hi | hi
    · rw [Multiset.eq_of_mem_replicate hi]; norm_num
    · rw [Multiset.eq_of_mem_replicate hi]; norm_num
  parts_sum := by
    simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
    omega

theorem cubePart_count (n x y : ℕ) (h : 8 * x + 27 * y = n) :
    (cubePart n x y h).parts.count 27 = y := by
  simp [cubePart, Multiset.count_replicate]

theorem cubePart_cubes (n x y : ℕ) (h : 8 * x + 27 * y = n) :
    ∀ p ∈ (cubePart n x y h).parts, ∃ m : ℕ, 2 ≤ m ∧ p = m ^ 3 := by
  intro p hp
  simp only [cubePart, Multiset.mem_add] at hp
  rcases hp with hp | hp
  · exact ⟨2, le_rfl, by rw [Multiset.eq_of_mem_replicate hp]; norm_num⟩
  · exact ⟨3, by norm_num, by rw [Multiset.eq_of_mem_replicate hp]; norm_num⟩

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a078128.main := by
  intro k
  refine ⟨27 * (8 * k + 7), ?_⟩
  intro n hn
  have hy : ∀ j : Fin (k + 1), 27 * ((3 * n) % 8 + 8 * (j : ℕ)) ≤ n := by
    intro j
    have := j.isLt
    omega
  have hx : ∀ j : Fin (k + 1),
      8 * ((n - 27 * ((3 * n) % 8 + 8 * (j : ℕ))) / 8) + 27 * ((3 * n) % 8 + 8 * (j : ℕ)) = n := by
    intro j
    have := hy j
    omega
  let f : Fin (k + 1) → { P : Nat.Partition n // ∀ p ∈ P.parts, ∃ m : ℕ, 2 ≤ m ∧ p = m ^ 3 } :=
    fun j => ⟨cubePart n _ _ (hx j), cubePart_cubes n _ _ (hx j)⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h1 := congrArg (fun P => P.1.parts.count 27) hij
    simp only [f, cubePart_count] at h1
    exact Fin.ext (by omega)
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  unfold OMA.S_oeis_a078128.a
  omega
