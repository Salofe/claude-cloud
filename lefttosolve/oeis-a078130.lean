import OMAStatements.S_oeis_a078130
import Mathlib

namespace OMA.Helpers

/-- The partition of `n` into `a` eights and `b` twenty-sevens. -/
def cubePart (n a b : ℕ) (h : 8 * a + 27 * b = n) : Nat.Partition n where
  parts := Multiset.replicate a 8 + Multiset.replicate b 27
  parts_pos := by
    intro i hi
    rcases Multiset.mem_add.mp hi with hi | hi
    · rw [Multiset.eq_of_mem_replicate hi]; norm_num
    · rw [Multiset.eq_of_mem_replicate hi]; norm_num
  parts_sum := by
    simp [Multiset.sum_replicate]
    omega

theorem cubePart_cubes (n a b : ℕ) (h : 8 * a + 27 * b = n) :
    ∀ p ∈ (cubePart n a b h).parts, ∃ m : ℕ, 2 ≤ m ∧ p = m ^ 3 := by
  intro p hp
  rcases Multiset.mem_add.mp hp with hp | hp
  · exact ⟨2, le_refl _, by rw [Multiset.eq_of_mem_replicate hp]; norm_num⟩
  · exact ⟨3, by norm_num, by rw [Multiset.eq_of_mem_replicate hp]; norm_num⟩

theorem cubePart_card (n a b : ℕ) (h : 8 * a + 27 * b = n) :
    Multiset.card (cubePart n a b h).parts = a + b := by
  simp [cubePart]

theorem bound (n : ℕ) (hn : 405 ≤ n) :
    OMA.S_oeis_a078130.numCubePartitions n ≠ 1 := by
  intro h1
  rw [OMA.S_oeis_a078130.numCubePartitions, Nat.card_eq_one_iff_unique] at h1
  obtain ⟨hs, -⟩ := h1
  set m := n - 216 with hm
  have h1 : 8 * ((m - 27 * (3 * m % 8)) / 8 + 27) + 27 * (3 * m % 8) = n := by omega
  have h2 : 8 * ((m - 27 * (3 * m % 8)) / 8) + 27 * (3 * m % 8 + 8) = n := by omega
  have e := hs.elim ⟨cubePart n _ _ h1, cubePart_cubes n _ _ h1⟩
    ⟨cubePart n _ _ h2, cubePart_cubes n _ _ h2⟩
  have e2 := congrArg (fun P => Multiset.card P.1.parts) e
  simp only [cubePart_card] at e2
  omega

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a078130.main := by
  apply (Set.finite_lt_nat 405).subset
  intro n hn
  change OMA.S_oeis_a078130.numCubePartitions n = 1 at hn
  change n < 405
  by_contra hc
  exact OMA.Helpers.bound n (by omega) hn
