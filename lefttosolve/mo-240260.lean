import OMAStatements.S_mo_240260
import Mathlib

namespace OMA.Helpers

open OMA.S_mo_240260

/-- Colour a permutation by its sign. -/
def signColor {n : ℕ} (σ : Equiv.Perm (Fin n)) : Fin 2 :=
  if Equiv.Perm.sign σ = 1 then 0 else 1

theorem sign_step {n : ℕ} {σ τ : Equiv.Perm (Fin n)}
    (h : ∃ a b : Fin n, b.val = a.val + 1 ∧ τ = Equiv.swap a b * σ) :
    Equiv.Perm.sign τ = - Equiv.Perm.sign σ := by
  obtain ⟨a, b, hab, rfl⟩ := h
  have hne : a ≠ b := by
    intro e; rw [e] at hab; omega
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne]
  simp

theorem signColor_ne {n : ℕ} {σ τ : Equiv.Perm (Fin n)}
    (h : Equiv.Perm.sign τ = - Equiv.Perm.sign σ) : signColor σ ≠ signColor τ := by
  unfold signColor
  rw [h]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]

theorem colorable2 (n : ℕ) : (permutahedronGraph n).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk signColor ?_⟩
  intro σ τ hadj
  rw [permutahedronGraph, SimpleGraph.fromRel_adj] at hadj
  rcases hadj.2 with h | h
  · exact signColor_ne (sign_step h)
  · exact (signColor_ne (sign_step h)).symm

theorem adj_one_swap (n : ℕ) (hn : 2 ≤ n) :
    (permutahedronGraph n).Adj 1 (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩) := by
  rw [permutahedronGraph, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ⟨⟨0, by omega⟩, ⟨1, by omega⟩, rfl, (mul_one _).symm⟩⟩
  intro e
  have := congrArg (fun f : Equiv.Perm (Fin n) => (f ⟨0, by omega⟩ : Fin n).val) e
  simp [Equiv.swap_apply_left] at this

end OMA.Helpers

open OMA.S_mo_240260 OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_mo_240260.main := by
  intro n hn
  apply le_antisymm
  · exact (colorable2 n).chromaticNumber_le
  · exact SimpleGraph.two_le_chromaticNumber_of_adj (adj_one_swap n hn)
