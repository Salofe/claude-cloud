import OMAStatements.S_mo_81816
import Mathlib

namespace OMA.Helpers

/-- With every exponent equal to `0`, both sides of the divisibility vanish: `0 ∣ 0`. -/
theorem mo81816_valid (m : ℕ) (hm : 2 ≤ m) :
    OMA.S_mo_81816.valid (fun _ : Fin m => 3) (fun _ : Fin m => 0) := by
  refine ⟨fun _ _ _ => le_refl 3, fun _ => ⟨Nat.prime_three, ⟨1, rfl⟩⟩, ?_⟩
  have h1 : (∏ _i : Fin m, (3 ^ 0 - 1 : ℕ)) = 0 := by
    simp only [pow_zero, Nat.sub_self]
    exact Finset.prod_eq_zero (Finset.mem_univ ⟨0, by omega⟩) rfl
  have h2 : (∏ _i : Fin m, (3 ^ 0 : ℕ)) - 1 = 0 := by simp
  rw [h1, h2]

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_mo_81816.main := by
  intro m hm
  exact ⟨fun _ => 3, fun _ => 0, OMA.Helpers.mo81816_valid m hm⟩
