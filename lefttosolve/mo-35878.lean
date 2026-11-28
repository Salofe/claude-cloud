import OMAStatements.S_mo_35878
import Mathlib

/-!
Proof of MathOverflow 35878: for a local ring A that is a finite-dimensional algebra over a field k,
the degree of the residue field over k divides the dimension of A over k.

More generally, for every A-module M that is finite-dimensional over k (compatibly), the degree
d = dim_k (A/m) divides dim_k M. By strong induction on dim_k M: a nonzero M is Artinian over A, so it
has a minimal nonzero submodule N; N is simple, hence isomorphic to A/m (m being the only maximal
ideal), so dim_k N = d, and dim_k M = dim_k N + dim_k (M/N) with dim_k (M/N) smaller.
-/

namespace OMA.Helpers

theorem mo35878_key (k A : Type) [Field k] [CommRing A] [Algebra k A] [IsLocalRing A] (n : ℕ) :
    ∀ (M : Type) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
      [FiniteDimensional k M], Module.finrank k M = n →
      Module.finrank k (A ⧸ IsLocalRing.maximalIdeal A) ∣ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ _ _ _ hM
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; exact dvd_zero _
  have : Nontrivial M := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  have hart : IsArtinian A M := isArtinian_of_tower k inferInstance
  have hatomic : IsAtomic (Submodule A M) :=
    isAtomic_of_orderBot_wellFounded_lt (wellFounded_lt (α := Submodule A M))
  obtain ⟨N, hN, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule A M)).resolve_left top_ne_bot
  have hS : IsSimpleModule A N := isSimpleModule_iff_isAtom.mpr hN
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hS
  obtain rfl := IsLocalRing.eq_maximalIdeal hI
  have hNd : Module.finrank k N = Module.finrank k (A ⧸ IsLocalRing.maximalIdeal A) :=
    (e.restrictScalars k).finrank_eq
  have hNfin : Module.Finite k N :=
    Module.Finite.of_injective ((N.restrictScalars k).subtype) Subtype.val_injective
  have hNpos : 0 < Module.finrank k N := by
    have : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN.1
    exact Module.finrank_pos
  have hsum := Submodule.finrank_quotient_add_finrank (N.restrictScalars k)
  have hq : Module.finrank k (M ⧸ N.restrictScalars k) = Module.finrank k (M ⧸ N) :=
    (Submodule.Quotient.restrictScalarsEquiv k N).finrank_eq
  have hr : Module.finrank k (N.restrictScalars k) = Module.finrank k N := rfl
  rw [hq, hr, hM] at hsum
  have hQ := ih (Module.finrank k (M ⧸ N)) (by omega) (M ⧸ N) rfl
  rw [← hsum, hNd] at *
  exact dvd_add hQ dvd_rfl

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_mo_35878.main := by
  intro k A _ _ _ _ _
  exact OMA.Helpers.mo35878_key k A _ A rfl
