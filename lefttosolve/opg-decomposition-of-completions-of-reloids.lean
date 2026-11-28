import OMAStatements.S_opg_decomposition_of_completions_of_reloids
import Mathlib

/-!
Disproof of the first clause of the statement.

Take `A` and `C` one-point types, `B` a copy of the natural numbers, `f = ⊤` (the principal reloid
of the full relation `A × B`) and `g` the reloid whose members are the relations containing all
pairs `(b, c)` with `b` outside a finite set. Then `f` is co-complete. Every row `{b} × C` can be
avoided by a member of `g`, so the completion of `g` contains the empty relation, and so does
`compose (compl g) f`. But every member of `compose g f` contains the single pair of `A × C`, so
the empty relation is not in `compl (compose g f)`. Hence
`compl (compose g f) ≠ compose (compl g) f` although `coCompl f = f`.
-/

namespace OMA.Helpers

open OMA.S_opg_decomposition_of_completions_of_reloids (ReLoid relComp compose fiberJoin coCompl)

universe u v w

theorem reloid_mem_fiberJoin {X I : Type*} (c : X → I) (f : Filter X) (t : Set X) :
    t ∈ fiberJoin c f ↔ ∀ i, ∃ r ∈ f, ∀ x ∈ r, c x = i → x ∈ t := Iff.rfl

theorem reloid_mem_compose {A B C : Type*} (g : ReLoid B C) (f : ReLoid A B)
    (t : Set (A × C)) : t ∈ compose g f ↔ ∃ r ∈ f, ∃ s ∈ g, relComp s r ⊆ t := Iff.rfl

/-- The full reloid from a point to a copy of the natural numbers. -/
def reloidTop : ReLoid PUnit.{u + 1} (ULift.{v} ℕ) := ⊤

/-- The reloid of relations containing all pairs whose first entry avoids a finite set. -/
def reloidCof : ReLoid (ULift.{v} ℕ) PUnit.{w + 1} := Filter.comap Prod.fst Filter.cofinite

theorem reloid_coCompl_top : coCompl reloidTop.{u, v} = reloidTop.{u, v} := by
  ext t
  rw [show coCompl reloidTop.{u, v} = fiberJoin Prod.snd reloidTop.{u, v} from rfl,
    reloid_mem_fiberJoin]
  constructor
  · intro h
    simp only [reloidTop, Filter.mem_top]
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨r, hr, hx⟩ := h x.2
    rw [reloidTop, Filter.mem_top] at hr
    exact hx x (hr ▸ Set.mem_univ x) rfl
  · intro ht i
    exact ⟨t, ht, fun x hx _ => hx⟩

theorem reloid_empty_mem :
    (∅ : Set (PUnit.{u + 1} × PUnit.{w + 1})) ∈
      compose (OMA.S_opg_decomposition_of_completions_of_reloids.compl reloidCof.{v, w})
        reloidTop.{u, v} := by
  rw [reloid_mem_compose]
  refine ⟨Set.univ, Filter.univ_mem, ∅, ?_, ?_⟩
  · show ∅ ∈ fiberJoin Prod.fst reloidCof.{v, w}
    rw [reloid_mem_fiberJoin]
    intro b
    refine ⟨Prod.fst ⁻¹' {b}ᶜ,
      Filter.preimage_mem_comap (Set.Finite.compl_mem_cofinite (Set.finite_singleton b)), ?_⟩
    intro x hx hxb
    exact absurd hxb hx
  · rintro p ⟨b, _, hb⟩
    simp at hb

theorem reloid_empty_not_mem :
    (∅ : Set (PUnit.{u + 1} × PUnit.{w + 1})) ∉
      OMA.S_opg_decomposition_of_completions_of_reloids.compl
        (compose reloidCof.{v, w} reloidTop.{u, v}) := by
  intro h
  rw [show OMA.S_opg_decomposition_of_completions_of_reloids.compl
      (compose reloidCof.{v, w} reloidTop.{u, v}) =
      fiberJoin Prod.fst (compose reloidCof.{v, w} reloidTop.{u, v}) from rfl,
    reloid_mem_fiberJoin] at h
  obtain ⟨t, ht, hsub⟩ := h PUnit.unit
  rw [reloid_mem_compose] at ht
  obtain ⟨r, hr, s, hs, hrs⟩ := ht
  rw [reloidTop, Filter.mem_top] at hr
  subst hr
  obtain ⟨t', ht', hts⟩ := Filter.mem_comap.mp hs
  obtain ⟨b, hb⟩ := Filter.nonempty_of_mem ht'
  have hmem : (PUnit.unit, PUnit.unit) ∈ relComp s Set.univ :=
    ⟨b, Set.mem_univ _, hts (show (b, PUnit.unit) ∈ Prod.fst ⁻¹' t' from hb)⟩
  have := hsub _ (hrs hmem) rfl
  simp at this

theorem reloid_counter :
    ¬ (∀ (A : Type u) (B : Type v) (C : Type w) (f : ReLoid A B) (g : ReLoid B C),
      coCompl f = f → OMA.S_opg_decomposition_of_completions_of_reloids.compl (compose g f) =
        compose (OMA.S_opg_decomposition_of_completions_of_reloids.compl g) f) := by
  intro h
  have key := h PUnit.{u + 1} (ULift.{v} ℕ) PUnit.{w + 1} reloidTop reloidCof reloid_coCompl_top
  apply reloid_empty_not_mem.{u, v, w}
  rw [key]
  exact reloid_empty_mem

end OMA.Helpers

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_decomposition_of_completions_of_reloids.main) :=
  fun h => OMA.Helpers.reloid_counter (fun A B C f g => (h A B C f g).1)
