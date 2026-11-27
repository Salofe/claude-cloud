import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R3

/-!
# Step H1 of the reduction Erdos151.erdos_151.variants.cliqueFree_four.R3

Local extension of a two-colouring: if every component of a graph L becomes properly
two-coloured by a side function after removing at most one exceptional edge, then for every
symmetric edge colouring c there is a vertex colouring d with no edge whose two endpoints
both carry the colour of that edge. Orient each component so that its exceptional edge
disagrees with the colour of its endpoints.
-/

namespace OMA.Helpers

theorem flip_inj (i j r k : Bool) :
    (if i = r then !k else k) = (if j = r then !k else k) → i = j := by
  cases i <;> cases j <;> cases r <;> cases k <;> decide

theorem flip_ne (k : Bool) : (!k) ≠ k := by cases k <;> decide

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R3.H1 := by
  intro V L hp c hc
  classical
  choose side a b hs using hp
  let adapt (C : L.ConnectedComponent) (x : V) :=
    if side C x = side C (a C) then !(c (a C) (b C)) else c (a C) (b C)
  refine ⟨fun x => adapt (L.connectedComponentMk x) x, ?_⟩
  intro x y hxy
  let C := L.connectedComponentMk x
  have he : L.connectedComponentMk y = C :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
  change ¬ (adapt C x = c x y ∧ adapt (L.connectedComponentMk y) y = c x y)
  rw [he]
  rintro ⟨hx, hy⟩
  have hside := OMA.Helpers.flip_inj (side C x) (side C y) (side C (a C)) (c (a C) (b C))
    (hx.trans hy.symm)
  rcases hs C x y hxy rfl hside with ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
  · have hx' := hx
    rw [show adapt C x = !(c (a C) (b C)) by simp [adapt, hxa]] at hx'
    rw [hxa, hyb] at hx'
    exact OMA.Helpers.flip_ne _ hx'
  · have hy' := hy
    rw [show adapt C y = !(c (a C) (b C)) by simp [adapt, hya]] at hy'
    rw [hxb, hya, hc (b C) (a C)] at hy'
    exact OMA.Helpers.flip_ne _ hy'
