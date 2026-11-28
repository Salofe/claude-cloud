import OMAStatements.S_opg_funcolidal_products_inside_an_inward_reloid
import Mathlib

open Filter

theorem OMA.solution : type_of% @OMA.S_opg_funcolidal_products_inside_an_inward_reloid.main := by
  intro A B δ _ 𝒜 ℬ hle X Y hXY
  by_contra hδ
  have hS : (X ×ˢ Y)ᶜ ∈ OMA.S_opg_funcolidal_products_inside_an_inward_reloid.rldIn δ := by
    unfold OMA.S_opg_funcolidal_products_inside_an_inward_reloid.rldIn
    simp only [Filter.mem_iSup]
    intro a b hab
    by_cases hX : X ∈ (a : Filter A)
    · by_cases hY : Y ∈ (b : Filter B)
      · exfalso
        apply hδ
        apply hab X Y
        refine ⟨?_, ?_⟩
        · exact Filter.inf_principal_neBot_iff.mpr fun U hU =>
            Filter.nonempty_of_mem (Filter.inter_mem hU hX)
        · exact Filter.inf_principal_neBot_iff.mpr fun U hU =>
            Filter.nonempty_of_mem (Filter.inter_mem hU hY)
      · have hc : Yᶜ ∈ (b : Filter B) := Ultrafilter.compl_mem_iff_notMem.mpr hY
        refine Filter.mem_of_superset (Filter.prod_mem_prod Filter.univ_mem hc) ?_
        rintro p ⟨_, hp⟩ ⟨_, hp'⟩
        exact hp hp'
    · have hc : Xᶜ ∈ (a : Filter A) := Ultrafilter.compl_mem_iff_notMem.mpr hX
      refine Filter.mem_of_superset (Filter.prod_mem_prod hc Filter.univ_mem) ?_
      rintro p ⟨hp, _⟩ ⟨hp', _⟩
      exact hp hp'
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp (hle hS)
  obtain ⟨hA, hB⟩ := hXY
  obtain ⟨x, hxU, hxX⟩ := Filter.inf_principal_neBot_iff.mp hA U hU
  obtain ⟨y, hyV, hyY⟩ := Filter.inf_principal_neBot_iff.mp hB V hV
  exact hUV (Set.mk_mem_prod hxU hyV) (Set.mk_mem_prod hxX hyY)
