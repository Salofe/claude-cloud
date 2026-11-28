import OMAReductions.R_Erdos1013_erdos_1013_variants_lower_R1
import Mathlib

/-! Mycielski's construction, written with vertices `Option (V × Bool)`: the apex is `none`,
`(v, false)` is an original vertex and `(v, true)` its shadow. Two non-apex vertices are
adjacent when their bases are adjacent in `G` and at least one of them is original; the apex
is adjacent to every shadow. -/

namespace OMA.Helpers

open SimpleGraph

variable {V : Type} (G : SimpleGraph V)

/-- Adjacency of the Mycielski graph. -/
def myAdj : Option (V × Bool) → Option (V × Bool) → Prop
  | none, none => False
  | none, some p => p.2 = true
  | some p, none => p.2 = true
  | some p, some q => G.Adj p.1 q.1 ∧ (p.2 = false ∨ q.2 = false)

/-- The Mycielski graph. -/
def myGraph : SimpleGraph (Option (V × Bool)) where
  Adj := myAdj G
  symm := ⟨by
    intro x y h
    rcases x with _ | ⟨a, b⟩ <;> rcases y with _ | ⟨c, d⟩ <;> simp only [myAdj] at h ⊢
    · exact h
    · exact h
    · exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by
    intro x h
    rcases x with _ | ⟨a, b⟩ <;> simp only [myAdj] at h
    exact G.loopless.irrefl a h.1⟩

lemma myGraph_adj (x y : Option (V × Bool)) : (myGraph G).Adj x y ↔ myAdj G x y := Iff.rfl

/-- A coloring of `G` with `α` gives a coloring of the Mycielski graph with `Option α`. -/
lemma myGraph_colorable {k : ℕ} (h : G.Colorable k) : (myGraph G).Colorable (k + 1) := by
  obtain ⟨C⟩ := h
  let D : (myGraph G).Coloring (Option (Fin k)) :=
    Coloring.mk (fun x => x.map (fun p => C p.1)) (by
      intro x y hxy
      rcases x with _ | ⟨a, b⟩ <;> rcases y with _ | ⟨c, d⟩ <;>
        simp only [myGraph_adj, myAdj] at hxy
      · simp
      · simp
      · simpa using C.valid hxy.1)
  simpa using D.colorable

/-- A coloring of the Mycielski graph with `α` colors gives a coloring of `G` avoiding the
apex color. -/
lemma colorable_of_myGraph {k : ℕ} (h : (myGraph G).Colorable (k + 1)) : G.Colorable k := by
  classical
  obtain ⟨C⟩ := h
  let z := C none
  let f : V → Fin (k + 1) := fun v =>
    if C (some (v, false)) = z then C (some (v, true)) else C (some (v, false))
  have hf (v : V) : f v ≠ z := by
    simp only [f]
    split_ifs with hv
    · exact C.valid (show (myGraph G).Adj (some (v, true)) none from rfl)
    · exact hv
  let D : G.Coloring {c : Fin (k + 1) // c ≠ z} :=
    Coloring.mk (fun v => ⟨f v, hf v⟩) (by
      intro v w hvw heq
      have heq' : f v = f w := congrArg Subtype.val heq
      have h1 : C (some (v, false)) ≠ C (some (w, false)) :=
        C.valid (show (myGraph G).Adj _ _ from ⟨hvw, Or.inl rfl⟩)
      have h2 : C (some (v, true)) ≠ C (some (w, false)) :=
        C.valid (show (myGraph G).Adj _ _ from ⟨hvw, Or.inr rfl⟩)
      have h3 : C (some (v, false)) ≠ C (some (w, true)) :=
        C.valid (show (myGraph G).Adj _ _ from ⟨hvw, Or.inl rfl⟩)
      simp only [f] at heq'
      split_ifs at heq' with hv hw hw
      · exact h1 (hv.trans hw.symm)
      · exact h2 heq'
      · exact h3 heq'
      · exact h1 heq')
  have hc : Fintype.card {c : Fin (k + 1) // c ≠ z} = k := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
    simp
  simpa [hc] using D.colorable

lemma myGraph_chi {k : ℕ} (h : G.chromaticNumber = (k + 1 : ℕ)) :
    (myGraph G).chromaticNumber = (k + 2 : ℕ) := by
  have h' : G.chromaticNumber = (k : ℕ∞) + 1 := by rw [h]; push_cast; rfl
  rw [chromaticNumber_eq_iff_colorable_not_colorable] at h'
  have : (myGraph G).chromaticNumber = ((k + 1 : ℕ) : ℕ∞) + 1 := by
    rw [chromaticNumber_eq_iff_colorable_not_colorable]
    exact ⟨myGraph_colorable G h'.1, fun hc => h'.2 (colorable_of_myGraph G hc)⟩
  rw [this]
  push_cast
  ring

lemma myGraph_cliqueFree (hG : G.CliqueFree 3) : (myGraph G).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.mp hs
  have tri (x y w : V) (hxy : G.Adj x y) (hxw : G.Adj x w) (hyw : G.Adj y w) : False := by
    exact hG {x, y, w} (is3Clique_triple_iff.mpr ⟨hxy, hxw, hyw⟩)
  rw [myGraph_adj] at hab hac hbc
  rcases a with _ | ⟨a, i⟩ <;> rcases b with _ | ⟨b, j⟩ <;> rcases c with _ | ⟨c, l⟩ <;>
    simp only [myAdj] at hab hac hbc
  · subst hab; subst hac
    rcases hbc.2 with h | h <;> simp at h
  · subst hab; subst hbc
    rcases hac.2 with h | h <;> simp at h
  · subst hac; subst hbc
    rcases hab.2 with h | h <;> simp at h
  · exact tri a b c hab.1 hac.1 hbc.1

lemma exists_type (j : ℕ) : ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
    G.CliqueFree 3 ∧ G.chromaticNumber = (j + 1 : ℕ) := by
  induction j with
  | zero =>
    refine ⟨Unit, inferInstance, ⊥, cliqueFree_bot (by norm_num), ?_⟩
    simpa using (chromaticNumber_bot (V := Unit))
  | succ j ih =>
    obtain ⟨V, hV, G, hG, hχ⟩ := ih
    exact ⟨Option (V × Bool), inferInstance, myGraph G, myGraph_cliqueFree G hG,
      myGraph_chi G hχ⟩

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_variants_lower_R1.H2 := by
  intro k hk
  obtain ⟨V, hV, G, hG, hχ⟩ := OMA.Helpers.exists_type (k - 1)
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [hk'] at hχ
  let e := G.overFinIso (rfl : Fintype.card V = Fintype.card V)
  refine ⟨Fintype.card V, G.overFin rfl, hG.comap e.isContained', ?_⟩
  rw [← hχ]
  exact le_antisymm (SimpleGraph.chromaticNumber_mono_of_hom e.symm.toHom)
    (SimpleGraph.chromaticNumber_mono_of_hom e.toHom)
