import OMAStatements.S_mo_134513
import Mathlib

/-!
Disproof: the graph on three vertices with a single edge `0 - 1` and an isolated vertex `2`
has constant edge imbalance `0`, but it is neither regular (degrees `1, 1, 0`) nor isomorphic
to the path on three vertices (in it no vertex has two distinct neighbours).
-/

namespace OMA.Helpers

/-- One edge between `0` and `1`, and an isolated vertex `2`. -/
def G1 : SimpleGraph (Fin 3) where
  Adj a b := a.val + b.val = 1
  symm := ⟨fun a b (h : a.val + b.val = 1) => by show b.val + a.val = 1; omega⟩
  loopless := ⟨fun a (h : a.val + a.val = 1) => by omega⟩

instance : DecidableRel G1.Adj := fun a b => inferInstanceAs (Decidable (a.val + b.val = 1))

theorem deg0 : G1.degree 0 = 1 := by decide
theorem deg1 : G1.degree 1 = 1 := by decide
theorem deg2 : G1.degree 2 = 0 := by decide

end OMA.Helpers

open OMA.Helpers in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_134513.main) := by
  intro h
  have hk : ∃ k : ℕ, ∀ u v : Fin 3, G1.Adj u v → Nat.dist (G1.degree u) (G1.degree v) = k := by
    refine ⟨0, ?_⟩
    intro u v huv
    have : u.val + v.val = 1 := huv
    have hu : u = 0 ∨ u = 1 := by omega
    have hv : v = 0 ∨ v = 1 := by omega
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp [deg0, deg1]
  rcases h (Fin 3) G1 hk with ⟨d, hd⟩ | hiso
  · have h0 := hd 0
    have h2 := hd 2
    rw [deg0] at h0
    rw [deg2] at h2
    omega
  · obtain ⟨φ⟩ := hiso
    have a01 : G1.Adj (φ.symm 0) (φ.symm 1) :=
      φ.symm.map_adj_iff.mpr (by simp [SimpleGraph.pathGraph_adj])
    have a12 : G1.Adj (φ.symm 1) (φ.symm 2) :=
      φ.symm.map_adj_iff.mpr (by simp [SimpleGraph.pathGraph_adj])
    have hne : φ.symm 0 ≠ φ.symm 2 := fun e => absurd (φ.symm.injective e) (by decide)
    have e1 : (φ.symm 0).val + (φ.symm 1).val = 1 := a01
    have e2 : (φ.symm 1).val + (φ.symm 2).val = 1 := a12
    have : (φ.symm 0).val ≠ (φ.symm 2).val := fun e => hne (Fin.ext e)
    omega
