import OMAReductions.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1
import Mathlib.Combinatorics.SimpleGraph.Diam

/-!
# Step H2 of the reduction WrittenOnTheWallII.GraphConjecture133.conjecture133.R1

Claim: every finite, connected, nontrivial graph satisfies `rad G + 1 ≤ path G`, where
`path G` is the largest number of vertices of an induced path. The four-cycle hypothesis of
H2 is not needed.

Proof. On a finite vertex set the radius is attained as a distance `d(u, v)`. Take a shortest
walk `u = x 0, x 1, ..., x d = v`. Then `d(u, x i) = i` for every `i`: the first `i` steps give
`d(u, x i) ≤ i`, the last `d - i` steps give `d(x i, v) ≤ d - i`, and the triangle inequality
forces equality. Adjacent vertices are distinct and their distances from `u` differ by at most
one, so `x i ~ x j` holds exactly when `|i - j| = 1`. Hence the vertex list of the walk is an
induced path on `d + 1 = rad G + 1` vertices.

The bound `length ≤ path G` for an induced path is proved below directly from the definition
of `path` (no upstream lemma is used).
-/

open SimpleGraph

namespace OMA.Helpers

/-- An element of a finite set of naturals is at most its maximum, read with default `0`. -/
theorem le_max_getD_zero {S : Finset ℕ} {n : ℕ} (hn : n ∈ S) : n ≤ S.max.getD 0 := by
  obtain ⟨m, hm⟩ := Finset.max_of_mem hn
  have h := Finset.le_max hn
  rw [hm] at h ⊢
  exact WithBot.coe_le_coe.mp h

/-- The number of vertices of an induced path is at most `path G`, straight from the
definition of `path`. -/
theorem length_le_path {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    (l : List α) (hl : G.isInducedPath l) : l.length ≤ SimpleGraph.path G := by
  classical
  rw [← List.toFinset_card_of_nodup hl.1]
  unfold SimpleGraph.path
  apply le_max_getD_zero
  rw [Finset.mem_image]
  refine ⟨l.toFinset, ?_, rfl⟩
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, l, rfl, hl⟩

/-- Along a shortest walk from `u`, the vertex in position `i` is at distance exactly `i`
from `u`. -/
theorem dist_start_getVert {α : Type} {G : SimpleGraph α} (hG : G.Connected) {u v : α}
    (p : G.Walk u v) (hp : p.length = G.dist u v) {i : ℕ} (hi : i ≤ p.length) :
    G.dist u (p.getVert i) = i := by
  have h1 : G.dist u (p.getVert i) ≤ i := by
    have h := SimpleGraph.dist_le (p.take i)
    rw [Walk.take_length] at h
    omega
  have h2 : G.dist (p.getVert i) v ≤ p.length - i := by
    have h := SimpleGraph.dist_le (p.drop i)
    rwa [Walk.drop_length] at h
  have h3 : G.dist u v ≤ G.dist u (p.getVert i) + G.dist (p.getVert i) v :=
    hG.dist_triangle
  omega

/-- The vertex list of a shortest walk is an induced path. -/
theorem isInducedPath_support_of_geodesic {α : Type} [Fintype α] [DecidableEq α]
    {G : SimpleGraph α} (hG : G.Connected) {u v : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v) : G.isInducedPath p.support := by
  refine ⟨(p.isPath_of_length_eq_dist hp).support_nodup, fun i j => ?_⟩
  have hsupp := p.length_support
  have hi : i.val ≤ p.length := by
    have h := i.isLt
    omega
  have hj : j.val ≤ p.length := by
    have h := j.isLt
    omega
  rw [List.get_eq_getElem, List.get_eq_getElem, ← p.getVert_eq_support_getElem hi,
    ← p.getVert_eq_support_getElem hj]
  constructor
  · intro hadj
    have hdi := dist_start_getVert hG p hp hi
    have hdj := dist_start_getVert hG p hp hj
    have hd := hadj.diff_dist_adj (u := u)
    rw [hdi, hdj] at hd
    have hne : i.val ≠ j.val := fun h => hadj.ne (by rw [h])
    omega
  · rintro (h | h)
    · rw [← h]
      exact p.adj_getVert_succ (by omega)
    · rw [← h]
      exact (p.adj_getVert_succ (by omega)).symm

/-- A finite, connected, nontrivial graph has an induced path on `rad G + 1` vertices. -/
theorem radius_add_one_le_path {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) (hG : G.Connected) :
    (G.radius.toNat : ℝ) + 1 ≤ (SimpleGraph.path G : ℝ) := by
  obtain ⟨u, v, huv⟩ := G.exists_edist_eq_radius_of_finite
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u v
  have hrad : G.radius.toNat = p.length := by
    rw [hp, ← huv]
    rfl
  have hlen := length_le_path G p.support (isInducedPath_support_of_geodesic hG p hp)
  rw [Walk.length_support] at hlen
  rw [hrad]
  exact_mod_cast hlen

end OMA.Helpers

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1.H2 := by
  intro α _ _ _ G hG _
  exact OMA.Helpers.radius_add_one_le_path G hG
