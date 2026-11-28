import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1
import Mathlib

/-!
# Step H1 of the reduction PoincareConjecture.poincare_conjecture.R1.H3.R1.H2.R1

A finite simplicial complex `K` in `EuclideanSpace ℝ (Fin n)` satisfying `Good` is re-embedded on
standard basis vectors. Its vertex set `V` is finite; we enumerate it by `Fin m`, send the vertex
number `j` to the basis vector `e j` (the map `iota`), and let `A` be the linear map with
`A (e j) = vertex j`, so that `A (iota v) = v` on `V`. The new complex `L` has the faces
`s.image iota` for `s` a face of `K`; it is built with `SimplicialComplex.ofAffineIndependent`,
since all its vertices are distinct basis vectors and hence affinely independent.

* `A` is injective on each simplex `convexHull (s.image iota)` because the vertices of `s` are
  affinely independent, and injective on all of `L.space` thanks to
  `K.inter_subset_convexHull`; it maps `L.space` onto `K.space`. As `L.space` is compact, this
  gives the homeomorphism `K.space ≃ₜ L.space`.
* Faces, links and stars of `L` are the images under `iota` of those of `K`, which transfers
  the cardinality conditions. Connectedness of edge links transfers through the closed embedding
  given by `A` on the compact set `L.space`. The vertex charts of `L` are `f ∘ A`, with affine
  pieces `a.comp A`.

Only Mathlib is used (no upstream theorem).
-/

open Set Geometry

namespace OMA.Helpers

lemma image_image_eq {E F : Type*} [DecidableEq E] [DecidableEq F] {iota : E → F} {A : F → E}
    {V : Set E} (hA : ∀ v ∈ V, A (iota v) = v) {s : Finset E} (hs : (s : Set E) ⊆ V) :
    (s.image iota).image A = s := by
  rw [Finset.image_image]
  conv_rhs => rw [← Finset.image_id (s := s)]
  exact Finset.image_congr (fun v hv => hA v (hs hv))

section Generic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma face_subset_vertices {K : SimplicialComplex ℝ E} {s : Finset E} (hs : s ∈ K.faces) :
    (s : Set E) ⊆ K.vertices := fun v hv =>
  K.down_closed hs (Finset.singleton_subset_iff.2 hv) (Finset.singleton_nonempty v)

noncomputable def reembed [DecidableEq F] (K : SimplicialComplex ℝ E) (iota : E → F)
    (hind : AffineIndependent ℝ (Subtype.val : ↥(iota '' K.vertices) → F)) :
    SimplicialComplex ℝ F :=
  SimplicialComplex.ofAffineIndependent (K.toPreAbstractSimplicialComplex.map iota)
    (hind.mono (by
      intro x hx
      simp only [Set.mem_iUnion, Finset.mem_coe] at hx
      obtain ⟨s, ⟨s', hs', rfl⟩, hx⟩ := hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨v, face_subset_vertices hs' hv, rfl⟩))

lemma reembed_faces [DecidableEq F] (K : SimplicialComplex ℝ E) (iota : E → F)
    (hind : AffineIndependent ℝ (Subtype.val : ↥(iota '' K.vertices) → F)) :
    (reembed K iota hind).faces = (fun s => s.image iota) '' K.faces := rfl

variable [DecidableEq E] [DecidableEq F] {K : SimplicialComplex ℝ E} {iota : E → F}
  {hind : AffineIndependent ℝ (Subtype.val : ↥(iota '' K.vertices) → F)} {A : F →L[ℝ] E}

lemma mem_reembed_faces_iff (hA : ∀ v ∈ K.vertices, A (iota v) = v) {s : Finset E}
    (hs : (s : Set E) ⊆ K.vertices) :
    s.image iota ∈ (reembed K iota hind).faces ↔ s ∈ K.faces := by
  constructor
  · rintro ⟨u, hu, hus⟩
    have hus' : u.image iota = s.image iota := hus
    have h1 := image_image_eq hA (face_subset_vertices hu)
    rw [hus', image_image_eq hA hs] at h1
    rw [h1]; exact hu
  · intro h; exact ⟨s, h, rfl⟩

omit [DecidableEq E] in
lemma image_convexHull_image (hA : ∀ v ∈ K.vertices, A (iota v) = v) {s : Finset E}
    (hs : (s : Set E) ⊆ K.vertices) :
    A '' convexHull ℝ ↑(s.image iota) = convexHull ℝ ↑s := by
  have h := (A : F →ₗ[ℝ] E).image_convexHull (↑(s.image iota) : Set F)
  simp only [ContinuousLinearMap.coe_coe] at h
  rw [h, Finset.coe_image, Set.image_image, Set.image_congr (g := fun v => v)
    (fun v hv => hA v (hs hv)), Set.image_id']

omit [DecidableEq E] in
lemma injOn_convexHull_image (hA : ∀ v ∈ K.vertices, A (iota v) = v) {s : Finset E}
    (hs : s ∈ K.faces) : InjOn A (convexHull ℝ ↑(s.image iota)) := by
  intro x hx y hy hxy
  have hsV := face_subset_vertices hs
  have hinj : Set.InjOn iota ↑s := fun a ha b hb hab => by
    rw [← hA a (hsV ha), ← hA b (hsV hb), hab]
  rw [Finset.mem_convexHull'] at hx hy
  obtain ⟨w, -, hw1, rfl⟩ := hx
  obtain ⟨u, -, hu1, rfl⟩ := hy
  simp only [Finset.sum_image hinj, map_sum, map_smul] at hw1 hu1 hxy ⊢
  have hxy' : ∑ v ∈ s, w (iota v) • v = ∑ v ∈ s, u (iota v) • v := by
    calc ∑ v ∈ s, w (iota v) • v = ∑ v ∈ s, w (iota v) • A (iota v) :=
          Finset.sum_congr rfl (fun v hv => by rw [hA v (hsV hv)])
      _ = ∑ v ∈ s, u (iota v) • A (iota v) := hxy
      _ = ∑ v ∈ s, u (iota v) • v := Finset.sum_congr rfl (fun v hv => by rw [hA v (hsV hv)])
  have key := (K.indep hs).eq_of_sum_eq_sum_subtype (w₁ := fun v => w (iota v))
    (w₂ := fun v => u (iota v)) (by rw [hw1, hu1]) hxy'
  exact Finset.sum_congr rfl (fun v hv => by rw [key v hv])

lemma injOn_space (hA : ∀ v ∈ K.vertices, A (iota v) = v) :
    InjOn A (reembed K iota hind).space := by
  intro x hx y hy hxy
  rw [SimplicialComplex.mem_space_iff] at hx hy
  obtain ⟨_, ⟨s, hs, rfl⟩, hx⟩ := hx
  obtain ⟨_, ⟨t, ht, rfl⟩, hy⟩ := hy
  have hsV := face_subset_vertices hs
  have htV := face_subset_vertices ht
  have hAx : A x ∈ convexHull ℝ (s : Set E) := by
    rw [← image_convexHull_image hA hsV]; exact ⟨x, hx, rfl⟩
  have hAy : A y ∈ convexHull ℝ (t : Set E) := by
    rw [← image_convexHull_image hA htV]; exact ⟨y, hy, rfl⟩
  have hint : A x ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
    rw [Finset.coe_inter]
    exact K.inter_subset_convexHull hs ht ⟨hAx, hxy ▸ hAy⟩
  have hstV : ((s ∩ t : Finset E) : Set E) ⊆ K.vertices :=
    (Finset.coe_subset.2 Finset.inter_subset_left).trans hsV
  rw [← image_convexHull_image hA hstV] at hint
  obtain ⟨z, hz, hzx⟩ := hint
  have hz1 : z ∈ convexHull ℝ ↑(s.image iota) :=
    convexHull_mono (Finset.coe_subset.2 (Finset.image_subset_image Finset.inter_subset_left)) hz
  have hz2 : z ∈ convexHull ℝ ↑(t.image iota) :=
    convexHull_mono (Finset.coe_subset.2 (Finset.image_subset_image Finset.inter_subset_right)) hz
  have e1 : z = x := injOn_convexHull_image hA hs hz1 hx hzx
  have e2 : z = y := injOn_convexHull_image hA ht hz2 hy (hzx.trans hxy)
  exact e1.symm.trans e2

omit [DecidableEq E] in
lemma image_carrier (hA : ∀ v ∈ K.vertices, A (iota v) = v) {G : Set (Finset E)}
    (hG : G ⊆ K.faces) :
    A '' (⋃ s ∈ (fun s => s.image iota) '' G, convexHull ℝ (s : Set F)) =
      ⋃ s ∈ G, convexHull ℝ (s : Set E) := by
  rw [Set.biUnion_image, Set.image_iUnion₂]
  exact Set.iUnion₂_congr (fun s hs => image_convexHull_image hA (face_subset_vertices (hG hs)))

omit [DecidableEq E] in
lemma image_space (hA : ∀ v ∈ K.vertices, A (iota v) = v) :
    A '' (reembed K iota hind).space = K.space :=
  image_carrier hA subset_rfl

omit [DecidableEq E] in
lemma isCompact_space (hfin : K.faces.Finite) : IsCompact (reembed K iota hind).space := by
  refine (hfin.image _).isCompact_biUnion (fun s _ => ?_)
  exact s.finite_toSet.isCompact_convexHull ℝ

omit [DecidableEq E] [DecidableEq F] in
lemma injOn_iota (hA : ∀ v ∈ K.vertices, A (iota v) = v) : InjOn iota K.vertices :=
  fun a ha b hb hab => by rw [← hA a ha, ← hA b hb, hab]

lemma reembed_link (hA : ∀ v ∈ K.vertices, A (iota v) = v) {t : Finset E} (ht : t ∈ K.faces) :
    {u | u ∈ (reembed K iota hind).faces ∧ Disjoint (t.image iota) u ∧
        t.image iota ∪ u ∈ (reembed K iota hind).faces} =
      (fun s => s.image iota) '' {u | u ∈ K.faces ∧ Disjoint t u ∧ t ∪ u ∈ K.faces} := by
  have htV := face_subset_vertices ht
  ext u
  constructor
  · rintro ⟨⟨u', hu', rfl⟩, hdisj, hunion⟩
    have hu'V := face_subset_vertices hu'
    have hU : ((t ∪ u' : Finset E) : Set E) ⊆ K.vertices := by
      rw [Finset.coe_union]; exact Set.union_subset htV hu'V
    refine ⟨u', ⟨hu', Disjoint.of_image_finset hdisj, ?_⟩, rfl⟩
    rw [← mem_reembed_faces_iff (hind := hind) hA hU, Finset.image_union]
    exact hunion
  · rintro ⟨u', ⟨hu', hdisj, hunion⟩, rfl⟩
    have hu'V := face_subset_vertices hu'
    have hU : ((t ∪ u' : Finset E) : Set E) ⊆ K.vertices := by
      rw [Finset.coe_union]; exact Set.union_subset htV hu'V
    refine ⟨⟨u', hu', rfl⟩, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx1
      obtain ⟨b, hb, hab⟩ := Finset.mem_image.1 hx2
      have hba : b = a := by rw [← hA b (hu'V hb), hab, hA a (htV ha)]
      exact Finset.disjoint_left.1 hdisj ha (hba ▸ hb)
    · show t.image iota ∪ u'.image iota ∈ (reembed K iota hind).faces
      rw [← Finset.image_union]
      exact (mem_reembed_faces_iff hA hU).2 hunion

lemma reembed_star (hA : ∀ v ∈ K.vertices, A (iota v) = v) {p : E} (hp : p ∈ K.vertices) :
    {u | u ∈ (reembed K iota hind).faces ∧ {iota p} ∪ u ∈ (reembed K iota hind).faces} =
      (fun s => s.image iota) '' {u | u ∈ K.faces ∧ {p} ∪ u ∈ K.faces} := by
  ext u
  constructor
  · rintro ⟨⟨u', hu', rfl⟩, hunion⟩
    have hU : (({p} ∪ u' : Finset E) : Set E) ⊆ K.vertices := by
      rw [Finset.coe_union, Finset.coe_singleton]
      exact Set.union_subset (Set.singleton_subset_iff.2 hp) (face_subset_vertices hu')
    refine ⟨u', ⟨hu', ?_⟩, rfl⟩
    rw [← mem_reembed_faces_iff (hind := hind) hA hU, Finset.image_union, Finset.image_singleton]
    exact hunion
  · rintro ⟨u', ⟨hu', hunion⟩, rfl⟩
    have hU : (({p} ∪ u' : Finset E) : Set E) ⊆ K.vertices := by
      rw [Finset.coe_union, Finset.coe_singleton]
      exact Set.union_subset (Set.singleton_subset_iff.2 hp) (face_subset_vertices hu')
    refine ⟨⟨u', hu', rfl⟩, ?_⟩
    show {iota p} ∪ u'.image iota ∈ (reembed K iota hind).faces
    rw [← Finset.image_singleton iota p, ← Finset.image_union]
    exact (mem_reembed_faces_iff hA hU).2 hunion

lemma reembed_link_vertices (hA : ∀ v ∈ K.vertices, A (iota v) = v) {t : Finset E}
    (ht : t ∈ K.faces) :
    {q : F | {q} ∈ {u | u ∈ (reembed K iota hind).faces ∧ Disjoint (t.image iota) u ∧
        t.image iota ∪ u ∈ (reembed K iota hind).faces}} =
      iota '' {q : E | {q} ∈ {u | u ∈ K.faces ∧ Disjoint t u ∧ t ∪ u ∈ K.faces}} := by
  rw [reembed_link hA ht]
  ext q
  constructor
  · rintro ⟨u', hu', hq⟩
    have hq' : u'.image iota = {q} := hq
    have h1 := image_image_eq hA (face_subset_vertices hu'.1)
    rw [hq', Finset.image_singleton] at h1
    refine ⟨A q, ?_, ?_⟩
    · show ({A q} : Finset E) ∈ {u | u ∈ K.faces ∧ Disjoint t u ∧ t ∪ u ∈ K.faces}
      rw [h1]; exact hu'
    · have h2 : ({iota (A q)} : Finset F) = {q} := by
        rw [← Finset.image_singleton, h1, hq']
      exact Finset.singleton_injective h2
  · rintro ⟨q', hq', rfl⟩
    exact ⟨{q'}, hq', Finset.image_singleton iota q'⟩

omit [DecidableEq E] in
lemma carrier_subset_space {G : Set (Finset E)} (hG : G ⊆ K.faces) :
    (⋃ s ∈ (fun s => s.image iota) '' G, convexHull ℝ (s : Set F)) ⊆
      (reembed K iota hind).space := by
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨_, ⟨u, hu, rfl⟩, hx⟩ := hx
  exact SimplicialComplex.mem_space_iff.2 ⟨_, ⟨u, hG hu, rfl⟩, hx⟩

end Generic

section Topo

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

lemma homeomorph_of_injOn {f : X → Y} {S : Set X} {T : Set Y} (hS : IsCompact S)
    (hf : Continuous f) (hinj : InjOn f S) (himg : f '' S = T) : Nonempty (T ≃ₜ S) := by
  have hbij : BijOn f S T := ⟨fun x hx => himg ▸ ⟨x, hx, rfl⟩, hinj, himg ▸ subset_rfl⟩
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hc : Continuous (hbij.equiv f) :=
    (hf.comp continuous_subtype_val).subtype_mk _
  exact ⟨(hc.homeoOfEquivCompactToT2).symm⟩

lemma isConnected_of_injOn {f : X → Y} {S U : Set X} (hS : IsCompact S)
    (hf : Continuous f) (hinj : InjOn f S) (hU : U ⊆ S) (h : IsConnected (f '' U)) :
    IsConnected U := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let g : S → Y := fun x => f x
  have hg : Continuous g := hf.comp continuous_subtype_val
  have hginj : Function.Injective g := fun a b hab => Subtype.ext (hinj a.2 b.2 hab)
  have hind : Topology.IsInducing g := (hg.isClosedEmbedding hginj).isInducing
  let U' : Set S := Subtype.val ⁻¹' U
  have hU' : Subtype.val '' U' = U := by
    simp only [U', Subtype.image_preimage_coe]; exact Set.inter_eq_right.2 hU
  have hgU : g '' U' = f '' U := by
    rw [← hU', Set.image_image]
  refine ⟨?_, ?_⟩
  · obtain ⟨y, x, hx, -⟩ := h.nonempty
    exact ⟨x, hx⟩
  · have h1 : IsPreconnected U' := by
      rw [← hind.isPreconnected_image, hgU]; exact h.isPreconnected
    rw [← hU']
    exact h1.image _ continuous_subtype_val.continuousOn

end Topo

lemma exists_reembedding {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Set E)
    (hV : V.Finite) :
    ∃ (m : ℕ) (iota : E → EuclideanSpace ℝ (Fin m)) (A : EuclideanSpace ℝ (Fin m) →L[ℝ] E),
      (∀ v ∈ V, A (iota v) = v) ∧
      AffineIndependent ℝ (Subtype.val : ↥(iota '' V) → EuclideanSpace ℝ (Fin m)) := by
  classical
  have : Finite V := hV.to_subtype
  let eV : V ≃ Fin (Nat.card V) := Finite.equivFin V
  let b := (EuclideanSpace.basisFun (Fin (Nat.card V)) ℝ).toBasis
  refine ⟨Nat.card V, fun v => if hv : v ∈ V then b (eV ⟨v, hv⟩) else 0,
    LinearMap.toContinuousLinearMap (b.constr ℝ (fun j => (eV.symm j : E))), ?_, ?_⟩
  · intro v hv
    simp only [hv, dite_true]
    rw [LinearMap.coe_toContinuousLinearMap', Module.Basis.constr_basis, Equiv.symm_apply_apply]
  · refine b.linearIndependent.affineIndependent.range.mono ?_
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨eV ⟨v, hv⟩, by simp [hv]⟩

/-- The `Good` predicate of the reduction. -/
def Good (m : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))) : Prop :=
    let E := EuclideanSpace ℝ (Fin m)
    letI : DecidableEq E := Classical.decEq E
    let link (s : Finset E) := {t | t ∈ K.faces ∧ Disjoint s t ∧ s ∪ t ∈ K.faces}
    let star (p : E) := {t | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}
    let carrier (F : Set (Finset E)) := ⋃ t ∈ F, convexHull ℝ (t : Set E)
    K.faces.Finite ∧ (∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) ∧
    (∀ t ∈ K.faces, t.card = 2 → IsConnected (carrier (link t))) ∧
    (∀ t ∈ K.faces, t.card = 3 → ({q : E | {q} ∈ link t} : Set E).ncard = 2) ∧
    (∀ p : E, {p} ∈ K.faces → ∃ f : E → EuclideanSpace ℝ (Fin 3),
      (∀ s ∈ star p, ∃ a : E →ᴬ[ℝ] EuclideanSpace ℝ (Fin 3), EqOn f a (convexHull ℝ (s : Set E))) ∧
      InjOn f (carrier (star p)) ∧ (interior (f '' carrier (star p))).Nonempty)

theorem main_thm (n : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) (hK : Good n K) :
    ∃ (m : ℕ) (L : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))),
      AffineIndependent ℝ ((↑) : L.vertices → EuclideanSpace ℝ (Fin m)) ∧
      Good m L ∧ Nonempty (K.space ≃ₜ L.space) := by
  obtain ⟨hfin, h4, hconn, htri, hchart⟩ := hK
  have hVfin : K.vertices.Finite := by
    rw [SimplicialComplex.vertices_eq]
    exact hfin.biUnion (fun s _ => s.finite_toSet)
  obtain ⟨m, iota, A, hA, hind⟩ := exists_reembedding K.vertices hVfin
  let : DecidableEq (EuclideanSpace ℝ (Fin m)) := Classical.decEq _
  let : DecidableEq (EuclideanSpace ℝ (Fin n)) := Classical.decEq _
  refine ⟨m, reembed K iota hind, ?_, ?_, ?_⟩
  · refine hind.mono ?_
    intro q hq
    obtain ⟨u, hu, hq⟩ := hq
    have hq' : u.image iota = {q} := hq
    have hmem : q ∈ u.image iota := by rw [hq']; exact Finset.mem_singleton_self q
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hmem
    exact ⟨v, face_subset_vertices hu hv, rfl⟩
  · dsimp only [Good]
    refine ⟨hfin.image _, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨s, hs, rfl⟩
      obtain ⟨t, ht, hst, hcard⟩ := h4 s hs
      refine ⟨t.image iota, ⟨t, ht, rfl⟩, Finset.image_subset_image hst, ?_⟩
      rw [Finset.card_image_of_injOn ((injOn_iota hA).mono (face_subset_vertices ht))]
      exact hcard
    · rintro _ ⟨t, ht, rfl⟩ hcard
      beta_reduce at hcard ⊢
      have hcard' : t.card = 2 := by
        rw [← Finset.card_image_of_injOn ((injOn_iota hA).mono (face_subset_vertices ht))]
        exact hcard
      rw [reembed_link hA ht]
      refine isConnected_of_injOn (isCompact_space (hind := hind) hfin) A.continuous
        (injOn_space (hind := hind) hA) (carrier_subset_space (hind := hind) (fun u hu => hu.1)) ?_
      rw [image_carrier hA (fun u hu => hu.1)]
      exact hconn t ht hcard'
    · rintro _ ⟨t, ht, rfl⟩ hcard
      beta_reduce at hcard ⊢
      have hcard' : t.card = 3 := by
        rw [← Finset.card_image_of_injOn ((injOn_iota hA).mono (face_subset_vertices ht))]
        exact hcard
      rw [reembed_link_vertices hA ht, ((injOn_iota hA).mono ?_).ncard_image]
      · exact htri t ht hcard'
      · intro q hq
        exact face_subset_vertices hq.1 (Finset.mem_singleton_self q)
    · intro q hq
      obtain ⟨u, hu, hq⟩ := hq
      have hq' : u.image iota = {q} := hq
      have hmem : q ∈ u.image iota := by rw [hq']; exact Finset.mem_singleton_self q
      obtain ⟨p, hpu, rfl⟩ := Finset.mem_image.1 hmem
      have hp : p ∈ K.vertices := face_subset_vertices hu hpu
      obtain ⟨f, hf1, hf2, hf3⟩ := hchart p hp
      rw [reembed_star hA hp]
      refine ⟨f ∘ A, ?_, ?_, ?_⟩
      · rintro _ ⟨s, hs, rfl⟩
        obtain ⟨a, ha⟩ := hf1 s hs
        refine ⟨a.comp A.toContinuousAffineMap, ?_⟩
        intro x hx
        have hAx : A x ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin n))) := by
          rw [← image_convexHull_image hA (face_subset_vertices hs.1)]
          exact ⟨x, hx, rfl⟩
        simp only [Function.comp, ContinuousAffineMap.comp_apply,
          ContinuousLinearMap.coe_toContinuousAffineMap]
        exact ha hAx
      · have hc := image_carrier (G := {u | u ∈ K.faces ∧ {p} ∪ u ∈ K.faces}) hA (fun u hu => hu.1)
        refine hf2.comp ((injOn_space (hind := hind) hA).mono
          (carrier_subset_space (hind := hind) (fun u hu => hu.1))) ?_
        intro x hx
        have hx' : A x ∈ A '' _ := ⟨x, hx, rfl⟩
        rw [hc] at hx'
        exact hx'
      · have hc := image_carrier (G := {u | u ∈ K.faces ∧ {p} ∪ u ∈ K.faces}) hA (fun u hu => hu.1)
        rw [Set.image_comp, hc]
        exact hf3
  · exact homeomorph_of_injOn (isCompact_space hfin) A.continuous (injOn_space hA)
      (image_space hA)

end OMA.Helpers

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1.H1 :=
  fun n K hK => OMA.Helpers.main_thm n K hK
