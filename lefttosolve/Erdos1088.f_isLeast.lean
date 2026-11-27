import FormalConjectures.ErdosProblems.«1088»

/-!
Every large enough finite subset of `ℝ^d` contains `n` points with pairwise distinct distances.
Potential argument: functions `x ↦ ⟪u, x⟫ + l ‖x‖² + c` form a `(d+2)`-dimensional space `V`;
for a finite set `S` let `ann S` be the subspace of those vanishing on `S`. Take a maximal
distinct-distance subset `A` of `S` (of size `< n`); every other point of `S` lies on a bisector
of two points of `A` or on a sphere centred at a point of `A` with radius a distance of `A`.
Each of these is the zero set of some `v ∈ V` not vanishing on `S`, so one of them contains many
points of `S`, and on that subset `ann` is strictly bigger. Induct on the codimension of `ann S`.
-/

open scoped EuclideanGeometry

namespace OMA.Helpers

open Erdos1088 Module

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev V (d : ℕ) := E d × ℝ × ℝ

noncomputable def ev {d : ℕ} (x : E d) : V d →ₗ[ℝ] ℝ where
  toFun v := inner ℝ v.1 x + v.2.1 * ‖x‖ ^ 2 + v.2.2
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, inner_add_left]
    ring
  map_smul' c v := by
    simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_left, smul_eq_mul, RingHom.id_apply]
    simp
    ring

theorem ev_apply {d : ℕ} (x : E d) (v : V d) :
    ev x v = inner ℝ v.1 x + v.2.1 * ‖x‖ ^ 2 + v.2.2 := rfl

noncomputable def w {d : ℕ} (a : E d) : V d := ((-2 : ℝ) • a, 1, ‖a‖ ^ 2)

def e3 {d : ℕ} : V d := (0, 0, 1)

theorem ev_w {d : ℕ} (x a : E d) : ev x (w a) = dist x a ^ 2 := by
  rw [ev_apply, w, dist_eq_norm, norm_sub_sq_real]
  simp only [inner_smul_left, real_inner_comm]
  simp
  ring

theorem ev_e3 {d : ℕ} (x : E d) : ev x (e3 : V d) = 1 := by
  simp [ev_apply, e3]

noncomputable def ann {d : ℕ} (S : Finset (E d)) : Submodule ℝ (V d) :=
  ⨅ x ∈ S, LinearMap.ker (ev x)

theorem mem_ann {d : ℕ} (S : Finset (E d)) (v : V d) :
    v ∈ ann S ↔ ∀ x ∈ S, ev x v = 0 := by
  simp [ann, Submodule.mem_iInf]

theorem ann_lt {d : ℕ} (S : Finset (E d)) (v : V d) (a : E d) (ha : a ∈ S) (hv : ev a v ≠ 0) :
    ann S < ann (S.filter (fun x => ev x v = 0)) := by
  rw [SetLike.lt_iff_le_and_exists]
  refine ⟨?_, v, ?_, ?_⟩
  · intro u hu
    rw [mem_ann] at hu ⊢
    intro x hx
    exact hu x (Finset.mem_filter.1 hx).1
  · rw [mem_ann]
    intro x hx
    exact (Finset.mem_filter.1 hx).2
  · rw [mem_ann]
    intro h
    exact hv (h a ha)

theorem empty_of_le {d : ℕ} (S : Finset (E d)) (h : finrank ℝ (V d) ≤ finrank ℝ (ann S)) :
    S = ∅ := by
  have htop : ann S = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) h)
  have he : (e3 : V d) ∈ ann S := htop ▸ Submodule.mem_top
  rw [mem_ann] at he
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  have h1 := he x hx
  rw [ev_e3] at h1
  exact one_ne_zero h1

theorem good_empty {d : ℕ} : PairwiseDistancesDistinct (∅ : Finset (E d)) := by
  simp [PairwiseDistancesDistinct, distinctDistances, distanceSet]

theorem good_insert {d : ℕ} {A : Finset (E d)} {x : E d} (hx : x ∉ A)
    (hA : PairwiseDistancesDistinct A)
    (h1 : ∀ a ∈ A, ∀ b ∈ A, dist x a = dist x b → a = b)
    (h2 : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, b ≠ c → dist x a ≠ dist b c) :
    PairwiseDistancesDistinct (insert x A) := by
  classical
  unfold PairwiseDistancesDistinct distinctDistances at *
  have hset : distanceSet (insert x A) = distanceSet A ∪ A.image (fun a => dist x a) := by
    ext t
    simp only [distanceSet, Finset.mem_union, Finset.mem_image, Finset.mem_offDiag,
      Finset.mem_insert, Prod.exists]
    constructor
    · rintro ⟨p, q, ⟨hp, hq, hpq⟩, rfl⟩
      rcases hp with rfl | hp <;> rcases hq with rfl | hq
      · exact absurd rfl hpq
      · exact Or.inr ⟨q, hq, rfl⟩
      · exact Or.inr ⟨p, hp, dist_comm _ _⟩
      · exact Or.inl ⟨p, q, ⟨hp, hq, hpq⟩, rfl⟩
    · rintro (⟨p, q, ⟨hp, hq, hpq⟩, rfl⟩ | ⟨a, ha, rfl⟩)
      · exact ⟨p, q, ⟨Or.inr hp, Or.inr hq, hpq⟩, rfl⟩
      · exact ⟨x, a, ⟨Or.inl rfl, Or.inr ha, fun h => hx (h ▸ ha)⟩, rfl⟩
  have hdisj : Disjoint (distanceSet A) (A.image (fun a => dist x a)) := by
    rw [Finset.disjoint_left]
    intro t ht ht'
    simp only [distanceSet, Finset.mem_image, Finset.mem_offDiag, Prod.exists] at ht ht'
    obtain ⟨b, c, ⟨hb, hc, hbc⟩, rfl⟩ := ht
    obtain ⟨a, ha, hEq⟩ := ht'
    exact h2 a ha b hb c hc hbc hEq
  have hinj : (A.image (fun a => dist x a)).card = A.card :=
    Finset.card_image_of_injOn (fun a ha b hb hab => h1 a ha b hb hab)
  rw [hset, Finset.card_union_of_disjoint hdisj, hinj, hA, Finset.card_insert_of_notMem hx,
    Nat.choose_succ_succ', Nat.choose_one_right]
  ring

theorem collision {d : ℕ} {A : Finset (E d)} {x : E d} (hx : x ∉ A)
    (hA : PairwiseDistancesDistinct A) (hbad : ¬ PairwiseDistancesDistinct (insert x A)) :
    (∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ dist x a = dist x b) ∨
    (∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, b ≠ c ∧ dist x a = dist b c) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  refine hbad (good_insert hx hA (fun a ha b hb hab => ?_) h2)
  by_contra hne
  exact h1 a ha b hb hne hab

/-- The finite set of test vectors attached to a subset `A`: bisectors and spheres. -/
noncomputable def Q {d : ℕ} (A : Finset (E d)) : Finset (V d) :=
  (A.offDiag.image (fun p => w p.1 - w p.2)) ∪
    ((A ×ˢ A.offDiag).image (fun t => w t.1 - (dist t.2.1 t.2.2 ^ 2) • (e3 : V d)))

theorem card_Q_le {d : ℕ} (A : Finset (E d)) :
    (Q A).card ≤ A.card * A.card + A.card * (A.card * A.card) := by
  unfold Q
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · refine Finset.card_image_le.trans ?_
    rw [Finset.offDiag_card]
    exact Nat.sub_le _ _
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Finset.offDiag_card]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

theorem Q_nonvanish {d : ℕ} (A : Finset (E d)) (v : V d) (hv : v ∈ Q A) :
    ∃ a ∈ A, ev a v ≠ 0 := by
  unfold Q at hv
  rcases Finset.mem_union.1 hv with h | h
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 h
    rw [Finset.mem_offDiag] at hab
    refine ⟨a, hab.1, ?_⟩
    rw [map_sub, ev_w, ev_w, dist_self]
    have : 0 < dist a b := dist_pos.2 hab.2.2
    nlinarith
  · obtain ⟨⟨a, b, c⟩, habc, rfl⟩ := Finset.mem_image.1 h
    rw [Finset.mem_product, Finset.mem_offDiag] at habc
    refine ⟨a, habc.1, ?_⟩
    rw [map_sub, map_smul, ev_w, ev_e3, dist_self]
    have : 0 < dist b c := dist_pos.2 habc.2.2.2
    simp only [smul_eq_mul, mul_one]
    nlinarith

theorem Q_cover {d : ℕ} {A : Finset (E d)} {x : E d} (hx : x ∉ A)
    (hA : PairwiseDistancesDistinct A) (hbad : ¬ PairwiseDistancesDistinct (insert x A)) :
    ∃ v ∈ Q A, ev x v = 0 := by
  rcases collision hx hA hbad with ⟨a, ha, b, hb, hab, h⟩ | ⟨a, ha, b, hb, c, hc, hbc, h⟩
  · refine ⟨w a - w b, ?_, ?_⟩
    · unfold Q
      refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨(a, b), ?_, rfl⟩)
      exact Finset.mem_offDiag.2 ⟨ha, hb, hab⟩
    · rw [map_sub, ev_w, ev_w, h, sub_self]
  · refine ⟨w a - (dist b c ^ 2) • (e3 : V d), ?_, ?_⟩
    · unfold Q
      refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨(a, b, c), ?_, rfl⟩)
      exact Finset.mem_product.2 ⟨ha, Finset.mem_offDiag.2 ⟨hb, hc, hbc⟩⟩
    · rw [map_sub, map_smul, ev_w, ev_e3, h, smul_eq_mul, mul_one, sub_self]

open Classical in
theorem main (d n : ℕ) : ∀ k : ℕ, ∃ M : ℕ, ∀ S : Finset (E d),
    finrank ℝ (V d) ≤ finrank ℝ (ann S) + k → M ≤ S.card →
      HasSubsetWithDistinctDistances n S := by
  intro k
  induction k with
  | zero =>
    refine ⟨1, fun S hS hcard => ?_⟩
    have h0 := empty_of_le S (by simpa using hS)
    subst h0
    simp at hcard
  | succ k ih =>
    obtain ⟨M, hM⟩ := ih
    refine ⟨n + (n * n + n * (n * n)) * M, fun S hS hcard => ?_⟩
    obtain ⟨A, hAmem, hAmax⟩ := Finset.exists_max_image
      (S.powerset.filter (fun B => B.card ≤ n ∧ PairwiseDistancesDistinct B)) Finset.card
      ⟨∅, by simp [good_empty]⟩
    rw [Finset.mem_filter, Finset.mem_powerset] at hAmem
    obtain ⟨hAS, hAn, hAgood⟩ := hAmem
    rcases lt_or_eq_of_le hAn with hlt | heq
    · -- every point outside `A` is on one of the test zero sets
      have hcov : ∀ x ∈ S, x ∉ A → ∃ v ∈ Q A, ev x v = 0 := by
        intro x hxS hxA
        refine Q_cover hxA hAgood (fun hgood => ?_)
        have hle := hAmax (insert x A) (by
          rw [Finset.mem_filter, Finset.mem_powerset]
          refine ⟨Finset.insert_subset hxS hAS, ?_, hgood⟩
          rw [Finset.card_insert_of_notMem hxA]
          omega)
        rw [Finset.card_insert_of_notMem hxA] at hle
        omega
      have hbig : ∃ v ∈ Q A, M ≤ (S.filter (fun x => ev x v = 0)).card := by
        by_contra hcon
        push Not at hcon
        have hsub : S ⊆ A ∪ (Q A).biUnion (fun v => S.filter (fun x => ev x v = 0)) := by
          intro x hx
          by_cases hxA : x ∈ A
          · exact Finset.mem_union_left _ hxA
          · obtain ⟨v, hv, hxv⟩ := hcov x hx hxA
            exact Finset.mem_union_right _
              (Finset.mem_biUnion.2 ⟨v, hv, Finset.mem_filter.2 ⟨hx, hxv⟩⟩)
        have key : S.card ≤ A.card + (Q A).card * M :=
          (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
            (Nat.add_le_add_left (Finset.card_biUnion_le_card_mul (Q A) _ M
              (fun v hv => (hcon v hv).le)) _))
        have h4 := card_Q_le A
        have h5 : A.card * A.card + A.card * (A.card * A.card) ≤ n * n + n * (n * n) := by
          have := Nat.mul_le_mul hAn hAn
          exact Nat.add_le_add this (Nat.mul_le_mul hAn this)
        have h6 : (Q A).card * M ≤ (n * n + n * (n * n)) * M :=
          Nat.mul_le_mul_right _ (h4.trans h5)
        omega
      obtain ⟨v, hvQ, hvM⟩ := hbig
      obtain ⟨a, haA, hav⟩ := Q_nonvanish A v hvQ
      have hlt' := Submodule.finrank_lt_finrank_of_lt (ann_lt S v a (hAS haA) hav)
      obtain ⟨B, hBT, hBcard, hBgood⟩ := hM (S.filter (fun x => ev x v = 0)) (by omega) hvM
      exact ⟨B, hBT.trans (Finset.filter_subset _ _), hBcard, hBgood⟩
    · exact ⟨A, hAS, heq, hAgood⟩

end OMA.Helpers

theorem OMA.solution : type_of% @Erdos1088.f_isLeast := by
  intro d n
  obtain ⟨M, hM⟩ := OMA.Helpers.main d n (Module.finrank ℝ (OMA.Helpers.V d))
  apply isLeast_csInf
  refine ⟨max n M, le_max_left _ _, fun S hS => hM S (Nat.le_add_left _ _) ?_⟩
  rw [hS]
  exact le_max_right _ _
