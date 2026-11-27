import FormalConjectures.ErdosProblems.«593»

/-!
# Obligatory 3-uniform hypergraphs are 2-colorable

Host: for the shift graph `G` on `(r+1)`-tuples of a well-ordered set `L = Set (iterSet r ℕ)`
(built as iterated line digraphs of the transitive tournament), take all triples `{a, b, d}` with
`a → b` an arc and `d ∉ {a, b}`.
* No countable proper coloring of `G` exists: a proper coloring of a line digraph by `C` yields one
  of the digraph by `Set C`, so `L` would inject into `iterSet r ℕ`, contradicting Cantor.
  Hence the host has chromatic cardinal `> ℵ₀` (a monochromatic arc forces its color class to be
  exactly that arc, which one extra bit can separate).
* Every set of at most `r` vertices of `G` induces a 2-colorable subgraph (induction on `r`,
  removing a vertex of minimal rank and projecting arcs to their tails).
With `r = card W`, an appearance of `F` in the host pulls back this local 2-coloring to `F`.
-/

open Cardinal

namespace OMA.Helpers

/-- A ranked digraph: arcs strictly increase the rank. -/
structure RDig (L : Type) [LinearOrder L] where
  V : Type
  A : V → V → Prop
  ρ : V → L
  hρ : ∀ u v, A u v → ρ u < ρ v

variable {L : Type} [LinearOrder L]

/-- The transitive tournament on `L`. -/
def RDig.base (L : Type) [LinearOrder L] : RDig L where
  V := L
  A u v := u < v
  ρ := id
  hρ _ _ h := h

/-- The line digraph. -/
def RDig.line (D : RDig L) : RDig L where
  V := {p : D.V × D.V // D.A p.1 p.2}
  A x y := x.1.2 = y.1.1
  ρ x := D.ρ x.1.1
  hρ x y h := by
    have h1 := D.hρ _ _ x.2
    rw [h] at h1
    exact h1

/-- Iterated line digraphs: the shift graphs. -/
def RDig.iter (L : Type) [LinearOrder L] : ℕ → RDig L
  | 0 => RDig.base L
  | n + 1 => (RDig.iter L n).line

lemma RDig.ne_of_A (D : RDig L) {u v : D.V} (h : D.A u v) : u ≠ v := by
  rintro rfl
  exact lt_irrefl _ (D.hρ u u h)

lemma RDig.not_A_symm (D : RDig L) {u v : D.V} (h : D.A u v) : ¬ D.A v u := fun h' =>
  lt_asymm (D.hρ u v h) (D.hρ v u h')

/-- Iterated power set. -/
def iterSet : ℕ → Type → Type
  | 0, C => C
  | n + 1, C => iterSet n (Set C)

lemma descent (D : RDig L) {C : Type} (c : D.line.V → C)
    (hc : ∀ x y, D.line.A x y → c x ≠ c y) :
    ∃ c' : D.V → Set C, ∀ u v, D.A u v → c' u ≠ c' v := by
  refine ⟨fun u => {k | ∃ x : D.line.V, x.1.2 = u ∧ c x = k}, ?_⟩
  intro u v huv heq
  let x0 : D.line.V := ⟨(u, v), huv⟩
  have hmem : c x0 ∈ (fun u => {k | ∃ x : D.line.V, x.1.2 = u ∧ c x = k}) v := ⟨x0, rfl, rfl⟩
  rw [← heq] at hmem
  obtain ⟨x, hx, hcx⟩ := hmem
  exact hc x x0 hx hcx

lemma iter_inj : ∀ (n : ℕ) (C : Type) (c : (RDig.iter L n).V → C),
    (∀ u v, (RDig.iter L n).A u v → c u ≠ c v) → ∃ g : L → iterSet n C, Function.Injective g
  | 0, C, c, hc => by
    refine ⟨c, fun u v huv => ?_⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hc u v h huv
    · exact hc v u h huv.symm
  | n + 1, C, c, hc => by
    obtain ⟨c', hc'⟩ := descent (RDig.iter L n) c hc
    exact iter_inj n (Set C) c' hc'

lemma iterSet_inj : ∀ (n : ℕ) (C D : Type) (f : C → D), Function.Injective f →
    ∃ g : iterSet n C → iterSet n D, Function.Injective g
  | 0, _, _, f, hf => ⟨f, hf⟩
  | n + 1, C, D, f, hf => iterSet_inj n (Set C) (Set D) (Set.image f) (Set.image_injective.mpr hf)

/-- A type that is too big. -/
def BigL (r : ℕ) : Type := Set (iterSet r ℕ)

noncomputable instance (r : ℕ) : LinearOrder (BigL r) := IsWellOrder.linearOrder WellOrderingRel

lemma no_countable_coloring (r : ℕ) (C : Type) [Countable C]
    (c : (RDig.iter (BigL r) r).V → C)
    (hc : ∀ u v, (RDig.iter (BigL r) r).A u v → c u ≠ c v) : False := by
  obtain ⟨g, hg⟩ := iter_inj r C c hc
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat C
  obtain ⟨h, hh⟩ := iterSet_inj r C ℕ f hf
  exact Function.cantor_injective (h ∘ g) (hh.comp hg)

/-- Every set of at most `m` vertices induces a two-colorable subgraph. -/
def LocalTwo (D : RDig L) (m : ℕ) : Prop :=
  ∀ S : Finset D.V, S.card ≤ m → ∃ c : D.V → Bool, ∀ x ∈ S, ∀ y ∈ S, D.A x y → c x ≠ c y

lemma localTwo_zero (D : RDig L) : LocalTwo D 0 := by
  intro S hS
  refine ⟨fun _ => true, ?_⟩
  intro x hx
  have : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hS)
  simp [this] at hx

lemma localTwo_line (D : RDig L) (m : ℕ) (hD : LocalTwo D m) : LocalTwo D.line (m + 1) := by
  classical
  intro S hS
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => true, by simp⟩
  obtain ⟨α, hαS, hαmin⟩ := S.exists_min_image (fun x => D.ρ x.1.1) hne
  have hTcard : ((S.erase α).image (fun x => x.1.1)).card ≤ m := by
    calc ((S.erase α).image (fun x => x.1.1)).card ≤ (S.erase α).card := Finset.card_image_le
      _ = S.card - 1 := Finset.card_erase_of_mem hαS
      _ ≤ m := by omega
  obtain ⟨c, hc⟩ := hD _ hTcard
  refine ⟨fun y => if y = α then !(c α.1.2) else c y.1.1, ?_⟩
  intro x hx y hy hxy
  have hxy' : x.1.2 = y.1.1 := hxy
  by_cases hxα : x = α
  · subst hxα
    have hyα : y ≠ x := fun h => (D.line.ne_of_A hxy) h.symm
    dsimp only
    rw [if_pos rfl, if_neg hyα, hxy']
    cases c y.1.1 <;> simp
  · by_cases hyα : y = α
    · subst hyα
      exfalso
      have h1 : D.ρ x.1.1 < D.ρ x.1.2 := D.hρ _ _ x.2
      rw [hxy'] at h1
      exact absurd (hαmin x hx) (not_le.mpr h1)
    · dsimp only
      rw [if_neg hxα, if_neg hyα]
      apply hc
      · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hxα, hx⟩, rfl⟩
      · exact Finset.mem_image.mpr ⟨y, Finset.mem_erase.mpr ⟨hyα, hy⟩, rfl⟩
      · have h2 := x.2
        rw [hxy'] at h2
        exact h2

lemma iter_localTwo (L : Type) [LinearOrder L] : ∀ n, LocalTwo (RDig.iter L n) n
  | 0 => localTwo_zero _
  | n + 1 => localTwo_line _ n (iter_localTwo L n)

/-- Edges of the host: an arc plus a third vertex. -/
def hostEdges (D : RDig L) : Set (Set D.V) :=
  {e | ∃ a b d, D.A a b ∧ d ≠ a ∧ d ≠ b ∧ e = {a, b, d}}

/-- The host hypergraph. -/
def host (D : RDig L) : UniformHypergraph D.V 3 where
  vertexSet := Set.univ
  edgeSet := hostEdges D
  subset_vertexSet_of_mem_edgeSet' := fun _ _ => Set.subset_univ _
  vertexSet_eq_univ := rfl
  uniform := by
    rintro e ⟨a, b, d, hab, hda, hdb, rfl⟩
    have hne : a ≠ b := D.ne_of_A hab
    rw [Set.encard_insert_of_notMem, Set.encard_pair]
    · rfl
    · exact fun h => hdb h.symm
    · simp [hne, Ne.symm hda]

lemma host_mono (D : RDig L) {C : Type} (f : D.V → C) (hf : (host D).IsProperColoring f)
    {x y w : D.V} (hxy : D.A x y) (hwx : w ≠ x) (hwy : w ≠ y) (h1 : f x = f y)
    (h2 : f w = f y) : False := by
  obtain ⟨u, hu, v, hv, huv⟩ := hf {x, y, w} ⟨x, y, w, hxy, hwx, hwy, rfl⟩
  have key : ∀ z ∈ ({x, y, w} : Set D.V), f z = f y := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact h1
    · rfl
    · exact h2
  exact huv ((key u hu).trans (key v hv).symm)

lemma host_chrom (r : ℕ) : ℵ₀ < (host (RDig.iter (BigL r) r)).chromaticCardinal := by
  set D := RDig.iter (BigL r) r with hD
  unfold UniformHypergraph.chromaticCardinal
  have hne : {κ : Cardinal.{0} | ∃ (C : Type), #C = κ ∧
      ∃ f : D.V → C, (host D).IsProperColoring f}.Nonempty := by
    refine ⟨#D.V, D.V, rfl, id, ?_⟩
    rintro e ⟨a, b, d, hab, -, -, rfl⟩
    exact ⟨a, by simp, b, by simp, D.ne_of_A hab⟩
  obtain ⟨C, hC, f, hf⟩ := csInf_mem hne
  by_contra hle
  rw [not_lt, ← hC] at hle
  have : Countable C := Cardinal.mk_le_aleph0_iff.mp hle
  classical
  apply no_countable_coloring r (C × Bool) (fun v => (f v, decide (∃ w, f w = f v ∧ D.A v w)))
  intro x y hxy hg
  have h1 : f x = f y := congrArg Prod.fst hg
  have h2 : decide (∃ w, f w = f x ∧ D.A x w) = decide (∃ w, f w = f y ∧ D.A y w) :=
    congrArg Prod.snd hg
  have hx : ∃ w, f w = f x ∧ D.A x w := ⟨y, h1.symm, hxy⟩
  obtain ⟨w, hw, hyw⟩ := (decide_eq_decide.mp h2).mp hx
  have hwy : w ≠ y := (D.ne_of_A hyw).symm
  have hwx : w ≠ x := by
    rintro rfl
    exact D.not_A_symm hxy hyw
  exact host_mono D f hf hxy hwx hwy h1 hw

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @Erdos593.erdos_593.variants.obligatory_implies_two_colorable := by
  intro W _ F hF
  classical
  obtain ⟨φ, -, hφ⟩ := hF (RDig.iter (BigL (Fintype.card W)) (Fintype.card W)).V
    (host (RDig.iter (BigL (Fintype.card W)) (Fintype.card W))) (host_chrom (Fintype.card W))
  obtain ⟨c, hc⟩ := iter_localTwo (BigL (Fintype.card W)) (Fintype.card W)
    (Finset.univ.image φ) (Finset.card_image_le.trans (le_of_eq Finset.card_univ))
  refine ⟨fun w => if c (φ w) then 1 else 0, ?_⟩
  intro e he
  have hmem := hφ ⟨e, he, rfl⟩
  obtain ⟨a, b, d, hab, -, -, heq⟩ := hmem
  have ha : a ∈ φ '' e := by rw [heq]; simp
  have hb : b ∈ φ '' e := by rw [heq]; simp
  obtain ⟨u, hu, rfl⟩ := ha
  obtain ⟨u', hu', rfl⟩ := hb
  refine ⟨u, hu, u', hu', ?_⟩
  have hcc := hc (φ u) (Finset.mem_image_of_mem φ (Finset.mem_univ u)) (φ u')
    (Finset.mem_image_of_mem φ (Finset.mem_univ u')) hab
  revert hcc
  dsimp only
  cases c (φ u) <;> cases c (φ u') <;> decide
