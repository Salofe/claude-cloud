import FormalConjectures.ErdosProblems.«174»

/-!
# Isosceles trapezoids are Ramsey (Kříž)

The four points `(±s, 0)`, `(±t, h)` are embedded isometrically in `ℂ × ℝ` as
`p₀`, `cj p₀`, `rot p₀`, `cj (rot p₀)`, where `rot (z, u) = (ζ z, -u)` for a root of unity `ζ` of
order `2 ^ a` (`a` large, depending on `s`, `t`, `h`) and `cj (z, u) = (conj z, u)`.
These points lie in a finite set `Orb` which is stable under `rot` and `cj`.

The combinatorial part is a Hales--Jewett type statement for words whose letters are points of a
finite set `X` and whose variables are distance-preserving permutations of `X`:
for every finite colouring of `ι → X` (with `ι` large) there is a map `Φ : X → ι → X`, each of
whose coordinates is constant or a distance-preserving map, with a number of non-constant
coordinates which does not depend on the colouring, and which is monochromatic on a prescribed
class. Classes are enlarged along a chain of index-two extensions: a pigeonhole argument and a
product argument (in the style of Shelah) for each step.
-/

open Erdos174

namespace OMA.Helpers

section Framework

variable {X : Type} (D : X → X → ℝ)

/-- `Φ` multiplies the (squared) distance `D` by `d`, summed over the coordinates. -/
def Dil (d : ℝ) {ι : Type} [Fintype ι] (Φ : X → ι → X) : Prop :=
  ∀ x x', ∑ i, D (Φ x i) (Φ x' i) = d * D x x'

/-- Every coordinate of `Φ` is constant or keeps every point in its `E`-class. -/
def Cls (E : X → X → Prop) {ι : Type} (Φ : X → ι → X) : Prop :=
  ∀ i, (∀ x x', Φ x i = Φ x' i) ∨ (∀ x, E (Φ x i) x)

/-- The Hales--Jewett type property with fixed dilation factor. -/
def Hyp (E R : X → X → Prop) (d : ℝ) : Prop :=
  ∀ (κ : Type) [Finite κ], ∃ (ι : Type) (_ : Fintype ι), ∀ c : (ι → X) → κ,
    ∃ Φ : X → ι → X, Dil D d Φ ∧ Cls E Φ ∧ ∀ x x', R x x' → c (Φ x) = c (Φ x')

theorem Hyp.mono {E E' R R' : X → X → Prop} {d : ℝ} (h : Hyp D E R d)
    (hE : ∀ a b, E a b → E' a b) (hR : ∀ x x', R' x x' → R x x') : Hyp D E' R' d := by
  intro κ _
  obtain ⟨ι, _, hι⟩ := h κ
  refine ⟨ι, inferInstance, fun c => ?_⟩
  obtain ⟨Φ, h1, h2, h3⟩ := hι c
  refine ⟨Φ, h1, fun i => ?_, fun x x' hx => h3 x x' (hR x x' hx)⟩
  rcases h2 i with h | h
  · exact Or.inl h
  · exact Or.inr fun x => hE _ _ (h x)

theorem dil_comp {J : Type} [Fintype J] {β : J → Type} [∀ j, Fintype (β j)] {d' d : ℝ}
    {Φ' : X → J → X} {Φ : ∀ j, X → β j → X} (h' : Dil D d' Φ') (h : ∀ j, Dil D d (Φ j)) :
    Dil D (d' * d) (fun x (p : Σ j, β j) => Φ p.1 (Φ' x p.1) p.2) := by
  intro x x'
  rw [Fintype.sum_sigma]
  have : ∀ j, ∑ b, D (Φ j (Φ' x j) b) (Φ j (Φ' x' j) b) = d * D (Φ' x j) (Φ' x' j) :=
    fun j => h j _ _
  simp only [this, ← Finset.mul_sum, h' x x']
  ring

theorem cls_comp {J : Type} {β : J → Type} {E₁ E₂ E₃ : X → X → Prop}
    {Φ' : X → J → X} {Φ : ∀ j, X → β j → X} (h' : Cls E₁ Φ') (h : ∀ j, Cls E₂ (Φ j))
    (hE : ∀ a b c, E₂ a b → E₁ b c → E₃ a c) :
    Cls E₃ (fun x (p : Σ j, β j) => Φ p.1 (Φ' x p.1) p.2) := by
  rintro ⟨j, b⟩
  rcases h' j with h1 | h1
  · left
    intro x x'
    simp only
    rw [h1 x x']
  · rcases h j b with h2 | h2
    · left
      intro x x'
      exact h2 _ _
    · right
      intro x
      exact hE _ _ _ (h2 _) (h1 x)

/-- A family of types indexed by `Option α`. -/
def optFam {α : Type} (ι₀ : Type) (β : α → Type) : Option α → Type
  | none => ι₀
  | some a => β a

/-- Glue a dependent function on `Option α`. -/
def optGlue {α : Type} {ι₀ : Type} {β : α → Type} {Y : Type} (w : ι₀ → Y)
    (rest : ∀ a, β a → Y) : ∀ o, optFam ι₀ β o → Y
  | none => w
  | some a => rest a

/-- Glue a family of words indexed by `Option α`. -/
def optWord {α : Type} {ι₀ : Type} {β : α → Type} {Y : Type} (Φ₀ : Y → ι₀ → Y)
    (Φ : ∀ a, Y → β a → Y) : ∀ o, Y → optFam ι₀ β o → Y
  | none => Φ₀
  | some a => Φ a

/-- The `Fintype` structures of a glued family. -/
abbrev optFin {α : Type} {ι₀ : Type} {β : α → Type} (h₀ : Fintype ι₀) (h : ∀ a, Fintype (β a)) :
    ∀ o, Fintype (optFam ι₀ β o)
  | none => h₀
  | some a => h a

theorem prod_lemma [Finite X] {E R : X → X → Prop} {d : ℝ} (h : Hyp D E R d) (J : Type)
    [Finite J] : ∀ (κ : Type) [Finite κ], ∃ (β : J → Type) (_ : ∀ j, Fintype (β j)),
      ∀ c : (∀ j, β j → X) → κ, ∃ Φ : ∀ j, X → β j → X,
        (∀ j, Dil D d (Φ j)) ∧ (∀ j, Cls E (Φ j)) ∧
        ∀ x x' : J → X, (∀ j, R (x j) (x' j) ∨ x j = x' j) →
          c (fun j => Φ j (x j)) = c (fun j => Φ j (x' j)) := by
  induction J using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro κ _
    obtain ⟨β, hβ, H⟩ := ih κ
    refine ⟨fun j => β (e.symm j), fun j => hβ (e.symm j), fun c => ?_⟩
    obtain ⟨Φ, h1, h2, h3⟩ := H (fun f => c (fun j => f (e.symm j)))
    refine ⟨fun j => Φ (e.symm j), fun j => h1 _, fun j => h2 _, fun x x' hx => ?_⟩
    have := h3 (fun a => x (e a)) (fun a => x' (e a)) (fun a => hx (e a))
    simpa using this
  | h_empty =>
    intro κ _
    refine ⟨fun _ => PEmpty, fun _ => inferInstance, fun c => ⟨fun j => j.elim, fun j => j.elim,
      fun j => j.elim, fun x x' _ => ?_⟩⟩
    congr 1
    funext j
    exact j.elim
  | @h_option α _ ih =>
    intro κ _
    obtain ⟨β, hβ, H⟩ := ih (X → κ)
    obtain ⟨ι₀, hι₀, H₀⟩ := h ((∀ a, β a → X) → κ)
    refine ⟨optFam ι₀ β, optFin hι₀ hβ, fun c => ?_⟩
    obtain ⟨Φ₀, a1, a2, a3⟩ := H₀ (fun w rest => c (optGlue w rest))
    obtain ⟨Φ, b1, b2, b3⟩ := H (fun rest x₀ => c (optGlue (Φ₀ x₀) rest))
    refine ⟨optWord Φ₀ Φ, fun o => ?_, fun o => ?_, fun x x' hx => ?_⟩
    · cases o with
      | none => exact a1
      | some a => exact b1 a
    · cases o with
      | none => exact a2
      | some a => exact b2 a
    · have e1 : ∀ z : Option α → X, (fun o => optWord Φ₀ Φ o (z o)) =
          optGlue (Φ₀ (z none)) (fun a => Φ a (z (some a))) := by
        intro z
        funext o
        cases o <;> rfl
      have s1 := congrFun (b3 (fun a => x (some a)) (fun a => x' (some a)) (fun a => hx (some a)))
        (x none)
      rw [e1 x, e1 x']
      refine Eq.trans s1 ?_
      rcases hx none with hR | heq
      · exact congrFun (a3 _ _ hR) _
      · rw [heq]

theorem hyp_two [Finite X] {E R₁ R₂ : X → X → Prop} {d₁ d₂ : ℝ}
    (htrans : ∀ a b c, E a b → E b c → E a c)
    (h₁ : Hyp D E R₁ d₁) (h₂ : Hyp D E R₂ d₂)
    (hR : ∀ x x', R₂ x x' → ∀ z z', E z x → E z' x' → R₂ z z') :
    Hyp D E (fun x x' => R₁ x x' ∨ R₂ x x') (d₁ * d₂) := by
  intro κ _
  obtain ⟨ι₁, _, hι₁⟩ := h₁ κ
  obtain ⟨β, _, hβ⟩ := prod_lemma D h₂ ι₁ κ
  refine ⟨Σ j, β j, inferInstance, fun c => ?_⟩
  obtain ⟨Φ, hΦd, hΦc, hΦ⟩ := hβ (fun f => c (fun p => f p.1 p.2))
  obtain ⟨Φ', hd', hc', hΦ'⟩ := hι₁ (fun x => c (fun p => Φ p.1 (x p.1) p.2))
  refine ⟨fun x p => Φ p.1 (Φ' x p.1) p.2, dil_comp D hd' hΦd,
    cls_comp hc' hΦc htrans, ?_⟩
  rintro x x' (h | h)
  · exact hΦ' x x' h
  · refine hΦ (Φ' x) (Φ' x') (fun j => ?_)
    rcases hc' j with hconst | hcl
    · exact Or.inr (hconst x x')
    · exact Or.inl (hR x x' h _ _ (hcl x) (hcl x'))

theorem hyp_merge [Finite X] {E R : X → X → Prop} {d : ℝ} (τ : X → X) (y₁ y₂ : X)
    (S₁ S₂ : X → Prop) (hD0 : ∀ x, D x x = 0) (hτ : ∀ x x', D (τ x) (τ x') = D x x')
    (h : Hyp D E R d)
    (hR1 : ∀ x x', S₁ x → S₁ x' → R x x') (hR2 : ∀ x x', S₂ x → S₂ x' → R x x')
    (hy1 : S₁ y₁) (hy2 : S₂ y₂) (hτ1 : ∀ x, S₁ x → S₂ (τ x)) (hτ2 : ∀ x, S₂ x → S₁ (τ x)) :
    Hyp D (fun a b => E a b ∨ E a (τ b))
      (fun x x' => (S₁ x ∨ S₂ x) ∧ (S₁ x' ∨ S₂ x')) (2 * d) := by
  classical
  intro κ _
  have : Fintype κ := Fintype.ofFinite κ
  obtain ⟨β, _, hβ⟩ := prod_lemma D h (Option κ) κ
  refine ⟨Σ j, β j, inferInstance, fun c => ?_⟩
  obtain ⟨Φ, hΦd, hΦc, hΦ⟩ := hβ (fun f => c (fun p => f p.1 p.2))
  obtain ⟨j₁, j₂, hne, hu⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun j₀ : Option κ => c (fun p => Φ p.1 (if p.1 = j₀ then y₂ else y₁) p.2))
    (by simp)
  have hne' : j₂ ≠ j₁ := fun h3 => hne h3.symm
  let Φ' : X → Option κ → X := fun x j => if j = j₁ then τ x else if j = j₂ then x else y₁
  have e1 : ∀ x, Φ' x j₁ = τ x := fun x => by simp [Φ']
  have e2 : ∀ x, Φ' x j₂ = x := fun x => by simp [Φ', hne']
  have e3 : ∀ x j, j ≠ j₁ → j ≠ j₂ → Φ' x j = y₁ := fun x j h1 h2 => by simp [Φ', h1, h2]
  have hd' : Dil D 2 Φ' := by
    intro x x'
    have : ∀ j, D (Φ' x j) (Φ' x' j) =
        (if j = j₁ then D x x' else 0) + (if j = j₂ then D x x' else 0) := by
      intro j
      rcases eq_or_ne j j₁ with rfl | h1
      · rw [e1, e1, hτ, if_pos rfl, if_neg hne, add_zero]
      · rcases eq_or_ne j j₂ with rfl | h2
        · rw [e2, e2, if_neg h1, if_pos rfl, zero_add]
        · rw [e3 x j h1 h2, e3 x' j h1 h2, hD0, if_neg h1, if_neg h2, add_zero]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hc' : Cls (fun a b => a = b ∨ a = τ b) Φ' := by
    intro j
    rcases eq_or_ne j j₁ with rfl | h1
    · exact Or.inr fun x => Or.inr (e1 x)
    · rcases eq_or_ne j j₂ with rfl | h2
      · exact Or.inr fun x => Or.inl (e2 x)
      · exact Or.inl fun x x' => by rw [e3 x j h1 h2, e3 x' j h1 h2]
  refine ⟨fun x p => Φ p.1 (Φ' x p.1) p.2, dil_comp D hd' hΦd, cls_comp hc' hΦc ?_, ?_⟩
  · rintro a b c hab (rfl | rfl)
    · exact Or.inl hab
    · exact Or.inr hab
  · have key1 : ∀ x, S₁ x → c (fun p => Φ p.1 (Φ' x p.1) p.2) =
        c (fun p => Φ p.1 (if p.1 = j₁ then y₂ else y₁) p.2) := by
      intro x hx
      refine hΦ (Φ' x) (fun j => if j = j₁ then y₂ else y₁) (fun j => ?_)
      rcases eq_or_ne j j₁ with rfl | h1
      · left
        rw [e1, if_pos rfl]
        exact hR2 _ _ (hτ1 x hx) hy2
      · rcases eq_or_ne j j₂ with rfl | h2
        · left
          rw [e2, if_neg h1]
          exact hR1 _ _ hx hy1
        · right
          rw [e3 x j h1 h2, if_neg h1]
    have key2 : ∀ x, S₂ x → c (fun p => Φ p.1 (Φ' x p.1) p.2) =
        c (fun p => Φ p.1 (if p.1 = j₂ then y₂ else y₁) p.2) := by
      intro x hx
      refine hΦ (Φ' x) (fun j => if j = j₂ then y₂ else y₁) (fun j => ?_)
      rcases eq_or_ne j j₁ with rfl | h1
      · left
        rw [e1, if_neg hne]
        exact hR1 _ _ (hτ2 x hx) hy1
      · rcases eq_or_ne j j₂ with rfl | h2
        · left
          rw [e2, if_pos rfl]
          exact hR2 _ _ hx hy2
        · right
          rw [e3 x j h1 h2, if_neg h2]
    have key : ∀ x, (S₁ x ∨ S₂ x) → c (fun p => Φ p.1 (Φ' x p.1) p.2) =
        c (fun p => Φ p.1 (if p.1 = j₁ then y₂ else y₁) p.2) := by
      rintro x (hx | hx)
      · exact key1 x hx
      · exact (key2 x hx).trans hu.symm
    rintro x x' ⟨hx, hx'⟩
    exact (key x hx).trans (key x' hx').symm

theorem hyp_step [Finite X] {E : X → X → Prop} {d : ℝ} (τ : X → X)
    (hD0 : ∀ x, D x x = 0) (hτ : ∀ x x', D (τ x) (τ x') = D x x')
    (hrefl : ∀ x, E x x) (htrans : ∀ a b c, E a b → E b c → E a c)
    (hb : ∀ x x', E x x' → E (τ x) (τ x')) (hc : ∀ x, E (τ (τ x)) x)
    (hQ : ∀ y, Hyp D E (fun x x' => E x y ∧ E x' y) d) (y : X) :
    Hyp D (fun a b => E a b ∨ E a (τ b))
      (fun x x' => (E x y ∨ E x (τ y)) ∧ (E x' y ∨ E x' (τ y))) (2 * (d * d)) := by
  have h2 := hyp_two D htrans (hQ y) (hQ (τ y))
    (fun x x' hx z z' hz hz' => ⟨htrans _ _ _ hz hx.1, htrans _ _ _ hz' hx.2⟩)
  exact hyp_merge D τ y (τ y) (fun x => E x y) (fun x => E x (τ y)) hD0 hτ h2
    (fun x x' hx hx' => Or.inl ⟨hx, hx'⟩) (fun x x' hx hx' => Or.inr ⟨hx, hx'⟩)
    (hrefl y) (hrefl (τ y)) (fun x hx => hb _ _ hx)
    (fun x hx => htrans _ _ _ (hb _ _ hx) (hc y))

/-- `x` lies in the forward orbit of `x'` under `f`. -/
def Ef (f : Equiv.Perm X) (x x' : X) : Prop := ∃ k : ℕ, x = (f ^ k) x'

theorem Ef_refl (f : Equiv.Perm X) (x : X) : Ef f x x := ⟨0, by simp⟩

theorem Ef_trans (f : Equiv.Perm X) (a b c : X) : Ef f a b → Ef f b c → Ef f a c := by
  rintro ⟨k, rfl⟩ ⟨l, rfl⟩
  exact ⟨k + l, by rw [pow_add, Equiv.Perm.mul_apply]⟩

theorem sq_step [Finite X] (f : Equiv.Perm X) (hD0 : ∀ x, D x x = 0)
    (hf : ∀ x x', D (f x) (f x') = D x x') {d : ℝ}
    (hQ : ∀ y, Hyp D (Ef (f * f)) (fun x x' => Ef (f * f) x y ∧ Ef (f * f) x' y) d) (y : X) :
    Hyp D (Ef f) (fun x x' => Ef f x y ∧ Ef f x' y) (2 * (d * d)) := by
  have hb : ∀ x x', Ef (f * f) x x' → Ef (f * f) (f x) (f x') := by
    rintro x x' ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← pow_two, ← pow_mul, ← pow_succ',
      ← pow_succ]
  have hc : ∀ x, Ef (f * f) (f (f x)) x := fun x => ⟨1, by simp⟩
  have h := hyp_step D f hD0 hf (Ef_refl (f * f)) (Ef_trans (f * f)) hb hc hQ y
  refine h.mono D ?_ ?_
  · rintro a b (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact ⟨2 * k, by rw [pow_mul, pow_two]⟩
    · exact ⟨2 * k + 1, by rw [pow_succ, pow_mul, pow_two, Equiv.Perm.mul_apply]⟩
  · have aux : ∀ x, Ef f x y → Ef (f * f) x y ∨ Ef (f * f) x (f y) := by
      rintro x ⟨k, rfl⟩
      rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
      · exact Or.inl ⟨m, by rw [pow_mul, pow_two]⟩
      · exact Or.inr ⟨m, by rw [pow_succ, pow_mul, pow_two, Equiv.Perm.mul_apply]⟩
    rintro x x' ⟨hx, hx'⟩
    exact ⟨aux x hx, aux x' hx'⟩

/-- The dilation factors along a chain of index-two extensions. -/
def dd : ℕ → ℝ
  | 0 => 1
  | (a + 1) => 2 * (dd a * dd a)

theorem dd_pos (a : ℕ) : 0 < dd a := by
  induction a with
  | zero => simp [dd]
  | succ a ih =>
    simp only [dd]
    positivity

theorem pow_two_case [Finite X] (hD0 : ∀ x, D x x = 0) : ∀ (a : ℕ) (f : Equiv.Perm X),
    (∀ x x', D (f x) (f x') = D x x') → f ^ (2 ^ a) = 1 →
    ∀ y, Hyp D (Ef f) (fun x x' => Ef f x y ∧ Ef f x' y) (dd a)
  | 0, f, _, h1, y => by
    have hf1 : f = 1 := by simpa using h1
    subst hf1
    intro κ _
    refine ⟨Unit, inferInstance, fun c => ⟨fun x _ => x, ?_, ?_, ?_⟩⟩
    · intro x x'
      simp [dd]
    · intro i
      exact Or.inr fun x => Ef_refl _ _
    · rintro x x' ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩
      simp
  | a + 1, f, hf, h1, y => by
    refine sq_step D f hD0 hf (pow_two_case hD0 a (f * f) ?_ ?_) y
    · intro x x'
      simp [hf]
    · rw [← pow_two, ← pow_mul, ← pow_succ']
      exact h1

theorem main_comb [Finite X] (hD0 : ∀ x, D x x = 0) (ρ σ : Equiv.Perm X)
    (hρ : ∀ x x', D (ρ x) (ρ x') = D x x') (hσ : ∀ x x', D (σ x) (σ x') = D x x') (a m : ℕ)
    (hρa : ρ ^ (2 ^ a) = 1) (hσσ : ∀ x, σ (σ x) = x) (hσρ : ∀ x, σ (ρ x) = (ρ ^ m) (σ x))
    (x₀ : X) (κ : Type) [Finite κ] :
    ∃ (ι : Type) (_ : Fintype ι), ∀ c : (ι → X) → κ, ∃ Φ : X → ι → X,
      Dil D (2 * (dd a * dd a)) Φ ∧ c (Φ (σ x₀)) = c (Φ x₀) ∧ c (Φ (ρ x₀)) = c (Φ x₀) ∧
        c (Φ (σ (ρ x₀))) = c (Φ x₀) := by
  have aux : ∀ (k : ℕ) (x : X), σ ((ρ ^ k) x) = (ρ ^ (m * k)) (σ x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih, hσρ, ← Equiv.Perm.mul_apply, ← pow_add,
        Nat.mul_succ]
  have hb : ∀ x x', Ef ρ x x' → Ef ρ (σ x) (σ x') := by
    rintro x x' ⟨k, rfl⟩
    exact ⟨m * k, aux k x'⟩
  have hc : ∀ x, Ef ρ (σ (σ x)) x := fun x => by
    rw [hσσ]
    exact Ef_refl ρ x
  have h := hyp_step D σ hD0 hσ (Ef_refl ρ) (Ef_trans ρ) hb hc
    (pow_two_case D hD0 a ρ hρ hρa) x₀
  obtain ⟨ι, hι, H⟩ := h κ
  refine ⟨ι, hι, fun c => ?_⟩
  obtain ⟨Φ, h1, _, h3⟩ := H c
  have b0 : Ef ρ x₀ x₀ ∨ Ef ρ x₀ (σ x₀) := Or.inl (Ef_refl ρ x₀)
  refine ⟨Φ, h1, h3 _ _ ⟨Or.inr (Ef_refl ρ _), b0⟩, h3 _ _ ⟨Or.inl ⟨1, by simp⟩, b0⟩,
    h3 _ _ ⟨Or.inr ⟨m, hσρ x₀⟩, b0⟩⟩

end Framework

section Geometry

/-- Squared distance in `ℂ × ℝ`, in coordinates. -/
def D2 (p q : ℂ × ℝ) : ℝ :=
  (p.1.re - q.1.re) ^ 2 + (p.1.im - q.1.im) ^ 2 + (p.2 - q.2) ^ 2

/-- Rotation of the complex coordinate together with a sign change of the real one. -/
noncomputable def rot (ζ : ℂ) (hζ : ζ ≠ 0) : Equiv.Perm (ℂ × ℝ) where
  toFun p := (ζ * p.1, -p.2)
  invFun p := (ζ⁻¹ * p.1, -p.2)
  left_inv p := by simp [hζ]
  right_inv p := by simp [hζ]

/-- Complex conjugation of the complex coordinate. -/
def cj : Equiv.Perm (ℂ × ℝ) where
  toFun p := (starRingEnd ℂ p.1, p.2)
  invFun p := (starRingEnd ℂ p.1, p.2)
  left_inv p := by simp
  right_inv p := by simp

theorem rot_apply (ζ : ℂ) (hζ : ζ ≠ 0) (p : ℂ × ℝ) : rot ζ hζ p = (ζ * p.1, -p.2) := rfl

theorem cj_apply (p : ℂ × ℝ) : cj p = (starRingEnd ℂ p.1, p.2) := rfl

theorem rot_pow (ζ : ℂ) (hζ : ζ ≠ 0) (k : ℕ) (p : ℂ × ℝ) :
    (rot ζ hζ ^ k) p = (ζ ^ k * p.1, (-1) ^ k * p.2) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, rot_apply]
    refine Prod.ext ?_ ?_
    · simp only [pow_succ]
      ring
    · simp only [pow_succ]
      ring

theorem D2_self (p : ℂ × ℝ) : D2 p p = 0 := by simp [D2]

theorem D2_rot (ζ : ℂ) (hζ : ζ ≠ 0) (h1 : ζ.re ^ 2 + ζ.im ^ 2 = 1) (p q : ℂ × ℝ) :
    D2 (rot ζ hζ p) (rot ζ hζ q) = D2 p q := by
  simp only [D2, rot_apply, Complex.mul_re, Complex.mul_im]
  linear_combination ((p.1.re - q.1.re) ^ 2 + (p.1.im - q.1.im) ^ 2) * h1

theorem D2_cj (p q : ℂ × ℝ) : D2 (cj p) (cj q) = D2 p q := by
  simp only [D2, cj_apply, Complex.conj_re, Complex.conj_im]
  ring

/-- A finite set of points which is stable under `rot` and `cj`. -/
def Orb (n : ℕ) (p₀ : ℂ × ℝ) : Set (ℂ × ℝ) :=
  {p | (p.1 ^ n = p₀.1 ^ n ∨ p.1 ^ n = (starRingEnd ℂ p₀.1) ^ n) ∧ (p.2 = p₀.2 ∨ p.2 = -p₀.2)}

theorem orb_finite (n : ℕ) (hn : 0 < n) (p₀ : ℂ × ℝ) : (Orb n p₀).Finite := by
  have h1 : ∀ c : ℂ, {x : ℂ | x ^ n = c}.Finite := fun c =>
    (Multiset.finite_toSet (Polynomial.nthRoots n c)).subset
      fun x hx => (Polynomial.mem_nthRoots hn).2 hx
  refine (((h1 (p₀.1 ^ n)).union (h1 ((starRingEnd ℂ p₀.1) ^ n))).prod
    (Set.toFinite {p₀.2, -p₀.2})).subset ?_
  rintro ⟨p1, p2⟩ ⟨h, h'⟩
  exact ⟨h, h'⟩

theorem orb_self (n : ℕ) (p₀ : ℂ × ℝ) : p₀ ∈ Orb n p₀ := ⟨Or.inl rfl, Or.inl rfl⟩

theorem orb_rot (n : ℕ) (p₀ : ℂ × ℝ) (ζ : ℂ) (hζ : ζ ≠ 0) (hn : ζ ^ n = 1) (p : ℂ × ℝ) :
    rot ζ hζ p ∈ Orb n p₀ ↔ p ∈ Orb n p₀ := by
  have e : (-p.2 = p₀.2 ∨ -p.2 = -p₀.2) ↔ (p.2 = p₀.2 ∨ p.2 = -p₀.2) := by
    constructor
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
  simp only [Orb, Set.mem_ofPred_eq, rot_apply, mul_pow, hn, one_mul, e]

theorem orb_cj (n : ℕ) (p₀ : ℂ × ℝ) (p : ℂ × ℝ) : cj p ∈ Orb n p₀ ↔ p ∈ Orb n p₀ := by
  have key : ∀ u v : ℂ, (starRingEnd ℂ u) ^ n = v ↔ u ^ n = starRingEnd ℂ v := by
    intro u v
    constructor
    · intro h
      have := congrArg (starRingEnd ℂ) h
      simpa using this
    · intro h
      have := congrArg (starRingEnd ℂ) h
      simpa using this
  simp only [Orb, Set.mem_ofPred_eq, cj_apply, key, map_pow, Complex.conj_conj]
  rw [or_comm]

theorem core (a : ℕ) (ha : 1 ≤ a) (ζ : ℂ) (hζ : ζ ≠ 0) (hζ1 : ζ.re ^ 2 + ζ.im ^ 2 = 1)
    (hζa : ζ ^ (2 ^ a) = 1) (p₀ : ℂ × ℝ) (κ : Type) [Finite κ] :
    ∃ (ι : Type) (_ : Fintype ι), ∀ c : (ι → ℂ × ℝ) → κ, ∃ Ψ : ℂ × ℝ → ι → ℂ × ℝ,
      (∀ p q, p ∈ Orb (2 ^ a) p₀ → q ∈ Orb (2 ^ a) p₀ →
        ∑ i, D2 (Ψ p i) (Ψ q i) = 2 * (dd a * dd a) * D2 p q) ∧
      c (Ψ (cj p₀)) = c (Ψ p₀) ∧ c (Ψ (rot ζ hζ p₀)) = c (Ψ p₀) ∧
        c (Ψ (cj (rot ζ hζ p₀))) = c (Ψ p₀) := by
  classical
  have hfin : Finite (Orb (2 ^ a) p₀) := (orb_finite (2 ^ a) (by positivity) p₀).to_subtype
  let ρ : Equiv.Perm (Orb (2 ^ a) p₀) :=
    (rot ζ hζ).subtypePerm (orb_rot (2 ^ a) p₀ ζ hζ hζa)
  let σ : Equiv.Perm (Orb (2 ^ a) p₀) := cj.subtypePerm (orb_cj (2 ^ a) p₀)
  let D : Orb (2 ^ a) p₀ → Orb (2 ^ a) p₀ → ℝ := fun x x' => D2 x.1 x'.1
  have hρval : ∀ (k : ℕ) (x : Orb (2 ^ a) p₀), ((ρ ^ k) x).1 = (rot ζ hζ ^ k) x.1 := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, Equiv.Perm.mul_apply]
      rfl
  have heven : ((-1 : ℝ)) ^ (2 ^ a) = 1 :=
    Even.neg_one_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = 2 ^ a := ⟨2 ^ a - 1, Nat.sub_add_cancel Nat.one_le_two_pow⟩
  have hodd : ((-1 : ℝ)) ^ m = -1 := by
    have : ((-1 : ℝ)) ^ m * (-1) = 1 := by rw [← pow_succ, hm, heven]
    linarith
  have hconj : starRingEnd ℂ ζ = ζ ^ m := by
    have h1 : starRingEnd ℂ ζ * ζ = 1 := by
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.one_re]
        linarith
      · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_im]
        ring
    have h2 : ζ ^ m * ζ = 1 := by rw [← pow_succ, hm, hζa]
    exact mul_right_cancel₀ hζ (h1.trans h2.symm)
  have hρa : ρ ^ (2 ^ a) = 1 := by
    refine Equiv.ext fun x => Subtype.ext ?_
    rw [hρval, rot_pow, hζa, heven]
    simp
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    refine Subtype.ext ?_
    change cj (cj x.1) = x.1
    simp [cj_apply]
  have hσρ : ∀ x, σ (ρ x) = (ρ ^ m) (σ x) := by
    intro x
    refine Subtype.ext ?_
    rw [hρval]
    change cj (rot ζ hζ x.1) = (rot ζ hζ ^ m) (cj x.1)
    rw [rot_pow, cj_apply, cj_apply, rot_apply, hodd, ← hconj]
    simp
  obtain ⟨ι, hι, H⟩ := main_comb D (fun x => D2_self x.1) ρ σ
    (fun x x' => D2_rot ζ hζ hζ1 x.1 x'.1) (fun x x' => D2_cj x.1 x'.1) a m hρa hσσ hσρ
    ⟨p₀, orb_self _ _⟩ κ
  refine ⟨ι, hι, fun c => ?_⟩
  obtain ⟨Φ, h1, h2, h3, h4⟩ := H (fun f => c (fun i => (f i).1))
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℂ × ℝ → ι → ℂ × ℝ, ∀ p (hp : p ∈ Orb (2 ^ a) p₀),
      Ψ p = fun i => (Φ ⟨p, hp⟩ i).1 :=
    ⟨fun p => if hp : p ∈ Orb (2 ^ a) p₀ then fun i => (Φ ⟨p, hp⟩ i).1 else fun _ => p,
      fun p hp => dif_pos hp⟩
  have m0 := orb_self (2 ^ a) p₀
  have m1 := (orb_cj (2 ^ a) p₀ p₀).2 m0
  have m2 := (orb_rot (2 ^ a) p₀ ζ hζ hζa p₀).2 m0
  have m3 := (orb_cj (2 ^ a) p₀ _).2 m2
  refine ⟨Ψ, ?_, ?_, ?_, ?_⟩
  · intro p q hp hq
    rw [hΨ p hp, hΨ q hq]
    exact h1 ⟨p, hp⟩ ⟨q, hq⟩
  · rw [hΨ _ m1, hΨ _ m0]
    exact h2
  · rw [hΨ _ m2, hΨ _ m0]
    exact h3
  · rw [hΨ _ m3, hΨ _ m0]
    exact h4

theorem exists_angle (s t h : ℝ) (hh : h ≠ 0) :
    ∃ (a : ℕ) (ζ : ℂ), 1 ≤ a ∧ ζ ≠ 0 ∧ ζ ^ (2 ^ a) = 1 ∧ ζ.re ^ 2 + ζ.im ^ 2 = 1 ∧ 0 < ζ.im ∧
      ((s + t) * (1 - ζ.re) / ζ.im) ^ 2 ≤ h ^ 2 := by
  have hpos : 0 < |h| := abs_pos.mpr hh
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = |s + t| + 1 := ⟨_, rfl⟩
  have hLpos : 0 < L := by rw [hL]; positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (5 * L / |h|)
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = m + 2 := ⟨_, rfl⟩
  have h2a : 5 * L / |h| < (2 : ℝ) ^ a := by
    have h1 : (m : ℝ) < (2 : ℝ) ^ m := by exact_mod_cast Nat.lt_two_pow_self
    have h2 : (2 : ℝ) ^ m ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have h4 : (4 : ℝ) ≤ 2 ^ a := by
    have h2 : (2 : ℝ) ^ 2 ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_four
  have hpi3 := Real.pi_gt_three
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 2 * Real.pi / 2 ^ a := ⟨_, rfl⟩
  have hδ' : δ * 2 ^ a = 2 * Real.pi := by rw [hδ]; field_simp
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδle : δ ≤ Real.pi / 2 := by nlinarith
  have hsinpos : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδpos (by linarith)
  refine ⟨a, Complex.exp (δ * Complex.I), by omega, Complex.exp_ne_zero _, ?_, ?_, ?_, ?_⟩
  · rw [← Complex.exp_nat_mul]
    have e : ((2 ^ a : ℕ) : ℂ) * ((δ : ℂ) * Complex.I) = 2 * Real.pi * Complex.I := by
      have : ((δ * 2 ^ a : ℝ) : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by rw [hδ']
      push_cast at this ⊢
      linear_combination Complex.I * this
    rw [e, Complex.exp_two_pi_mul_I]
  · rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    exact Real.cos_sq_add_sin_sq δ
  · rw [Complex.exp_ofReal_mul_I_im]
    exact hsinpos
  · rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    have hsin : 2 / Real.pi * δ ≤ Real.sin δ := Real.mul_le_sin hδpos.le hδle
    have hcos : 1 - δ ^ 2 / 2 ≤ Real.cos δ := Real.one_sub_sq_div_two_le_cos
    have hcos1 : Real.cos δ ≤ 1 := Real.cos_le_one δ
    have h5 : 5 * L < |h| * 2 ^ a := by
      rw [div_lt_iff₀ hpos] at h2a
      linarith
    have e3 : L * δ * Real.pi ≤ 4 * |h| := by
      have hpi315 := Real.pi_lt_d2
      have hpp : Real.pi ^ 2 ≤ 10 := by nlinarith
      have e4 : L * δ * Real.pi * 2 ^ a = 2 * L * Real.pi ^ 2 := by
        linear_combination L * Real.pi * hδ'
      have e5 : 2 * L * Real.pi ^ 2 ≤ 4 * |h| * 2 ^ a := by nlinarith
      have e6 : L * δ * Real.pi * 2 ^ a ≤ 4 * |h| * 2 ^ a := by rw [e4]; exact e5
      exact le_of_mul_le_mul_right e6 (by positivity)
    have key : |s + t| * (1 - Real.cos δ) ≤ |h| * Real.sin δ := by
      have e1 : |s + t| * (1 - Real.cos δ) ≤ L * (δ ^ 2 / 2) :=
        mul_le_mul (by rw [hL]; linarith) (by linarith) (by linarith) hLpos.le
      have e2 : L * (δ ^ 2 / 2) ≤ |h| * (2 / Real.pi * δ) := by
        have e7 : |h| * (2 / Real.pi * δ) = (4 * |h|) * (δ / (2 * Real.pi)) := by
          field_simp
          ring
        have e8 : L * (δ ^ 2 / 2) = (L * δ * Real.pi) * (δ / (2 * Real.pi)) := by
          field_simp
        rw [e7, e8]
        exact mul_le_mul_of_nonneg_right e3 (by positivity)
      calc |s + t| * (1 - Real.cos δ) ≤ L * (δ ^ 2 / 2) := e1
        _ ≤ |h| * (2 / Real.pi * δ) := e2
        _ ≤ |h| * Real.sin δ := mul_le_mul_of_nonneg_left hsin hpos.le
    rw [← sq_abs, ← sq_abs h]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    rw [abs_div, abs_mul, abs_of_pos hsinpos, abs_of_nonneg (by linarith : 0 ≤ 1 - Real.cos δ),
      div_le_iff₀ hsinpos]
    exact key

/-- The point of a Euclidean space attached to a word. -/
noncomputable def Pt {ι : Type} [Fintype ι] (lam : ℝ) (f : ι → ℂ × ℝ) :
    EuclideanSpace ℝ (Fin (Fintype.card (ι × Fin 3))) :=
  WithLp.toLp 2 fun m =>
    lam * (![(f ((Fintype.equivFin (ι × Fin 3)).symm m).1).1.re,
      (f ((Fintype.equivFin (ι × Fin 3)).symm m).1).1.im,
      (f ((Fintype.equivFin (ι × Fin 3)).symm m).1).2] : Fin 3 → ℝ)
        ((Fintype.equivFin (ι × Fin 3)).symm m).2

theorem dist_Pt {ι : Type} [Fintype ι] (lam : ℝ) (f f' : ι → ℂ × ℝ) :
    dist (Pt lam f) (Pt lam f') ^ 2 = lam ^ 2 * ∑ i, D2 (f i) (f' i) := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have e := Equiv.sum_comp (Fintype.equivFin (ι × Fin 3)).symm
    (fun q : ι × Fin 3 => (lam * (![(f q.1).1.re, (f q.1).1.im, (f q.1).2] : Fin 3 → ℝ) q.2 -
      lam * (![(f' q.1).1.re, (f' q.1).1.im, (f' q.1).2] : Fin 3 → ℝ) q.2) ^ 2)
  simp only [Pt, Real.dist_eq, sq_abs]
  rw [e, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_three]
  simp only [D2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  ring

end Geometry

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @Erdos174.erdos_174.variants.trapezoid := by
  intro s t h hh
  refine ⟨Set.toFinite _, fun k _ => ?_⟩
  obtain ⟨a, ζ, ha, hζ, hζa, hζ1, him, hg⟩ := exists_angle s t h hh
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ, g = (s + t) * (1 - ζ.re) / ζ.im := ⟨_, rfl⟩
  obtain ⟨xA, hxA⟩ : ∃ xA : ℝ, xA = (t - s * ζ.re) / ζ.im := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = Real.sqrt (h ^ 2 - g ^ 2) / 2 := ⟨_, rfl⟩
  rw [← hgdef] at hg
  have hw2 : g ^ 2 + 4 * w ^ 2 = h ^ 2 := by
    rw [hw, div_pow, Real.sq_sqrt (by linarith)]
    ring
  have hne : ζ.im ≠ 0 := him.ne'
  have hg1 : g * ζ.im = (s + t) * (1 - ζ.re) := by rw [hgdef]; field_simp
  have hx1 : xA * ζ.im = t - s * ζ.re := by rw [hxA]; field_simp
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : ℂ × ℝ, p₀ = ((⟨xA, s⟩ : ℂ), w) := ⟨_, rfl⟩
  obtain ⟨ι, hι, H⟩ := core a ha ζ hζ hζ1 hζa p₀ (Fin k)
  have hdpos : 0 < 2 * (dd a * dd a) := by
    have := dd_pos a
    positivity
  refine ⟨Fintype.card (ι × Fin 3), fun c => ?_⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = (Real.sqrt (2 * (dd a * dd a)))⁻¹ := ⟨_, rfl⟩
  have hlam2 : lam ^ 2 * (2 * (dd a * dd a)) = 1 := by
    rw [hlam, inv_pow, Real.sq_sqrt hdpos.le]
    exact inv_mul_cancel₀ hdpos.ne'
  obtain ⟨Ψ, hΨ, c1, c2, c3⟩ := H (fun f => c (Pt lam f))
  have m0 := orb_self (2 ^ a) p₀
  have m1 := (orb_cj (2 ^ a) p₀ p₀).2 m0
  have m2 := (orb_rot (2 ^ a) p₀ ζ hζ hζa p₀).2 m0
  have m3 := (orb_cj (2 ^ a) p₀ _).2 m2
  obtain ⟨emb, hemb⟩ : ∃ emb : EuclideanSpace ℝ (Fin 2) → ℂ × ℝ, ∀ v, emb v =
      ((⟨xA - g * (v 1 / h), v 0⟩ : ℂ), w - 2 * w * (v 1 / h)) := ⟨_, fun _ => rfl⟩
  have eA : emb !₂[s, 0] = p₀ := by
    rw [hemb, hp₀]
    simp
  have eB : emb !₂[-s, 0] = cj p₀ := by
    rw [hemb, hp₀, cj_apply]
    refine Prod.ext (Complex.ext ?_ ?_) ?_ <;> simp
  have hre : ζ.re * xA - ζ.im * s = xA - g := by
    have e : (ζ.re * xA - ζ.im * s - (xA - g)) * ζ.im = 0 := by
      linear_combination (ζ.re - 1) * hx1 + hg1 - s * hζ1
    have e' := (mul_eq_zero.1 e).resolve_right hne
    linarith
  have him' : ζ.re * s + ζ.im * xA = t := by linear_combination hx1
  have eC : emb !₂[t, h] = rot ζ hζ p₀ := by
    rw [hemb, hp₀, rot_apply]
    refine Prod.ext (Complex.ext ?_ ?_) ?_
    · simp only [Complex.mul_re]
      simp [hh]
      linarith [hre]
    · simp only [Complex.mul_im]
      simp
      linarith [him']
    · simp [hh]
      ring
  have eD : emb !₂[-t, h] = cj (rot ζ hζ p₀) := by
    rw [← eC, hemb, hemb, cj_apply]
    refine Prod.ext (Complex.ext ?_ ?_) ?_ <;> simp
  have hmem : ∀ v ∈ ({!₂[-s, 0], !₂[s, 0], !₂[-t, h], !₂[t, h]} :
      Set (EuclideanSpace ℝ (Fin 2))),
      emb v ∈ Orb (2 ^ a) p₀ ∧ c (Pt lam (Ψ (emb v))) = c (Pt lam (Ψ p₀)) := by
    rintro v (rfl | rfl | rfl | rfl)
    · rw [eB]
      exact ⟨m1, c1⟩
    · rw [eA]
      exact ⟨m0, rfl⟩
    · rw [eD]
      exact ⟨m3, c3⟩
    · rw [eC]
      exact ⟨m2, c2⟩
  have hD : ∀ v v' : EuclideanSpace ℝ (Fin 2), D2 (emb v) (emb v') = dist v v' ^ 2 := by
    intro v v'
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Fin.sum_univ_two, hemb, hemb]
    simp only [D2, Real.dist_eq, sq_abs]
    have e : (v 1 - v' 1) ^ 2 = h ^ 2 * (v 1 / h - v' 1 / h) ^ 2 := by
      field_simp
    rw [e, ← hw2]
    ring
  refine ⟨fun v => Pt lam (Ψ (emb v.1)), ?_, c (Pt lam (Ψ p₀)), fun v => (hmem v.1 v.2).2⟩
  rw [congruent_iff_dist_eq]
  intro v v'
  have e : dist (Pt lam (Ψ (emb v.1))) (Pt lam (Ψ (emb v'.1))) ^ 2 = dist v.1 v'.1 ^ 2 := by
    rw [dist_Pt, hΨ _ _ (hmem v.1 v.2).1 (hmem v'.1 v'.2).1, hD, ← mul_assoc, hlam2, one_mul]
  exact ((sq_eq_sq₀ dist_nonneg dist_nonneg).1 e).symm
