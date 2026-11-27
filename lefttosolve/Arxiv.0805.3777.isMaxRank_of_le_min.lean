import FormalConjectures.Arxiv.«0805.3777».TensorRank
import Mathlib

open Submodule Matrix

namespace OMA.Helpers

section Plumbing

open Holor

def idx3 {m n p : ℕ} (i : Fin m) (j : Fin n) (k : Fin p) : HolorIndex [m, n, p] :=
  ⟨[i.1, j.1, k.1], List.Forall₂.cons i.2 (List.Forall₂.cons j.2 (List.Forall₂.cons k.2 List.Forall₂.nil))⟩

/-- a 1-holor from a vector -/

def vecH {d : ℕ} (v : Fin d → ℂ) : Holor ℂ [d] :=
  fun t => if h : t.1.headI < d then v ⟨t.1.headI, h⟩ else 0

def oneH : Holor ℂ [] := fun _ => 1

def r1 {m n p : ℕ} (a : Fin m → ℂ) (b : Fin n → ℂ) (c : Fin p → ℂ) : Holor ℂ [m, n, p] :=
  Holor.mul (vecH a) (Holor.mul (vecH b) (Holor.mul (vecH c) oneH))

theorem r1_apply {m n p : ℕ} (a : Fin m → ℂ) (b : Fin n → ℂ) (c : Fin p → ℂ)
    (i : Fin m) (j : Fin n) (k : Fin p) :
    r1 a b c (idx3 i j k) = a i * (b j * c k) := by
  simp [r1, idx3, Holor.mul, HolorIndex.take, HolorIndex.drop, vecH, oneH]

theorem r1_rank {m n p : ℕ} (a : Fin m → ℂ) (b : Fin n → ℂ) (c : Fin p → ℂ) :
    CPRankMax1 (r1 a b c) :=
  CPRankMax1.cons _ _ (CPRankMax1.cons _ _ (CPRankMax1.cons _ _ (CPRankMax1.nil _)))

theorem holor3_ext {m n p : ℕ} (T T' : Holor ℂ [m, n, p])
    (h : ∀ i j k, T (idx3 i j k) = T' (idx3 i j k)) : T = T' := by
  funext t
  obtain ⟨is, his⟩ := t
  match is, his with
  | [i, j, k], his =>
    have hi : i < m := by
      cases his with | cons h1 h2 => exact h1
    have hj : j < n := by
      cases his with | cons h1 h2 => cases h2 with | cons h3 h4 => exact h3
    have hk : k < p := by
      cases his with | cons h1 h2 => cases h2 with | cons h3 h4 => cases h4 with | cons h5 h6 => exact h5
    exact h ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩

theorem sum_apply_holor {ds : List ℕ} {β : Type} (s : Finset β) (f : β → Holor ℂ ds)
    (t : HolorIndex ds) : (∑ x ∈ s, f x) t = ∑ x ∈ s, f x t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

theorem cprankMax_of_sum {m n p r : ℕ} (T : Holor ℂ [m, n, p])
    (a : Fin r → Fin m → ℂ) (b : Fin r → Fin n → ℂ) (c : Fin r → Fin p → ℂ)
    (h : ∀ i j k, T (idx3 i j k) = ∑ s, a s i * (b s j * c s k)) : CPRankMax r T := by
  have h1 : T = ∑ s : Fin r, r1 (a s) (b s) (c s) := by
    apply holor3_ext
    intro i j k
    rw [h, sum_apply_holor]
    simp [r1_apply]
  have h2 := Holor.cprankMax_sum (n := 1) (Finset.univ : Finset (Fin r))
    (fun s => r1 (a s) (b s) (c s)) (fun s _ => cprankMax_1 (r1_rank _ _ _))
  rw [h1]
  simpa using h2

def idx1 {d : ℕ} (i : Fin d) : HolorIndex [d] :=
  ⟨[i.1], List.Forall₂.cons i.2 List.Forall₂.nil⟩

theorem cprankMax1_inv {d : ℕ} {ds : List ℕ} (x : Holor ℂ (d :: ds)) (h : CPRankMax1 x) :
    ∃ (x₁ : Holor ℂ [d]) (y₁ : Holor ℂ ds), CPRankMax1 y₁ ∧ x = Holor.mul x₁ y₁ := by
  cases h with
  | cons x₁ y₁ h₁ => exact ⟨x₁, y₁, h₁, rfl⟩

theorem cprankMax_sum_inv {ds : List ℕ} {r : ℕ} {T : Holor ℂ ds} (h : CPRankMax r T) :
    ∃ f : Fin r → Holor ℂ ds, (∀ s, CPRankMax1 (f s)) ∧ T = ∑ s, f s := by
  induction h with
  | zero => exact ⟨fun _ => 0, fun s => s.elim0, by simp⟩
  | succ n x y hx hy ih =>
    obtain ⟨f, hf, hsum⟩ := ih
    refine ⟨Fin.cons x f, ?_, ?_⟩
    · intro s
      refine Fin.cases ?_ ?_ s
      · simpa using hx
      · intro i; simpa using hf i
    · rw [Fin.sum_univ_succ]; simp [hsum]

theorem r1_inv {m n p : ℕ} (x : Holor ℂ [m, n, p]) (h : CPRankMax1 x) :
    ∃ (a : Fin m → ℂ) (b : Fin n → ℂ) (c : Fin p → ℂ),
      ∀ i j k, x (idx3 i j k) = a i * (b j * c k) := by
  obtain ⟨x₁, y₁, h₁, rfl⟩ := cprankMax1_inv x h
  obtain ⟨x₂, y₂, h₂, rfl⟩ := cprankMax1_inv y₁ h₁
  obtain ⟨x₃, y₃, h₃, rfl⟩ := cprankMax1_inv y₂ h₂
  refine ⟨fun i => x₁ (idx1 i), fun j => x₂ (idx1 j),
    fun k => x₃ (idx1 k) * y₃ ⟨[], List.Forall₂.nil⟩, ?_⟩
  intro i j k
  simp [idx3, idx1, Holor.mul, HolorIndex.take, HolorIndex.drop]

theorem sum_of_cprankMax {m n p r : ℕ} (T : Holor ℂ [m, n, p]) (h : CPRankMax r T) :
    ∃ (a : Fin r → Fin m → ℂ) (b : Fin r → Fin n → ℂ) (c : Fin r → Fin p → ℂ),
      ∀ i j k, T (idx3 i j k) = ∑ s, a s i * (b s j * c s k) := by
  obtain ⟨f, hf, rfl⟩ := cprankMax_sum_inv h
  choose a b c habc using fun s => r1_inv (f s) (hf s)
  refine ⟨a, b, c, ?_⟩
  intro i j k
  rw [sum_apply_holor]
  exact Finset.sum_congr rfl (fun s _ => habc s i j k)

theorem cprank_le_of {ds : List ℕ} {r : ℕ} {T : Holor ℂ ds} (h : CPRankMax r T) : T.cprank ≤ r := by
  classical
  unfold Holor.cprank
  exact Nat.find_min' _ h

theorem cprankMax_cprank {ds : List ℕ} (T : Holor ℂ ds) : CPRankMax T.cprank T := by
  classical
  unfold Holor.cprank
  exact Nat.find_spec (p := fun n => CPRankMax n T) ⟨ds.prod, Holor.cprankMax_upper_bound T⟩

end Plumbing

theorem perp_pair (a b c d : ℂ) (h : a * c + b * d = 0) (hcd : c ≠ 0 ∨ d ≠ 0) :
    ∃ l : ℂ, a = l * d ∧ b = -(l * c) := by
  rcases hcd with hc | hd
  · refine ⟨-b / c, ?_, ?_⟩
    · field_simp; linear_combination h
    · field_simp
  · refine ⟨a / d, ?_, ?_⟩
    · field_simp
    · field_simp; linear_combination h

theorem claimP {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (A B D : Y →ₗ[ℂ] Z) (y₀ z : Y)
    (hind : ∀ s t : ℂ, s • A y₀ + t • B y₀ = 0 → s = 0 ∧ t = 0)
    (hD : ∀ y, ∃ p q : ℂ, D y = p • A y + q • B y)
    (hD0 : D y₀ = 0)
    (φ : Z →ₗ[ℂ] ℂ) (hφ1 : φ (A y₀) = 0) (hφ2 : φ (B y₀) = 0)
    (hφ : φ (A z) ≠ 0 ∨ φ (B z) ≠ 0) : D z = 0 := by
  obtain ⟨p, q, hpq⟩ := hD z
  have key : ∀ t : ℂ, t ≠ 0 → ∃ l : ℂ,
      p • A y₀ + q • B y₀ + l • ((φ (B z) • A y₀ - φ (A z) • B y₀)
        + t • (φ (B z) • A z - φ (A z) • B z)) = 0 := by
    intro t ht
    obtain ⟨pt, qt, h⟩ := hD (y₀ + t • z)
    have h1 : t • (p • A z + q • B z) = pt • (A y₀ + t • A z) + qt • (B y₀ + t • B z) := by
      have h0 : D (y₀ + t • z) = t • D z := by simp [hD0]
      rw [h0, hpq] at h
      simpa [map_add, map_smul] using h
    have h2 : (pt - p) * φ (A z) + (qt - q) * φ (B z) = 0 := by
      have h3 := congrArg φ h1
      simp only [map_add, map_smul, hφ1, hφ2, smul_eq_mul] at h3
      have h4 : t * ((pt - p) * φ (A z) + (qt - q) * φ (B z)) = 0 := by linear_combination -h3
      exact (mul_eq_zero.mp h4).resolve_left ht
    obtain ⟨l, hl1, hl2⟩ := perp_pair _ _ _ _ h2 hφ
    refine ⟨l, ?_⟩
    have hpt : pt = p + l * φ (B z) := by linear_combination hl1
    have hqt : qt = q - l * φ (A z) := by linear_combination hl2
    rw [hpt, hqt] at h1
    linear_combination (norm := module) (-1 : ℂ) • h1
  by_cases hf : p • A y₀ + q • B y₀ = 0
  · obtain ⟨hp, hq⟩ := hind p q hf
    rw [hpq, hp, hq]; simp
  · obtain ⟨l1, h1⟩ := key 1 one_ne_zero
    obtain ⟨l2, h2⟩ := key 2 two_ne_zero
    have hl1 : l1 ≠ 0 := by
      rintro rfl; apply hf; simpa using h1
    have hl2 : l2 ≠ 0 := by
      rintro rfl; apply hf; simpa using h2
    set f := p • A y₀ + q • B y₀ with hfdef
    set g := φ (B z) • A y₀ - φ (A z) • B y₀ with hgdef
    set h := φ (B z) • A z - φ (A z) • B z with hhdef
    have e1 : g + h = (-(1 / l1)) • f := by
      have h3 : l1 • (g + h) = -f := by linear_combination (norm := module) h1
      have h4 : (1 / l1) • (l1 • (g + h)) = g + h := by
        rw [smul_smul, one_div, inv_mul_cancel₀ hl1, one_smul]
      rw [← h4, h3]; module
    have e2 : g + (2 : ℂ) • h = (-(1 / l2)) • f := by
      have h3 : l2 • (g + (2 : ℂ) • h) = -f := by linear_combination (norm := module) h2
      have h4 : (1 / l2) • (l2 • (g + (2 : ℂ) • h)) = g + (2 : ℂ) • h := by
        rw [smul_smul, one_div, inv_mul_cancel₀ hl2, one_smul]
      rw [← h4, h3]; module
    have eh : h = (1 / l1 - 1 / l2) • f := by linear_combination (norm := module) e2 - e1
    have eg : g = (1 / l2 - 2 / l1) • f := by linear_combination (norm := module) (2 : ℂ) • e1 - e2
    set η := 1 / l1 - 1 / l2 with hη
    set γ := 1 / l2 - 2 / l1 with hγ
    have hγ0 : γ ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at eg
      have h5 := hind (φ (B z)) (-φ (A z)) (by rw [← eg, hgdef]; module)
      rcases hφ with ha | hb
      · exact ha (by simpa using h5.2)
      · exact hb h5.1
    by_cases hη0 : η = 0
    · rw [hη0, zero_smul] at eh
      have h5 : (φ (B z) - γ * p) • A y₀ + (-φ (A z) - γ * q) • B y₀ = 0 := by
        have h6 : g - γ • f = 0 := by rw [eg]; simp
        rw [hgdef, hfdef] at h6
        linear_combination (norm := module) h6
      obtain ⟨hb1, ha1⟩ := hind _ _ h5
      have h6 : γ • D z = 0 := by
        rw [hpq]
        have h8 : φ (B z) = γ * p := by linear_combination hb1
        have h7 : φ (A z) = -(γ * q) := by linear_combination -ha1
        rw [hhdef, h8, h7] at eh
        linear_combination (norm := module) eh
      rcases smul_eq_zero.mp h6 with h8 | h8
      · exact absurd h8 hγ0
      · exact h8
    · exfalso
      have ht : -γ / η ≠ 0 := div_ne_zero (neg_ne_zero.mpr hγ0) hη0
      obtain ⟨l3, h3⟩ := key (-γ / η) ht
      apply hf
      rw [eg, eh] at h3
      have h10 : (1 + l3 * (γ + (-γ / η) * η)) • f = 0 := by
        linear_combination (norm := module) h3
      have h11 : γ + (-γ / η) * η = 0 := by field_simp; ring
      rw [h11] at h10
      simpa using h10

theorem oneSided {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (A B C : Y →ₗ[ℂ] Z) (y₀ : Y)
    (hind : ∀ s t : ℂ, s • A y₀ + t • B y₀ = 0 → s = 0 ∧ t = 0)
    (hC : ∀ y, C y ∈ span ℂ {A y, B y}) :
    (∃ α β : ℂ, C = α • A + β • B) ∨
      (∀ z, A z ∈ span ℂ {A y₀, B y₀} ∧ B z ∈ span ℂ {A y₀, B y₀}) := by
  by_cases hdeg : ∀ z, A z ∈ span ℂ {A y₀, B y₀} ∧ B z ∈ span ℂ {A y₀, B y₀}
  · exact Or.inr hdeg
  · left
    obtain ⟨α, β, hαβ⟩ := mem_span_pair.mp (hC y₀)
    refine ⟨α, β, ?_⟩
    set D : Y →ₗ[ℂ] Z := C - (α • A + β • B) with hDdef
    have hD0 : D y₀ = 0 := by simp [hDdef, hαβ]
    have hD : ∀ y, ∃ p q : ℂ, D y = p • A y + q • B y := by
      intro y
      obtain ⟨p, q, hpq⟩ := mem_span_pair.mp (hC y)
      refine ⟨p - α, q - β, ?_⟩
      simp only [hDdef, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, ← hpq]
      module
    have key : ∀ z, ¬ (A z ∈ span ℂ {A y₀, B y₀} ∧ B z ∈ span ℂ {A y₀, B y₀}) → D z = 0 := by
      intro z hz
      have h1 : A y₀ ∈ span ℂ ({A y₀, B y₀} : Set Z) := subset_span (by simp)
      have h2 : B y₀ ∈ span ℂ ({A y₀, B y₀} : Set Z) := subset_span (by simp)
      rw [not_and_or] at hz
      rcases hz with hz | hz
      · obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_notMem hz
        exact claimP A B D y₀ z hind hD hD0 φ (hle h1) (hle h2) (Or.inl hφ)
      · obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_notMem hz
        exact claimP A B D y₀ z hind hD hD0 φ (hle h1) (hle h2) (Or.inr hφ)
    obtain ⟨z₀, hz₀⟩ := not_forall.mp hdeg
    have hDz : ∀ z, D z = 0 := by
      intro z
      by_cases hz : A z ∈ span ℂ {A y₀, B y₀} ∧ B z ∈ span ℂ {A y₀, B y₀}
      · have h3 : ¬ (A (z + z₀) ∈ span ℂ {A y₀, B y₀} ∧ B (z + z₀) ∈ span ℂ {A y₀, B y₀}) := by
          rintro ⟨h4, h5⟩
          apply hz₀
          constructor
          · have := Submodule.sub_mem _ h4 hz.1
            simpa [map_add] using this
          · have := Submodule.sub_mem _ h5 hz.2
            simpa [map_add] using this
        have h6 := key _ h3
        have h7 := key _ hz₀
        rw [map_add, h7, add_zero] at h6
        exact h6
      · exact key z hz
    have hD' : D = 0 := LinearMap.ext hDz
    rw [hDdef] at hD'
    exact sub_eq_zero.mp hD'

theorem lld {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (A B : Y →ₗ[ℂ] Z)
    (h : ∀ y, ∃ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) ∧ s • A y + t • B y = 0) :
    ∃ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) ∧ ∃ v : Z, ∀ y, ∃ c : ℂ, (s • A + t • B) y = c • v := by
  by_cases hA : ∀ y, A y = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, 0, fun y => ⟨0, by simp [hA y]⟩⟩
  · obtain ⟨y₀, hy₀⟩ := not_forall.mp hA
    obtain ⟨s₀, t₀, hst, hrel⟩ := h y₀
    have ht₀ : t₀ ≠ 0 := by
      intro ht
      rw [ht, zero_smul, add_zero] at hrel
      rcases smul_eq_zero.mp hrel with h1 | h1
      · rcases hst with h2 | h2
        · exact h2 h1
        · exact h2 ht
      · exact hy₀ h1
    set lam : ℂ := -s₀ / t₀ with hlam
    have hB0 : B y₀ = lam • A y₀ := by
      have h1 : t₀ • B y₀ = (-s₀) • A y₀ := by linear_combination (norm := module) hrel
      have h2 : B y₀ = (1 / t₀) • (t₀ • B y₀) := by
        rw [smul_smul, one_div, inv_mul_cancel₀ ht₀, one_smul]
      rw [h2, h1, smul_smul, hlam]; congr 1; field_simp
    refine ⟨-lam, 1, Or.inr one_ne_zero, A y₀, ?_⟩
    intro y
    have hw : ((-lam) • A + (1 : ℂ) • B) y = B y - lam • A y := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply]; module
    rw [hw]
    by_cases hw0 : B y - lam • A y = 0
    · exact ⟨0, by simp [hw0]⟩
    · have rel : ∀ k : ℂ, k ≠ 0 → ∃ c : ℂ, A y₀ + k • A y = c • (B y - lam • A y) := by
        intro k hk
        obtain ⟨s, t, hst', hr⟩ := h (y₀ + k • y)
        have h3 : (s + t * lam) • (A y₀ + k • A y) + (t * k) • (B y - lam • A y) = 0 := by
          rw [map_add, map_add, map_smul, map_smul, hB0] at hr
          linear_combination (norm := module) hr
        have hσ : s + t * lam ≠ 0 := by
          intro hσ
          rw [hσ, zero_smul, zero_add] at h3
          rcases smul_eq_zero.mp h3 with h4 | h4
          · have ht : t = 0 := by
              rcases mul_eq_zero.mp h4 with h5 | h5
              · exact h5
              · exact absurd h5 hk
            have hs : s = 0 := by rw [ht] at hσ; simpa using hσ
            rcases hst' with h6 | h6
            · exact h6 hs
            · exact h6 ht
          · exact hw0 h4
        refine ⟨-(t * k) / (s + t * lam), ?_⟩
        have h5 : (s + t * lam) • (A y₀ + k • A y) = (-(t * k)) • (B y - lam • A y) := by
          linear_combination (norm := module) h3
        have h6 : A y₀ + k • A y = (1 / (s + t * lam)) • ((s + t * lam) • (A y₀ + k • A y)) := by
          rw [smul_smul, one_div, inv_mul_cancel₀ hσ, one_smul]
        rw [h6, h5, smul_smul]; congr 1; field_simp
      obtain ⟨c1, hc1⟩ := rel 1 one_ne_zero
      obtain ⟨c2, hc2⟩ := rel 2 two_ne_zero
      have h7 : A y₀ = (2 * c1 - c2) • (B y - lam • A y) := by
        linear_combination (norm := module) (2 : ℂ) • hc1 - hc2
      have h8 : 2 * c1 - c2 ≠ 0 := by
        intro h9; rw [h9, zero_smul] at h7; exact hy₀ h7
      refine ⟨1 / (2 * c1 - c2), ?_⟩
      rw [h7, smul_smul, one_div, inv_mul_cancel₀ h8, one_smul]

def IsR1 {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) : Prop :=
  ∃ (u : Fin m → ℂ) (v : Fin n → ℂ), M = Matrix.vecMulVec u v

theorem mem_span_of_perp {m : ℕ} (a b c : Fin m → ℂ)
    (h : ∀ x : Fin m → ℂ, x ⬝ᵥ a = 0 → x ⬝ᵥ b = 0 → x ⬝ᵥ c = 0) :
    c ∈ span ℂ ({a, b} : Set (Fin m → ℂ)) := by
  by_contra hc
  obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_notMem hc
  have hx : ∀ v : Fin m → ℂ, φ v = (fun i => φ (fun j => if i = j then 1 else 0)) ⬝ᵥ v := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ φ v]
    simp [dotProduct, mul_comm]
  have ha : φ a = 0 := hle (subset_span (by simp))
  have hb : φ b = 0 := hle (subset_span (by simp))
  apply hφ
  rw [hx] at ha hb ⊢
  exact h _ ha hb

theorem r1_of_range {m n : ℕ} (N : Matrix (Fin m) (Fin n) ℂ) (v : Fin m → ℂ)
    (h : ∀ y, ∃ c : ℂ, N *ᵥ y = c • v) : IsR1 N := by
  choose c hc using fun j : Fin n => h (Pi.single j 1)
  refine ⟨v, c, ?_⟩
  ext i j
  have h1 := congrFun (hc j) i
  simp only [Matrix.mulVec_single_one, Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at h1
  rw [Matrix.vecMulVec_apply, h1, mul_comm]

theorem oneSidedMat {m n : ℕ} (A B C : Matrix (Fin m) (Fin n) ℂ)
    (hN : ∀ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) → ¬ IsR1 (s • A + t • B))
    (hC : ∀ x y, x ⬝ᵥ A *ᵥ y = 0 → x ⬝ᵥ B *ᵥ y = 0 → x ⬝ᵥ C *ᵥ y = 0) :
    (∃ α β : ℂ, C = α • A + β • B) ∨
    ∃ y₀, (∀ s t : ℂ, s • A *ᵥ y₀ + t • B *ᵥ y₀ = 0 → s = 0 ∧ t = 0) ∧
      ∀ z, A *ᵥ z ∈ span ℂ {A *ᵥ y₀, B *ᵥ y₀} ∧ B *ᵥ z ∈ span ℂ {A *ᵥ y₀, B *ᵥ y₀} := by
  have hy₀ : ∃ y₀, ∀ s t : ℂ, s • A *ᵥ y₀ + t • B *ᵥ y₀ = 0 → s = 0 ∧ t = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s, t, hst, v, hv⟩ := lld A.mulVecLin B.mulVecLin (fun y => by
      obtain ⟨s, t, h1, h2⟩ := hcon y
      refine ⟨s, t, ?_, by simpa using h1⟩
      by_cases hs : s = 0
      · exact Or.inr (h2 hs)
      · exact Or.inl hs)
    refine hN s t hst (r1_of_range _ v (fun y => ?_))
    obtain ⟨c, hc⟩ := hv y
    refine ⟨c, ?_⟩
    rw [← hc]
    simp [Matrix.add_mulVec, Matrix.smul_mulVec]
  obtain ⟨y₀, hy₀⟩ := hy₀
  rcases oneSided A.mulVecLin B.mulVecLin C.mulVecLin y₀ (by simpa using hy₀)
    (fun y => by
      simp only [Matrix.mulVecLin_apply]
      exact mem_span_of_perp _ _ _ (fun x => hC x y)) with ⟨α, β, h⟩ | h
  · left
    refine ⟨α, β, ?_⟩
    ext i j
    have h1 := congrFun (LinearMap.congr_fun h (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one] using h1
  · right
    exact ⟨y₀, hy₀, by simpa using h⟩

theorem eig2 (a₁ a₂ b₁ b₂ : ℂ) : ∃ μ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) ∧
    a₁ * s + b₁ * t = μ * s ∧ a₂ * s + b₂ * t = μ * t := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_eq_mul_self (discrim 1 (-(a₁ + b₂)) (a₁ * b₂ - a₂ * b₁))
  obtain ⟨μ, hμ⟩ := exists_quadratic_eq_zero (a := (1 : ℂ)) one_ne_zero ⟨r, hr⟩
  by_cases h1 : b₁ ≠ 0 ∨ μ - a₁ ≠ 0
  · exact ⟨μ, b₁, μ - a₁, h1, by ring, by linear_combination -hμ⟩
  · by_cases h2 : μ - b₂ ≠ 0 ∨ a₂ ≠ 0
    · exact ⟨μ, μ - b₂, a₂, h2, by linear_combination -hμ, by ring⟩
    · rw [not_or, not_not, not_not] at h1 h2
      refine ⟨μ, 1, 0, Or.inl one_ne_zero, ?_, ?_⟩
      · linear_combination -h1.2
      · linear_combination h2.2

theorem bil_transpose {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (x : Fin m → ℂ) (y : Fin n → ℂ) :
    y ⬝ᵥ Mᵀ *ᵥ x = x ⬝ᵥ M *ᵥ y := by
  rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]

theorem row_dot {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (y : Fin n → ℂ) :
    (Mᵀ *ᵥ Pi.single i 1) ⬝ᵥ y = (M *ᵥ y) i := by
  rw [Matrix.mulVec_single_one]
  simp [Matrix.mulVec, dotProduct]

theorem r3 {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) (y₀ : Fin n → ℂ)
    (hy : ∀ z, A *ᵥ z ∈ span ℂ {A *ᵥ y₀, B *ᵥ y₀} ∧ B *ᵥ z ∈ span ℂ {A *ᵥ y₀, B *ᵥ y₀})
    (x₀ : Fin m → ℂ)
    (hx : ∀ x, Aᵀ *ᵥ x ∈ span ℂ {Aᵀ *ᵥ x₀, Bᵀ *ᵥ x₀} ∧ Bᵀ *ᵥ x ∈ span ℂ {Aᵀ *ᵥ x₀, Bᵀ *ᵥ x₀}) :
    ∃ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) ∧ IsR1 (s • A + t • B) := by
  by_cases hcase : ∀ z, ∃ c : ℂ, A *ᵥ (z - c • y₀) = 0 ∧ B *ᵥ (z - c • y₀) = 0
  · refine ⟨1, 0, Or.inl one_ne_zero, r1_of_range _ (A *ᵥ y₀) (fun z => ?_)⟩
    obtain ⟨c, hc, -⟩ := hcase z
    refine ⟨c, ?_⟩
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_eq_zero] at hc
    simpa using hc
  · obtain ⟨z, hz⟩ := not_forall.mp hcase
    obtain ⟨a₁, a₂, ha⟩ := mem_span_pair.mp (hy z).1
    obtain ⟨b₁, b₂, hb⟩ := mem_span_pair.mp (hy z).2
    obtain ⟨μ, s, t, hst, he1, he2⟩ := eig2 a₁ a₂ b₁ b₂
    refine ⟨s, t, hst, ?_⟩
    set ys := z - μ • y₀ with hys
    have hNy : (s • A + t • B) *ᵥ ys = 0 := by
      rw [hys, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_sub,
        Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, ← ha, ← hb]
      have e1 : a₁ * s + b₁ * t - μ * s = 0 := by linear_combination he1
      have e2 : a₂ * s + b₂ * t - μ * t = 0 := by linear_combination he2
      have : s • (a₁ • A *ᵥ y₀ + a₂ • B *ᵥ y₀ - μ • A *ᵥ y₀) +
          t • (b₁ • A *ᵥ y₀ + b₂ • B *ᵥ y₀ - μ • B *ᵥ y₀)
          = (a₁ * s + b₁ * t - μ * s) • A *ᵥ y₀ + (a₂ * s + b₂ * t - μ * t) • B *ᵥ y₀ := by
        module
      rw [this, e1, e2]; simp
    have hnz : ¬ (A *ᵥ ys = 0 ∧ B *ᵥ ys = 0) := by
      intro h; exact hz ⟨μ, h⟩
    choose p q hpq using fun i : Fin m => mem_span_pair.mp (hx (Pi.single i 1)).1
    choose p' q' hpq' using fun i : Fin m => mem_span_pair.mp (hx (Pi.single i 1)).2
    set f₁ := Aᵀ *ᵥ x₀ with hf₁
    set f₂ := Bᵀ *ᵥ x₀ with hf₂
    have hA : ∀ i, (A *ᵥ ys) i = p i * (f₁ ⬝ᵥ ys) + q i * (f₂ ⬝ᵥ ys) := by
      intro i
      rw [← row_dot, ← hpq i]
      simp [add_dotProduct, smul_dotProduct]
    have hB : ∀ i, (B *ᵥ ys) i = p' i * (f₁ ⬝ᵥ ys) + q' i * (f₂ ⬝ᵥ ys) := by
      intro i
      rw [← row_dot, ← hpq' i]
      simp [add_dotProduct, smul_dotProduct]
    have hφ : f₁ ⬝ᵥ ys ≠ 0 ∨ f₂ ⬝ᵥ ys ≠ 0 := by
      by_contra hcon
      rw [not_or, not_not, not_not] at hcon
      apply hnz
      constructor
      · funext i; rw [hA i, hcon.1, hcon.2]; simp
      · funext i; rw [hB i, hcon.1, hcon.2]; simp
    have hrow : ∀ i, (s * p i + t * p' i) * (f₁ ⬝ᵥ ys) + (s * q i + t * q' i) * (f₂ ⬝ᵥ ys) = 0 := by
      intro i
      have h1 := congrFun hNy i
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, hA i, hB i] at h1
      linear_combination h1
    choose l hl1 hl2 using fun i => perp_pair _ _ _ _ (hrow i) hφ
    refine ⟨l, (f₂ ⬝ᵥ ys) • f₁ - (f₁ ⬝ᵥ ys) • f₂, ?_⟩
    ext i j
    have h1 := congrFun (hpq i) j
    have h2 := congrFun (hpq' i) j
    simp only [Matrix.mulVec_single_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.col_apply, Matrix.transpose_apply] at h1 h2
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply,
      Pi.sub_apply, Pi.smul_apply, ← h1, ← h2]
    linear_combination (f₁ j) * hl1 i + (f₂ j) * hl2 i

theorem refl_r1free {m n : ℕ} (A B C : Matrix (Fin m) (Fin n) ℂ)
    (hN : ∀ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) → ¬ IsR1 (s • A + t • B))
    (hC : ∀ x y, x ⬝ᵥ A *ᵥ y = 0 → x ⬝ᵥ B *ᵥ y = 0 → x ⬝ᵥ C *ᵥ y = 0) :
    ∃ α β : ℂ, C = α • A + β • B := by
  rcases oneSidedMat A B C hN hC with h | ⟨y₀, -, hy⟩
  · exact h
  · have hNT : ∀ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) → ¬ IsR1 (s • Aᵀ + t • Bᵀ) := by
      rintro s t hst ⟨u, v, huv⟩
      refine hN s t hst ⟨v, u, ?_⟩
      ext i j
      have h1 := congrFun (congrFun huv j) i
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply,
        Matrix.vecMulVec_apply] at h1
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply]
      rw [h1, mul_comm]
    have hCT : ∀ y x, y ⬝ᵥ Aᵀ *ᵥ x = 0 → y ⬝ᵥ Bᵀ *ᵥ x = 0 → y ⬝ᵥ Cᵀ *ᵥ x = 0 := by
      intro y x h1 h2
      rw [bil_transpose] at h1 h2 ⊢
      exact hC x y h1 h2
    rcases oneSidedMat Aᵀ Bᵀ Cᵀ hNT hCT with ⟨α, β, h⟩ | ⟨x₀, -, hx⟩
    · refine ⟨α, β, ?_⟩
      have h1 := congrArg Matrix.transpose h
      simpa using h1
    · exfalso
      obtain ⟨s, t, hst, hr⟩ := r3 A B y₀ hy x₀ (by simpa using hx)
      exact hN s t hst hr

def pairB (m n : ℕ) : Matrix (Fin m) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin n) ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun A X => ∑ i, ∑ j, A i j * X i j)
    (by intros; simp [add_mul, Finset.sum_add_distrib])
    (by intros; simp [Finset.mul_sum, _root_.mul_assoc])
    (by intros; simp [mul_add, Finset.sum_add_distrib])
    (by intros; simp [Finset.mul_sum, mul_left_comm])

theorem pairB_apply {m n : ℕ} (A X : Matrix (Fin m) (Fin n) ℂ) :
    pairB m n A X = ∑ i, ∑ j, A i j * X i j := rfl

theorem pairB_vecMulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (x : Fin m → ℂ) (y : Fin n → ℂ) :
    pairB m n A (vecMulVec x y) = x ⬝ᵥ A *ᵥ y := by
  simp only [pairB_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

theorem pairB_single {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    pairB m n A (Matrix.single i j 1) = A i j := by
  rw [pairB_apply]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb.symm]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero (fun j' _ => ?_)
    simp [hb.symm]
  · simp

theorem dual_repr {m n : ℕ} (f : Module.Dual ℂ (Matrix (Fin m) (Fin n) ℂ)) :
    ∃ C : Matrix (Fin m) (Fin n) ℂ, f = pairB m n C := by
  refine ⟨Matrix.of (fun i j => f (Matrix.single i j 1)), ?_⟩
  refine (Matrix.stdBasis ℂ (Fin m) (Fin n)).ext (fun ij => ?_)
  obtain ⟨i, j⟩ := ij
  rw [Matrix.stdBasis_eq_single, pairB_single]
  rfl

theorem pairB_injective (m n : ℕ) : Function.Injective (pairB m n) := by
  intro A B h
  ext i j
  have h1 := LinearMap.congr_fun h (Matrix.single i j 1)
  rwa [pairB_single, pairB_single] at h1

theorem up_general {m n p : ℕ} (S : Fin p → Matrix (Fin m) (Fin n) ℂ)
    (P : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ))
    (horth : ∀ A ∈ P, ∀ k, pairB m n A (S k) = 0)
    (hrefl : ∀ C : Matrix (Fin m) (Fin n) ℂ,
      (∀ x y, (∀ A ∈ P, x ⬝ᵥ A *ᵥ y = 0) → x ⬝ᵥ C *ᵥ y = 0) → C ∈ P) :
    ∃ r : ℕ, r + Module.finrank ℂ P ≤ m * n ∧
      ∃ (xs : Fin r → Fin m → ℂ) (ys : Fin r → Fin n → ℂ) (cs : Fin r → Fin p → ℂ),
        ∀ k, S k = ∑ s, cs s k • vecMulVec (xs s) (ys s) := by
  set gens : Set (Matrix (Fin m) (Fin n) ℂ) :=
    {X | ∃ x y, X = vecMulVec x y ∧ ∀ A ∈ P, x ⬝ᵥ A *ᵥ y = 0} with hgens
  obtain ⟨g, hg, hgspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq ℂ gens
  refine ⟨Module.finrank ℂ (span ℂ gens), ?_, ?_⟩
  · have h1 : P.map (pairB m n) ≤ (span ℂ gens).dualAnnihilator := by
      rintro f ⟨A, hA, rfl⟩
      rw [Submodule.mem_dualAnnihilator]
      intro w hw
      have h2 : span ℂ gens ≤ LinearMap.ker (pairB m n A) := by
        rw [Submodule.span_le]
        rintro X ⟨x, y, rfl, hxy⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker]
        rw [pairB_vecMulVec]
        exact hxy A hA
      exact h2 hw
    have h3 := Submodule.finrank_mono h1
    have h4 : Module.finrank ℂ (P.map (pairB m n)) = Module.finrank ℂ P :=
      (Submodule.equivMapOfInjective _ (pairB_injective m n) P).finrank_eq.symm
    have h5 := Subspace.finrank_add_finrank_dualAnnihilator_eq (span ℂ gens)
    have h6 : Module.finrank ℂ (Matrix (Fin m) (Fin n) ℂ) = m * n := by
      simp [Module.finrank_matrix]
    rw [h4] at h3
    exact (Nat.add_le_add_left h3 _).trans (le_of_eq (h5.trans h6))
  · have hS : ∀ k, S k ∈ span ℂ gens := by
      intro k
      rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
      intro f hf
      obtain ⟨C, rfl⟩ := dual_repr f
      have hC : C ∈ P := by
        apply hrefl
        intro x y hxy
        rw [← pairB_vecMulVec]
        rw [Submodule.mem_dualAnnihilator] at hf
        exact hf _ (subset_span ⟨x, y, rfl, hxy⟩)
      exact horth C hC k
    choose xs ys hxy using hg
    rw [← hgspan] at hS
    choose cs hcs using fun k => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hS k)
    refine ⟨xs, ys, fun s k => cs k s, fun k => ?_⟩
    rw [← hcs k]
    exact Finset.sum_congr rfl (fun s _ => by rw [(hxy s).1])

theorem bil4 {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (i i₀ : Fin m) (j j₀ : Fin n) (a b : ℂ) :
    (Pi.single i 1 + a • Pi.single i₀ 1) ⬝ᵥ M *ᵥ (Pi.single j 1 + b • Pi.single j₀ 1)
      = M i j + b * M i j₀ + a * M i₀ j + a * b * M i₀ j₀ := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, smul_dotProduct,
    dotProduct_add, dotProduct_smul, Matrix.mulVec_single_one, single_one_dotProduct,
    Matrix.col_apply, smul_eq_mul]
  ring

theorem refl0 {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℂ) (h : ∀ x y, x ⬝ᵥ C *ᵥ y = 0) : C = 0 := by
  ext i j
  have h1 := h (Pi.single i 1 + (0 : ℂ) • Pi.single i 1) (Pi.single j 1 + (0 : ℂ) • Pi.single j 1)
  rw [bil4] at h1
  simpa using h1

theorem refl1 {m n : ℕ} (A C : Matrix (Fin m) (Fin n) ℂ) (hA : A ≠ 0)
    (hC : ∀ x y, x ⬝ᵥ A *ᵥ y = 0 → x ⬝ᵥ C *ᵥ y = 0) : ∃ α : ℂ, C = α • A := by
  obtain ⟨i₀, j₀, h₀⟩ : ∃ i₀ j₀, A i₀ j₀ ≠ 0 := by
    by_contra hcon
    apply hA
    ext i j
    by_contra hij
    exact hcon ⟨i, j, hij⟩
  refine ⟨C i₀ j₀ / A i₀ j₀, ?_⟩
  set α := C i₀ j₀ / A i₀ j₀ with hα
  have hD : ∀ (i : Fin m) (j : Fin n) (a b : ℂ),
      A i j + b * A i j₀ + a * A i₀ j + a * b * A i₀ j₀ = 0 →
      C i j + b * C i j₀ + a * C i₀ j + a * b * C i₀ j₀ = 0 := by
    intro i j a b h
    have h1 := hC (Pi.single i 1 + a • Pi.single i₀ 1) (Pi.single j 1 + b • Pi.single j₀ 1)
    rw [bil4, bil4] at h1
    exact h1 h
  have h00 : C i₀ j₀ = α * A i₀ j₀ := by rw [hα]; field_simp
  have hcol : ∀ i, C i j₀ = α * A i j₀ := by
    intro i
    have h1 := hD i j₀ (-(A i j₀ / A i₀ j₀)) 0 (by field_simp; ring)
    have h2 : C i j₀ = (A i j₀ / A i₀ j₀) * C i₀ j₀ := by linear_combination h1
    rw [h2, h00]; field_simp
  have hrow : ∀ j, C i₀ j = α * A i₀ j := by
    intro j
    have h1 := hD i₀ j 0 (-(A i₀ j / A i₀ j₀)) (by field_simp; ring)
    have h2 : C i₀ j = (A i₀ j / A i₀ j₀) * C i₀ j₀ := by linear_combination h1
    rw [h2, h00]; field_simp
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  have h1 := hD i j (1 - A i j₀ / A i₀ j₀) (-(A i j + (1 - A i j₀ / A i₀ j₀) * A i₀ j) / A i₀ j₀)
    (by field_simp; ring)
  rw [hcol i, hrow j, h00] at h1
  have h3 : A i j + (-(A i j + (1 - A i j₀ / A i₀ j₀) * A i₀ j) / A i₀ j₀) * A i j₀
      + (1 - A i j₀ / A i₀ j₀) * A i₀ j
      + (1 - A i j₀ / A i₀ j₀) * (-(A i j + (1 - A i j₀ / A i₀ j₀) * A i₀ j) / A i₀ j₀) * A i₀ j₀
      = 0 := by field_simp; ring
  linear_combination h1 - α * h3

theorem ker_lemma {n : ℕ} (v l : Fin n → ℂ) (h : ∀ y : Fin n → ℂ, v ⬝ᵥ y = 0 → l ⬝ᵥ y = 0) :
    ∃ α : ℂ, l = α • v := by
  by_cases hv : ∀ j, v j = 0
  · refine ⟨0, ?_⟩
    funext j
    have h1 := h (Pi.single j 1) (by simp [hv j])
    simpa using h1
  · obtain ⟨j₀, hj₀⟩ := not_forall.mp hv
    refine ⟨l j₀ / v j₀, ?_⟩
    funext j
    have h1 := h (Pi.single j 1 - (v j / v j₀) • Pi.single j₀ 1) (by
      simp only [dotProduct_sub, dotProduct_smul, dotProduct_single_one, smul_eq_mul]
      field_simp; ring)
    simp only [dotProduct_sub, dotProduct_smul, dotProduct_single_one, smul_eq_mul] at h1
    simp only [Pi.smul_apply, smul_eq_mul]
    have h2 : l j = v j / v j₀ * l j₀ := by linear_combination h1
    rw [h2]; ring

theorem vecMulVec_mulVec' {m n : ℕ} (u : Fin m → ℂ) (v y : Fin n → ℂ) :
    vecMulVec u v *ᵥ y = (v ⬝ᵥ y) • u := by
  funext i
  simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem refl_r1pair {m n : ℕ} (u₁ u₂ : Fin m → ℂ) (v₁ v₂ : Fin n → ℂ)
    (hu : ∀ s t : ℂ, s • u₁ + t • u₂ = 0 → s = 0 ∧ t = 0)
    (C : Matrix (Fin m) (Fin n) ℂ)
    (hC : ∀ x y, x ⬝ᵥ vecMulVec u₁ v₁ *ᵥ y = 0 → x ⬝ᵥ vecMulVec u₂ v₂ *ᵥ y = 0 →
      x ⬝ᵥ C *ᵥ y = 0) :
    ∃ α β : ℂ, C = α • vecMulVec u₁ v₁ + β • vecMulVec u₂ v₂ := by
  have hmem : ∀ y, ∃ p q : ℂ, C *ᵥ y = (p * (v₁ ⬝ᵥ y)) • u₁ + (q * (v₂ ⬝ᵥ y)) • u₂ := by
    intro y
    have h1 := mem_span_of_perp _ _ _ (fun x => hC x y)
    obtain ⟨p, q, hpq⟩ := mem_span_pair.mp h1
    refine ⟨p, q, ?_⟩
    rw [← hpq, vecMulVec_mulVec', vecMulVec_mulVec', smul_smul, smul_smul]
  choose l₁ l₂ hl using fun j : Fin n => hmem (Pi.single j 1)
  have hcol : ∀ i j, C i j = (l₁ j * v₁ j) * u₁ i + (l₂ j * v₂ j) * u₂ i := by
    intro i j
    have h1 := congrFun (hl j) i
    simpa [Matrix.mulVec_single_one, dotProduct_single_one] using h1
  have hCy : ∀ y : Fin n → ℂ, C *ᵥ y =
      ((fun j => l₁ j * v₁ j) ⬝ᵥ y) • u₁ + ((fun j => l₂ j * v₂ j) ⬝ᵥ y) • u₂ := by
    intro y
    funext i
    simp only [Matrix.mulVec, dotProduct, hcol, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hk₁ : ∀ y : Fin n → ℂ, v₁ ⬝ᵥ y = 0 → (fun j => l₁ j * v₁ j) ⬝ᵥ y = 0 := by
    intro y hy
    obtain ⟨p, q, hpq⟩ := hmem y
    rw [hCy y, hy] at hpq
    have h2 := hu ((fun j => l₁ j * v₁ j) ⬝ᵥ y) ((fun j => l₂ j * v₂ j) ⬝ᵥ y - q * (v₂ ⬝ᵥ y)) (by
      linear_combination (norm := module) hpq)
    exact h2.1
  have hk₂ : ∀ y : Fin n → ℂ, v₂ ⬝ᵥ y = 0 → (fun j => l₂ j * v₂ j) ⬝ᵥ y = 0 := by
    intro y hy
    obtain ⟨p, q, hpq⟩ := hmem y
    rw [hCy y, hy] at hpq
    have h2 := hu ((fun j => l₁ j * v₁ j) ⬝ᵥ y - p * (v₁ ⬝ᵥ y)) ((fun j => l₂ j * v₂ j) ⬝ᵥ y) (by
      linear_combination (norm := module) hpq)
    exact h2.2
  obtain ⟨α, hα⟩ := ker_lemma _ _ hk₁
  obtain ⟨β, hβ⟩ := ker_lemma _ _ hk₂
  refine ⟨α, β, ?_⟩
  ext i j
  have h1 := congrFun hα j
  have h2 := congrFun hβ j
  simp only [Pi.smul_apply, smul_eq_mul] at h1 h2
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply]
  rw [hcol, h1, h2]; ring

theorem transpose_vecMulVec' {m n : ℕ} (u : Fin m → ℂ) (v : Fin n → ℂ) :
    (vecMulVec u v)ᵀ = vecMulVec v u := by
  ext i j
  simp [vecMulVec_apply, mul_comm]

theorem refl_r1pair' {m n : ℕ} (u₁ u₂ : Fin m → ℂ) (v₁ v₂ : Fin n → ℂ)
    (hv : ∀ s t : ℂ, s • v₁ + t • v₂ = 0 → s = 0 ∧ t = 0)
    (C : Matrix (Fin m) (Fin n) ℂ)
    (hC : ∀ x y, x ⬝ᵥ vecMulVec u₁ v₁ *ᵥ y = 0 → x ⬝ᵥ vecMulVec u₂ v₂ *ᵥ y = 0 →
      x ⬝ᵥ C *ᵥ y = 0) :
    ∃ α β : ℂ, C = α • vecMulVec u₁ v₁ + β • vecMulVec u₂ v₂ := by
  obtain ⟨α, β, h⟩ := refl_r1pair v₁ v₂ u₁ u₂ hv Cᵀ (by
    intro y x h1 h2
    rw [← transpose_vecMulVec' u₁ v₁, bil_transpose] at h1
    rw [← transpose_vecMulVec' u₂ v₂, bil_transpose] at h2
    rw [bil_transpose]
    exact hC x y h1 h2)
  refine ⟨α, β, ?_⟩
  have h1 := congrArg Matrix.transpose h
  simpa [transpose_vecMulVec'] using h1

theorem r1pair_cases {m n : ℕ} (u₁ u₂ : Fin m → ℂ) (v₁ v₂ : Fin n → ℂ)
    (h : ∀ s t : ℂ, s • vecMulVec u₁ v₁ + t • vecMulVec u₂ v₂ = 0 → s = 0 ∧ t = 0) :
    (∀ s t : ℂ, s • u₁ + t • u₂ = 0 → s = 0 ∧ t = 0) ∨
      (∀ s t : ℂ, s • v₁ + t • v₂ = 0 → s = 0 ∧ t = 0) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [not_forall] at h1 h2
  obtain ⟨s, h1⟩ := h1
  obtain ⟨s', h2⟩ := h2
  rw [not_forall] at h1 h2
  obtain ⟨t, h1⟩ := h1
  obtain ⟨t', h2⟩ := h2
  rw [Classical.not_imp] at h1 h2
  obtain ⟨hst, hne⟩ := h1
  obtain ⟨hst', hne'⟩ := h2
  have hrel : (s * s') • vecMulVec u₁ v₁ + (-(t * t')) • vecMulVec u₂ v₂ = 0 := by
    ext i j
    have e1 := congrFun hst i
    have e2 := congrFun hst' j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply,
      Matrix.zero_apply]
    have e3 : s * u₁ i = -(t * u₂ i) := by linear_combination e1
    have e4 : s' * v₁ j = -(t' * v₂ j) := by linear_combination e2
    linear_combination (s' * v₁ j) * e3 - (t * u₂ i) * e4
  obtain ⟨hss, htt⟩ := h _ _ hrel
  have hR2 : vecMulVec u₂ v₂ = 0 := by
    rcases mul_eq_zero.mp hss with hs | hs'
    · have ht : t ≠ 0 := fun ht => hne ⟨hs, ht⟩
      have hu₂ : u₂ = 0 := by
        rw [hs, zero_smul, zero_add] at hst
        exact (smul_eq_zero.mp hst).resolve_left ht
      ext i j; simp [vecMulVec_apply, hu₂]
    · have ht : t' ≠ 0 := fun ht => hne' ⟨hs', ht⟩
      have hv₂ : v₂ = 0 := by
        rw [hs', zero_smul, zero_add] at hst'
        exact (smul_eq_zero.mp hst').resolve_left ht
      ext i j; simp [vecMulVec_apply, hv₂]
  have h3 := h 0 1 (by rw [hR2]; simp)
  exact one_ne_zero h3.2

theorem dich {m n : ℕ} (L : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ))
    (hL : 3 ≤ Module.finrank ℂ L) :
    ∃ B₁ ∈ L, ∃ B₂ ∈ L, (∀ s t : ℂ, s • B₁ + t • B₂ = 0 → s = 0 ∧ t = 0) ∧
      ((∀ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) → ¬ IsR1 (s • B₁ + t • B₂)) ∨ (IsR1 B₁ ∧ IsR1 B₂)) := by
  by_cases h : ∃ R ∈ L, R ≠ 0 ∧ IsR1 R
  · obtain ⟨R, hRL, hR0, hR1⟩ := h
    have hv : LinearIndependent ℂ (fun _ : Fin 1 => (⟨R, hRL⟩ : L)) := by
      rw [linearIndependent_unique_iff]
      intro h0
      exact hR0 (congrArg Subtype.val h0)
    obtain ⟨x₁, h1⟩ := exists_linearIndependent_cons_of_lt_finrank hv (by omega)
    obtain ⟨x₂, h2⟩ := exists_linearIndependent_cons_of_lt_finrank h1 (by omega)
    have key : ∀ a b c : ℂ, a • (x₂ : Matrix (Fin m) (Fin n) ℂ) + b • (x₁ : Matrix (Fin m) (Fin n) ℂ)
        + c • R = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
      intro a b c habc
      have h3 := Fintype.linearIndependent_iff.mp h2 (Fin.cons a (Fin.cons b (fun _ => c))) (by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
        apply Subtype.ext
        simp only [Fin.cons_zero, Fin.cons_succ]
        simpa [add_assoc] using habc)
      have h30 := h3 0
      have h31 := h3 (Fin.succ 0)
      have h32 := h3 (Fin.succ (Fin.succ 0))
      simp only [Fin.cons_zero, Fin.cons_succ] at h30 h31 h32
      exact ⟨h30, h31, h32⟩
    by_cases h3 : ∃ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) ∧
        IsR1 (s • (x₁ : Matrix (Fin m) (Fin n) ℂ) + t • (x₂ : Matrix (Fin m) (Fin n) ℂ))
    · obtain ⟨s, t, hst, hr⟩ := h3
      refine ⟨R, hRL, s • (x₁ : Matrix (Fin m) (Fin n) ℂ) + t • (x₂ : Matrix (Fin m) (Fin n) ℂ),
        L.add_mem (L.smul_mem _ x₁.2) (L.smul_mem _ x₂.2), ?_, Or.inr ⟨hR1, hr⟩⟩
      intro a b hab
      obtain ⟨h4, h5, h6⟩ := key (b * t) (b * s) a (by rw [← hab]; module)
      refine ⟨h6, ?_⟩
      rcases hst with hs | ht
      · exact (mul_eq_zero.mp h5).resolve_right hs
      · exact (mul_eq_zero.mp h4).resolve_right ht
    · refine ⟨x₁, x₁.2, x₂, x₂.2, ?_, Or.inl (fun s t hst hr => h3 ⟨s, t, hst, hr⟩)⟩
      intro a b hab
      obtain ⟨h4, h5, -⟩ := key b a 0 (by rw [← hab]; module)
      exact ⟨h5, h4⟩
  · obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := ℂ) (M := L) (n := 2) (by omega)
    have key : ∀ a b : ℂ, a • (f 0 : Matrix (Fin m) (Fin n) ℂ) + b • (f 1 : Matrix (Fin m) (Fin n) ℂ)
        = 0 → a = 0 ∧ b = 0 := by
      intro a b hab
      have h3 := Fintype.linearIndependent_iff.mp hf ![a, b] (by
        apply Subtype.ext
        simp only [Fin.sum_univ_two]
        simpa using hab)
      exact ⟨by simpa using h3 0, by simpa using h3 1⟩
    refine ⟨f 0, (f 0).2, f 1, (f 1).2, key, Or.inl ?_⟩
    intro s t hst hr
    apply h
    refine ⟨_, L.add_mem (L.smul_mem _ (f 0).2) (L.smul_mem _ (f 1).2), ?_, hr⟩
    intro h0
    obtain ⟨h1, h2⟩ := key s t h0
    rcases hst with hs | ht
    · exact hs h1
    · exact ht h2

def slice {m n p : ℕ} (T : Holor ℂ [m, n, p]) (k : Fin p) : Matrix (Fin m) (Fin n) ℂ :=
  Matrix.of fun i j => T (idx3 i j k)

theorem upper_of_P {m n p : ℕ} (T : Holor ℂ [m, n, p])
    (P : Submodule ℂ (Matrix (Fin m) (Fin n) ℂ))
    (horth : ∀ A ∈ P, ∀ k, pairB m n A (slice T k) = 0)
    (hrefl : ∀ C : Matrix (Fin m) (Fin n) ℂ,
      (∀ x y, (∀ A ∈ P, x ⬝ᵥ A *ᵥ y = 0) → x ⬝ᵥ C *ᵥ y = 0) → C ∈ P) :
    T.cprank + Module.finrank ℂ P ≤ m * n := by
  obtain ⟨r, hr, xs, ys, cs, h⟩ := up_general (slice T) P horth hrefl
  have h1 : Holor.CPRankMax r T := cprankMax_of_sum T xs ys cs (by
    intro i j k
    have h2 := congrFun (congrFun (h k) i) j
    simp only [slice, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply,
      smul_eq_mul] at h2
    rw [h2]
    exact Finset.sum_congr rfl (fun s _ => by ring))
  have h3 := cprank_le_of h1
  omega

def orthL {m n p : ℕ} (S : Fin p → Matrix (Fin m) (Fin n) ℂ) :
    Submodule ℂ (Matrix (Fin m) (Fin n) ℂ) :=
  LinearMap.ker (LinearMap.pi (fun k => (pairB m n).flip (S k)))

theorem mem_orthL {m n p : ℕ} (S : Fin p → Matrix (Fin m) (Fin n) ℂ)
    (A : Matrix (Fin m) (Fin n) ℂ) : A ∈ orthL S ↔ ∀ k, pairB m n A (S k) = 0 := by
  simp [orthL, LinearMap.mem_ker, funext_iff]

theorem finrank_orthL {m n p : ℕ} (S : Fin p → Matrix (Fin m) (Fin n) ℂ) :
    m * n ≤ Module.finrank ℂ (orthL S) + p := by
  have h1 := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.pi (fun k => (pairB m n).flip (S k)))
  have h2 : Module.finrank ℂ (LinearMap.range (LinearMap.pi (fun k => (pairB m n).flip (S k))))
      ≤ p := by
    refine (Submodule.finrank_le _).trans ?_
    simp
  have h3 : Module.finrank ℂ (Matrix (Fin m) (Fin n) ℂ) = m * n := by
    simp [Module.finrank_matrix]
  unfold orthL
  omega

theorem bil_smul {m n : ℕ} (c : ℂ) (A : Matrix (Fin m) (Fin n) ℂ) (x : Fin m → ℂ)
    (y : Fin n → ℂ) : x ⬝ᵥ (c • A) *ᵥ y = c * (x ⬝ᵥ A *ᵥ y) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem bil_add {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) (x : Fin m → ℂ)
    (y : Fin n → ℂ) : x ⬝ᵥ (A + B) *ᵥ y = x ⬝ᵥ A *ᵥ y + x ⬝ᵥ B *ᵥ y := by
  rw [Matrix.add_mulVec, dotProduct_add]

theorem upper0 {m n p : ℕ} (T : Holor ℂ [m, n, p]) : T.cprank ≤ m * n := by
  have h := upper_of_P T ⊥ (by
      intro A hA k
      rw [(Submodule.mem_bot ℂ).mp hA]
      simp)
    (by
      intro C hC
      rw [Submodule.mem_bot]
      refine refl0 C (fun x y => hC x y ?_)
      intro A hA
      rw [(Submodule.mem_bot ℂ).mp hA]
      simp)
  omega

theorem upper1 {m n p : ℕ} (T : Holor ℂ [m, n, p]) (hp : p + 1 ≤ m * n) :
    T.cprank ≤ m * n - 1 := by
  have h1 := finrank_orthL (slice T)
  have h2 : 0 < Module.finrank ℂ (orthL (slice T)) := by omega
  obtain ⟨A, hA0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h2
  have hA := (mem_orthL _ _).mp A.2
  have hA0' : (A : Matrix (Fin m) (Fin n) ℂ) ≠ 0 := by
    intro h0
    exact hA0 (Subtype.ext h0)
  have h := upper_of_P T (ℂ ∙ (A : Matrix (Fin m) (Fin n) ℂ)) (by
      intro A' hA' k
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hA'
      simp [hA k])
    (by
      intro C hC
      obtain ⟨α, rfl⟩ := refl1 (A : Matrix (Fin m) (Fin n) ℂ) C hA0' (fun x y hxy => hC x y (by
        intro A' hA'
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hA'
        rw [bil_smul, hxy]
        simp))
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  rw [finrank_span_singleton hA0'] at h
  omega

theorem upper2 {m n p : ℕ} (T : Holor ℂ [m, n, p]) (hp : p + 3 ≤ m * n) :
    T.cprank ≤ m * n - 2 := by
  have h1 := finrank_orthL (slice T)
  obtain ⟨B₁, hB₁, B₂, hB₂, hind, halt⟩ := dich (orthL (slice T)) (by omega)
  have hfr : Module.finrank ℂ (span ℂ ({B₁, B₂} : Set (Matrix (Fin m) (Fin n) ℂ))) = 2 := by
    have hli : LinearIndependent ℂ ![B₁, B₂] := LinearIndependent.pair_iff.mpr hind
    have h3 := finrank_span_eq_card hli
    rw [Matrix.range_cons_cons_empty] at h3
    simpa using h3
  have h := upper_of_P T (span ℂ {B₁, B₂}) (by
      intro A hA k
      obtain ⟨a, b, rfl⟩ := mem_span_pair.mp hA
      simp [(mem_orthL _ _).mp hB₁ k, (mem_orthL _ _).mp hB₂ k])
    (by
      intro C hC
      have hC' : ∀ x y, x ⬝ᵥ B₁ *ᵥ y = 0 → x ⬝ᵥ B₂ *ᵥ y = 0 → x ⬝ᵥ C *ᵥ y = 0 := by
        intro x y h1 h2
        apply hC
        intro A hA
        obtain ⟨a, b, rfl⟩ := mem_span_pair.mp hA
        rw [bil_add, bil_smul, bil_smul, h1, h2]
        simp
      have hex : ∃ α β : ℂ, C = α • B₁ + β • B₂ := by
        rcases halt with hfree | ⟨⟨u₁, v₁, rfl⟩, ⟨u₂, v₂, rfl⟩⟩
        · exact refl_r1free B₁ B₂ C hfree hC'
        · rcases r1pair_cases u₁ u₂ v₁ v₂ hind with hu | hv
          · exact refl_r1pair u₁ u₂ v₁ v₂ hu C hC'
          · exact refl_r1pair' u₁ u₂ v₁ v₂ hv C hC'
      obtain ⟨α, β, rfl⟩ := hex
      exact mem_span_pair.mpr ⟨α, β, rfl⟩)
  rw [hfr] at h
  omega

theorem dim_lemma {M E : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    [AddCommGroup E] [Module ℂ E]
    {p r : ℕ} (S : Fin p → M) (hS : LinearIndependent ℂ S) (R : Fin r → M)
    (hSR : ∀ k, S k ∈ span ℂ (Set.range R)) (β : M →ₗ[ℂ] E) (hβ : ∀ k, β (S k) = 0) :
    p + Module.finrank ℂ (LinearMap.range (β.domRestrict (span ℂ (Set.range R)))) ≤ r := by
  have hVr : Module.finrank ℂ (span ℂ (Set.range R)) ≤ r :=
    (finrank_range_le_card (R := ℂ) R).trans (by simp)
  have h1 := LinearMap.finrank_range_add_finrank_ker (β.domRestrict (span ℂ (Set.range R)))
  have hW : span ℂ (Set.range S) ≤ span ℂ (Set.range R) :=
    span_le.mpr (by rintro _ ⟨k, rfl⟩; exact hSR k)
  have hinc : Function.Injective (Submodule.inclusion hW) := Submodule.inclusion_injective hW
  have hker : span ℂ (Set.range S) ≤ LinearMap.ker β :=
    span_le.mpr (by rintro _ ⟨k, rfl⟩; exact hβ k)
  have h2 : LinearMap.range (Submodule.inclusion hW) ≤
      LinearMap.ker (β.domRestrict (span ℂ (Set.range R))) := by
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    rw [LinearMap.mem_ker]
    exact hker hw
  have h3 := Submodule.finrank_mono h2
  rw [LinearMap.finrank_range_of_inj hinc, finrank_span_eq_card hS, Fintype.card_fin] at h3
  omega

def wit (m n u : ℕ) : Holor ℂ [m, n, m * n - u] := fun t =>
  (if t.1.getD 2 0 = t.1.getD 0 0 * n + t.1.getD 1 0 then (1 : ℂ) else 0)
  - (if 2 ≤ u ∧ t.1.getD 0 0 = m - 1 ∧ t.1.getD 1 0 = n - 2 ∧
      t.1.getD 2 0 = (m - 2) * n + (n - 1) then (1 : ℂ) else 0)
  - (if 4 ≤ u ∧ t.1.getD 0 0 = m - 1 ∧ t.1.getD 1 0 = n - 4 ∧
      t.1.getD 2 0 = (m - 2) * n + (n - 3) then (1 : ℂ) else 0)

theorem slice_wit (m n u : ℕ) (i : Fin m) (j : Fin n) (k : Fin (m * n - u)) :
    slice (wit m n u) k i j =
      (if k.1 = i.1 * n + j.1 then (1 : ℂ) else 0)
      - (if 2 ≤ u ∧ i.1 = m - 1 ∧ j.1 = n - 2 ∧ k.1 = (m - 2) * n + (n - 1) then (1 : ℂ) else 0)
      - (if 4 ≤ u ∧ i.1 = m - 1 ∧ j.1 = n - 4 ∧ k.1 = (m - 2) * n + (n - 3) then (1 : ℂ) else 0) :=
  rfl

theorem wit_indep {m n u : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hu : u ≤ 4) (hum : u ≤ m) :
    LinearIndependent ℂ (slice (wit m n u)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k'
  have hn : 0 < n := by omega
  have hk' : k'.1 < m * n := by have := k'.2; omega
  have hi : k'.1 / n < m := Nat.div_lt_of_lt_mul (lt_of_lt_of_eq hk' (Nat.mul_comm m n))
  have hj : k'.1 % n < n := Nat.mod_lt _ hn
  have hdm : k'.1 / n * n + k'.1 % n = k'.1 := Nat.div_add_mod' _ _
  have hsub : (m - 1) * n = m * n - n := Nat.sub_one_mul m n
  have hle : n ≤ m * n := Nat.le_mul_of_pos_left n (by omega)
  have key : ∀ k : Fin (m * n - u),
      slice (wit m n u) k ⟨k'.1 / n, hi⟩ ⟨k'.1 % n, hj⟩ = if k = k' then 1 else 0 := by
    intro k
    rw [slice_wit]
    have h2 : ¬ (2 ≤ u ∧ k'.1 / n = m - 1 ∧ k'.1 % n = n - 2 ∧
        k.1 = (m - 2) * n + (n - 1)) := by
      rintro ⟨h2u, e1, e2, -⟩
      rw [e1, e2] at hdm
      have := k'.2
      omega
    have h4 : ¬ (4 ≤ u ∧ k'.1 / n = m - 1 ∧ k'.1 % n = n - 4 ∧
        k.1 = (m - 2) * n + (n - 3)) := by
      rintro ⟨h4u, e1, e2, -⟩
      rw [e1, e2] at hdm
      have := k'.2
      omega
    simp only [h2, h4, if_false, sub_zero, hdm]
    by_cases hkk : k = k'
    · simp [hkk]
    · have : k.1 ≠ k'.1 := fun h => hkk (Fin.ext h)
      simp [hkk, this]
  have h1 := congrFun (congrFun hg ⟨k'.1 / n, hi⟩) ⟨k'.1 % n, hj⟩
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, key, Matrix.zero_apply] at h1
  simpa using h1

theorem w23 (x₁ x₂ y₁ y₂ : ℂ) (h1 : x₁ * y₁ = 0) (h2 : x₁ * y₂ + x₂ * y₁ = 0) :
    x₁ * y₂ = 0 := by
  rcases mul_eq_zero.mp h1 with h | h
  · simp [h]
  · rw [h] at h2
    simpa using h2

theorem w4 (σ₁ σ₂ σ₃ σ₄ : ℂ) : ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧
    ∀ x₁ x₂ y₁ y₂ y₃ y₄ l : ℂ, x₁ * y₁ = l * σ₁ → x₁ * y₂ + x₂ * y₁ = l * σ₂ →
      x₁ * y₃ = l * σ₃ → x₁ * y₄ + x₂ * y₃ = l * σ₄ → x₂ * (a * y₁ + b * y₃) = 0 := by
  by_cases h13 : σ₁ ≠ 0 ∨ σ₃ ≠ 0
  · refine ⟨σ₃, -σ₁, ?_, ?_⟩
    · rcases h13 with h | h
      · exact Or.inr (neg_ne_zero.mpr h)
      · exact Or.inl h
    · intro x₁ x₂ y₁ y₂ y₃ y₄ l e1 e2 e3 e4
      have h5 : x₁ * (σ₃ * y₁ + -σ₁ * y₃) = 0 := by linear_combination σ₃ * e1 - σ₁ * e3
      rcases mul_eq_zero.mp h5 with hx | hy
      · rw [hx, zero_mul] at e1 e3
        rw [hx, zero_mul, zero_add] at e2 e4
        have hl : l = 0 := by
          rcases h13 with h | h
          · exact (mul_eq_zero.mp e1.symm).resolve_right h
          · exact (mul_eq_zero.mp e3.symm).resolve_right h
        rw [hl, zero_mul] at e2 e4
        linear_combination σ₃ * e2 - σ₁ * e4
      · rw [hy, mul_zero]
  · rw [not_or, not_not, not_not] at h13
    obtain ⟨hs1, hs3⟩ := h13
    by_cases h24 : σ₂ ≠ 0 ∨ σ₄ ≠ 0
    · refine ⟨σ₄, -σ₂, ?_, ?_⟩
      · rcases h24 with h | h
        · exact Or.inr (neg_ne_zero.mpr h)
        · exact Or.inl h
      · intro x₁ x₂ y₁ y₂ y₃ y₄ l e1 e2 e3 e4
        rw [hs1, mul_zero] at e1
        rw [hs3, mul_zero] at e3
        by_cases hx : x₁ = 0
        · rw [hx, zero_mul, zero_add] at e2 e4
          linear_combination σ₄ * e2 - σ₂ * e4
        · have hy1 : y₁ = 0 := (mul_eq_zero.mp e1).resolve_left hx
          have hy3 : y₃ = 0 := (mul_eq_zero.mp e3).resolve_left hx
          rw [hy1, hy3]; ring
    · rw [not_or, not_not, not_not] at h24
      obtain ⟨hs2, hs4⟩ := h24
      refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
      intro x₁ x₂ y₁ y₂ y₃ y₄ l e1 e2 e3 e4
      rw [hs1, mul_zero] at e1
      rw [hs2, mul_zero] at e2
      have h6 := w23 x₁ x₂ y₁ y₂ e1 e2
      have h7 : x₂ * y₁ = 0 := by linear_combination e2 - h6
      linear_combination h7

def beta2 {m n : ℕ} (i1 i2 : Fin m) (j1 j2 : Fin n) :
    Matrix (Fin m) (Fin n) ℂ →ₗ[ℂ] ℂ × ℂ where
  toFun X := (X i1 j1, X i1 j2 + X i2 j1)
  map_add' X Y := by
    simp only [Matrix.add_apply, Prod.mk_add_mk]
    congr 1
    ring
  map_smul' c X := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Prod.smul_mk]
    congr 1
    ring

def beta4 {m n : ℕ} (i1 i2 : Fin m) (j1 j2 j3 j4 : Fin n) :
    Matrix (Fin m) (Fin n) ℂ →ₗ[ℂ] ℂ × ℂ × ℂ × ℂ where
  toFun X := (X i1 j1, X i1 j2 + X i2 j1, X i1 j3, X i1 j4 + X i2 j3)
  map_add' X Y := by
    simp only [Matrix.add_apply, Prod.mk_add_mk]
    congr 1
    congr 1
    · ring
    · congr 1
      ring
  map_smul' c X := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Prod.smul_mk]
    congr 1
    congr 1
    · ring
    · congr 1
      ring

theorem beta2_apply {m n : ℕ} (i1 i2 : Fin m) (j1 j2 : Fin n) (X : Matrix (Fin m) (Fin n) ℂ) :
    beta2 i1 i2 j1 j2 X = (X i1 j1, X i1 j2 + X i2 j1) := rfl

theorem beta4_apply {m n : ℕ} (i1 i2 : Fin m) (j1 j2 j3 j4 : Fin n)
    (X : Matrix (Fin m) (Fin n) ℂ) :
    beta4 i1 i2 j1 j2 j3 j4 X = (X i1 j1, X i1 j2 + X i2 j1, X i1 j3, X i1 j4 + X i2 j3) := rfl

theorem wit_entry {m n u : ℕ} (k : Fin (m * n - u)) (i j : ℕ) (hi : i < m) (hj : j < n) :
    slice (wit m n u) k ⟨i, hi⟩ ⟨j, hj⟩ =
      (if k.1 = i * n + j then (1 : ℂ) else 0)
      - (if 2 ≤ u ∧ i = m - 1 ∧ j = n - 2 ∧ k.1 = (m - 2) * n + (n - 1) then (1 : ℂ) else 0)
      - (if 4 ≤ u ∧ i = m - 1 ∧ j = n - 4 ∧ k.1 = (m - 2) * n + (n - 3) then (1 : ℂ) else 0) :=
  rfl

theorem dim_cor0 {M E : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    [AddCommGroup E] [Module ℂ E]
    {p r : ℕ} (S : Fin p → M) (hS : LinearIndependent ℂ S) (R : Fin r → M)
    (hSR : ∀ k, S k ∈ span ℂ (Set.range R)) (β : M →ₗ[ℂ] E) (hβ : ∀ k, β (S k) = 0)
    (hr : r ≤ p) : ∀ s, β (R s) = 0 := by
  have h1 := dim_lemma S hS R hSR β hβ
  have h2 : Module.finrank ℂ (LinearMap.range (β.domRestrict (span ℂ (Set.range R)))) = 0 := by
    omega
  have h3 := Submodule.finrank_eq_zero.mp h2
  intro s
  have h4 : β (R s) ∈ LinearMap.range (β.domRestrict (span ℂ (Set.range R))) :=
    ⟨⟨R s, subset_span ⟨s, rfl⟩⟩, rfl⟩
  rw [h3, Submodule.mem_bot] at h4
  exact h4

theorem dim_cor1 {M E : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    [AddCommGroup E] [Module ℂ E]
    {p r : ℕ} (S : Fin p → M) (hS : LinearIndependent ℂ S) (R : Fin r → M)
    (hSR : ∀ k, S k ∈ span ℂ (Set.range R)) (β : M →ₗ[ℂ] E) (hβ : ∀ k, β (S k) = 0)
    (hr : r ≤ p + 1) : ∃ σ : E, ∀ s, ∃ l : ℂ, l • σ = β (R s) := by
  have h1 := dim_lemma S hS R hSR β hβ
  have h2 : Module.finrank ℂ (LinearMap.range (β.domRestrict (span ℂ (Set.range R)))) ≤ 1 := by
    omega
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp h2
  refine ⟨v.1, fun s => ?_⟩
  obtain ⟨l, hl⟩ := hv ⟨β (R s), ⟨⟨R s, subset_span ⟨s, rfl⟩⟩, rfl⟩⟩
  exact ⟨l, congrArg Subtype.val hl⟩

theorem dim_cor_le {M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    {p r : ℕ} (S : Fin p → M) (hS : LinearIndependent ℂ S) (R : Fin r → M)
    (hSR : ∀ k, S k ∈ span ℂ (Set.range R)) : p ≤ r := by
  have h1 := dim_lemma S hS R hSR (0 : M →ₗ[ℂ] ℂ) (fun k => rfl)
  omega

theorem wit_piv1 {m n u : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hu : u ≤ 4) (hum : u ≤ m)
    (hu2 : 2 ≤ u) (k : Fin (m * n - u)) (h1 : m - 1 < m) (h2 : n - 1 < n) :
    slice (wit m n u) k ⟨m - 1, h1⟩ ⟨n - 1, h2⟩ = 0 := by
  have hk := k.2
  have hsub1 : (m - 1) * n = m * n - n := Nat.sub_one_mul m n
  have hle : 3 * n ≤ m * n := Nat.mul_le_mul_right n hm
  rw [wit_entry]
  split_ifs <;> first | (exfalso; omega) | norm_num

theorem wit_piv2 {m n u : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hu : u ≤ 4) (hum : u ≤ m)
    (hu2 : 2 ≤ u) (k : Fin (m * n - u)) (h1 : m - 1 < m) (h2 : n - 2 < n) :
    slice (wit m n u) k ⟨m - 1, h1⟩ ⟨n - 2, h2⟩ =
      -(if k.1 = (m - 2) * n + (n - 1) then (1 : ℂ) else 0) := by
  have hk := k.2
  have hsub1 : (m - 1) * n = m * n - n := Nat.sub_one_mul m n
  have hle : 3 * n ≤ m * n := Nat.mul_le_mul_right n hm
  rw [wit_entry]
  split_ifs <;> first | (exfalso; omega) | norm_num

theorem wit_piv2' {m n u : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n)
    (k : Fin (m * n - u)) (h1 : m - 2 < m) (h2 : n - 1 < n) :
    slice (wit m n u) k ⟨m - 2, h1⟩ ⟨n - 1, h2⟩ =
      (if k.1 = (m - 2) * n + (n - 1) then (1 : ℂ) else 0) := by
  rw [wit_entry]
  split_ifs <;> first | (exfalso; omega) | norm_num

theorem wit_piv3 {m n u : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hum : u ≤ m)
    (hu4 : u = 4) (k : Fin (m * n - u)) (h1 : m - 1 < m) (h2 : n - 3 < n) :
    slice (wit m n u) k ⟨m - 1, h1⟩ ⟨n - 3, h2⟩ = 0 := by
  have hk := k.2
  have hsub1 : (m - 1) * n = m * n - n := Nat.sub_one_mul m n
  have hle : 3 * n ≤ m * n := Nat.mul_le_mul_right n hm
  rw [wit_entry]
  split_ifs <;> first | (exfalso; omega) | norm_num

theorem wit_piv4 {m n u : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hum : u ≤ m)
    (hu4 : u = 4) (k : Fin (m * n - u)) (h1 : m - 1 < m) (h2 : n - 4 < n) :
    slice (wit m n u) k ⟨m - 1, h1⟩ ⟨n - 4, h2⟩ =
      -(if k.1 = (m - 2) * n + (n - 3) then (1 : ℂ) else 0) := by
  have hk := k.2
  have hsub1 : (m - 1) * n = m * n - n := Nat.sub_one_mul m n
  have hle : 3 * n ≤ m * n := Nat.mul_le_mul_right n hm
  rw [wit_entry]
  split_ifs <;> first | (exfalso; omega) | norm_num

theorem wit_piv4' {m n u : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n)
    (k : Fin (m * n - u)) (h1 : m - 2 < m) (h2 : n - 3 < n) :
    slice (wit m n u) k ⟨m - 2, h1⟩ ⟨n - 3, h2⟩ =
      (if k.1 = (m - 2) * n + (n - 3) then (1 : ℂ) else 0) := by
  rw [wit_entry]
  split_ifs <;> first | (exfalso; omega) | norm_num

theorem lower {m n u : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) (hu : u ≤ 4) (hum : u ≤ m) (r : ℕ)
    (h : Holor.CPRankMax r (wit m n u)) : m * n - (u + 1) / 2 ≤ r := by
  obtain ⟨a, b, c, habc⟩ := sum_of_cprankMax _ h
  have hS : ∀ (k : Fin (m * n - u)) (i : Fin m) (j : Fin n),
      slice (wit m n u) k i j = ∑ s, c s k * (a s i * b s j) := by
    intro k i j
    show wit m n u (idx3 i j k) = _
    rw [habc]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  have hSR : ∀ k, slice (wit m n u) k ∈
      span ℂ (Set.range (fun s => vecMulVec (a s) (b s))) := by
    intro k
    have h1 : slice (wit m n u) k = ∑ s, c s k • vecMulVec (a s) (b s) := by
      ext i j
      rw [hS]
      simp [Matrix.sum_apply, vecMulVec_apply]
    rw [h1]
    exact Submodule.sum_mem _ (fun s _ => Submodule.smul_mem _ _ (subset_span ⟨s, rfl⟩))
  have hind := wit_indep hm hmn hu hum
  have hsub2 : (m - 2) * n = m * n - 2 * n := Nat.sub_mul m 2 n
  have hle : 3 * n ≤ m * n := Nat.mul_le_mul_right n hm
  by_contra hlt
  rw [not_le] at hlt
  have hpr := dim_cor_le _ hind _ hSR
  have hu2 : 2 ≤ u := by
    by_contra hu01
    omega
  have hk0 : (m - 2) * n + (n - 1) < m * n - u := by omega
  have hm1 : m - 1 < m := by omega
  have hm2 : m - 2 < m := by omega
  have hn1 : n - 1 < n := by omega
  have hn2 : n - 2 < n := by omega
  have hn3 : n - 3 < n := by omega
  have hn4 : n - 4 < n := by omega
  by_cases hu4 : u = 4
  · have hk1 : (m - 2) * n + (n - 3) < m * n - u := by omega
    have hβ : ∀ k, beta4 (⟨m - 1, hm1⟩ : Fin m) ⟨m - 2, hm2⟩
        (⟨n - 1, hn1⟩ : Fin n) ⟨n - 2, hn2⟩ ⟨n - 3, hn3⟩ ⟨n - 4, hn4⟩
        (slice (wit m n u) k) = 0 := by
      intro k
      rw [beta4_apply, wit_piv1 hm hmn hu hum hu2, wit_piv2 hm hmn hu hum hu2,
        wit_piv2' hm hmn, wit_piv3 hm hmn hum hu4, wit_piv4 hm hmn hum hu4, wit_piv4' hm hmn]
      simp
    obtain ⟨σ, hσ⟩ := dim_cor1 _ hind _ hSR _ hβ (by omega)
    obtain ⟨a', b', hab, hw⟩ := w4 σ.1 σ.2.1 σ.2.2.1 σ.2.2.2
    have hs : ∀ s, a s ⟨m - 2, hm2⟩ *
        (a' * b s ⟨n - 1, hn1⟩ + b' * b s ⟨n - 3, hn3⟩) = 0 := by
      intro s
      obtain ⟨l, hl⟩ := hσ s
      simp only [beta4_apply, vecMulVec_apply] at hl
      have e1 := congrArg Prod.fst hl
      have e2 := congrArg (fun q => q.2.1) hl
      have e3 := congrArg (fun q => q.2.2.1) hl
      have e4 := congrArg (fun q => q.2.2.2) hl
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e2 e3 e4
      exact hw _ _ _ _ _ _ l e1.symm e2.symm e3.symm e4.symm
    have hall : ∀ k : Fin (m * n - u),
        a' * slice (wit m n u) k ⟨m - 2, hm2⟩ ⟨n - 1, hn1⟩
          + b' * slice (wit m n u) k ⟨m - 2, hm2⟩ ⟨n - 3, hn3⟩ = 0 := by
      intro k
      rw [hS, hS, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero (fun s _ => ?_)
      linear_combination (c s k) * hs s
    have ha0 := hall ⟨(m - 2) * n + (n - 1), hk0⟩
    have hb0 := hall ⟨(m - 2) * n + (n - 3), hk1⟩
    rw [wit_piv2' hm hmn, wit_piv4' hm hmn] at ha0 hb0
    dsimp only at ha0 hb0
    have hne : (m - 2) * n + (n - 1) ≠ (m - 2) * n + (n - 3) := by omega
    rw [if_pos rfl, if_neg hne] at ha0
    rw [if_neg (Ne.symm hne), if_pos rfl] at hb0
    have ha' : a' = 0 := by simpa using ha0
    have hb' : b' = 0 := by simpa using hb0
    rcases hab with h | h
    · exact h ha'
    · exact h hb'
  · have hu3 : u ≤ 3 := by omega
    have hβ : ∀ k, beta2 (⟨m - 1, hm1⟩ : Fin m) ⟨m - 2, hm2⟩
        (⟨n - 1, hn1⟩ : Fin n) ⟨n - 2, hn2⟩ (slice (wit m n u) k) = 0 := by
      intro k
      rw [beta2_apply, wit_piv1 hm hmn hu hum hu2, wit_piv2 hm hmn hu hum hu2,
        wit_piv2' hm hmn]
      simp
    have hz := dim_cor0 _ hind _ hSR _ hβ (by omega)
    have hs : ∀ s, a s ⟨m - 1, hm1⟩ * b s ⟨n - 2, hn2⟩ = 0 := by
      intro s
      have h4 := hz s
      simp only [beta2_apply, vecMulVec_apply, Prod.mk_eq_zero] at h4
      exact w23 _ _ _ _ h4.1 h4.2
    have h5 := hS ⟨(m - 2) * n + (n - 1), hk0⟩ ⟨m - 1, hm1⟩ ⟨n - 2, hn2⟩
    have h6 : (∑ s, c s ⟨(m - 2) * n + (n - 1), hk0⟩ *
        (a s ⟨m - 1, hm1⟩ * b s ⟨n - 2, hn2⟩)) = 0 :=
      Finset.sum_eq_zero (fun s _ => by rw [hs s]; ring)
    rw [wit_piv2 hm hmn hu hum hu2, h6] at h5
    dsimp only at h5
    rw [if_pos rfl] at h5
    norm_num at h5

end OMA.Helpers

theorem OMA.solution : type_of% @Arxiv.«0805.3777».isMaxRank_of_le_min := by
  intro m n u hm hmn hu
  have hu4 : u ≤ 4 := le_trans hu (min_le_left _ _)
  have hum : u ≤ m := le_trans hu (min_le_right _ _)
  have hceil : u ⌈/⌉ 2 = (u + 1) / 2 := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    omega
  have hmn9 : 9 ≤ m * n := by nlinarith
  have hup : ∀ T : Holor ℂ [m, n, m * n - u], T.cprank ≤ m * n - (u + 1) / 2 := by
    intro T
    by_cases h0 : u = 0
    · have := OMA.Helpers.upper0 T
      omega
    · by_cases h3 : u ≤ 2
      · have := OMA.Helpers.upper1 T (by omega)
        omega
      · have := OMA.Helpers.upper2 T (by omega)
        omega
  rw [hceil]
  refine ⟨⟨OMA.Helpers.wit m n u, ?_⟩, ?_⟩
  · exact le_antisymm (hup _)
      (OMA.Helpers.lower hm hmn hu4 hum _ (OMA.Helpers.cprankMax_cprank _))
  · rintro _ ⟨T, rfl⟩
    exact hup T
