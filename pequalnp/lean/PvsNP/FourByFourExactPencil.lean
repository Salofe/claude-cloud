import PvsNP.FourByFourExactBase

/-!
# Exact five-term bound: pencils of two forms

Let `Φ₁, Φ₂` be two bilinear forms such that, for every `l` with nonzero coordinates, the
slice matrix `B^l_u` of the permanent is singular for all `u` with `Φ₁(l,u) = Φ₂(l,u) = 0`.
The main result of this file, `weakS`, says that then either two columns of both forms vanish,
or both forms lie in `span(alt_ab, s_cd)` for a splitting `{a,b} | {c,d}` of the columns
(`InPair`). Behind it: `det B_u = -4 σ(u)` with `σ = e₁ e₃ - 4 e₄`, and the classification of
the planes on which `σ` vanishes (`chart_class`, sixteen planes; `planes_of_sigma`).
-/

namespace PvsNP

open Matrix

section Pencil

variable {K : Type*} [Field K]

/-- The quartic `σ = e₁ e₃ - 4 e₄` in four variables. -/
def sig4 (x0 x1 x2 x3 : K) : K :=
  (x0 + x1 + x2 + x3) * (x1 * x2 * x3 + x0 * x2 * x3 + x0 * x1 * x3 + x0 * x1 * x2)
    - 4 * (x0 * x1 * x2 * x3)

/-- **Planes on the quartic, in a chart.** If `σ` vanishes on the plane spanned by
`(1, 0, a, b)` and `(0, 1, c, d)`, then `(a, b, c, d)` is one of seven points. -/
lemma chart_class [CharZero K] (a b c d : K)
    (H : ∀ s t : K, sig4 s t (a * s + c * t) (b * s + d * t) = 0) :
    (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) ∨ (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = -1) ∨
    (a = 0 ∧ b = 1 ∧ c = -1 ∧ d = 0) ∨ (a = 0 ∧ b = -1 ∧ c = 1 ∧ d = 0) ∨
    (a = -1 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨ (a = 0 ∧ b = -1 ∧ c = 0 ∧ d = -1) ∨
    (a = -1 ∧ b = 0 ∧ c = -1 ∧ d = 0) := by
  have h10 := H 1 0
  have h01 := H 0 1
  have h11 := H 1 1
  have h1m := H 1 (-1)
  have h12 := H 1 2
  simp only [sig4] at h10 h01 h11 h1m h12
  have e3 : d = b + c - a := by
    have h : (a - b - c + d) ^ 2 = 0 := by linear_combination -h1m
    have h' := pow_eq_zero_iff (two_ne_zero) |>.mp h
    linear_combination h'
  subst e3
  have e1 : a * b * (a + b + 1) = 0 := by linear_combination h10
  have e2 : c * (b + c - a) * (2 * c + b - a + 1) = 0 := by linear_combination h01
  have c22 : -3*a^2*b - 3*a^2*c + 3*a*b^2 + 6*a*b*c - a*b + 3*a*c^2 + a*c + 3*b^2*c + 2*b^2
      + 3*b*c^2 + 3*b*c + 2*b + c^2 + 2*c = 0 := by
    linear_combination (1 / 2 : K) * h11 + (1 / 2 : K) * h1m - h10 - h01
  have c13 : a^3 - 2*a^2*b - 3*a^2*c + a*b^2 - a*b - a*c - a + 3*b^2*c + b^2 + 6*b*c^2 + 3*b*c
      + b + 2*c^3 + 2*c^2 + 2*c = 0 := by
    linear_combination (1 / 6 : K) * h12 + (1 / 2 : K) * h10 - 2 * h01 - (1 / 2 : K) * h11
      - (1 / 6 : K) * h1m
  have c31 : -a^3 + a^2*c + 3*a*b^2 + 4*a*b*c + a*b + a*c + a + b^2*c + b^2 + b*c + b = 0 := by
    linear_combination (1 / 2 : K) * h11 - (1 / 2 : K) * h1m - c13
  clear h10 h01 h11 h1m h12 H
  by_cases ha : a = 0
  · subst ha
    have h : b * (b + 1) * (c + 1) = 0 := by linear_combination c31
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with hb | hb
      · subst hb
        have h2 : c * c * (2 * c + 1) = 0 := by linear_combination e2
        rcases mul_eq_zero.mp h2 with h3 | h3
        · have hc : c = 0 := by simpa using h3
          subst hc
          norm_num
        · exfalso
          have : (3 : K) = 0 := by linear_combination -4 * c22 + (2 * c + 3) * h3
          norm_num at this
      · have hb' : b = -1 := by linear_combination hb
        subst hb'
        have h2 : c * c * (c - 1) = 0 := by linear_combination (1 / 2 : K) * e2
        rcases mul_eq_zero.mp h2 with h3 | h3
        · have hc : c = 0 := by simpa using h3
          subst hc
          norm_num
        · have hc : c = 1 := by linear_combination h3
          subst hc
          norm_num
    · have hc : c = -1 := by linear_combination h
      subst hc
      have h2 : (b - 1) ^ 2 = 0 := by linear_combination -e2
      have hb : b = 1 := by
        have := pow_eq_zero_iff (two_ne_zero) |>.mp h2
        linear_combination this
      subst hb
      norm_num
  · by_cases hb : b = 0
    · subst hb
      have h : a * (a + 1) * (c - a + 1) = 0 := by linear_combination c31
      rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h ha
        · have ha' : a = -1 := by linear_combination h
          subst ha'
          have h2 : c * (c + 1) * (c + 1) = 0 := by linear_combination (1 / 2 : K) * e2
          rcases mul_eq_zero.mp h2 with h3 | h3
          · rcases mul_eq_zero.mp h3 with h4 | h4
            · subst h4
              norm_num
            · have hc : c = -1 := by linear_combination h4
              subst hc
              norm_num
          · have hc : c = -1 := by linear_combination h3
            subst hc
            norm_num
      · have hc : c = a - 1 := by linear_combination h
        subst hc
        have h2 : (a - 1) ^ 2 = 0 := by linear_combination -e2
        have ha' : a = 1 := by
          have := pow_eq_zero_iff (two_ne_zero) |>.mp h2
          linear_combination this
        subst ha'
        norm_num
    · exfalso
      have hab : a + b + 1 = 0 := by
        rcases mul_eq_zero.mp e1 with h | h
        · rcases mul_eq_zero.mp h with h | h
          · exact absurd h ha
          · exact absurd h hb
        · exact h
      have hb' : b = -1 - a := by linear_combination hab
      subst hb'
      have h : a * (a + 1) * (a - c + 2) = 0 := by linear_combination (1 / 2 : K) * c31
      have ha1 : a + 1 ≠ 0 := fun h' => hb (by linear_combination -h')
      have hc : c = a + 2 := by
        rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · exact absurd h ha
          · exact absurd h ha1
        · linear_combination -h
      subst hc
      have h3 : (3 : K) = 0 := by linear_combination (-1 / 4 : K) * c22 + (1 / 4 : K) * e2
      norm_num at h3

/-- Four pairwise distinct indices. -/
abbrev D4 (i j k m : Fin 4) : Prop := i ≠ j ∧ i ≠ k ∧ i ≠ m ∧ j ≠ k ∧ j ≠ m ∧ k ≠ m

/-- `σ` is a symmetric function. -/
lemma sig4_chart : ∀ i j k m : Fin 4, D4 i j k m → ∀ w : Fin 4 → K,
    sig4 (w i) (w j) (w k) (w m) = sig4 (w 0) (w 1) (w 2) (w 3) := by
  intro i j k m hd w
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases m <;>
    first
      | (exfalso; simp [D4] at hd; done)
      | rfl
      | (simp only [sig4, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]; ring)

/-- The equations of the sixteen planes: `planeEq (tag, i, j, k, m) e c = 0` for `e = 0, 1`
says that the covector `c` vanishes on the plane `span(e_i, e_j)` (`tag = 0`),
`span(e_i + e_k, e_j - e_m)` (`tag = 1`) or `span(e_i - e_m, e_j - e_m)` (`tag = 2`). -/
def planeEq (n : Fin 3 × Fin 4 × Fin 4 × Fin 4 × Fin 4) (e : Fin 2) (c : Fin 4 → K) : K :=
  (![![c n.2.1, c n.2.2.1], ![c n.2.1 + c n.2.2.2.1, c n.2.2.1 - c n.2.2.2.2],
    ![c n.2.1 - c n.2.2.2.2, c n.2.2.1 - c n.2.2.2.2]] : Fin 3 → Fin 2 → K) n.1 e

lemma dot4_add_smul (c p q : Fin 4 → K) (s t : K) :
    dot4 c (s • p + t • q) = s * dot4 c p + t * dot4 c q := by
  simp only [dot4_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Planes on the quartic.** If `σ` vanishes on the common kernel of two covectors, the two
covectors vanish on one of the sixteen planes. -/
theorem planes_of_sigma [CharZero K] (c1 c2 : Fin 4 → K)
    (H : ∀ w : Fin 4 → K, dot4 c1 w = 0 → dot4 c2 w = 0 → sig4 (w 0) (w 1) (w 2) (w 3) = 0) :
    ∃ n : Fin 3 × Fin 4 × Fin 4 × Fin 4 × Fin 4, D4 n.2.1 n.2.2.1 n.2.2.2.1 n.2.2.2.2 ∧
      ∀ e : Fin 2, planeEq n e c1 = 0 ∧ planeEq n e c2 = 0 := by
  obtain ⟨i, j, k, m, hd, a, b, c, d, e1, e2, e3, e4⟩ := exists_chart c1 c2
  obtain ⟨hij, hik, him, hjk, hjm, hkm⟩ := hd
  have hcls := chart_class a b c d fun s t => by
    have := H (s • chartVec i k m a b + t • chartVec j k m c d)
      (by rw [dot4_add_smul, e1, e3]; ring) (by rw [dot4_add_smul, e2, e4]; ring)
    rw [← sig4_chart i j k m ⟨hij, hik, him, hjk, hjm, hkm⟩] at this
    simp [chartVec, hij, hik, him, hjk, hjm, hkm, hij.symm, hik.symm, him.symm,
      hjk.symm, hjm.symm, hkm.symm] at this
    rw [show a * s + c * t = s * a + t * c by ring, show b * s + d * t = s * b + t * d by ring]
    exact this
  rw [dot4_chartVec] at e1 e2 e3 e4
  rcases hcls with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · refine ⟨(0, i, j, k, m), ⟨hij, hik, him, hjk, hjm, hkm⟩, Fin.forall_fin_two.mpr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
    · show c1 i = 0
      linear_combination e1
    · show c2 i = 0
      linear_combination e2
    · show c1 j = 0
      linear_combination e3
    · show c2 j = 0
      linear_combination e4
  · refine ⟨(1, i, j, k, m), ⟨hij, hik, him, hjk, hjm, hkm⟩, Fin.forall_fin_two.mpr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
    · show c1 i + c1 k = 0
      linear_combination e1
    · show c2 i + c2 k = 0
      linear_combination e2
    · show c1 j - c1 m = 0
      linear_combination e3
    · show c2 j - c2 m = 0
      linear_combination e4
  · refine ⟨(1, i, j, m, k), ⟨hij, him, hik, hjm, hjk, hkm.symm⟩, Fin.forall_fin_two.mpr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
    · show c1 i + c1 m = 0
      linear_combination e1
    · show c2 i + c2 m = 0
      linear_combination e2
    · show c1 j - c1 k = 0
      linear_combination e3
    · show c2 j - c2 k = 0
      linear_combination e4
  · refine ⟨(1, j, i, k, m), ⟨hij.symm, hjk, hjm, hik, him, hkm⟩, Fin.forall_fin_two.mpr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
    · show c1 j + c1 k = 0
      linear_combination e3
    · show c2 j + c2 k = 0
      linear_combination e4
    · show c1 i - c1 m = 0
      linear_combination e1
    · show c2 i - c2 m = 0
      linear_combination e2
  · refine ⟨(1, j, i, m, k), ⟨hij.symm, hjm, hjk, him, hik, hkm.symm⟩, Fin.forall_fin_two.mpr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
    · show c1 j + c1 m = 0
      linear_combination e3
    · show c2 j + c2 m = 0
      linear_combination e4
    · show c1 i - c1 k = 0
      linear_combination e1
    · show c2 i - c2 k = 0
      linear_combination e2
  · refine ⟨(2, i, j, k, m), ⟨hij, hik, him, hjk, hjm, hkm⟩, Fin.forall_fin_two.mpr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
    · show c1 i - c1 m = 0
      linear_combination e1
    · show c2 i - c2 m = 0
      linear_combination e2
    · show c1 j - c1 m = 0
      linear_combination e3
    · show c2 j - c2 m = 0
      linear_combination e4
  · refine ⟨(2, i, j, m, k), ⟨hij, him, hik, hjm, hjk, hkm.symm⟩, Fin.forall_fin_two.mpr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
    · show c1 i - c1 k = 0
      linear_combination e1
    · show c2 i - c2 k = 0
      linear_combination e2
    · show c1 j - c1 k = 0
      linear_combination e3
    · show c2 j - c2 k = 0
      linear_combination e4

/-- `InPair a b c d M`: the coefficient table `M` lies in the span of `alt_ab = E_ab - E_ba`
and `s_cd = E_cd + E_dc`. -/
def InPair (a b c d : Fin 4) (M : Matrix (Fin 4) (Fin 4) K) : Prop :=
  M a a = 0 ∧ M b b = 0 ∧ M c c = 0 ∧ M d d = 0 ∧ M b a = -M a b ∧ M d c = M c d ∧
  M a c = 0 ∧ M a d = 0 ∧ M b c = 0 ∧ M b d = 0 ∧ M c a = 0 ∧ M c b = 0 ∧ M d a = 0 ∧ M d b = 0

/-- The covector `w ↦ bil Φ l (l * w)`. -/
def cv (Φ : Matrix (Fin 4) (Fin 4) K) (l : Fin 4 → K) : Fin 4 → K := fun q => colf Φ l q * l q

lemma dot4_cv (Φ : Matrix (Fin 4) (Fin 4) K) (l w : Fin 4 → K) :
    dot4 (cv Φ l) w = bil Φ l (l * w) := by
  rw [bil_eq_dot]
  simp only [dot4, cv, Pi.mul_apply, mul_assoc]

lemma isPoly_cv (Φ : Matrix (Fin 4) (Fin 4) K) (q : Fin 4) : IsPoly (fun l => cv Φ l q) :=
  (IsPoly.sum _ _ fun p => (IsPoly.const (Φ p q)).mul (IsPoly.coord p)).mul (IsPoly.coord q)

lemma cv_single_self (Φ : Matrix (Fin 4) (Fin 4) K) (x : Fin 4) :
    cv Φ (Pi.single x 1) x = Φ x x := by
  simp [cv, colf, Pi.single_apply]

lemma cv_single_ne (Φ : Matrix (Fin 4) (Fin 4) K) {x q : Fin 4} (h : q ≠ x) :
    cv Φ (Pi.single x 1) q = 0 := by
  simp [cv, h]

lemma cv_two_left (Φ : Matrix (Fin 4) (Fin 4) K) {x y : Fin 4} (h : x ≠ y) :
    cv Φ (Pi.single x 1 + Pi.single y 1) x = Φ x x + Φ y x := by
  simp [cv, colf, Pi.single_apply, mul_add, Finset.sum_add_distrib, h]

lemma cv_two_right (Φ : Matrix (Fin 4) (Fin 4) K) {x y : Fin 4} (h : x ≠ y) :
    cv Φ (Pi.single x 1 + Pi.single y 1) y = Φ x y + Φ y y := by
  simp [cv, colf, Pi.single_apply, mul_add, Finset.sum_add_distrib, h.symm]

lemma cv_two_ne (Φ : Matrix (Fin 4) (Fin 4) K) {x y q : Fin 4} (hx : q ≠ x) (hy : q ≠ y) :
    cv Φ (Pi.single x 1 + Pi.single y 1) q = 0 := by
  simp [cv, hx, hy]

/-- If `bil Φ l (l * e_x)` vanishes for all `l`, column `x` of `Φ` vanishes. -/
lemma quad1 (Φ : Matrix (Fin 4) (Fin 4) K) (x : Fin 4) (h : ∀ l, cv Φ l x = 0) :
    ∀ z, Φ z x = 0 := by
  have hx : Φ x x = 0 := by
    have := h (Pi.single x 1)
    rwa [cv_single_self] at this
  intro z
  by_cases hz : z = x
  · rw [hz]
    exact hx
  · have := h (Pi.single z 1 + Pi.single x 1)
    rw [cv_two_right Φ hz] at this
    linear_combination this - hx

/-- The coefficient equations of `α * bil Φ l (l * e_x) + β * bil Φ l (l * e_y) = 0`. -/
lemma quad2 (Φ : Matrix (Fin 4) (Fin 4) K) {x y : Fin 4} (hxy : x ≠ y) (α β : K)
    (h : ∀ l, α * cv Φ l x + β * cv Φ l y = 0) :
    α * Φ x x = 0 ∧ β * Φ y y = 0 ∧ α * Φ y x + β * Φ x y = 0 ∧
      ∀ z, z ≠ x → z ≠ y → α * Φ z x = 0 ∧ β * Φ z y = 0 := by
  have h1 : α * Φ x x = 0 := by
    have := h (Pi.single x 1)
    rw [cv_single_self, cv_single_ne Φ hxy.symm] at this
    linear_combination this
  have h2 : β * Φ y y = 0 := by
    have := h (Pi.single y 1)
    rw [cv_single_self, cv_single_ne Φ hxy] at this
    linear_combination this
  refine ⟨h1, h2, ?_, fun z hzx hzy => ⟨?_, ?_⟩⟩
  · have := h (Pi.single x 1 + Pi.single y 1)
    rw [cv_two_left Φ hxy, cv_two_right Φ hxy] at this
    linear_combination this - h1 - h2
  · have := h (Pi.single z 1 + Pi.single x 1)
    rw [cv_two_right Φ hzx, cv_two_ne Φ hzy.symm hxy.symm] at this
    linear_combination this - h1
  · have := h (Pi.single z 1 + Pi.single y 1)
    rw [cv_two_right Φ hzy, cv_two_ne Φ hzx.symm hxy] at this
    linear_combination this - h2

lemma isPoly_planeEq (n : Fin 3 × Fin 4 × Fin 4 × Fin 4 × Fin 4) (e : Fin 2)
    (Φ : Matrix (Fin 4) (Fin 4) K) : IsPoly (fun l => planeEq n e (cv Φ l)) := by
  obtain ⟨tag, i, j, k, m⟩ := n
  fin_cases tag <;> fin_cases e
  · exact isPoly_cv Φ i
  · exact isPoly_cv Φ j
  · exact (isPoly_cv Φ i).add (isPoly_cv Φ k)
  · exact (isPoly_cv Φ j).sub (isPoly_cv Φ m)
  · exact (isPoly_cv Φ i).sub (isPoly_cv Φ m)
  · exact (isPoly_cv Φ j).sub (isPoly_cv Φ m)

/-- **Structure of a pencil whose slices are singular.** Let `Φ 0, Φ 1` be two forms such
that, for every `l` with nonzero coordinates, `σ(w) = 0` whenever
`Φ 0 (l, l * w) = Φ 1 (l, l * w) = 0`. Then two columns of both forms vanish, or both forms
lie in `span(alt_ab, s_cd)` for some splitting of the columns. -/
theorem weakS [CharZero K] (Φ : Fin 2 → Matrix (Fin 4) (Fin 4) K)
    (H : ∀ l : Fin 4 → K, (∀ i, l i ≠ 0) → ∀ w : Fin 4 → K, bil (Φ 0) l (l * w) = 0 →
      bil (Φ 1) l (l * w) = 0 → sig4 (w 0) (w 1) (w 2) (w 3) = 0) :
    (∃ i j : Fin 4, i ≠ j ∧ ∀ v p, Φ v p i = 0 ∧ Φ v p j = 0) ∨
      (∃ a b c d : Fin 4, D4 a b c d ∧ ∀ v, InPair a b c d (Φ v)) := by
  have : Infinite K := CharZero.infinite K
  have hstep : ∀ l : Fin 4 → K, (∀ i, l i ≠ 0) →
      ∃ n : Fin 3 × Fin 4 × Fin 4 × Fin 4 × Fin 4, D4 n.2.1 n.2.2.1 n.2.2.2.1 n.2.2.2.2 ∧
        ∀ ev : Fin 2 × Fin 2, planeEq n ev.1 (cv (Φ ev.2) l) = 0 := by
    intro l hl
    obtain ⟨n, hn, he⟩ := planes_of_sigma (cv (Φ 0) l) (cv (Φ 1) l)
      (fun w h0 h1 => H l hl w (by rwa [← dot4_cv]) (by rwa [← dot4_cv]))
    refine ⟨n, hn, fun ev => ?_⟩
    obtain ⟨e, v⟩ := ev
    fin_cases v
    · exact (he e).1
    · exact (he e).2
  obtain ⟨⟨tag, i, j, k, m⟩, hd, hn⟩ := poly_union
    (fun n : Fin 3 × Fin 4 × Fin 4 × Fin 4 × Fin 4 => D4 n.2.1 n.2.2.1 n.2.2.2.1 n.2.2.2.2)
    (fun n (ev : Fin 2 × Fin 2) l => planeEq n ev.1 (cv (Φ ev.2) l))
    (fun n ev => isPoly_planeEq n ev.1 (Φ ev.2)) hstep
  obtain ⟨hij, hik, him, hjk, hjm, hkm⟩ := hd
  fin_cases tag
  · left
    exact ⟨i, j, hij, fun v p => ⟨quad1 (Φ v) i (fun l => hn (0, v) l) p,
      quad1 (Φ v) j (fun l => hn (1, v) l) p⟩⟩
  · right
    refine ⟨i, k, j, m, ⟨hik, hij, him, hjk.symm, hkm, hjm⟩, fun v => ?_⟩
    obtain ⟨A1, A2, A3, A4⟩ := quad2 (Φ v) hik 1 1 (fun l => by
      have : cv (Φ v) l i + cv (Φ v) l k = 0 := hn (0, v) l
      linear_combination this)
    obtain ⟨B1, B2, B3, B4⟩ := quad2 (Φ v) hjm 1 (-1) (fun l => by
      have : cv (Φ v) l j - cv (Φ v) l m = 0 := hn (1, v) l
      linear_combination this)
    have Aj := A4 j hij.symm hjk
    have Am := A4 m him.symm hkm.symm
    have Bi := B4 i hij him
    have Bk := B4 k hjk.symm hkm
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination A1
    · linear_combination A2
    · linear_combination B1
    · linear_combination -B2
    · linear_combination A3
    · linear_combination B3
    · linear_combination Bi.1
    · linear_combination -Bi.2
    · linear_combination Bk.1
    · linear_combination -Bk.2
    · linear_combination Aj.1
    · linear_combination Aj.2
    · linear_combination Am.1
    · linear_combination Am.2
  · left
    refine ⟨i, j, hij, fun v => ?_⟩
    obtain ⟨A1, A2, A3, A4⟩ := quad2 (Φ v) him 1 (-1) (fun l => by
      have : cv (Φ v) l i - cv (Φ v) l m = 0 := hn (0, v) l
      linear_combination this)
    obtain ⟨B1, B2, B3, B4⟩ := quad2 (Φ v) hjm 1 (-1) (fun l => by
      have : cv (Φ v) l j - cv (Φ v) l m = 0 := hn (1, v) l
      linear_combination this)
    have Aj := A4 j hij.symm hjm
    have Ak := A4 k hik.symm hkm
    have Bi := B4 i hij him
    have Bk := B4 k hjk.symm hkm
    intro p
    rcases all_four ⟨hij, hik, him, hjk, hjm, hkm⟩ p with rfl | rfl | rfl | rfl
    · exact ⟨by linear_combination A1, by linear_combination Bi.1⟩
    · exact ⟨by linear_combination Aj.1, by linear_combination B1⟩
    · exact ⟨by linear_combination Ak.1, by linear_combination Bk.1⟩
    · exact ⟨by linear_combination A3 - Bi.2, by linear_combination B3 - Aj.2⟩

/-! ### The slice matrix and its determinant -/

/-- The slice matrix `B_w` of the permanent: `B_w x y = E3 w x y`. -/
def Bmat (w : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, w 2 + w 3, w 1 + w 3, w 1 + w 2; w 2 + w 3, 0, w 0 + w 3, w 0 + w 2;
    w 1 + w 3, w 0 + w 3, 0, w 0 + w 1; w 1 + w 2, w 0 + w 2, w 0 + w 1, 0]

lemma Bmat_apply (w : Fin 4 → K) (i j : Fin 4) :
    Bmat w i j = E3 w (Pi.single i 1) (Pi.single j 1) := by
  fin_cases i <;> fin_cases j <;> simp [Bmat, E3_eq]

lemma det_Bmat (w : Fin 4 → K) : (Bmat w).det = -4 * sig4 (w 0) (w 1) (w 2) (w 3) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Bmat, Fin.succAbove, Matrix.submatrix, sig4]
  ring

/-- If a nonzero multiple of `B_w` is a sum of fewer than four rank-one matrices, then
`σ(w) = 0`. -/
lemma sig_of_rank [CharZero K] (w : Fin 4 → K) {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι < 4) (c : K) (hc : c ≠ 0) (P Q : ι → Fin 4 → K)
    (h : ∀ i j : Fin 4, c * E3 w (Pi.single i 1) (Pi.single j 1) = ∑ t, P t i * Q t j) :
    sig4 (w 0) (w 1) (w 2) (w 3) = 0 := by
  have hdet := det_sum_rank_one_lt hι P Q
  have e : (Matrix.of fun i j : Fin 4 => ∑ t, P t i * Q t j) = c • Bmat w := by
    ext i j
    rw [Matrix.of_apply, ← h, Matrix.smul_apply, Bmat_apply, smul_eq_mul]
  rw [e, Matrix.det_smul, det_Bmat, Fintype.card_fin] at hdet
  have h4 : c ^ 4 * (-4 : K) ≠ 0 := mul_ne_zero (pow_ne_zero 4 hc) (by norm_num)
  have h' : c ^ 4 * (-4 : K) * sig4 (w 0) (w 1) (w 2) (w 3) = 0 := by linear_combination hdet
  exact (mul_eq_zero.mp h').resolve_left h4

lemma torus_prod_ne_zero {l : Fin 4 → K} (hl : ∀ i, l i ≠ 0) : l 0 * l 1 * l 2 * l 3 ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (hl 0) (hl 1)) (hl 2)) (hl 3)

/-- **Slices of a pencil.** In a decomposition with two terms on the pairing `01|23` and at
most three other terms, the pencil `F0 0, F0 1` satisfies the hypothesis of `weakS`. -/
lemma Dec4.pencil_sigma [CharZero K] {n1 n2 : ℕ} (hn : n1 + n2 < 4)
    {F0 G0 : Fin 2 → Matrix (Fin 4) (Fin 4) K} {F1 G1 : Fin n1 → Matrix (Fin 4) (Fin 4) K}
    {F2 G2 : Fin n2 → Matrix (Fin 4) (Fin 4) K} (h : Dec4 F0 G0 F1 G1 F2 G2)
    (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0) (w : Fin 4 → K) (h0 : bil (F0 0) l (l * w) = 0)
    (h1 : bil (F0 1) l (l * w) = 0) : sig4 (w 0) (w 1) (w 2) (w 3) = 0 := by
  refine sig_of_rank w (ι := Fin n1 ⊕ Fin n2) (by simpa using hn) (l 0 * l 1 * l 2 * l 3)
    (torus_prod_ne_zero hl)
    (Sum.elim (fun v i => bil (F1 v) l (l * Pi.single i 1))
      (fun v i => bil (G2 v) (l * w) (l * Pi.single i 1)))
    (Sum.elim (fun v j => bil (G1 v) (l * w) (l * Pi.single j 1))
      (fun v j => bil (F2 v) l (l * Pi.single j 1))) (fun i j => ?_)
  rw [← perm4_scale, h l (l * w) (l * Pi.single i 1) (l * Pi.single j 1), Fin.sum_univ_two, h0,
    h1, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zero_mul, add_zero, zero_add]
  congr 1
  exact Finset.sum_congr rfl fun v _ => mul_comm _ _

/-- **Kernel lemma on the torus.** Let `l` have nonzero coordinates and let the slice form
`perm4 l (l * w) · ·` be a sum of `r` rank-one forms `α t ⊗ β t`. If `B_w` has a nonzero
`r × r` minor and `z` is in the kernel of `B_w`, then all `α t` and `β t` vanish at `l * z`. -/
lemma scaled_kernel {r : ℕ} (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0) (w : Fin 4 → K)
    (α β : Fin r → (Fin 4 → K) → K) (hB : ∀ x y, perm4 l (l * w) x y = ∑ t, α t x * β t y)
    (p q : Fin r → Fin 4 → K) (hdet : Matrix.det (Matrix.of fun i j => E3 w (p i) (q j)) ≠ 0)
    (z : Fin 4 → K) (hz : ∀ y, E3 w z y = 0) (t : Fin r) : α t (l * z) = 0 ∧ β t (l * z) = 0 := by
  have hc := torus_prod_ne_zero hl
  have hdiv : ∀ y : Fin 4 → K, y = l * fun i => y i / l i := fun y => by
    funext i
    simp only [Pi.mul_apply]
    field_simp [hl i]
  have hker := kernel_of_minor (fun x y => perm4 l (l * w) x y) α β hB (fun i => l * p i)
    (fun j => l * q j) (by
      have e : (Matrix.of fun i j => perm4 l (l * w) (l * p i) (l * q j))
          = (l 0 * l 1 * l 2 * l 3) • Matrix.of fun i j => E3 w (p i) (q j) := by
        ext i j
        simp [perm4_scale]
      rw [e, Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ hc) hdet) (l * z)
  refine ⟨hker.1 (fun y => ?_) t, hker.2 (fun x => ?_) t⟩
  · show perm4 l (l * w) (l * z) y = 0
    rw [hdiv y, perm4_scale, hz, mul_zero]
  · show perm4 l (l * w) x (l * z) = 0
    rw [hdiv x, perm4_scale, E3_swap23, hz, mul_zero]

/-! ### Relabelling the columns -/

lemma exists_perm_of_D4 {a b c d : Fin 4} (hd : D4 a b c d) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = a ∧ σ 1 = b ∧ σ 2 = c ∧ σ 3 = d :=
  ⟨Equiv.ofBijective ![a, b, c, d]
    (Finite.injective_iff_bijective.mp ((injective_vec4_iff a b c d).mpr hd)), rfl, rfl, rfl, rfl⟩

lemma InPair.transpose {a b c d : Fin 4} {M : Matrix (Fin 4) (Fin 4) K}
    (h : InPair a b c d M) : InPair a b c d Mᵀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, ?_, h11, h13, h12, h14, h7, h9, h8, h10⟩
  · simp only [Matrix.transpose_apply]
    linear_combination h5
  · simp only [Matrix.transpose_apply]
    linear_combination -h6

/-- In a decomposition with two terms on the pairing `01|23` and at most three other terms,
after a relabelling of the columns either the columns `0, 1` of the pencil vanish or the
pencil lies in `span(alt_01, s_23)`. -/
theorem Dec4.pencil_cases [CharZero K] {n1 n2 : ℕ} (hn : n1 + n2 < 4)
    {F0 G0 : Fin 2 → Matrix (Fin 4) (Fin 4) K} {F1 G1 : Fin n1 → Matrix (Fin 4) (Fin 4) K}
    {F2 G2 : Fin n2 → Matrix (Fin 4) (Fin 4) K} (h : Dec4 F0 G0 F1 G1 F2 G2) :
    ∃ σ : Equiv.Perm (Fin 4),
      (∀ v p, (F0 v).submatrix σ σ p 0 = 0 ∧ (F0 v).submatrix σ σ p 1 = 0) ∨
      (∀ v, InPair 0 1 2 3 ((F0 v).submatrix σ σ)) := by
  rcases weakS F0 (fun l hl w h0 h1 => h.pencil_sigma hn l hl w h0 h1) with
    ⟨i, j, hij, hC⟩ | ⟨a, b, c, d, hd, hS⟩
  · obtain ⟨σ, h0, h1⟩ := exists_perm_01 i j hij
    refine ⟨σ, Or.inl fun v p => ?_⟩
    simp only [Matrix.submatrix_apply, h0, h1]
    exact hC v (σ p)
  · obtain ⟨σ, h0, h1, h2, h3⟩ := exists_perm_of_D4 hd
    refine ⟨σ, Or.inr fun v => ?_⟩
    simp only [InPair, Matrix.submatrix_apply, h0, h1, h2, h3]
    exact hS v

end Pencil

end PvsNP
