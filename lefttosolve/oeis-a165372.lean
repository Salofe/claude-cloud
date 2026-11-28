import OMAStatements.S_oeis_a165372

/-!
Proof of Barker's conjectures for A165372 (slanted n X 3 arrays with entries 1..4 whose four
value classes are connected, with 1, 2, 3, 4 in the four corners).

The cell `(i, k)` lies on the layer `2i + k`, and every edge of the array joins two consecutive
layers. The odd layer `2i + 1` holds only the middle cell `(i, 1)`, so a path inside one value
class meets the middle cell of every odd layer between its ends (`path_layers`, `key`). The
middle cells form the spine; the even layer `2i + 2` holds the side cells `(i + 1, 0)` and
`(i, 2)`, and both are adjacent exactly to the middle cells of rows `i` and `i + 1`.

For `n ≥ 3` this gives a local characterization (`char`): an array is counted iff its corners
are right, the spine never decreases, a step 1 → 2 along the spine happens only between rows
0 and 1, a step 3 → 4 only between rows n - 2 and n - 1, and every side cell that is not a
corner holds the value of one of its two middle neighbours. Counting spine by spine
(`a_eq_sum`), the side cells contribute a product of diamond weights, and the sum over spines
is a product of 4 × 4 transfer matrices: `Tf` for the first diamond, `Tm` for the inner ones,
`Tl` for the last one. The partial sums are (1, 3, 5 + 16t, 5 + 16t) (`Q_mid`), which gives
a(n) = 40 + 64 (n - 3) = 8 (8n - 19) for n ≥ 3 (`a_closed`). The 2 × 3 array is handled
directly (`a_two`): exactly the 9 arrays whose middle cells hold x ≠ 4 (top) and y ≠ 1 (bottom)
are counted. The generating function follows by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a165372 Finset

/-! ### Layers -/

/-- The layer of a cell: twice its row plus its position in the row. -/
def lay {n : ℕ} (u : Fin n × Fin 3) : ℕ := 2 * (u.1 : ℕ) + (u.2 : ℕ)

theorem adj_symm {n : ℕ} {u v : Fin n × Fin 3} (h : Adj u v) : Adj v u := by
  unfold Adj at *
  omega

theorem adj_lay {n : ℕ} {u v : Fin n × Fin 3} (h : Adj u v) :
    lay u + 1 = lay v ∨ lay v + 1 = lay u := by
  have h1 := u.2.isLt
  have h2 := v.2.isLt
  unfold Adj at h
  unfold lay
  omega

theorem rtg_symm {α : Type*} {r : α → α → Prop} (hr : ∀ a b, r a b → r b a) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hr _ _ hbc) ih

/-- A path inside one colour class meets every layer between its ends. -/
theorem path_layers {n : ℕ} {f : Fin n × Fin 3 → Fin 4} {c : Fin 4} {u v : Fin n × Fin 3}
    (h : Relation.ReflTransGen (fun x y => Adj x y ∧ f x = c ∧ f y = c) u v) (hu : f u = c) :
    ∀ p : ℕ, (lay u ≤ p ∧ p ≤ lay v) ∨ (lay v ≤ p ∧ p ≤ lay u) →
      ∃ w, f w = c ∧ lay w = p := by
  induction h with
  | refl =>
    intro p hp
    exact ⟨u, hu, by omega⟩
  | tail _ hbd ih =>
    rename_i b d _
    obtain ⟨had, _, hfd⟩ := hbd
    have hl := adj_lay had
    intro p hp
    by_cases hq : (lay u ≤ p ∧ p ≤ lay b) ∨ (lay b ≤ p ∧ p ≤ lay u)
    · exact ih p hq
    · exact ⟨d, hfd, by omega⟩

/-- The only cell of an odd layer `2m + 1` is the middle cell of row `m`. -/
theorem lay_odd {n : ℕ} {w : Fin n × Fin 3} {m : ℕ} (h : lay w = 2 * m + 1) :
    (w.1 : ℕ) = m ∧ w.2 = 1 := by
  have h1 := w.2.isLt
  unfold lay at h
  refine ⟨by omega, ?_⟩
  rw [Fin.ext_iff]
  simp only [Fin.val_one]
  omega

theorem lay_mid {n : ℕ} {m : ℕ} (hm : m < n) :
    lay ((⟨m, hm⟩ : Fin n), (1 : Fin 3)) = 2 * m + 1 := by
  simp [lay]

/-! ### Neighbours -/

theorem nbr0 {n : ℕ} {u w : Fin n × Fin 3} (hu : u.2 = 0) (h : Adj u w) :
    w.2 = 1 ∧ ((w.1 : ℕ) = u.1 ∨ (w.1 : ℕ) + 1 = u.1) := by
  have h1 := w.2.isLt
  have hu' : (u.2 : ℕ) = 0 := by rw [hu]; rfl
  unfold Adj at h
  have hw : (w.2 : ℕ) = 1 := by omega
  exact ⟨Fin.ext hw, by omega⟩

theorem nbr2 {n : ℕ} {u w : Fin n × Fin 3} (hu : u.2 = 2) (h : Adj u w) :
    w.2 = 1 ∧ ((w.1 : ℕ) = u.1 ∨ (w.1 : ℕ) = u.1 + 1) := by
  have h1 := w.2.isLt
  have hu' : (u.2 : ℕ) = 2 := by rw [hu]; rfl
  unfold Adj at h
  have hw : (w.2 : ℕ) = 1 := by omega
  exact ⟨Fin.ext hw, by omega⟩

theorem adj_01 {n i : ℕ} (hi : i < n) :
    Adj ((⟨i, hi⟩ : Fin n), (0 : Fin 3)) (⟨i, hi⟩, 1) := by
  unfold Adj
  simp

theorem adj_12 {n i : ℕ} (hi : i < n) :
    Adj ((⟨i, hi⟩ : Fin n), (1 : Fin 3)) (⟨i, hi⟩, 2) := by
  unfold Adj
  simp

theorem adj_v0 {n i : ℕ} (hi : i < n) (hi' : i + 1 < n) :
    Adj ((⟨i, hi⟩ : Fin n), (1 : Fin 3)) (⟨i + 1, hi'⟩, 0) := by
  unfold Adj
  simp

theorem adj_v2 {n i : ℕ} (hi : i < n) (hi' : i + 1 < n) :
    Adj ((⟨i, hi⟩ : Fin n), (2 : Fin 3)) (⟨i + 1, hi'⟩, 1) := by
  unfold Adj
  simp only [Fin.val_two, Fin.val_one, Nat.cast_ofNat, Nat.cast_one, Nat.cast_add]
  omega

theorem adj_v0' {n i j : ℕ} (hi : i < n) (hj : j < n) (hij : j = i + 1) :
    Adj ((⟨i, hi⟩ : Fin n), (1 : Fin 3)) (⟨j, hj⟩, 0) := by
  subst hij
  exact adj_v0 hi hj

theorem adj_v2' {n i j : ℕ} (hi : i < n) (hj : j < n) (hij : j = i + 1) :
    Adj ((⟨i, hi⟩ : Fin n), (2 : Fin 3)) (⟨j, hj⟩, 1) := by
  subst hij
  exact adj_v2 hi hj

theorem fin4_cases : ∀ c : Fin 4, c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by decide

theorem fin3_cases : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide

/-! ### Spine and corners -/

/-- The colours along a spine, indexed by `ℕ` (0 outside the array). -/
def g {n : ℕ} (s : Fin n → Fin 4) (m : ℕ) : Fin 4 := if h : m < n then s ⟨m, h⟩ else 0

/-- The spine of an array: its middle cells. -/
def sp {n : ℕ} (f : Fin n × Fin 3 → Fin 4) : Fin n → Fin 4 := fun i => f (i, 1)

theorem g_sp {n : ℕ} (f : Fin n × Fin 3 → Fin 4) {m : ℕ} (hm : m < n) :
    g (sp f) m = f (⟨m, hm⟩, 1) := by
  simp [g, sp, hm]

theorem g_sp_of {n : ℕ} (f : Fin n × Fin 3 → Fin 4) {w : Fin n × Fin 3} (hw : w.2 = 1) :
    g (sp f) (w.1 : ℕ) = f w := by
  obtain ⟨w1, w2⟩ := w
  simp only at hw
  subst hw
  simp [g, sp]

/-- The corner holding the colour `c`. -/
def K {n : ℕ} (hn : 0 < n) (c : Fin 4) : Fin n × Fin 3 :=
  (⟨if (c : ℕ) < 2 then 0 else n - 1, by split_ifs <;> omega⟩,
    if (c : ℕ) % 2 = 0 then 0 else 2)

theorem K_val {n : ℕ} (hn : 0 < n) {f : Fin n × Fin 3 → Fin 4} (h : CornersOK f) (c : Fin 4) :
    f (K hn c) = c := by
  have hc := h (K hn c)
  fin_cases c <;> simp [K] at hc ⊢ <;> tauto

theorem lay_K {n : ℕ} (hn : 0 < n) (c : Fin 4) :
    lay (K hn c) =
      (if (c : ℕ) < 2 then 0 else 2 * n - 2) + (if (c : ℕ) % 2 = 0 then 0 else 2) := by
  simp only [lay, K]
  split_ifs <;> simp <;> omega

theorem K0 {n : ℕ} (hn : 0 < n) : K hn 0 = (⟨0, hn⟩, 0) := rfl

theorem K1 {n : ℕ} (hn : 0 < n) : K hn 1 = (⟨0, hn⟩, 2) := rfl

theorem K2 {n : ℕ} (hn : 0 < n) : K hn 2 = (⟨n - 1, by omega⟩, 0) := rfl

theorem K3 {n : ℕ} (hn : 0 < n) : K hn 3 = (⟨n - 1, by omega⟩, 2) := rfl

theorem K_row {n : ℕ} (hn : 0 < n) (c : Fin 4) :
    ((K hn c).1 : ℕ) = 0 ∨ ((K hn c).1 : ℕ) = n - 1 := by
  simp only [K]
  split_ifs <;> simp

/-- Two cells of the same colour joined inside their class: the middle cell of every odd layer
between them has that colour too. -/
theorem key {n : ℕ} {f : Fin n × Fin 3 → Fin 4} (hconn : ∀ c, ClassConnected f c) {c : Fin 4}
    {u v : Fin n × Fin 3} (hu : f u = c) (hv : f v = c) {m : ℕ} (hm : m < n)
    (h1 : lay u ≤ 2 * m + 1) (h2 : 2 * m + 1 ≤ lay v) : f (⟨m, hm⟩, 1) = c := by
  obtain ⟨w, hw, hlw⟩ := path_layers (hconn c u v hu hv) hu (2 * m + 1) (Or.inl ⟨h1, h2⟩)
  obtain ⟨h3, h4⟩ := lay_odd hlw
  have hw' : w = (⟨m, hm⟩, 1) := Prod.ext (Fin.ext h3) h4
  rw [← hw']
  exact hw

theorem K_sep {n : ℕ} (hn : 3 ≤ n) (hn0 : 0 < n) {x y : Fin 4} (hxy : y < x) {m : ℕ}
    (hm : m + 1 < n) :
    lay (K hn0 y) ≤ 2 * m + 1 ∨ 2 * (m + 1) + 1 ≤ lay (K hn0 x) := by
  rw [lay_K, lay_K]
  fin_cases x <;> fin_cases y <;> simp at hxy ⊢ <;> omega

/-! ### The local conditions -/

/-- The allowed pairs of consecutive spine colours at the diamond after row `m`. -/
def ok (n m : ℕ) (x y : Fin 4) : Prop :=
  x ≤ y ∧ (1 ≤ m → ¬ (x = 0 ∧ y = 1)) ∧ (m + 3 ≤ n → ¬ (x = 2 ∧ y = 3))

instance ok_dec (n m : ℕ) (x y : Fin 4) : Decidable (ok n m x y) := by
  unfold ok
  infer_instance

/-- A spine all of whose consecutive pairs are allowed. -/
def Good {n : ℕ} (s : Fin n → Fin 4) : Prop :=
  ∀ m : ℕ, m + 1 < n → ok n m (g s m) (g s (m + 1))

/-- The allowed colours of a cell, given the spine. -/
def A {n : ℕ} (s : Fin n → Fin 4) (u : Fin n × Fin 3) : Finset (Fin 4) :=
  if u.2 = 1 then {g s u.1}
  else if (u.1 : ℕ) = 0 then (if u.2 = 0 then {0} else {1})
  else if (u.1 : ℕ) = n - 1 then (if u.2 = 0 then {2} else {3})
  else if u.2 = 0 then {g s ((u.1 : ℕ) - 1), g s u.1}
  else {g s u.1, g s ((u.1 : ℕ) + 1)}

/-! ### Forward direction -/

section forward

variable {n : ℕ} {f : Fin n × Fin 3 → Fin 4}

theorem fwd_mono (hn : 3 ≤ n) (hf : IsCounted f) {m : ℕ} (hm : m + 1 < n) :
    g (sp f) m ≤ g (sp f) (m + 1) := by
  obtain ⟨hconn, hcor⟩ := hf
  have hn0 : 0 < n := by omega
  have hm0 : m < n := by omega
  rw [g_sp f hm0, g_sp f hm]
  by_contra hlt
  rw [not_le] at hlt
  rcases K_sep hn hn0 hlt hm with h | h
  · have := key hconn (K_val hn0 hcor _) rfl hm0 h (by rw [lay_mid]; omega)
    exact absurd this (ne_of_gt hlt)
  · have := key hconn rfl (K_val hn0 hcor _) hm (by rw [lay_mid]; omega) h
    exact absurd this (ne_of_lt hlt)

theorem fwd_12 (hn : 3 ≤ n) (hf : IsCounted f) {m : ℕ} (hm : m + 1 < n) (h1 : 1 ≤ m) :
    ¬ (g (sp f) m = 0 ∧ g (sp f) (m + 1) = 1) := by
  obtain ⟨hconn, hcor⟩ := hf
  have hn0 : 0 < n := by omega
  have hm0 : m < n := by omega
  rw [g_sp f hm0, g_sp f hm]
  rintro ⟨h0, h1'⟩
  have := key hconn (K_val hn0 hcor 1) h1' hm0 (by rw [lay_K]; simp; omega)
    (by rw [lay_mid]; omega)
  rw [h0] at this
  exact absurd this (by decide)

theorem fwd_34 (hn : 3 ≤ n) (hf : IsCounted f) {m : ℕ} (hm : m + 1 < n) (h3 : m + 3 ≤ n) :
    ¬ (g (sp f) m = 2 ∧ g (sp f) (m + 1) = 3) := by
  obtain ⟨hconn, hcor⟩ := hf
  have hn0 : 0 < n := by omega
  have hm0 : m < n := by omega
  rw [g_sp f hm0, g_sp f hm]
  rintro ⟨h2, h3'⟩
  have := key hconn h2 (K_val hn0 hcor 2) hm (by rw [lay_mid]; omega)
    (by rw [lay_K]; simp; omega)
  rw [h3'] at this
  exact absurd this (by decide)

theorem fwd_good (hn : 3 ≤ n) (hf : IsCounted f) : Good (sp f) :=
  fun _ hm => ⟨fwd_mono hn hf hm, fun h1 => fwd_12 hn hf hm h1, fun h3 => fwd_34 hn hf hm h3⟩

theorem not_K (hn0 : 0 < n) (u : Fin n × Fin 3) (h1 : 1 ≤ (u.1 : ℕ))
    (h2 : (u.1 : ℕ) + 2 ≤ n) (c : Fin 4) : u ≠ K hn0 c := by
  intro h
  have := K_row hn0 c
  rw [← h] at this
  omega

/-- A side cell that is not a corner has the colour of one of its two middle neighbours. -/
theorem fwd_side (hn : 3 ≤ n) (hf : IsCounted f) (u : Fin n × Fin 3) (hu : u.2 ≠ 1)
    (h1 : 1 ≤ (u.1 : ℕ)) (h2 : (u.1 : ℕ) + 2 ≤ n) :
    ∃ b : Fin n × Fin 3, Adj u b ∧ b.2 = 1 ∧ f b = f u := by
  obtain ⟨hconn, hcor⟩ := hf
  have hn0 : 0 < n := by omega
  have hr := hconn (f u) u (K hn0 (f u)) rfl (K_val hn0 hcor _)
  rcases hr.cases_head with h | ⟨b, ⟨hab, _, hfb⟩, _⟩
  · exact absurd h (not_K hn0 u h1 h2 _)
  · refine ⟨b, hab, ?_, hfb⟩
    have h3 := u.2.isLt
    have h4 : (u.2 : ℕ) ≠ 1 := fun h => hu (Fin.ext h)
    rcases Nat.lt_or_ge (u.2 : ℕ) 1 with h5 | h5
    · exact (nbr0 (Fin.ext (by simp; omega)) hab).1
    · exact (nbr2 (Fin.ext (by simp; omega)) hab).1

theorem fwd_A (hn : 3 ≤ n) (hf : IsCounted f) (u : Fin n × Fin 3) : f u ∈ A (sp f) u := by
  have hcor := hf.2 u
  have hk := u.2.isLt
  unfold A
  split_ifs with h1 h2 h3 h4 h5 h6
  · rw [mem_singleton, g_sp_of f h1]
  · rw [mem_singleton]; exact hcor.1 h2 h3
  · have h3' : u.2 = 2 := Fin.ext (by
      have := fun h => h1 (Fin.ext h)
      have := fun h => h3 (Fin.ext h)
      simp at *; omega)
    rw [mem_singleton]; exact hcor.2.1 h2 h3'
  · rw [mem_singleton]; exact hcor.2.2.1 h4 h5
  · have h5' : u.2 = 2 := Fin.ext (by
      have := fun h => h1 (Fin.ext h)
      have := fun h => h5 (Fin.ext h)
      simp at *; omega)
    rw [mem_singleton]; exact hcor.2.2.2 h4 h5'
  · have hu1 : 1 ≤ (u.1 : ℕ) := by omega
    have hu2 : (u.1 : ℕ) + 2 ≤ n := by have := u.1.isLt; omega
    obtain ⟨b, hab, hb1, hfb⟩ := fwd_side hn hf u h1 hu1 hu2
    have hgb := g_sp_of f hb1
    rw [hfb] at hgb
    rw [mem_insert, mem_singleton, ← hgb]
    rcases (nbr0 h6 hab).2 with h | h
    · right; rw [h]
    · left; rw [← h, Nat.add_sub_cancel]
  · have hu1 : 1 ≤ (u.1 : ℕ) := by omega
    have hu2 : (u.1 : ℕ) + 2 ≤ n := by have := u.1.isLt; omega
    have h6' : u.2 = 2 := Fin.ext (by
      have := fun h => h1 (Fin.ext h)
      have := fun h => h6 (Fin.ext h)
      simp at *; omega)
    obtain ⟨b, hab, hb1, hfb⟩ := fwd_side hn hf u h1 hu1 hu2
    have hgb := g_sp_of f hb1
    rw [hfb] at hgb
    rw [mem_insert, mem_singleton, ← hgb]
    rcases (nbr2 h6' hab).2 with h | h
    · left; rw [h]
    · right; rw [h]

end forward

/-! ### Backward direction -/

/-- Adjacent cells both holding `c`. -/
def R {n : ℕ} (f : Fin n × Fin 3 → Fin 4) (c : Fin 4) (x y : Fin n × Fin 3) : Prop :=
  Adj x y ∧ f x = c ∧ f y = c

theorem R_symm {n : ℕ} {f : Fin n × Fin 3 → Fin 4} {c : Fin 4} :
    ∀ a b, R f c a b → R f c b a :=
  fun _ _ ⟨h1, h2, h3⟩ => ⟨adj_symm h1, h3, h2⟩

section backward

variable {n : ℕ} {f : Fin n × Fin 3 → Fin 4}

theorem bwd_corner (hn : 3 ≤ n) (hA : ∀ u, f u ∈ A (sp f) u) : CornersOK f := by
  intro u
  have h := hA u
  unfold A at h
  have hn1 : n - 1 ≠ 0 := by omega
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · rw [if_neg (by rw [h2]; decide), if_pos h1, if_pos h2] at h
    exact mem_singleton.1 h
  · rw [if_neg (by rw [h2]; decide), if_pos h1, if_neg (by rw [h2]; decide)] at h
    exact mem_singleton.1 h
  · rw [if_neg (by rw [h2]; decide), if_neg (by rw [h1]; exact hn1), if_pos h1, if_pos h2] at h
    exact mem_singleton.1 h
  · rw [if_neg (by rw [h2]; decide), if_neg (by rw [h1]; exact hn1), if_pos h1,
      if_neg (by rw [h2]; decide)] at h
    exact mem_singleton.1 h

theorem bwd_side0 (hA : ∀ u, f u ∈ A (sp f) u) {i : ℕ} (hi : i < n) (h1 : 1 ≤ i)
    (h2 : i + 2 ≤ n) :
    f (⟨i, hi⟩, 0) = g (sp f) (i - 1) ∨ f (⟨i, hi⟩, 0) = g (sp f) i := by
  have h := hA (⟨i, hi⟩, 0)
  unfold A at h
  rw [if_neg (by simp), if_neg (by simp; omega), if_neg (by simp; omega), if_pos rfl] at h
  simpa using h

theorem bwd_side2 (hA : ∀ u, f u ∈ A (sp f) u) {i : ℕ} (hi : i < n) (h1 : 1 ≤ i)
    (h2 : i + 2 ≤ n) :
    f (⟨i, hi⟩, 2) = g (sp f) i ∨ f (⟨i, hi⟩, 2) = g (sp f) (i + 1) := by
  have h := hA (⟨i, hi⟩, 2)
  unfold A at h
  rw [if_neg (by simp), if_neg (by simp; omega), if_neg (by simp; omega), if_neg (by simp)] at h
  simpa using h

theorem bwd_mono (hG : Good (sp f)) {a b : ℕ} (hab : a ≤ b) (hb : b < n) :
    g (sp f) a ≤ g (sp f) b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => exact le_trans (ih (by omega)) (hG b hb).1

theorem diamond (hn : 3 ≤ n) (hA : ∀ u, f u ∈ A (sp f) u) {c : Fin 4} {b : ℕ} (hb : b < n)
    (hb' : b + 1 < n) (h1 : g (sp f) b = c) (h2 : g (sp f) (b + 1) = c) :
    Relation.ReflTransGen (R f c) (⟨b, hb⟩, 1) (⟨b + 1, hb'⟩, 1) := by
  by_cases hb3 : b + 3 ≤ n
  · have hs := bwd_side0 hA hb' (by omega) (by omega)
    rw [Nat.add_sub_cancel, h1, h2, or_self] at hs
    rw [g_sp f hb] at h1
    rw [g_sp f hb'] at h2
    exact Relation.ReflTransGen.head ⟨adj_v0 hb hb', h1, hs⟩
      (Relation.ReflTransGen.single ⟨adj_01 hb', hs, h2⟩)
  · have hs := bwd_side2 hA hb (by omega) (by omega)
    rw [h1, h2, or_self] at hs
    rw [g_sp f hb] at h1
    rw [g_sp f hb'] at h2
    exact Relation.ReflTransGen.head ⟨adj_12 hb, h1, hs⟩
      (Relation.ReflTransGen.single ⟨adj_v2 hb hb', hs, h2⟩)

theorem chain (hn : 3 ≤ n) (hG : Good (sp f)) (hA : ∀ u, f u ∈ A (sp f) u) {c : Fin 4}
    {a : ℕ} (ha : a < n) (hca : g (sp f) a = c) :
    ∀ b (hb : b < n), a ≤ b → g (sp f) b = c →
      Relation.ReflTransGen (R f c) (⟨a, ha⟩, 1) (⟨b, hb⟩, 1) := by
  intro b
  induction b with
  | zero =>
    intro hb hab _
    have : a = 0 := by omega
    subst this
    exact Relation.ReflTransGen.refl
  | succ b ih =>
    intro hb hab hcb
    rcases Nat.eq_or_lt_of_le hab with h | h
    · subst h
      exact Relation.ReflTransGen.refl
    · have hbn : b < n := by omega
      have hcb' : g (sp f) b = c := by
        apply le_antisymm
        · rw [← hcb]; exact (hG b hb).1
        · rw [← hca]; exact bwd_mono hG (by omega) hbn
      exact (ih hbn (by omega) hcb').trans (diamond hn hA hbn hb hcb' hcb)

theorem chain' (hn : 3 ≤ n) (hG : Good (sp f)) (hA : ∀ u, f u ∈ A (sp f) u) {c : Fin 4}
    {a b : ℕ} (ha : a < n) (hb : b < n) (hca : g (sp f) a = c) (hcb : g (sp f) b = c) :
    Relation.ReflTransGen (R f c) (⟨a, ha⟩, 1) (⟨b, hb⟩, 1) := by
  rcases le_total a b with h | h
  · exact chain hn hG hA ha hca b hb h hcb
  · exact rtg_symm R_symm (chain hn hG hA hb hcb a ha h hca)

theorem down1 (hG : Good (sp f)) :
    ∀ t, 1 ≤ t → t < n → g (sp f) t = 1 → g (sp f) 1 = 1 := by
  intro t
  induction t with
  | zero => intro h; omega
  | succ t ih =>
    intro h1 ht h
    rcases Nat.eq_or_lt_of_le h1 with h' | h'
    · rw [h']; exact h
    · have hok := hG t ht
      rw [h] at hok
      obtain ⟨hle, h12, _⟩ := hok
      have hne : g (sp f) t ≠ 0 := fun h0 => h12 (by omega) ⟨h0, rfl⟩
      have key : ∀ x : Fin 4, x ≤ 1 → x ≠ 0 → x = 1 := by decide
      exact ih (by omega) (by omega) (key _ hle hne)

theorem up2 (hG : Good (sp f)) :
    ∀ d t, t + 2 + d = n → g (sp f) t = 2 → g (sp f) (n - 2) = 2 := by
  intro d
  induction d with
  | zero =>
    intro t ht h
    rw [show n - 2 = t by omega]
    exact h
  | succ d ih =>
    intro t ht h
    have hok := hG t (by omega)
    rw [h] at hok
    obtain ⟨hle, _, h34⟩ := hok
    have hne : g (sp f) (t + 1) ≠ 3 := fun h3 => h34 (by omega) ⟨rfl, h3⟩
    have key : ∀ x : Fin 4, 2 ≤ x → x ≠ 3 → x = 2 := by decide
    exact ih (t + 1) (by omega) (key _ hle hne)

theorem spine_corner (hn : 3 ≤ n) (hn0 : 0 < n) (hG : Good (sp f))
    (hA : ∀ u, f u ∈ A (sp f) u) {j : ℕ} (hj : j < n) {c : Fin 4} (hc : g (sp f) j = c) :
    Relation.ReflTransGen (R f c) (⟨j, hj⟩, 1) (K hn0 c) := by
  have hcor := bwd_corner hn hA
  have hKc := K_val hn0 hcor c
  rcases fin4_cases c with rfl | rfl | rfl | rfl
  · have hs : g (sp f) 0 = 0 := by
      have := bwd_mono hG (Nat.zero_le j) hj
      rw [hc] at this
      have key : ∀ x : Fin 4, x ≤ 0 → x = 0 := by decide
      exact key _ this
    refine (chain' hn hG hA hj hn0 hc hs).tail ⟨?_, ?_, hKc⟩
    · rw [K0]; exact adj_symm (adj_01 hn0)
    · rw [← g_sp f hn0]; exact hs
  · by_cases hj0 : j = 0
    · subst hj0
      refine Relation.ReflTransGen.single ⟨?_, ?_, hKc⟩
      · rw [K1]; exact adj_12 hj
      · rw [← g_sp f hj]; exact hc
    · have h1n : 1 < n := by omega
      have hs : g (sp f) 1 = 1 := down1 hG j (by omega) hj hc
      refine (chain' hn hG hA hj h1n hc hs).tail ⟨?_, ?_, hKc⟩
      · rw [K1]; exact adj_symm (adj_v2' hn0 h1n rfl)
      · rw [← g_sp f h1n]; exact hs
  · by_cases hjn : j = n - 1
    · subst hjn
      refine Relation.ReflTransGen.single ⟨?_, ?_, hKc⟩
      · rw [K2]; exact adj_symm (adj_01 hj)
      · rw [← g_sp f hj]; exact hc
    · have hn2 : n - 2 < n := by omega
      have hs : g (sp f) (n - 2) = 2 := up2 hG (n - 2 - j) j (by omega) hc
      refine (chain' hn hG hA hj hn2 hc hs).tail ⟨?_, ?_, hKc⟩
      · rw [K2]; exact adj_v0' hn2 _ (by omega)
      · rw [← g_sp f hn2]; exact hs
  · have hn1 : n - 1 < n := by omega
    have hs : g (sp f) (n - 1) = 3 := by
      have := bwd_mono hG (show j ≤ n - 1 by omega) hn1
      rw [hc] at this
      have key : ∀ x : Fin 4, 3 ≤ x → x = 3 := by decide
      exact key _ this
    refine (chain' hn hG hA hj hn1 hc hs).tail ⟨?_, ?_, hKc⟩
    · rw [K3]; exact adj_12 hn1
    · rw [← g_sp f hn1]; exact hs

theorem cell_corner (hn : 3 ≤ n) (hn0 : 0 < n) (hG : Good (sp f))
    (hA : ∀ u, f u ∈ A (sp f) u) (w : Fin n × Fin 3) :
    Relation.ReflTransGen (R f (f w)) w (K hn0 (f w)) := by
  have hcor := bwd_corner hn hA
  obtain ⟨⟨i, hi⟩, k⟩ := w
  rcases fin3_cases k with rfl | rfl | rfl
  · by_cases hi0 : i = 0
    · subst hi0
      have h00 : f (⟨0, hi⟩, 0) = 0 := (hcor _).1 rfl rfl
      rw [h00, K0]
    · by_cases hin : i = n - 1
      · subst hin
        have h10 : f (⟨n - 1, hi⟩, 0) = 2 := (hcor _).2.2.1 rfl rfl
        rw [h10, K2]
      · have hi1 : i - 1 < n := by omega
        rcases bwd_side0 hA hi (by omega) (by omega) with h | h
        · refine Relation.ReflTransGen.head ⟨?_, rfl, ?_⟩
            (spine_corner hn hn0 hG hA hi1 h.symm)
          · exact adj_symm (adj_v0' hi1 hi (by omega))
          · rw [← g_sp f hi1]; exact h.symm
        · refine Relation.ReflTransGen.head ⟨adj_01 hi, rfl, ?_⟩
            (spine_corner hn hn0 hG hA hi h.symm)
          rw [← g_sp f hi]; exact h.symm
  · exact spine_corner hn hn0 hG hA hi (g_sp f hi)
  · by_cases hi0 : i = 0
    · subst hi0
      have h02 : f (⟨0, hi⟩, 2) = 1 := (hcor _).2.1 rfl rfl
      rw [h02, K1]
    · by_cases hin : i = n - 1
      · subst hin
        have h12 : f (⟨n - 1, hi⟩, 2) = 3 := (hcor _).2.2.2 rfl rfl
        rw [h12, K3]
      · have hi1 : i + 1 < n := by omega
        rcases bwd_side2 hA hi (by omega) (by omega) with h | h
        · refine Relation.ReflTransGen.head ⟨adj_symm (adj_12 hi), rfl, ?_⟩
            (spine_corner hn hn0 hG hA hi h.symm)
          rw [← g_sp f hi]; exact h.symm
        · refine Relation.ReflTransGen.head ⟨adj_v2 hi hi1, rfl, ?_⟩
            (spine_corner hn hn0 hG hA hi1 h.symm)
          rw [← g_sp f hi1]; exact h.symm

theorem bwd_conn (hn : 3 ≤ n) (hG : Good (sp f)) (hA : ∀ u, f u ∈ A (sp f) u) :
    ∀ c, ClassConnected f c := by
  intro c u v hu hv
  have hn0 : 0 < n := by omega
  have h1 := cell_corner hn hn0 hG hA u
  have h2 := cell_corner hn hn0 hG hA v
  rw [hu] at h1
  rw [hv] at h2
  exact h1.trans (rtg_symm R_symm h2)

end backward

/-- The local characterization of the counted arrays, for `n ≥ 3`. -/
theorem char {n : ℕ} (hn : 3 ≤ n) (f : Fin n × Fin 3 → Fin 4) :
    IsCounted f ↔ Good (sp f) ∧ ∀ u, f u ∈ A (sp f) u :=
  ⟨fun hf => ⟨fwd_good hn hf, fwd_A hn hf⟩,
    fun ⟨hG, hA⟩ => ⟨bwd_conn hn hG hA, bwd_corner hn hA⟩⟩

/-! ### Counting the arrays with a given spine -/

/-- The number of colours among `x, y`. -/
def D (x y : Fin 4) : ℕ := ({x, y} : Finset (Fin 4)).card

theorem D_eq (x y : Fin 4) : D x y = if x = y then 1 else 2 := by
  unfold D
  split_ifs with h
  · subst h
    simp
  · exact card_pair h

/-- The weight of the diamond after row `m`: zero for a forbidden pair of spine colours,
otherwise the number of colourings of its side cells that are not corners. -/
def W (n m : ℕ) (x y : Fin 4) : ℕ :=
  if ok n m x y then (if m + 2 = n then 1 else D x y) * (if m = 0 then 1 else D x y) else 0

/-- The number of allowed colours of the cell `(i, 0)`. -/
def a0 {n : ℕ} (s : Fin n → Fin 4) (i : ℕ) : ℕ :=
  if i = 0 then 1 else if i = n - 1 then 1 else D (g s (i - 1)) (g s i)

/-- The number of allowed colours of the cell `(i, 2)`. -/
def a2 {n : ℕ} (s : Fin n → Fin 4) (i : ℕ) : ℕ :=
  if i = 0 then 1 else if i = n - 1 then 1 else D (g s i) (g s (i + 1))

theorem card_A0 {n : ℕ} (s : Fin n → Fin 4) (i : Fin n) : (A s (i, 0)).card = a0 s i := by
  unfold A a0
  rw [if_neg (by simp)]
  dsimp only
  split_ifs <;> first | rfl | simp_all

theorem card_A1 {n : ℕ} (s : Fin n → Fin 4) (i : Fin n) : (A s (i, 1)).card = 1 := by
  unfold A
  rw [if_pos rfl]
  rfl

theorem card_A2 {n : ℕ} (s : Fin n → Fin 4) (i : Fin n) : (A s (i, 2)).card = a2 s i := by
  unfold A a2
  rw [if_neg (by simp)]
  dsimp only
  split_ifs <;> first | rfl | simp_all

theorem prod_A {n : ℕ} (hn : 3 ≤ n) (s : Fin n → Fin 4) :
    ∏ u, (A s u).card = ∏ m ∈ range (n - 1),
      (if m + 2 = n then 1 else D (g s m) (g s (m + 1))) *
        (if m = 0 then 1 else D (g s m) (g s (m + 1))) := by
  rw [Fintype.prod_prod_type]
  simp only [Fin.prod_univ_three, card_A0, card_A1, card_A2, mul_one]
  rw [prod_mul_distrib, Fin.prod_univ_eq_prod_range (a0 s) n,
    Fin.prod_univ_eq_prod_range (a2 s) n]
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, prod_range_succ', prod_range_succ]
  have e0 : a0 s 0 = 1 := by simp [a0]
  have eN : a2 s N = 1 := by simp [a2]
  rw [e0, eN, mul_one, mul_one, ← prod_mul_distrib]
  refine prod_congr rfl (fun m hm => ?_)
  rw [mem_range] at hm
  simp only [a0, a2, Nat.add_sub_cancel]
  rw [if_neg (by omega : m + 1 ≠ 0), if_neg (by omega : m ≠ N)]
  congr 1
  by_cases h : m + 1 = N
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem prod_W_good {n : ℕ} (hn : 3 ≤ n) (s : Fin n → Fin 4) (hG : Good s) :
    ∏ u, (A s u).card = ∏ m ∈ range (n - 1), W n m (g s m) (g s (m + 1)) := by
  rw [prod_A hn s]
  refine prod_congr rfl (fun m hm => ?_)
  rw [mem_range] at hm
  rw [W, if_pos (hG m (by omega))]

theorem prod_W_bad {n : ℕ} (s : Fin n → Fin 4) (hG : ¬ Good s) :
    ∏ m ∈ range (n - 1), W n m (g s m) (g s (m + 1)) = 0 := by
  by_contra hne
  apply hG
  intro m hm
  by_contra hok
  exact hne (prod_eq_zero (i := m) (mem_range.2 (by omega)) (by rw [W, if_neg hok]))

theorem sp_of_mem {n : ℕ} {f : Fin n × Fin 3 → Fin 4} {s : Fin n → Fin 4}
    (h : ∀ u, f u ∈ A s u) : sp f = s := by
  funext i
  have h1 := h (i, 1)
  unfold A at h1
  rw [if_pos rfl, mem_singleton] at h1
  show f (i, 1) = s i
  rw [h1]
  simp [g]

/-- For `n ≥ 3`, the count is a sum over spines of products of diamond weights. -/
theorem a_eq_sum {n : ℕ} (hn : 3 ≤ n) :
    a n = ∑ s : Fin n → Fin 4, ∏ m ∈ range (n - 1), W n m (g s m) (g s (m + 1)) := by
  classical
  have h1 : a n = (univ.filter (fun f : Fin n × Fin 3 → Fin 4 => IsCounted f)).card := by
    unfold a
    rw [Fintype.card_subtype]
  rw [h1, card_eq_sum_card_fiberwise (f := sp) (t := univ) (fun _ _ => mem_univ _)]
  refine sum_congr rfl (fun s _ => ?_)
  by_cases hG : Good s
  · rw [← prod_W_good hn s hG, ← Fintype.card_piFinset]
    congr 1
    ext f
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hf, rfl⟩
      exact ((char hn f).1 hf).2
    · intro hf
      have hs := sp_of_mem hf
      subst hs
      exact ⟨(char hn f).2 ⟨hG, hf⟩, rfl⟩
  · rw [prod_W_bad s hG, card_eq_zero, filter_eq_empty_iff]
    intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    rintro rfl
    exact hG ((char hn f).1 hf).1

/-! ### The transfer recursion along the spine -/

/-- The weighted number of spines of length `j + 1` ending with the colour `y`. -/
def Q (n j : ℕ) (y : Fin 4) : ℕ :=
  ∑ s : Fin (j + 1) → Fin 4,
    if s (Fin.last j) = y then ∏ m ∈ range j, W n m (g s m) (g s (m + 1)) else 0

theorem g_snoc {j : ℕ} (s : Fin (j + 1) → Fin 4) (z : Fin 4) {m : ℕ} (hm : m < j + 1) :
    g (Fin.snoc s z : Fin (j + 2) → Fin 4) m = g s m := by
  rw [g, dif_pos (by omega : m < j + 2), g, dif_pos hm]
  exact Fin.snoc_castSucc (α := fun _ => Fin 4) (p := s) (x := z) (i := ⟨m, hm⟩)

theorem g_snoc_last {j : ℕ} (s : Fin (j + 1) → Fin 4) (z : Fin 4) :
    g (Fin.snoc s z : Fin (j + 2) → Fin 4) (j + 1) = z := by
  rw [g, dif_pos (by omega : j + 1 < j + 2)]
  exact Fin.snoc_last (α := fun _ => Fin 4) (p := s) (x := z)

theorem g_last {j : ℕ} (s : Fin (j + 1) → Fin 4) : g s j = s (Fin.last j) := by
  rw [g, dif_pos (by omega : j < j + 1)]
  rfl

theorem sum_Q (n j : ℕ) :
    ∑ s : Fin (j + 1) → Fin 4, ∏ m ∈ range j, W n m (g s m) (g s (m + 1)) =
      ∑ y, Q n j y := by
  unfold Q
  rw [sum_comm]
  refine sum_congr rfl (fun s _ => ?_)
  rw [sum_ite_eq]
  simp

theorem Q_zero (n : ℕ) (y : Fin 4) : Q n 0 y = 1 := by
  unfold Q
  simp only [range_zero, prod_empty]
  rw [← (Equiv.funUnique (Fin 1) (Fin 4)).symm.sum_comp]
  simp

theorem Q_succ (n j : ℕ) (y : Fin 4) : Q n (j + 1) y = ∑ x, Q n j x * W n j x y := by
  have key : ∀ (s : Fin (j + 1) → Fin 4) (z : Fin 4),
      ∏ m ∈ range (j + 1), W n m (g (Fin.snoc s z : Fin (j + 2) → Fin 4) m)
          (g (Fin.snoc s z : Fin (j + 2) → Fin 4) (m + 1)) =
        (∏ m ∈ range j, W n m (g s m) (g s (m + 1))) * W n j (s (Fin.last j)) z := by
    intro s z
    rw [prod_range_succ, g_snoc s z (by omega : j < j + 1), g_snoc_last, g_last]
    congr 1
    refine prod_congr rfl (fun m hm => ?_)
    rw [mem_range] at hm
    rw [g_snoc s z (by omega), g_snoc s z (by omega)]
  have e : ∀ p : Fin 4 × (Fin (j + 1) → Fin 4),
      (Fin.snocEquiv (fun _ : Fin (j + 2) => Fin 4)) p = Fin.snoc p.2 p.1 := fun _ => rfl
  unfold Q
  rw [← (Fin.snocEquiv (fun _ : Fin (j + 2) => Fin 4)).sum_comp, Fintype.sum_prod_type]
  simp only [e, Fin.snoc_last, key]
  rw [Fintype.sum_eq_single y (fun z hz => by simp [hz])]
  simp only [if_true, sum_mul, ite_mul, zero_mul]
  rw [sum_comm (s := univ) (t := univ) (f := fun x s => if s (Fin.last j) = x then
    (∏ m ∈ range j, W n m (g s m) (g s (m + 1))) * W n j x y else 0)]
  refine sum_congr rfl (fun s _ => ?_)
  rw [sum_ite_eq]
  simp

/-- The diamond weight as a function of four boolean features of its position. -/
def Wf (p q r t : Bool) (x y : Fin 4) : ℕ :=
  if x ≤ y ∧ (p = true → ¬ (x = 0 ∧ y = 1)) ∧ (q = true → ¬ (x = 2 ∧ y = 3)) then
    (if r = true then 1 else if x = y then 1 else 2) *
      (if t = true then 1 else if x = y then 1 else 2)
  else 0

theorem W_eq (n m : ℕ) (x y : Fin 4) :
    W n m x y =
      Wf (decide (1 ≤ m)) (decide (m + 3 ≤ n)) (decide (m + 2 = n)) (decide (m = 0)) x y := by
  simp only [W, Wf, ok, D_eq, decide_eq_true_eq]

/-- The first diamond (`m = 0`, `n ≥ 3`). -/
def Tf : Fin 4 → Fin 4 → ℕ := ![![1, 2, 2, 2], ![0, 1, 2, 2], ![0, 0, 1, 0], ![0, 0, 0, 1]]

/-- An inner diamond (`1 ≤ m`, `m + 3 ≤ n`). -/
def Tm : Fin 4 → Fin 4 → ℕ := ![![1, 0, 4, 4], ![0, 1, 4, 4], ![0, 0, 1, 0], ![0, 0, 0, 1]]

/-- The last diamond (`1 ≤ m`, `m + 2 = n`). -/
def Tl : Fin 4 → Fin 4 → ℕ := ![![1, 0, 2, 2], ![0, 1, 2, 2], ![0, 0, 1, 2], ![0, 0, 0, 1]]

theorem Wf_first : ∀ x y, Wf false true false true x y = Tf x y := by decide

theorem Wf_mid : ∀ x y, Wf true true false false x y = Tm x y := by decide

theorem Wf_last : ∀ x y, Wf true false true false x y = Tl x y := by decide

theorem W_first {n : ℕ} (hn : 3 ≤ n) (x y : Fin 4) : W n 0 x y = Tf x y := by
  have e2 : decide (0 + 3 ≤ n) = true := decide_eq_true (by omega)
  have e3 : decide (0 + 2 = n) = false := decide_eq_false (by omega)
  rw [W_eq, e2, e3, ← Wf_first x y]
  rfl

theorem W_mid {n m : ℕ} (h1 : 1 ≤ m) (h2 : m + 3 ≤ n) (x y : Fin 4) : W n m x y = Tm x y := by
  have e1 : decide (1 ≤ m) = true := decide_eq_true h1
  have e2 : decide (m + 3 ≤ n) = true := decide_eq_true h2
  have e3 : decide (m + 2 = n) = false := decide_eq_false (by omega)
  have e4 : decide (m = 0) = false := decide_eq_false (by omega)
  rw [W_eq, e1, e2, e3, e4, Wf_mid]

theorem W_last {n m : ℕ} (h1 : 1 ≤ m) (h2 : m + 2 = n) (x y : Fin 4) : W n m x y = Tl x y := by
  have e1 : decide (1 ≤ m) = true := decide_eq_true h1
  have e2 : decide (m + 3 ≤ n) = false := decide_eq_false (by omega)
  have e3 : decide (m + 2 = n) = true := decide_eq_true h2
  have e4 : decide (m = 0) = false := decide_eq_false (by omega)
  rw [W_eq, e1, e2, e3, e4, Wf_last]

theorem Q_one {n : ℕ} (hn : 3 ≤ n) (y : Fin 4) : Q n 1 y = ![1, 3, 5, 5] y := by
  rw [Q_succ, Fin.sum_univ_four]
  simp only [Q_zero, one_mul, W_first hn]
  fin_cases y <;> rfl

theorem Q_mid (k : ℕ) :
    ∀ t, t ≤ k → ∀ y, Q (k + 3) (t + 1) y = ![1, 3, 5 + 16 * t, 5 + 16 * t] y := by
  intro t
  induction t with
  | zero =>
    intro _ y
    rw [Q_one (by omega)]
  | succ t ih =>
    intro ht y
    rw [Q_succ, Fin.sum_univ_four, ih (by omega), ih (by omega), ih (by omega), ih (by omega)]
    simp only [W_mid (by omega : 1 ≤ t + 1) (by omega : t + 1 + 3 ≤ k + 3)]
    fin_cases y <;> simp [Tm] <;> ring

theorem spine_total (k : ℕ) :
    ∑ s : Fin (k + 3) → Fin 4, ∏ m ∈ range (k + 2), W (k + 3) m (g s m) (g s (m + 1)) =
      64 * k + 40 := by
  have h := sum_Q (k + 3) (k + 2)
  refine h.trans ?_
  have hq : ∀ y, Q (k + 3) (k + 2) y = ∑ x, Q (k + 3) (k + 1) x * W (k + 3) (k + 1) x y :=
    fun y => Q_succ (k + 3) (k + 1) y
  simp only [hq, Fin.sum_univ_four, Q_mid k k le_rfl,
    W_last (by omega : 1 ≤ k + 1) (by omega : k + 1 + 2 = k + 3)]
  simp [Tl]
  ring

theorem a_closed (k : ℕ) : a (k + 3) = 64 * k + 40 := by
  rw [a_eq_sum (by omega), show k + 3 - 1 = k + 2 by omega]
  exact spine_total k

/-! ### The case n = 2 -/

instance decAdj {n : ℕ} (u v : Fin n × Fin 3) : Decidable (Adj u v) :=
  inferInstanceAs (Decidable (_ = 1))

/-- The allowed colours of the cells of the `2 × 3` array. -/
def B (u : Fin 2 × Fin 3) : Finset (Fin 4) :=
  if u.2 = 1 then (if (u.1 : ℕ) = 0 then {0, 1, 2} else {1, 2, 3})
  else if (u.1 : ℕ) = 0 then (if u.2 = 0 then {0} else {1})
  else (if u.2 = 0 then {2} else {3})

theorem fin2_cases : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide

theorem two_fwd {f : Fin 2 × Fin 3 → Fin 4} (hf : IsCounted f) (u : Fin 2 × Fin 3) :
    f u ∈ B u := by
  obtain ⟨hconn, hcor⟩ := hf
  have c00 : f (0, 0) = 0 := (hcor (0, 0)).1 rfl rfl
  have c02 : f (0, 2) = 1 := (hcor (0, 2)).2.1 rfl rfl
  have c10 : f (1, 0) = 2 := (hcor (1, 0)).2.2.1 rfl rfl
  have c12 : f (1, 2) = 3 := (hcor (1, 2)).2.2.2 rfl rfl
  have lay2 : ∀ w : Fin 2 × Fin 3, lay w = 2 → w = (1, 0) ∨ w = (0, 2) := by decide
  have h01 : f (0, 1) ≠ 3 := by
    intro h
    obtain ⟨w, hw, hlw⟩ :=
      path_layers (hconn 3 (0, 1) (1, 2) h c12) h 2 (Or.inl ⟨by decide, by decide⟩)
    rcases lay2 w hlw with rfl | rfl
    · rw [c10] at hw; exact absurd hw (by decide)
    · rw [c02] at hw; exact absurd hw (by decide)
  have h11 : f (1, 1) ≠ 0 := by
    intro h
    obtain ⟨w, hw, hlw⟩ :=
      path_layers (hconn 0 (1, 1) (0, 0) h c00) h 2 (Or.inr ⟨by decide, by decide⟩)
    rcases lay2 w hlw with rfl | rfl
    · rw [c10] at hw; exact absurd hw (by decide)
    · rw [c02] at hw; exact absurd hw (by decide)
  have m3 : ∀ x : Fin 4, x ≠ 3 → x ∈ ({0, 1, 2} : Finset (Fin 4)) := by decide
  have m0 : ∀ x : Fin 4, x ≠ 0 → x ∈ ({1, 2, 3} : Finset (Fin 4)) := by decide
  obtain ⟨i, k⟩ := u
  rcases fin2_cases i with rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl
  · rw [c00]; decide
  · exact m3 _ h01
  · rw [c02]; decide
  · rw [c10]; decide
  · exact m0 _ h11
  · rw [c12]; decide

theorem two_bwd {f : Fin 2 × Fin 3 → Fin 4} (hB : ∀ u, f u ∈ B u) : IsCounted f := by
  have c00 : f (0, 0) = 0 := mem_singleton.1 (hB (0, 0))
  have c02 : f (0, 2) = 1 := mem_singleton.1 (hB (0, 2))
  have c10 : f (1, 0) = 2 := mem_singleton.1 (hB (1, 0))
  have c12 : f (1, 2) = 3 := mem_singleton.1 (hB (1, 2))
  have h01 : f (0, 1) = 0 ∨ f (0, 1) = 1 ∨ f (0, 1) = 2 := by
    have := hB (0, 1)
    simpa [B] using this
  have h11 : f (1, 1) = 1 ∨ f (1, 1) = 2 ∨ f (1, 1) = 3 := by
    have := hB (1, 1)
    simpa [B] using this
  have hcor : CornersOK f := by
    intro u
    obtain ⟨i, k⟩ := u
    rcases fin2_cases i with rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl <;>
      simp [c00, c02, c10, c12]
  refine ⟨?_, hcor⟩
  have hn0 : 0 < 2 := by norm_num
  have K0' : K hn0 0 = (0, 0) := rfl
  have K1' : K hn0 1 = (0, 2) := rfl
  have K2' : K hn0 2 = (1, 0) := rfl
  have K3' : K hn0 3 = (1, 2) := rfl
  have cell : ∀ w : Fin 2 × Fin 3, Relation.ReflTransGen (R f (f w)) w (K hn0 (f w)) := by
    intro w
    obtain ⟨i, k⟩ := w
    rcases fin2_cases i with rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl
    · rw [c00, K0']
    · rcases h01 with h | h | h
      · rw [h, K0']; exact Relation.ReflTransGen.single ⟨by decide, h, c00⟩
      · rw [h, K1']; exact Relation.ReflTransGen.single ⟨by decide, h, c02⟩
      · rw [h, K2']; exact Relation.ReflTransGen.single ⟨by decide, h, c10⟩
    · rw [c02, K1']
    · rw [c10, K2']
    · rcases h11 with h | h | h
      · rw [h, K1']; exact Relation.ReflTransGen.single ⟨by decide, h, c02⟩
      · rw [h, K2']; exact Relation.ReflTransGen.single ⟨by decide, h, c10⟩
      · rw [h, K3']; exact Relation.ReflTransGen.single ⟨by decide, h, c12⟩
    · rw [c12, K3']
  intro c u v hu hv
  have h1 := cell u
  have h2 := cell v
  rw [hu] at h1
  rw [hv] at h2
  exact h1.trans (rtg_symm R_symm h2)

theorem a_two : a 2 = 9 := by
  classical
  have h1 : a 2 = (univ.filter (fun f : Fin 2 × Fin 3 → Fin 4 => IsCounted f)).card := by
    unfold a
    rw [Fintype.card_subtype]
  have h2 : univ.filter (fun f : Fin 2 × Fin 3 → Fin 4 => IsCounted f) = Fintype.piFinset B := by
    ext f
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    exact ⟨two_fwd, two_bwd⟩
  rw [h1, h2, Fintype.card_piFinset]
  decide

/-! ### The conjectures -/

theorem a_closedQ {n : ℕ} (hn : 3 ≤ n) : (a n : ℚ) = 64 * n - 152 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [a_closed]
  push_cast
  ring

theorem closed_form (n : ℕ) (hn : 2 < n) : (a n : ℤ) = 8 * (8 * n - 19) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [a_closed]
  push_cast
  ring

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n < 2 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 2 =
      X ^ 2 * (9 + 22 * X + 33 * X ^ 2) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n < 2 then (0 : ℚ) else (a n : ℚ)) with hA
  have hsq : ((1 : ℚ⟦X⟧) - X) ^ 2 = 1 - X ^ 1 - X ^ 1 + X ^ 2 := by ring
  have hrhs : (X : ℚ⟦X⟧) ^ 2 * (9 + 22 * X + 33 * X ^ 2) =
      C (9 : ℚ) * X ^ 2 + C (22 : ℚ) * X ^ 3 + C (33 : ℚ) * X ^ 4 := by
    simp only [map_ofNat]
    ring
  rw [hsq, hrhs]
  ext k
  simp only [map_add, coeff_C_mul_X_pow]
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mul_X_pow', hA, coeff_mk]
  have h2 : (a 2 : ℚ) = 9 := by rw [a_two]; norm_num
  rcases k with _ | _ | _ | _ | _ | j
  · simp
  · simp
  · norm_num [h2]
  · norm_num [h2, a_closedQ]
  · norm_num [h2, a_closedQ]
  · have e : j + 1 + 1 + 1 + 1 + 1 = j + 5 := rfl
    simp only [e, show ¬ (j + 5 < 2) by omega, show 1 ≤ j + 5 by omega,
      show 2 ≤ j + 5 by omega, show j + 5 - 1 = j + 4 by omega, show j + 5 - 2 = j + 3 by omega,
      show ¬ (j + 4 < 2) by omega, show ¬ (j + 3 < 2) by omega, show ¬ (j + 5 = 2) by omega,
      show ¬ (j + 5 = 3) by omega, show ¬ (j + 5 = 4) by omega, if_true, if_false]
    rw [a_closedQ (by omega : 3 ≤ j + 5), a_closedQ (by omega : 3 ≤ j + 4),
      a_closedQ (by omega : 3 ≤ j + 3)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a165372.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.closed_form⟩
