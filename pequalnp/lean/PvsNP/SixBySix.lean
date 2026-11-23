import PvsNP.PermanentLaplace

/-!
# The middle layer of the 6 × 6 permanent: 17 split products in the limit

Rows `0, …, 5`, columns in two blocks `{0, 1, 2}` and `{3, 4, 5}`. A split product is a
function of three of the rows times a function of the other three. Laplace expansion along
three rows writes the permanent with `20 = 6.choose 3` of them.

Here `lam * permanent A` is written as ten "squares" (one for each way of splitting the rows
three against three), minus four times seven products that all use the splitting `012|345`,
minus `lam ^ 2` times ten more. Dividing by `lam` and letting `lam → 0`, the last group
vanishes: seventeen split products suffice in the limit.

The construction is the polarisation of
`2 * lam * (y₀ ⋯ y₅) = (y₀y₁y₂ + lam * y₃y₄y₅) ^ 2 - (y₀y₁y₂) ^ 2 - lam ^ 2 * (y₃y₄y₅) ^ 2`,
and the same recipe works for every even size.
-/

namespace PvsNP

open Matrix

section Ring

variable {R : Type*} [CommRing R]

/-- The `3 × 3` permanent of the row vectors `u, v, w` on columns `p, q, r`. -/
def perm3 (p q r : Fin 6) (u v w : Fin 6 → R) : R :=
  u p * v q * w r + u p * v r * w q + u q * v p * w r
    + u q * v r * w p + u r * v p * w q + u r * v q * w p

/-- Row vectors `u, v, w` using column `p` twice and column `q` once. -/
def twoOne (p q : Fin 6) (u v w : Fin 6 → R) : R :=
  u p * v p * w q + u p * v q * w p + u q * v p * w p

/-- The "square root": first-block permanent plus `lam` times second-block permanent. -/
def sq (lam : R) (u v w : Fin 6 → R) : R :=
  perm3 0 1 2 u v w + lam * perm3 3 4 5 u v w

/-- The `6 × 6` permanent via Laplace expansion along the first three columns: a sum over the
twenty ways of choosing which three rows use them. -/
theorem permanent_fin_six_laplace (A : Matrix (Fin 6) (Fin 6) R) :
    A.permanent =
      perm3 0 1 2 (A 0) (A 1) (A 2) * perm3 3 4 5 (A 3) (A 4) (A 5)
      + perm3 0 1 2 (A 0) (A 1) (A 3) * perm3 3 4 5 (A 2) (A 4) (A 5)
      + perm3 0 1 2 (A 0) (A 1) (A 4) * perm3 3 4 5 (A 2) (A 3) (A 5)
      + perm3 0 1 2 (A 0) (A 1) (A 5) * perm3 3 4 5 (A 2) (A 3) (A 4)
      + perm3 0 1 2 (A 0) (A 2) (A 3) * perm3 3 4 5 (A 1) (A 4) (A 5)
      + perm3 0 1 2 (A 0) (A 2) (A 4) * perm3 3 4 5 (A 1) (A 3) (A 5)
      + perm3 0 1 2 (A 0) (A 2) (A 5) * perm3 3 4 5 (A 1) (A 3) (A 4)
      + perm3 0 1 2 (A 0) (A 3) (A 4) * perm3 3 4 5 (A 1) (A 2) (A 5)
      + perm3 0 1 2 (A 0) (A 3) (A 5) * perm3 3 4 5 (A 1) (A 2) (A 4)
      + perm3 0 1 2 (A 0) (A 4) (A 5) * perm3 3 4 5 (A 1) (A 2) (A 3)
      + perm3 0 1 2 (A 1) (A 2) (A 3) * perm3 3 4 5 (A 0) (A 4) (A 5)
      + perm3 0 1 2 (A 1) (A 2) (A 4) * perm3 3 4 5 (A 0) (A 3) (A 5)
      + perm3 0 1 2 (A 1) (A 2) (A 5) * perm3 3 4 5 (A 0) (A 3) (A 4)
      + perm3 0 1 2 (A 1) (A 3) (A 4) * perm3 3 4 5 (A 0) (A 2) (A 5)
      + perm3 0 1 2 (A 1) (A 3) (A 5) * perm3 3 4 5 (A 0) (A 2) (A 4)
      + perm3 0 1 2 (A 1) (A 4) (A 5) * perm3 3 4 5 (A 0) (A 2) (A 3)
      + perm3 0 1 2 (A 2) (A 3) (A 4) * perm3 3 4 5 (A 0) (A 1) (A 5)
      + perm3 0 1 2 (A 2) (A 3) (A 5) * perm3 3 4 5 (A 0) (A 1) (A 4)
      + perm3 0 1 2 (A 2) (A 4) (A 5) * perm3 3 4 5 (A 0) (A 1) (A 3)
      + perm3 0 1 2 (A 3) (A 4) (A 5) * perm3 3 4 5 (A 0) (A 1) (A 2) := by
  simp [permanent_succ_column_zero, Fin.sum_univ_succ, Fin.succAbove, perm3]
  ring

/-- The ten squares, one for each splitting of the rows three against three. -/
def squares (A : Matrix (Fin 6) (Fin 6) R) (lam : R) : R :=
  sq lam (A 0) (A 1) (A 2) * sq lam (A 3) (A 4) (A 5)
    + sq lam (A 0) (A 1) (A 3) * sq lam (A 2) (A 4) (A 5)
    + sq lam (A 0) (A 1) (A 4) * sq lam (A 2) (A 3) (A 5)
    + sq lam (A 0) (A 1) (A 5) * sq lam (A 2) (A 3) (A 4)
    + sq lam (A 0) (A 2) (A 3) * sq lam (A 1) (A 4) (A 5)
    + sq lam (A 0) (A 2) (A 4) * sq lam (A 1) (A 3) (A 5)
    + sq lam (A 0) (A 2) (A 5) * sq lam (A 1) (A 3) (A 4)
    + sq lam (A 0) (A 3) (A 4) * sq lam (A 1) (A 2) (A 5)
    + sq lam (A 0) (A 3) (A 5) * sq lam (A 1) (A 2) (A 4)
    + sq lam (A 0) (A 4) (A 5) * sq lam (A 1) (A 2) (A 3)

/-- What the squares leave behind in the first block, expanded along the splitting `012|345`:
seven products. -/
def garbage (A : Matrix (Fin 6) (Fin 6) R) : R :=
  perm3 0 1 2 (A 0) (A 1) (A 2) * perm3 0 1 2 (A 3) (A 4) (A 5)
    + twoOne 0 2 (A 0) (A 1) (A 2) * twoOne 1 2 (A 3) (A 4) (A 5)
    + twoOne 0 1 (A 0) (A 1) (A 2) * twoOne 2 1 (A 3) (A 4) (A 5)
    + twoOne 1 2 (A 0) (A 1) (A 2) * twoOne 0 2 (A 3) (A 4) (A 5)
    + twoOne 1 0 (A 0) (A 1) (A 2) * twoOne 2 0 (A 3) (A 4) (A 5)
    + twoOne 2 1 (A 0) (A 1) (A 2) * twoOne 0 1 (A 3) (A 4) (A 5)
    + twoOne 2 0 (A 0) (A 1) (A 2) * twoOne 1 0 (A 3) (A 4) (A 5)

/-- What the squares leave behind in the second block: ten products. It enters with a factor
`lam ^ 2`. -/
def rest (A : Matrix (Fin 6) (Fin 6) R) : R :=
  perm3 3 4 5 (A 0) (A 1) (A 2) * perm3 3 4 5 (A 3) (A 4) (A 5)
    + perm3 3 4 5 (A 0) (A 1) (A 3) * perm3 3 4 5 (A 2) (A 4) (A 5)
    + perm3 3 4 5 (A 0) (A 1) (A 4) * perm3 3 4 5 (A 2) (A 3) (A 5)
    + perm3 3 4 5 (A 0) (A 1) (A 5) * perm3 3 4 5 (A 2) (A 3) (A 4)
    + perm3 3 4 5 (A 0) (A 2) (A 3) * perm3 3 4 5 (A 1) (A 4) (A 5)
    + perm3 3 4 5 (A 0) (A 2) (A 4) * perm3 3 4 5 (A 1) (A 3) (A 5)
    + perm3 3 4 5 (A 0) (A 2) (A 5) * perm3 3 4 5 (A 1) (A 3) (A 4)
    + perm3 3 4 5 (A 0) (A 3) (A 4) * perm3 3 4 5 (A 1) (A 2) (A 5)
    + perm3 3 4 5 (A 0) (A 3) (A 5) * perm3 3 4 5 (A 1) (A 2) (A 4)
    + perm3 3 4 5 (A 0) (A 4) (A 5) * perm3 3 4 5 (A 1) (A 2) (A 3)

/-- **Seventeen-term identity.** `lam` times the `6 × 6` permanent is ten squares, minus four
times seven products for the splitting `012|345`, minus `lam ^ 2` times ten more products. -/
theorem six_squares_identity (A : Matrix (Fin 6) (Fin 6) R) (lam : R) :
    lam * A.permanent = squares A lam - 4 * garbage A - lam ^ 2 * rest A := by
  rw [permanent_fin_six_laplace]
  simp only [squares, garbage, rest, sq, perm3, twoOne]
  ring

end Ring

section Field

variable {K : Type*} [Field K]

/-- A function of rows `a, b, c` times a function of rows `d, e, f`. -/
def mk (a b c d e f : Fin 6) (F G : (Fin 6 → K) → (Fin 6 → K) → (Fin 6 → K) → K) :
    Matrix (Fin 6) (Fin 6) K → K :=
  fun A => F (A a) (A b) (A c) * G (A d) (A e) (A f)

/-- `t` is a split product: for some splitting of the six rows into `a, b, c` and `d, e, f`,
it is a function of the first three rows times a function of the last three. -/
def IsSplit3 (t : Matrix (Fin 6) (Fin 6) K → K) : Prop :=
  ∃ a b c d e f : Fin 6, [a, b, c, d, e, f].Nodup ∧
    ∃ F G : (Fin 6 → K) → (Fin 6 → K) → (Fin 6 → K) → K, t = mk a b c d e f F G

theorem isSplit3_mk (a b c d e f : Fin 6) (h : [a, b, c, d, e, f].Nodup)
    (F G : (Fin 6 → K) → (Fin 6 → K) → (Fin 6 → K) → K) : IsSplit3 (mk a b c d e f F G) :=
  ⟨a, b, c, d, e, f, h, F, G, rfl⟩

/-- **Border bound for the 6 × 6 permanent.** For every nonzero `lam`, the permanent plus
`lam * rest A` is a sum of seventeen split products (the factors used are trilinear forms in
the rows). Laplace expansion uses twenty. -/
theorem permanent_sub_eq_seventeen_split (lam : K) (hlam : lam ≠ 0) :
    ∃ ts : List (Matrix (Fin 6) (Fin 6) K → K), ts.length = 17 ∧ (∀ t ∈ ts, IsSplit3 t) ∧
      ∀ A : Matrix (Fin 6) (Fin 6) K, A.permanent + lam * rest A = (ts.map fun t => t A).sum := by
  refine ⟨[
      mk 0 1 2 3 4 5 (fun u v w => lam⁻¹ * sq lam u v w) (fun u v w => sq lam u v w),
      mk 0 1 3 2 4 5 (fun u v w => lam⁻¹ * sq lam u v w) (fun u v w => sq lam u v w),
      mk 0 1 4 2 3 5 (fun u v w => lam⁻¹ * sq lam u v w) (fun u v w => sq lam u v w),
      mk 0 1 5 2 3 4 (fun u v w => lam⁻¹ * sq lam u v w) (fun u v w => sq lam u v w),
      mk 0 2 3 1 4 5 (fun u v w => lam⁻¹ * sq lam u v w) (fun u v w => sq lam u v w),
      mk 0 2 4 1 3 5 (fun u v w => lam⁻¹ * sq lam u v w) (fun u v w => sq lam u v w),
      mk 0 2 5 1 3 4 (fun u v w => lam⁻¹ * sq lam u v w) (fun u v w => sq lam u v w),
      mk 0 3 4 1 2 5 (fun u v w => lam⁻¹ * sq lam u v w) (fun u v w => sq lam u v w),
      mk 0 3 5 1 2 4 (fun u v w => lam⁻¹ * sq lam u v w) (fun u v w => sq lam u v w),
      mk 0 4 5 1 2 3 (fun u v w => lam⁻¹ * sq lam u v w) (fun u v w => sq lam u v w),
      mk 0 1 2 3 4 5 (fun u v w => -4 * lam⁻¹ * perm3 0 1 2 u v w) (fun u v w => perm3 0 1 2 u v w),
      mk 0 1 2 3 4 5 (fun u v w => -4 * lam⁻¹ * twoOne 0 2 u v w) (fun u v w => twoOne 1 2 u v w),
      mk 0 1 2 3 4 5 (fun u v w => -4 * lam⁻¹ * twoOne 0 1 u v w) (fun u v w => twoOne 2 1 u v w),
      mk 0 1 2 3 4 5 (fun u v w => -4 * lam⁻¹ * twoOne 1 2 u v w) (fun u v w => twoOne 0 2 u v w),
      mk 0 1 2 3 4 5 (fun u v w => -4 * lam⁻¹ * twoOne 1 0 u v w) (fun u v w => twoOne 2 0 u v w),
      mk 0 1 2 3 4 5 (fun u v w => -4 * lam⁻¹ * twoOne 2 1 u v w) (fun u v w => twoOne 0 1 u v w),
      mk 0 1 2 3 4 5 (fun u v w => -4 * lam⁻¹ * twoOne 2 0 u v w) (fun u v w => twoOne 1 0 u v w)], rfl, ?_, ?_⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact isSplit3_mk _ _ _ _ _ _ (by decide) _ _
  · intro A
    have h := six_squares_identity A lam
    simp only [squares, garbage] at h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mk]
    field_simp
    linear_combination h

end Field

end PvsNP
