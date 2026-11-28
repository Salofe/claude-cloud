import OMAReductions.R_OpenQuantumProblem23_hasSICPOVM_68_R1

/-!
# Step H2 of the reduction OpenQuantumProblem23.hasSICPOVM_68.R1

From an array `F` satisfying the reflection relation, the restricted convolution equations and
the unimodularity of `τ ∘ F` off the origin, we build a rank-one Weyl fiducial projector `A`
in dimension 68 whose characteristic function has squared modulus `1/69` off the origin.

The argument is a self-contained finite Fourier computation (only the reflection, convolution
and unimodularity hypotheses are used):

* `ψ = τ ∘ stdAddChar` is a primitive character of `ZMod 68`, so `∑ t, ψ (t * c) = 68 [c = 0]`.
* Pick `η` with `η ^ 2 = ψ 1` and put `Φ x = η ^ (x.val ^ 2)`. Since 68 is even,
  `Φ (x + y) = Φ x * Φ y * ψ (x * y)` and `Φ x ^ 2 = ψ (x ^ 2)`.
* With `G = τ ∘ F` and `K a b = G a b * Φ (a - b)`, the image of the convolution equations under
  `τ` becomes the twisted convolution identity `K ⋆ K = 68 σ K + 68 ^ 2 δ`, where
  `σ = τ (√65)` and `(U ⋆ V) a b = ∑ c, ∑ β, U (a - c) β * V c (b - β) * ψ (-(β * c))`.
* The origin equation together with the reflection relation gives
  `x ^ 2 - 68 σ x - 1 = 0` for `x = G 0 0`, hence `(68 σ - 2 x) ^ 2 = (66 √69) ^ 2`, which yields a
  real `l = ± 1 / √69` with `l * (68 σ - 2 x) = 66`.
* `H = l K + (1 - l x) δ` satisfies `H ⋆ H = 68 H`, `H 0 0 = 1`, the Hermitian symmetry
  `star (H a b) = ψ (a * b) * H (-a) (-b)`, and `|H a b| ^ 2 = 1 / 69` off the origin.
* `A x y = (1 / 68) ∑ β, H (x - y) β * ψ (-(β * y))` is then a Hermitian idempotent of trace one
  with `∑ t, A (t + a) t * ψ (b * t) = H a b`; finally `stdAddChar c = ψ (m * c)` for some `m`,
  which converts the characteristic function back to the standard character.
-/

namespace OMA.Helpers

open scoped BigOperators

theorem oq_sum_char (ψ : AddChar (ZMod 68) ℂ) (hψ : ψ.IsPrimitive) (c : ZMod 68) :
    ∑ t : ZMod 68, ψ (t * c) = if c = 0 then 68 else 0 := by
  rw [AddChar.sum_mulShift c hψ, ZMod.card]
  norm_num

theorem oq_char_natCast (ψ : AddChar (ZMod 68) ℂ) (n : ℕ) : ψ 1 ^ n = ψ (n : ZMod 68) := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_one]

theorem oq_char_pow (ψ : AddChar (ZMod 68) ℂ) (c : ZMod 68) : ψ c = ψ 1 ^ c.val := by
  rw [oq_char_natCast, ZMod.natCast_zmod_val]

theorem oq_char_pow68 (ψ : AddChar (ZMod 68) ℂ) (c : ZMod 68) : ψ c ^ 68 = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have h : ((68 : ℕ) : ZMod 68) = 0 := ZMod.natCast_self 68
  rw [h, zero_mul, AddChar.map_zero_eq_one]

theorem oq_char_norm (ψ : AddChar (ZMod 68) ℂ) (c : ZMod 68) : ‖ψ c‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (oq_char_pow68 ψ c) (by norm_num)

theorem oq_char_star (ψ : AddChar (ZMod 68) ℂ) (c : ZMod 68) : star (ψ c) = ψ (-c) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (oq_char_norm ψ c)]
  rfl

theorem oq_prim_root (ψ : AddChar (ZMod 68) ℂ) (hψ : ψ.IsPrimitive) : IsPrimitiveRoot (ψ 1) 68 := by
  refine ⟨?_, ?_⟩
  · rw [oq_char_natCast]
    rw [ZMod.natCast_self, AddChar.map_zero_eq_one]
  · intro l hl
    rw [oq_char_natCast] at hl
    have h := (AddChar.IsPrimitive.zmod_char_eq_one_iff 68 hψ _).mp hl
    exact (ZMod.natCast_eq_zero_iff l 68).mp h

theorem oq_pow_mod (η : ℂ) (h : η ^ 136 = 1) (m n : ℕ) (hmn : m % 136 = n % 136) :
    η ^ m = η ^ n := by
  rw [← Nat.div_add_mod m 136, ← Nat.div_add_mod n 136, pow_add, pow_add, pow_mul, pow_mul, h,
    one_pow, one_pow, hmn]

theorem oq_sq_mod (p q : ℕ) :
    ((p + q) % 68) ^ 2 % 136 = (p ^ 2 + q ^ 2 + 2 * (p * q % 68)) % 136 := by
  have h1 := Nat.div_add_mod (p + q) 68
  have h2 := Nat.div_add_mod (p * q) 68
  set r := (p + q) % 68
  set k := (p + q) / 68
  set s := p * q % 68
  set l := p * q / 68
  have key : r ^ 2 + 136 * (34 * k ^ 2 + k * r) = p ^ 2 + q ^ 2 + 2 * s + 136 * l := by
    have e1 : r ^ 2 + 136 * (34 * k ^ 2 + k * r) = (68 * k + r) ^ 2 := by ring
    have e2 : p ^ 2 + q ^ 2 + 2 * s + 136 * l = p ^ 2 + q ^ 2 + 2 * (68 * l + s) := by ring
    rw [e1, e2, h1, h2]
    ring
  calc r ^ 2 % 136 = (r ^ 2 + 136 * (34 * k ^ 2 + k * r)) % 136 := by
        rw [Nat.add_mul_mod_self_left]
    _ = (p ^ 2 + q ^ 2 + 2 * s + 136 * l) % 136 := by rw [key]
    _ = (p ^ 2 + q ^ 2 + 2 * s) % 136 := by rw [Nat.add_mul_mod_self_left]

theorem oq_half_mul (ψ : AddChar (ZMod 68) ℂ) (η : ℂ) (hη : η ^ 2 = ψ 1) (x y : ZMod 68) :
    η ^ ((x + y).val ^ 2) = η ^ (x.val ^ 2) * η ^ (y.val ^ 2) * ψ (x * y) := by
  have h136 : η ^ 136 = 1 := by
    rw [show (136 : ℕ) = 2 * 68 by norm_num, pow_mul, hη, oq_char_pow68]
  rw [oq_char_pow ψ (x * y), ← hη, ← pow_mul, ← pow_add, ← pow_add]
  apply oq_pow_mod η h136
  rw [ZMod.val_add, ZMod.val_mul, oq_sq_mod]

theorem oq_half_sq (ψ : AddChar (ZMod 68) ℂ) (η : ℂ) (hη : η ^ 2 = ψ 1) (x : ZMod 68) :
    (η ^ (x.val ^ 2)) ^ 2 = ψ (x ^ 2) := by
  rw [← pow_mul, mul_comm, pow_mul, hη, oq_char_natCast]
  push_cast
  rw [ZMod.natCast_zmod_val]

theorem oq_half_norm (ψ : AddChar (ZMod 68) ℂ) (η : ℂ) (hη : η ^ 2 = ψ 1) (n : ℕ) :
    ‖η ^ n‖ = 1 := by
  have h136 : η ^ 136 = 1 := by
    rw [show (136 : ℕ) = 2 * 68 by norm_num, pow_mul, hη, oq_char_pow68]
  rw [norm_pow, Complex.norm_eq_one_of_pow_eq_one h136 (by norm_num), one_pow]

/-- the matrix built from a function `H` -/
noncomputable def oqA (ψ : AddChar (ZMod 68) ℂ) (H : ZMod 68 → ZMod 68 → ℂ) :
    Matrix (ZMod 68) (ZMod 68) ℂ :=
  fun x y => (68 : ℂ)⁻¹ * ∑ β, H (x - y) β * ψ (-(β * y))

theorem oq_charfn (ψ : AddChar (ZMod 68) ℂ) (hψ : ψ.IsPrimitive) (H : ZMod 68 → ZMod 68 → ℂ)
    (a b : ZMod 68) : ∑ t, oqA ψ H (t + a) t * ψ (b * t) = H a b := by
  have e1 : ∀ t, oqA ψ H (t + a) t * ψ (b * t) =
      (68 : ℂ)⁻¹ * ∑ β, H a β * ψ (t * (b - β)) := by
    intro t
    unfold oqA
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro β _
    rw [show t + a - t = a by ring, mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun t _ => e1 t), ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, oq_sum_char ψ hψ]
  rw [Fintype.sum_eq_single b]
  · simp only [sub_self, if_true]
    field_simp
  · intro β hβ
    simp [sub_eq_zero, Ne.symm hβ]

theorem oq_trace (ψ : AddChar (ZMod 68) ℂ) (hψ : ψ.IsPrimitive) (H : ZMod 68 → ZMod 68 → ℂ) :
    (oqA ψ H).trace = H 0 0 := by
  rw [← oq_charfn ψ hψ H 0 0]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro t _
  simp

theorem oq_herm (ψ : AddChar (ZMod 68) ℂ) (H : ZMod 68 → ZMod 68 → ℂ)
    (hsymm : ∀ a b, star (H a b) = ψ (a * b) * H (-a) (-b)) : (oqA ψ H).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  unfold oqA
  rw [star_mul', star_sum]
  have h68 : star ((68 : ℂ)⁻¹) = (68 : ℂ)⁻¹ := by
    rw [star_inv₀]
    congr 1
    exact Complex.conj_ofNat 68
  rw [h68]
  congr 1
  have e1 : ∀ β, star (H (j - i) β * ψ (-(β * i))) = H (i - j) (-β) * ψ (-((-β) * j)) := by
    intro β
    rw [star_mul', hsymm, oq_char_star]
    have hp : ψ ((j - i) * β) * ψ (-(-(β * i))) = ψ (-((-β) * j)) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [show -(j - i) = i - j by ring]
    linear_combination H (i - j) (-β) * hp
  rw [Finset.sum_congr rfl (fun β _ => e1 β)]
  exact Equiv.sum_comp (Equiv.neg (ZMod 68)) (fun β => H (i - j) β * ψ (-(β * j)))

theorem oq_idem (ψ : AddChar (ZMod 68) ℂ) (H : ZMod 68 → ZMod 68 → ℂ)
    (hconvH : ∀ a b, (∑ c, ∑ β, H (a - c) β * H c (b - β) * ψ (-(β * c))) = 68 * H a b) :
    oqA ψ H * oqA ψ H = oqA ψ H := by
  ext x z
  rw [Matrix.mul_apply]
  unfold oqA
  have hH : ∀ δ, H (x - z) δ * ψ (-(δ * z)) =
      (68 : ℂ)⁻¹ * ∑ c, ∑ β, H (x - z - c) β * H c (δ - β) * ψ (-(β * c)) * ψ (-(δ * z)) := by
    intro δ
    have e : ∑ c, ∑ β, H (x - z - c) β * H c (δ - β) * ψ (-(β * c)) * ψ (-(δ * z)) =
        (∑ c, ∑ β, H (x - z - c) β * H c (δ - β) * ψ (-(β * c))) * ψ (-(δ * z)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_mul]
    rw [e, hconvH]
    field_simp
  rw [Finset.sum_congr rfl (fun δ _ => hH δ), ← Finset.mul_sum]
  have lhs : ∀ y, ((68 : ℂ)⁻¹ * ∑ β, H (x - y) β * ψ (-(β * y))) *
      ((68 : ℂ)⁻¹ * ∑ γ, H (y - z) γ * ψ (-(γ * z))) =
      (68 : ℂ)⁻¹ * ((68 : ℂ)⁻¹ * ∑ β, ∑ γ,
        H (x - y) β * ψ (-(β * y)) * (H (y - z) γ * ψ (-(γ * z)))) := by
    intro y
    rw [← Finset.sum_mul_sum]
    ring
  rw [Finset.sum_congr rfl (fun y _ => lhs y), ← Finset.mul_sum, ← Finset.mul_sum]
  congr 2
  have step1 : ∀ c, ∑ δ, ∑ β, H (x - z - c) β * H c (δ - β) * ψ (-(β * c)) * ψ (-(δ * z)) =
      ∑ β, ∑ γ, H (x - z - c) β * H c γ * ψ (-(β * c)) * ψ (-((β + γ) * z)) := by
    intro c
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro β _
    rw [← Equiv.sum_comp (Equiv.addLeft β)]
    apply Finset.sum_congr rfl
    intro γ _
    simp only [Equiv.coe_addLeft]
    rw [show β + γ - β = γ by ring]
  have rhs : ∑ δ, ∑ c, ∑ β, H (x - z - c) β * H c (δ - β) * ψ (-(β * c)) * ψ (-(δ * z)) =
      ∑ y, ∑ β, ∑ γ, H (x - y) β * ψ (-(β * y)) * (H (y - z) γ * ψ (-(γ * z))) := by
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun c _ => step1 c)]
    rw [← Equiv.sum_comp (Equiv.subRight z)]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro β _
    apply Finset.sum_congr rfl
    intro γ _
    simp only [Equiv.subRight_apply]
    rw [show x - z - (y - z) = x - y by ring]
    have hp : ψ (-(β * (y - z))) * ψ (-((β + γ) * z)) = ψ (-(β * y)) * ψ (-(γ * z)) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [mul_assoc (H (x - y) β * H (y - z) γ), hp]
    ring
  exact rhs.symm

/-- the delta function at the origin -/
noncomputable def oqD (x y : ZMod 68) : ℂ := if x = 0 ∧ y = 0 then 1 else 0

theorem oq_K_conv (ψ : AddChar (ZMod 68) ℂ) (G K : ZMod 68 → ZMod 68 → ℂ) (Φ : ZMod 68 → ℂ)
    (σ : ℂ) (hK : ∀ x y, K x y = G x y * Φ (x - y)) (hΦ0 : Φ 0 = 1)
    (hΦmul : ∀ x y, Φ (x + y) = Φ x * Φ y * ψ (x * y))
    (hconv' : ∀ r s, (68 : ℂ)⁻¹ * ∑ i, ∑ j, G i j * G (r - i) (s - j) *
      ψ (i ^ 2 - i * j + j ^ 2) * ψ (-i * r + j * (r - s)) =
      σ * G r s + if (r, s) = (0, 0) then 68 else 0)
    (a b : ZMod 68) :
    ∑ c, ∑ β, K (a - c) β * K c (b - β) * ψ (-(β * c)) =
      68 * σ * K a b + 68 * (68 * oqD a b) := by
  have key : ∀ i j, K (a - i) (b - j) * K i j * ψ (-((b - j) * i)) =
      Φ (a - b) * (G i j * G (a - i) (b - j) * ψ (i ^ 2 - i * j + j ^ 2) *
        ψ (-i * a + j * (a - b))) := by
    intro i j
    have h1 := hΦmul (i - j) ((a - i) - (b - j))
    rw [show i - j + (a - i - (b - j)) = a - b by ring] at h1
    rw [h1, hK, hK]
    have h2 : ψ (-((b - j) * i)) = ψ ((i - j) * ((a - i) - (b - j))) *
        ψ (i ^ 2 - i * j + j ^ 2) * ψ (-i * a + j * (a - b)) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [h2]
    ring
  calc ∑ c, ∑ β, K (a - c) β * K c (b - β) * ψ (-(β * c))
      = ∑ c, ∑ j, K (a - c) (b - j) * K c j * ψ (-((b - j) * c)) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [← Equiv.sum_comp (Equiv.subLeft b)]
        apply Finset.sum_congr rfl
        intro j _
        simp only [Equiv.subLeft_apply]
        rw [sub_sub_cancel]
    _ = ∑ c, ∑ j, Φ (a - b) * (G c j * G (a - c) (b - j) * ψ (c ^ 2 - c * j + j ^ 2) *
        ψ (-c * a + j * (a - b))) := by
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro j _
        exact key c j
    _ = Φ (a - b) * ∑ c, ∑ j, (G c j * G (a - c) (b - j) * ψ (c ^ 2 - c * j + j ^ 2) *
        ψ (-c * a + j * (a - b))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.mul_sum]
    _ = Φ (a - b) * (68 * (σ * G a b + if (a, b) = (0, 0) then 68 else 0)) := by
        rw [← hconv' a b]
        field_simp
    _ = 68 * σ * K a b + 68 * (68 * oqD a b) := by
        rw [hK]
        by_cases h : a = 0 ∧ b = 0
        · obtain ⟨rfl, rfl⟩ := h
          simp [oqD, hΦ0]
          ring
        · have h' : ¬ ((a, b) = ((0 : ZMod 68), (0 : ZMod 68))) := by
            rw [Prod.mk.injEq]
            exact h
          rw [if_neg h']
          simp only [oqD, if_neg h]
          ring

theorem oq_conv_affine (ψ : AddChar (ZMod 68) ℂ) (K : ZMod 68 → ZMod 68 → ℂ) (lam mu : ℂ)
    (a b : ZMod 68) :
    ∑ c, ∑ β, (lam * K (a - c) β + mu * oqD (a - c) β) *
      (lam * K c (b - β) + mu * oqD c (b - β)) * ψ (-(β * c)) =
    lam ^ 2 * ∑ c, ∑ β, K (a - c) β * K c (b - β) * ψ (-(β * c)) +
      2 * lam * mu * K a b + mu ^ 2 * oqD a b := by
  have e : ∀ c β, (lam * K (a - c) β + mu * oqD (a - c) β) *
      (lam * K c (b - β) + mu * oqD c (b - β)) * ψ (-(β * c)) =
      lam ^ 2 * (K (a - c) β * K c (b - β) * ψ (-(β * c))) +
      lam * mu * (K (a - c) β * oqD c (b - β) * ψ (-(β * c))) +
      lam * mu * (oqD (a - c) β * K c (b - β) * ψ (-(β * c))) +
      mu ^ 2 * (oqD (a - c) β * oqD c (b - β) * ψ (-(β * c))) := by
    intros
    ring
  simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  have s1 : ∑ c, ∑ β, K (a - c) β * oqD c (b - β) * ψ (-(β * c)) = K a b := by
    rw [Fintype.sum_eq_single 0]
    · rw [Fintype.sum_eq_single b]
      · simp [oqD]
      · intro β hβ
        simp [oqD, sub_eq_zero, Ne.symm hβ]
    · intro c hc
      apply Finset.sum_eq_zero
      intro β _
      simp [oqD, hc]
  have s2 : ∑ c, ∑ β, oqD (a - c) β * K c (b - β) * ψ (-(β * c)) = K a b := by
    rw [Fintype.sum_eq_single a]
    · rw [Fintype.sum_eq_single 0]
      · simp [oqD]
      · intro β hβ
        simp [oqD, hβ]
    · intro c hc
      apply Finset.sum_eq_zero
      intro β _
      simp [oqD, sub_eq_zero, Ne.symm hc]
  have s3 : ∑ c, ∑ β, oqD (a - c) β * oqD c (b - β) * ψ (-(β * c)) = oqD a b := by
    rw [Fintype.sum_eq_single a]
    · rw [Fintype.sum_eq_single 0]
      · simp [oqD]
      · intro β hβ
        simp [oqD, hβ]
    · intro c hc
      apply Finset.sum_eq_zero
      intro β _
      simp [oqD, sub_eq_zero, Ne.symm hc]
  rw [s1, s2, s3]
  ring

theorem oq_lambda (σ x0 : ℂ) (hσ : σ ^ 2 = 65) (hx : x0 ^ 2 - 68 * σ * x0 - 1 = 0) :
    ∃ l : ℝ, (l : ℂ) * (68 * σ - 2 * x0) = 66 ∧ 69 * l ^ 2 = 1 := by
  have h69 : ((Real.sqrt 69 : ℝ) : ℂ) ^ 2 = 69 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hw : (68 * σ - 2 * x0) ^ 2 = ((66 * Real.sqrt 69 : ℝ) : ℂ) ^ 2 := by
    push_cast
    linear_combination 4 * hx + 4624 * hσ - 4356 * h69
  have hs : Real.sqrt 69 ≠ 0 := by positivity
  have hr : (Real.sqrt 69)⁻¹ * (66 * Real.sqrt 69) = 66 := by
    field_simp
  have hsq : 69 * ((Real.sqrt 69)⁻¹) ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hw with h | h
  · refine ⟨(Real.sqrt 69)⁻¹, ?_, hsq⟩
    rw [h, ← Complex.ofReal_mul, hr]
    norm_num
  · refine ⟨-(Real.sqrt 69)⁻¹, ?_, ?_⟩
    · rw [h, Complex.ofReal_neg, neg_mul_neg, ← Complex.ofReal_mul, hr]
      norm_num
    · rw [neg_sq]
      exact hsq

theorem oq_x0_eq (ψ : AddChar (ZMod 68) ℂ) (G : ZMod 68 → ZMod 68 → ℂ) (σ : ℂ)
    (hrefl' : ∀ i j, (i, j) ≠ (0, 0) → G i j * G (-i) (-j) = ψ (-(i ^ 2 - i * j + j ^ 2)))
    (hconv' : ∀ r s, (68 : ℂ)⁻¹ * ∑ i, ∑ j, G i j * G (r - i) (s - j) *
      ψ (i ^ 2 - i * j + j ^ 2) * ψ (-i * r + j * (r - s)) =
      σ * G r s + if (r, s) = (0, 0) then 68 else 0) :
    G 0 0 ^ 2 - 68 * σ * G 0 0 - 1 = 0 := by
  have h := hconv' 0 0
  have hterm : ∀ i j, G i j * G (0 - i) (0 - j) * ψ (i ^ 2 - i * j + j ^ 2) *
      ψ (-i * 0 + j * (0 - 0)) = 1 + oqD i j * (G 0 0 ^ 2 - 1) := by
    intro i j
    by_cases hij : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := hij
      simp [oqD]
      ring
    · have hne : (i, j) ≠ (0, 0) := by
        rw [Ne, Prod.mk.injEq]
        exact hij
      rw [zero_sub, zero_sub, hrefl' i j hne, ← AddChar.map_add_eq_mul,
        ← AddChar.map_add_eq_mul,
        show -(i ^ 2 - i * j + j ^ 2) + (i ^ 2 - i * j + j ^ 2) + (-i * 0 + j * (0 - 0)) = 0 by ring,
        AddChar.map_zero_eq_one]
      simp [oqD, hij]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hterm i j))] at h
  have hsum : ∑ i : ZMod 68, ∑ j : ZMod 68, (1 + oqD i j * (G 0 0 ^ 2 - 1)) =
      4624 + (G 0 0 ^ 2 - 1) := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib), Finset.sum_add_distrib]
    have h1 : ∑ i : ZMod 68, ∑ j : ZMod 68, oqD i j * (G 0 0 ^ 2 - 1) = G 0 0 ^ 2 - 1 := by
      rw [Fintype.sum_eq_single 0]
      · rw [Fintype.sum_eq_single 0]
        · simp [oqD]
        · intro j hj
          simp [oqD, hj]
      · intro i hi
        apply Finset.sum_eq_zero
        intro j _
        simp [oqD, hi]
    rw [h1]
    simp [ZMod.card]
    norm_num
  rw [hsum] at h
  simp only [if_true] at h
  linear_combination 68 * h

theorem oq_Phi_star (ψ : AddChar (ZMod 68) ℂ) (Φ : ZMod 68 → ℂ)
    (hΦsq : ∀ x, Φ x ^ 2 = ψ (x ^ 2)) (hΦnorm : ∀ x, ‖Φ x‖ = 1) (x : ZMod 68) :
    star (Φ x) = Φ x * ψ (-(x ^ 2)) := by
  have hn := hΦnorm x
  have h0 : Φ x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  rw [show star (Φ x) = (Φ x)⁻¹ from (Complex.inv_eq_conj hn).symm, AddChar.map_neg_eq_inv,
    ← hΦsq, pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]

theorem oq_Phi_neg (ψ : AddChar (ZMod 68) ℂ) (Φ : ZMod 68 → ℂ) (hΦ0 : Φ 0 = 1)
    (hΦmul : ∀ x y, Φ (x + y) = Φ x * Φ y * ψ (x * y))
    (hΦsq : ∀ x, Φ x ^ 2 = ψ (x ^ 2)) (hΦnorm : ∀ x, ‖Φ x‖ = 1) (x : ZMod 68) :
    Φ (-x) = Φ x := by
  have h1 := hΦmul x (-x)
  rw [add_neg_cancel, hΦ0, show x * -x = -(x ^ 2) by ring] at h1
  have h2 := oq_Phi_star ψ Φ hΦsq hΦnorm x
  have hn := hΦnorm x
  have h0 : Φ x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have h3 : star (Φ x) * Φ x = 1 := by
    rw [show star (Φ x) = (Φ x)⁻¹ from (Complex.inv_eq_conj hn).symm, inv_mul_cancel₀ h0]
  calc Φ (-x) = Φ (-x) * (star (Φ x) * Φ x) := by rw [h3, mul_one]
    _ = (Φ x * Φ (-x) * ψ (-(x ^ 2))) * Φ x := by rw [h2]; ring
    _ = Φ x := by rw [← h1, one_mul]

theorem oq_G_star (ψ : AddChar (ZMod 68) ℂ) (G : ZMod 68 → ZMod 68 → ℂ)
    (hrefl' : ∀ i j, (i, j) ≠ (0, 0) → G i j * G (-i) (-j) = ψ (-(i ^ 2 - i * j + j ^ 2)))
    (hcirc : ∀ i j, (i, j) ≠ (0, 0) → ‖G i j‖ = 1) (a b : ZMod 68) (hne : (a, b) ≠ (0, 0)) :
    star (G a b) = G (-a) (-b) * ψ (a ^ 2 - a * b + b ^ 2) := by
  have h1 := hrefl' a b hne
  have hn := hcirc a b hne
  have h0 : G a b ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hq : ψ (-(a ^ 2 - a * b + b ^ 2)) * ψ (a ^ 2 - a * b + b ^ 2) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  calc star (G a b) = (G a b)⁻¹ := (Complex.inv_eq_conj hn).symm
    _ = (G a b)⁻¹ * (ψ (-(a ^ 2 - a * b + b ^ 2)) * ψ (a ^ 2 - a * b + b ^ 2)) := by
        rw [hq, mul_one]
    _ = (G a b)⁻¹ * (G a b * G (-a) (-b) * ψ (a ^ 2 - a * b + b ^ 2)) := by rw [h1]
    _ = G (-a) (-b) * ψ (a ^ 2 - a * b + b ^ 2) := by
        rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]

theorem oq_K_star (ψ : AddChar (ZMod 68) ℂ) (G K : ZMod 68 → ZMod 68 → ℂ) (Φ : ZMod 68 → ℂ)
    (hK : ∀ x y, K x y = G x y * Φ (x - y)) (hΦ0 : Φ 0 = 1)
    (hΦmul : ∀ x y, Φ (x + y) = Φ x * Φ y * ψ (x * y))
    (hΦsq : ∀ x, Φ x ^ 2 = ψ (x ^ 2)) (hΦnorm : ∀ x, ‖Φ x‖ = 1)
    (hrefl' : ∀ i j, (i, j) ≠ (0, 0) → G i j * G (-i) (-j) = ψ (-(i ^ 2 - i * j + j ^ 2)))
    (hcirc : ∀ i j, (i, j) ≠ (0, 0) → ‖G i j‖ = 1) (a b : ZMod 68) (hne : (a, b) ≠ (0, 0)) :
    star (K a b) = ψ (a * b) * K (-a) (-b) := by
  rw [hK, hK, star_mul', oq_G_star ψ G hrefl' hcirc a b hne, oq_Phi_star ψ Φ hΦsq hΦnorm,
    show -a - -b = -(a - b) by ring, oq_Phi_neg ψ Φ hΦ0 hΦmul hΦsq hΦnorm]
  have hp : ψ (a ^ 2 - a * b + b ^ 2) * ψ (-((a - b) ^ 2)) = ψ (a * b) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  linear_combination (G (-a) (-b) * Φ (a - b)) * hp

theorem oq_main (F : ZMod 68 → ZMod 68 → ℂ) (τ : ℂ →+* ℂ)
    (hreflect : ∀ i j, (i, j) ≠ (0, 0) →
      F i j * F (-i) (-j) = (ZMod.stdAddChar (i ^ 2 - i * j + j ^ 2))⁻¹)
    (hconv : ∀ r s, (68 : ℂ)⁻¹ * ∑ i, ∑ j, F i j * F (r - i) (s - j) *
      ZMod.stdAddChar (i ^ 2 - i * j + j ^ 2) * ZMod.stdAddChar (-i * r + j * (r - s)) =
      (Real.sqrt 65 : ℂ) * F r s + if (r, s) = (0, 0) then 68 else 0)
    (hcircle : ∀ i j, (i, j) ≠ (0, 0) → ‖τ (F i j)‖ = 1) :
    ∃ A : Matrix (ZMod 68) (ZMod 68) ℂ, A.IsHermitian ∧ A * A = A ∧ A.trace = 1 ∧
      ∀ a b : ZMod 68, (a, b) ≠ (0, 0) →
        Complex.normSq (∑ t, A (t + a) t * ZMod.stdAddChar (b * t)) = (69 : ℝ)⁻¹ := by
  -- the conjugated character
  set ψ : AddChar (ZMod 68) ℂ := τ.toMonoidHom.compAddChar (ZMod.stdAddChar (N := 68)) with hψdef
  have hψ : ∀ t, ψ t = τ (ZMod.stdAddChar t) := fun t => rfl
  have hψprim : ψ.IsPrimitive :=
    AddChar.IsPrimitive.compMulHom_of_isPrimitive (ZMod.isPrimitive_stdAddChar 68) τ.injective
  set G : ZMod 68 → ZMod 68 → ℂ := fun i j => τ (F i j) with hGdef
  set σ : ℂ := τ (Real.sqrt 65 : ℂ) with hσdef
  have hσ : σ ^ 2 = 65 := by
    rw [hσdef, ← map_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    have h65 : (((65 : ℝ) : ℂ)) = (65 : ℂ) := by norm_num
    rw [h65]
    exact map_ofNat τ 65
  have hrefl' : ∀ i j, (i, j) ≠ (0, 0) → G i j * G (-i) (-j) = ψ (-(i ^ 2 - i * j + j ^ 2)) := by
    intro i j h
    have h1 := congrArg τ (hreflect i j h)
    rw [map_mul, map_inv₀] at h1
    rw [AddChar.map_neg_eq_inv, hψ]
    exact h1
  have hconv' : ∀ r s, (68 : ℂ)⁻¹ * ∑ i, ∑ j, G i j * G (r - i) (s - j) *
      ψ (i ^ 2 - i * j + j ^ 2) * ψ (-i * r + j * (r - s)) =
      σ * G r s + if (r, s) = (0, 0) then 68 else 0 := by
    intro r s
    have h := congrArg τ (hconv r s)
    simp only [map_mul, map_sum, map_inv₀, map_add, map_ofNat] at h
    rw [show τ (if (r, s) = (0, 0) then (68 : ℂ) else 0) = if (r, s) = (0, 0) then 68 else 0 by
      split_ifs
      · exact map_ofNat τ 68
      · exact map_zero τ] at h
    exact h
  have hcirc : ∀ i j, (i, j) ≠ (0, 0) → ‖G i j‖ = 1 := hcircle
  -- the half character
  obtain ⟨η, hη⟩ := IsAlgClosed.exists_pow_nat_eq (ψ 1) (by norm_num : 0 < 2)
  set Φ : ZMod 68 → ℂ := fun x => η ^ (x.val ^ 2) with hΦdef
  have hΦ0 : Φ 0 = 1 := by
    rw [hΦdef]
    simp
  have hΦmul : ∀ x y, Φ (x + y) = Φ x * Φ y * ψ (x * y) := oq_half_mul ψ η hη
  have hΦsq : ∀ x, Φ x ^ 2 = ψ (x ^ 2) := oq_half_sq ψ η hη
  have hΦnorm : ∀ x, ‖Φ x‖ = 1 := fun x => oq_half_norm ψ η hη _
  -- the scalar lambda
  have hx0 := oq_x0_eq ψ G σ hrefl' hconv'
  obtain ⟨l, hl1, hl2⟩ := oq_lambda σ (G 0 0) hσ hx0
  set K : ZMod 68 → ZMod 68 → ℂ := fun a b => G a b * Φ (a - b) with hKdef
  have hK : ∀ x y, K x y = G x y * Φ (x - y) := fun x y => rfl
  set mu : ℂ := 1 - (l : ℂ) * G 0 0 with hmu
  set H : ZMod 68 → ZMod 68 → ℂ := fun a b => (l : ℂ) * K a b + mu * oqD a b with hHdef
  have hH : ∀ a b, H a b = (l : ℂ) * K a b + mu * oqD a b := fun a b => rfl
  have h00 : H 0 0 = 1 := by
    rw [hH, hK, hmu]
    simp [oqD, hΦ0]
  have hconvH : ∀ a b, (∑ c, ∑ β, H (a - c) β * H c (b - β) * ψ (-(β * c))) = 68 * H a b := by
    intro a b
    simp only [hH]
    rw [oq_conv_affine ψ K (l : ℂ) mu a b, oq_K_conv ψ G K Φ σ hK hΦ0 hΦmul hconv' a b]
    have c1 : 68 * (l : ℂ) ^ 2 * σ + 2 * (l : ℂ) * mu = 68 * (l : ℂ) := by
      rw [hmu]
      linear_combination (l : ℂ) * hl1
    have hl2' : 69 * (l : ℂ) ^ 2 = 1 := by exact_mod_cast hl2
    have c2 : 4624 * (l : ℂ) ^ 2 + mu ^ 2 = 68 * mu := by
      rw [hmu]
      linear_combination (1156 * (l : ℂ) ^ 2) * hσ + 1156 * hl2' +
        (((l : ℂ) * (68 * σ - 2 * G 0 0) - 66) / 4 - 34 * (l : ℂ) * σ) * hl1
    linear_combination (K a b) * c1 + (oqD a b) * c2
  have hsymm : ∀ a b, star (H a b) = ψ (a * b) * H (-a) (-b) := by
    intro a b
    by_cases h : a = 0 ∧ b = 0
    · obtain ⟨rfl, rfl⟩ := h
      rw [neg_zero, h00, mul_zero, AddChar.map_zero_eq_one, star_one, one_mul]
    · have hne : (a, b) ≠ (0, 0) := by
        rw [Ne, Prod.mk.injEq]
        exact h
      have h' : ¬ (-a = 0 ∧ -b = 0) := by
        rwa [neg_eq_zero, neg_eq_zero]
      rw [hH, hH]
      simp only [oqD, if_neg h, if_neg h', mul_zero, add_zero]
      rw [star_mul', Complex.star_def, Complex.conj_ofReal,
        ← Complex.star_def, oq_K_star ψ G K Φ hK hΦ0 hΦmul hΦsq hΦnorm hrefl' hcirc a b hne]
      ring
  have hnorm : ∀ a b, (a, b) ≠ (0, 0) → Complex.normSq (H a b) = (69 : ℝ)⁻¹ := by
    intro a b hne
    have h : ¬ (a = 0 ∧ b = 0) := by
      rwa [Ne, Prod.mk.injEq] at hne
    rw [hH, hK]
    simp only [oqD, if_neg h, mul_zero, add_zero]
    rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.normSq_eq_norm_sq (G a b), Complex.normSq_eq_norm_sq (Φ (a - b)), hcirc a b hne,
      hΦnorm]
    linear_combination hl2 / 69
  -- the matrix
  refine ⟨oqA ψ H, oq_herm ψ H hsymm, oq_idem ψ H hconvH, by rw [oq_trace ψ hψprim H, h00], ?_⟩
  intro a b hab
  obtain ⟨m, -, hm⟩ := (oq_prim_root ψ hψprim).eq_pow_of_pow_eq_one
    (oq_char_pow68 ZMod.stdAddChar 1)
  have he : ∀ c, ZMod.stdAddChar c = ψ ((m : ZMod 68) * c) := by
    intro c
    rw [oq_char_pow ZMod.stdAddChar c, ← hm, ← pow_mul, oq_char_natCast]
    push_cast
    rw [ZMod.natCast_zmod_val]
  have hsum : ∑ t, oqA ψ H (t + a) t * ZMod.stdAddChar (b * t) = H a (m * b) := by
    rw [← oq_charfn ψ hψprim H a (m * b)]
    apply Finset.sum_congr rfl
    intro t _
    rw [he, mul_assoc]
  rw [hsum]
  have hab' : (a, (m : ZMod 68) * b) ≠ (0, 0) := by
    intro h
    rw [Prod.mk.injEq] at h
    apply hab
    have hb : b = 0 := by
      have h1 : ZMod.stdAddChar b = 1 := by
        rw [he, h.2, AddChar.map_zero_eq_one]
      exact (AddChar.IsPrimitive.zmod_char_eq_one_iff 68 (ZMod.isPrimitive_stdAddChar 68) b).mp h1
    rw [h.1, hb]
  exact hnorm a (m * b) hab'

end OMA.Helpers

theorem OMA.solution : OMA.R_OpenQuantumProblem23_hasSICPOVM_68_R1.H2 := by
  intro F τ _hzero hreflect hconv hcircle
  exact OMA.Helpers.oq_main F τ hreflect hconv hcircle
