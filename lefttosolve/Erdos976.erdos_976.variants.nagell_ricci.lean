import FormalConjectures.ErdosProblems.«976»

/-!
# Erdős Problem 976, the Nagell-Ricci bound `F_f(n) ≫ n log n`

`f` is an irreducible integer polynomial of degree `d ≥ 2`, `Z = ∏_{m ≤ n} |f m|` and `F f n` is
the greatest prime factor of `Z`.  The proof is elementary (no number fields, no prime ideal
theorem) and compares two evaluations of `log Z = ∑_p v_p(Z) log p`.

* Lower bound (`log_prod_ge`): `|f m| ≥ m ^ d / (2L) ^ d`, hence `log Z ≥ d (n log n - n) - O(n)`.
* Primes `p > n` (`factorization_le_large`): `v_p(Z) ≤ d ^ 2`, so their contribution is at most
  `d ^ 2 θ(F f n) ≤ d ^ 2 log 4 * F f n` (Chebyshev).
* Primes `p ≤ n` (`small_part`): `v_p(Z) = ∑_k cnt (p ^ k)` where `cnt q` counts the `m ≤ n` with
  `q ∣ f m`.  For `k = 1` this is at most `rho p * (n / p + 1)`; for `k ≥ 2` a Hensel-type
  uniqueness statement obtained from a Bezout identity `f u + f' v = R ≠ 0` (`lifting`,
  `cnt_pow_le`) gives `cnt (p ^ k) ≤ B (n / p ^ k + 1)`.  So the contribution is
  `n ∑_{p ≤ n} rho p log p / p + O(n)`.
* The saving (`saving`): `∑_{p ≤ n} rho p log p / p ≤ (d / 2) log n + O(1)`.  With the binary
  form `G a b = b ^ d f (a / b)` and the box `[0, N) ^ 2`, `N ^ 2 ≈ n`: for a root `r` of `f`
  modulo `p` the pairs `(u, v)` of box points with `u - v` in the lattice `a ≡ r b (mod p)` number
  at least `N ^ 4 / p` by Cauchy-Schwarz, `p ∣ G (u - v)` for such pairs, the lattices of two
  roots meet in `p ℤ ^ 2` only, and `∑_{u ≠ v} log |G (u - v)| ≤ N ^ 4 (d log N + O(1))`.

Since `d / 2 < d`, the primes `p > n` must carry `(d / 2) n log n - O(n)`, which is the claim.
-/

open Polynomial Finset

namespace OMA.Helpers

/-- sum of absolute values of the coefficients -/
noncomputable def Lf (f : ℤ[X]) : ℕ := ∑ i ∈ range (f.natDegree + 1), (f.coeff i).natAbs

/-- homogenization of `f` -/
noncomputable def G (f : ℤ[X]) (a b : ℤ) : ℤ :=
  ∑ i ∈ range (f.natDegree + 1), f.coeff i * a ^ i * b ^ (f.natDegree - i)

/-- number of roots of `f` modulo `p` among `0, ..., p-1` -/
noncomputable def rho (f : ℤ[X]) (p : ℕ) : ℕ :=
  ((range p).filter (fun r : ℕ => (p : ℤ) ∣ f.eval (r : ℤ))).card

/-- number of `m` in `[1,n]` with `q ∣ f m` -/
noncomputable def cnt (f : ℤ[X]) (n q : ℕ) : ℕ :=
  ((Icc 1 n).filter (fun m : ℕ => (q : ℤ) ∣ f.eval (m : ℤ))).card

/-- no integer roots -/
lemma eval_ne_zero (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (m : ℤ) :
    f.eval m ≠ 0 :=
  hf.not_isRoot_of_natDegree_ne_one (x := m) (by omega)

/-- Bezout identity between `f` and its derivative, with a nonzero integer constant. -/
lemma bezout (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) :
    ∃ R : ℤ, R ≠ 0 ∧ ∃ u v : ℤ[X], ∀ m : ℤ,
      f.eval m * u.eval m + (derivative f).eval m * v.eval m = R := by
  have hprim : f.IsPrimitive := hf.isPrimitive (by omega)
  have hirr := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).1 hf
  have hinj : Function.Injective (Int.castRingHom ℚ) := RingHom.injective_int _
  obtain ⟨p, q, -, -, hpq⟩ := exists_mul_add_mul_eq_C_resultant f (derivative f)
    (m := f.natDegree) (n := (derivative f).natDegree) le_rfl le_rfl (Or.inl (by omega))
  refine ⟨f.resultant (derivative f) f.natDegree (derivative f).natDegree, ?_, p, q, ?_⟩
  · intro h0
    have hcop : IsCoprime (f.map (Int.castRingHom ℚ)) (derivative (f.map (Int.castRingHom ℚ))) :=
      (separable_def _).1 hirr.separable
    have hne := resultant_ne_zero _ _ hcop
    apply hne
    have h1 : (f.map (Int.castRingHom ℚ)).natDegree = f.natDegree :=
      natDegree_map_eq_of_injective hinj f
    have h2 : (derivative (f.map (Int.castRingHom ℚ))).natDegree = (derivative f).natDegree := by
      rw [derivative_map]
      exact natDegree_map_eq_of_injective hinj _
    rw [h1, h2, derivative_map, resultant_map_map, h0]
    simp
  · intro m
    have := congrArg (Polynomial.eval m) hpq
    simpa using this

lemma rho_le (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) {p : ℕ} (hp : p.Prime) :
    rho f p ≤ f.natDegree := by
  have := Fact.mk hp
  have hg0 : f.map (Int.castRingHom (ZMod p)) ≠ 0 := by
    intro h0
    have hprim : f.IsPrimitive := hf.isPrimitive (by omega)
    have hdvd : C (p : ℤ) ∣ f := by
      rw [C_dvd_iff_dvd_coeff]
      intro i
      have h1 : (f.map (Int.castRingHom (ZMod p))).coeff i = 0 := by rw [h0]; simp
      rw [coeff_map] at h1
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by simpa using h1)
    have h2 := Int.isUnit_iff.1 (hprim _ hdvd)
    have h3 := hp.two_le
    omega
  calc rho f p ≤ (f.map (Int.castRingHom (ZMod p))).roots.toFinset.card := by
        unfold rho
        apply Finset.card_le_card_of_injOn (fun r : ℕ => (r : ZMod p))
        · intro r hr
          simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hr
          simp only [mem_coe, Multiset.mem_toFinset]
          rw [mem_roots hg0, IsRoot.def]
          have h1 := eval_intCast_map (Int.castRingHom (ZMod p)) f (r : ℤ)
          simp only [Int.cast_natCast, eq_intCast] at h1
          rw [h1]
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hr.2
        · intro a ha b hb hab
          simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at ha hb
          have h1 := (ZMod.natCast_eq_natCast_iff' a b p).1 hab
          rwa [Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at h1
    _ ≤ Multiset.card (f.map (Int.castRingHom (ZMod p))).roots := Multiset.toFinset_card_le _
    _ ≤ (f.map (Int.castRingHom (ZMod p))).natDegree := card_roots' _
    _ ≤ f.natDegree := natDegree_map_le

lemma G_one (f : ℤ[X]) (a : ℤ) : G f a 1 = f.eval a := by
  rw [eval_eq_sum_range]
  simp [G]

lemma G_abs_le (f : ℤ[X]) (a b : ℤ) (N : ℕ) (ha : |a| ≤ N) (hb : |b| ≤ N) :
    |G f a b| ≤ (Lf f : ℤ) * (N : ℤ) ^ f.natDegree := by
  unfold G Lf
  push_cast
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i hi => ?_))
  have hi' : i ≤ f.natDegree := by
    have := Finset.mem_range.1 hi
    omega
  rw [abs_mul, abs_mul, abs_pow, abs_pow, mul_assoc]
  have h1 : |a| ^ i * |b| ^ (f.natDegree - i) ≤ (N : ℤ) ^ i * (N : ℤ) ^ (f.natDegree - i) :=
    mul_le_mul (pow_le_pow_left₀ (abs_nonneg a) ha i)
      (pow_le_pow_left₀ (abs_nonneg b) hb _) (by positivity) (by positivity)
  rw [← pow_add, Nat.add_sub_cancel' hi'] at h1
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

lemma G_ne_zero (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (a b : ℤ)
    (hab : a ≠ 0 ∨ b ≠ 0) : G f a b ≠ 0 := by
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := by tauto
    have h1 : G f a 0 = f.leadingCoeff * a ^ f.natDegree := by
      unfold G
      rw [Finset.sum_eq_single f.natDegree]
      · simp
      · intro i hi hne
        have := Finset.mem_range.1 hi
        have h2 : f.natDegree - i ≠ 0 := by omega
        simp [h2]
      · intro h
        exact absurd (Finset.mem_range.2 (Nat.lt_succ_self _)) h
    rw [h1]
    have hf0 : f ≠ 0 := hf.ne_zero
    exact mul_ne_zero (leadingCoeff_ne_zero.2 hf0) (pow_ne_zero _ ha)
  · have hprim : f.IsPrimitive := hf.isPrimitive (by omega)
    have hirr := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).1 hf
    have hdeg : (f.map (Int.castRingHom ℚ)).natDegree = f.natDegree :=
      natDegree_map_eq_of_injective (RingHom.injective_int _) f
    have hroot : (f.map (Int.castRingHom ℚ)).eval ((a : ℚ) / b) ≠ 0 :=
      hirr.not_isRoot_of_natDegree_ne_one (x := (a : ℚ) / b) (by omega)
    have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    have key : ((G f a b : ℤ) : ℚ)
        = (b : ℚ) ^ f.natDegree * (f.map (Int.castRingHom ℚ)).eval ((a : ℚ) / b) := by
      rw [eval_map, eval₂_eq_sum_range, Finset.mul_sum]
      unfold G
      push_cast
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' : i ≤ f.natDegree := by
        have := Finset.mem_range.1 hi
        omega
      have h3 : (b : ℚ) ^ f.natDegree = (b : ℚ) ^ i * (b : ℚ) ^ (f.natDegree - i) := by
        rw [← pow_add, Nat.add_sub_cancel' hi']
      rw [h3, div_pow]
      simp only [eq_intCast]
      field_simp
    intro h0
    rw [h0] at key
    simp only [Int.cast_zero] at key
    exact hroot (by
      rcases mul_eq_zero.1 key.symm with h | h
      · exact absurd (pow_eq_zero_iff (by omega) |>.1 h) hbq
      · exact h)

lemma Lf_pos (f : ℤ[X]) (hf0 : f ≠ 0) : 1 ≤ Lf f := by
  unfold Lf
  have h1 : (f.coeff f.natDegree).natAbs ≤ ∑ i ∈ range (f.natDegree + 1), (f.coeff i).natAbs :=
    Finset.single_le_sum (f := fun i => (f.coeff i).natAbs) (fun i _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.lt_succ_self _))
  have h2 : 1 ≤ (f.coeff f.natDegree).natAbs := by
    rw [Nat.one_le_iff_ne_zero, Int.natAbs_ne_zero]
    exact leadingCoeff_ne_zero.2 hf0
  omega

/-- `p ^ k ∣ h * w` and `¬ p ^ (e + 1) ∣ w` give `p ^ (k - e) ∣ h`. -/
lemma pow_dvd_of_pow_dvd_mul {p : ℤ} (hp : Prime p) :
    ∀ (e k : ℕ) (h w : ℤ), p ^ k ∣ h * w → ¬ p ^ (e + 1) ∣ w → p ^ (k - e) ∣ h := by
  intro e
  induction e with
  | zero =>
    intro k h w h1 h2
    simp only [zero_add, pow_one] at h2
    simpa using hp.pow_dvd_of_dvd_mul_right k h2 h1
  | succ e ih =>
    intro k h w h1 h2
    by_cases hw : p ∣ w
    · obtain ⟨w', rfl⟩ := hw
      rcases k with _ | k
      · simp
      · have h3 : p ^ k ∣ h * w' := by
          have h5 : p ^ (k + 1) ∣ p * (h * w') := by
            rw [show p * (h * w') = h * (p * w') by ring]
            exact h1
          rw [pow_succ'] at h5
          exact (mul_dvd_mul_iff_left hp.ne_zero).1 h5
        have h4 : ¬ p ^ (e + 1) ∣ w' := by
          intro h5
          apply h2
          rw [pow_succ']
          exact mul_dvd_mul_left p h5
        have h6 := ih k h w' h3 h4
        rwa [show k + 1 - (e + 1) = k - e by omega]
    · have h6 := hp.pow_dvd_of_dvd_mul_right k hw h1
      exact (pow_dvd_pow p (by omega)).trans h6

/-- Hensel-type uniqueness: two roots modulo `p ^ k` that agree modulo `p ^ (e + 1)` agree
modulo `p ^ (k - e)`, where `p ^ (e + 1)` does not divide the Bezout constant. -/
lemma lifting (f u v : ℤ[X]) (R : ℤ)
    (hR : ∀ m : ℤ, f.eval m * u.eval m + (derivative f).eval m * v.eval m = R)
    {p : ℕ} (hp : p.Prime) (e k : ℕ) (hek : e + 1 ≤ k) (hpR : ¬ (p : ℤ) ^ (e + 1) ∣ R)
    (m m' : ℤ) (h1 : (p : ℤ) ^ k ∣ f.eval m) (h2 : (p : ℤ) ^ k ∣ f.eval m')
    (h3 : (p : ℤ) ^ (e + 1) ∣ m' - m) : (p : ℤ) ^ (k - e) ∣ m' - m := by
  obtain ⟨c, hc⟩ := f.binomExpansion m (m' - m)
  have hm' : m + (m' - m) = m' := by ring
  rw [hm'] at hc
  have h4 : (p : ℤ) ^ k ∣ (m' - m) * ((derivative f).eval m + c * (m' - m)) := by
    have h5 : (m' - m) * ((derivative f).eval m + c * (m' - m)) = f.eval m' - f.eval m := by
      rw [hc]; ring
    rw [h5]
    exact dvd_sub h2 h1
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  apply pow_dvd_of_pow_dvd_mul hpz e k _ _ h4
  intro h5
  apply hpR
  have h6 : (p : ℤ) ^ (e + 1) ∣ (derivative f).eval m := by
    have h8 := dvd_sub h5 (Dvd.dvd.mul_left h3 c)
    simpa using h8
  have h7 : (p : ℤ) ^ (e + 1) ∣ f.eval m := (pow_dvd_pow _ hek).trans h1
  rw [← hR m]
  exact dvd_add (Dvd.dvd.mul_right h7 _) (Dvd.dvd.mul_right h6 _)

lemma card_le_of_modEq {n q : ℕ} (_hq : 0 < q) (S : Finset ℕ) (hS : ∀ x ∈ S, x ≤ n)
    (h : ∀ x ∈ S, ∀ y ∈ S, x % q = y % q) : S.card ≤ n / q + 1 := by
  have h0 : S.card ≤ (range (n / q + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun x => x / q)
    · intro x hx
      simp only [coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (hS x hx))
    · intro x hx y hy hxy
      have h1 := h x hx y hy
      have h2 := Nat.div_add_mod x q
      have h3 := Nat.div_add_mod y q
      simp only at hxy
      rw [hxy, h1] at h2
      omega
  simpa using h0

lemma card_le_mul_of_fibers {α : Type*} [DecidableEq α] {n q : ℕ} (hq : 0 < q) (S : Finset ℕ)
    (hS : ∀ x ∈ S, x ≤ n) (φ : ℕ → α) (T : Finset α) (hφ : ∀ x ∈ S, φ x ∈ T)
    (h : ∀ x ∈ S, ∀ y ∈ S, φ x = φ y → x % q = y % q) : S.card ≤ T.card * (n / q + 1) := by
  rw [mul_comm]
  apply Finset.card_le_mul_card_image_of_maps_to hφ
  intro b hb
  apply card_le_of_modEq hq
  · intro x hx
    exact hS x (Finset.mem_filter.1 hx).1
  · intro x hx y hy
    have hx' := Finset.mem_filter.1 hx
    have hy' := Finset.mem_filter.1 hy
    exact h x hx'.1 y hy'.1 (hx'.2.trans hy'.2.symm)

lemma dvd_eval_mod (f : ℤ[X]) {q : ℕ} (x : ℕ) (hx : (q : ℤ) ∣ f.eval (x : ℤ)) :
    (q : ℤ) ∣ f.eval ((x % q : ℕ) : ℤ) := by
  have h1 : ((x : ℤ) - ((x % q : ℕ) : ℤ)) ∣ f.eval (x : ℤ) - f.eval ((x % q : ℕ) : ℤ) :=
    sub_dvd_eval_sub _ _ f
  have h2 : (q : ℤ) ∣ (x : ℤ) - ((x % q : ℕ) : ℤ) :=
    Nat.modEq_iff_dvd.1 (Nat.mod_modEq x q)
  exact (dvd_sub_right hx).1 (h2.trans h1)

lemma cnt_prime_le (f : ℤ[X]) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    cnt f n p ≤ rho f p * (n / p + 1) := by
  unfold cnt rho
  apply card_le_mul_of_fibers hp.pos _
    (fun x hx => (Finset.mem_Icc.1 (Finset.mem_filter.1 hx).1).2) (fun x => x % p)
  · intro x hx
    have hx' := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.mod_lt _ hp.pos), dvd_eval_mod f x hx'.2⟩
  · intro x _ y _ hxy
    exact hxy

lemma cnt_pow_le_cnt (f : ℤ[X]) (p n k : ℕ) (hk : 1 ≤ k) : cnt f n (p ^ k) ≤ cnt f n p := by
  unfold cnt
  apply Finset.card_le_card
  intro x hx
  have hx' := Finset.mem_filter.1 hx
  refine Finset.mem_filter.2 ⟨hx'.1, ?_⟩
  have h1 : (p : ℤ) ∣ ((p ^ k : ℕ) : ℤ) := by
    push_cast
    exact dvd_pow_self _ (by omega)
  exact h1.trans hx'.2

lemma cnt_le_self (f : ℤ[X]) (n q : ℕ) : cnt f n q ≤ n := by
  unfold cnt
  calc ((Icc 1 n).filter (fun m : ℕ => (q : ℤ) ∣ f.eval (m : ℤ))).card ≤ (Icc 1 n).card :=
        Finset.card_filter_le _ _
    _ = n := by simp

/-- uniform bound on the number of roots of `f` modulo prime powers in an interval -/
lemma cnt_pow_le (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) :
    ∃ B : ℕ, f.natDegree ≤ B ∧ ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ,
      (cnt f n (p ^ k) : ℝ) ≤ B * ((n : ℝ) / (p : ℝ) ^ k + 1) := by
  obtain ⟨R, hR0, u, v, hR⟩ := bezout f hf hd
  refine ⟨f.natDegree + R.natAbs ^ 3, Nat.le_add_right _ _, ?_⟩
  intro p hp k hk n
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hRabs : (1 : ℝ) ≤ (R.natAbs : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Int.natAbs_ne_zero.2 hR0)
  have hpk0 : (0 : ℝ) < (p : ℝ) ^ k := by positivity
  have hfrac : (0 : ℝ) ≤ (n : ℝ) / (p : ℝ) ^ k := by positivity
  by_cases hpR : (p : ℤ) ∣ R
  · -- bad prime
    set e := R.natAbs.factorization p with he
    have he1 : p ^ e ∣ R.natAbs := Nat.ordProj_dvd _ _
    have he2 : ¬ p ^ (e + 1) ∣ R.natAbs :=
      Nat.pow_succ_factorization_not_dvd (Int.natAbs_ne_zero.2 hR0) hp
    have he2' : ¬ (p : ℤ) ^ (e + 1) ∣ R := by
      intro h
      apply he2
      have h' : ((p ^ (e + 1) : ℕ) : ℤ) ∣ R := by push_cast; exact h
      exact Int.natCast_dvd.1 h'
    have he0 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · exfalso
        apply he2
        rw [h]
        simpa using Int.natCast_dvd.1 hpR
      · exact h
    have hpe : p ^ e ≤ R.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hR0) he1
    have hpeR : ((p : ℝ)) ^ e ≤ (R.natAbs : ℝ) := by exact_mod_cast hpe
    have hpple : (p : ℝ) ≤ (p : ℝ) ^ e := le_self_pow₀ hp1 (by omega)
    have hpe0 : (0 : ℝ) < (p : ℝ) ^ e := by positivity
    have hBge : ((R.natAbs : ℝ)) ^ 3 ≤ ((f.natDegree + R.natAbs ^ 3 : ℕ) : ℝ) := by
      push_cast
      linarith [(Nat.cast_nonneg f.natDegree : (0 : ℝ) ≤ f.natDegree)]
    have hsum0 : (0 : ℝ) ≤ (n : ℝ) / (p : ℝ) ^ k + 1 := by linarith
    refine le_trans ?_ (mul_le_mul_of_nonneg_right hBge hsum0)
    by_cases hke : k ≤ e
    · -- trivial bound
      have h1 : (cnt f n (p ^ k) : ℝ) ≤ n := by exact_mod_cast cnt_le_self f n _
      have h2 : (p : ℝ) ^ k ≤ (p : ℝ) ^ e := pow_le_pow_right₀ hp1 hke
      have h3 : (n : ℝ) = (p : ℝ) ^ k * ((n : ℝ) / (p : ℝ) ^ k) := by field_simp
      have h4 : (p : ℝ) ^ k ≤ (R.natAbs : ℝ) ^ 3 := by
        calc (p : ℝ) ^ k ≤ (R.natAbs : ℝ) := h2.trans hpeR
          _ ≤ (R.natAbs : ℝ) ^ 3 := le_self_pow₀ hRabs (by norm_num)
      calc (cnt f n (p ^ k) : ℝ) ≤ (p : ℝ) ^ k * ((n : ℝ) / (p : ℝ) ^ k) := by rw [← h3]; exact h1
        _ ≤ (R.natAbs : ℝ) ^ 3 * ((n : ℝ) / (p : ℝ) ^ k) :=
            mul_le_mul_of_nonneg_right h4 hfrac
        _ ≤ (R.natAbs : ℝ) ^ 3 * ((n : ℝ) / (p : ℝ) ^ k + 1) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith
    · have hke' : e + 1 ≤ k := by omega
      have h1 : cnt f n (p ^ k) ≤ p ^ (e + 1) * (n / p ^ (k - e) + 1) := by
        unfold cnt
        have h2 := card_le_mul_of_fibers (q := p ^ (k - e)) (n := n) (pow_pos hp.pos _)
          ((Icc 1 n).filter (fun m : ℕ => ((p ^ k : ℕ) : ℤ) ∣ f.eval (m : ℤ)))
          (fun x hx => (Finset.mem_Icc.1 (Finset.mem_filter.1 hx).1).2)
          (fun x => x % p ^ (e + 1)) (range (p ^ (e + 1)))
          (fun x _ => Finset.mem_range.2 (Nat.mod_lt _ (pow_pos hp.pos _)))
          (by
            intro x hx y hy hxy
            have hx' := (Finset.mem_filter.1 hx).2
            have hy' := (Finset.mem_filter.1 hy).2
            push_cast at hx' hy'
            have h3 : (p : ℤ) ^ (e + 1) ∣ (y : ℤ) - x := by
              have := Nat.modEq_iff_dvd.1 (show x ≡ y [MOD p ^ (e + 1)] from hxy)
              simpa using this
            have h4 := lifting f u v R hR hp e k hke' he2' x y hx' hy' h3
            have h5 : x ≡ y [MOD p ^ (k - e)] := by
              apply Nat.modEq_iff_dvd.2
              push_cast
              exact h4
            exact h5)
        simpa using h2
      have h2 : (cnt f n (p ^ k) : ℝ) ≤ (p : ℝ) ^ (e + 1) * ((n : ℝ) / (p : ℝ) ^ (k - e) + 1) := by
        have h3 : (cnt f n (p ^ k) : ℝ) ≤ ((p ^ (e + 1) * (n / p ^ (k - e) + 1) : ℕ) : ℝ) := by
          exact_mod_cast h1
        refine h3.trans ?_
        push_cast
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h4 : ((n / p ^ (k - e) : ℕ) : ℝ) ≤ (n : ℝ) / ((p ^ (k - e) : ℕ) : ℝ) := Nat.cast_div_le
        push_cast at h4
        linarith
      have h5 : (p : ℝ) ^ (k - e) * (p : ℝ) ^ e = (p : ℝ) ^ k := by
        rw [← pow_add]; congr 1; omega
      have h6 : (n : ℝ) / (p : ℝ) ^ (k - e) = (p : ℝ) ^ e * ((n : ℝ) / (p : ℝ) ^ k) := by
        rw [← h5]; field_simp
      have h7 : (p : ℝ) ^ (e + 1) = (p : ℝ) * (p : ℝ) ^ e := pow_succ' _ _
      have h8 : (p : ℝ) * (p : ℝ) ^ e * (p : ℝ) ^ e ≤ (R.natAbs : ℝ) ^ 3 := by
        calc (p : ℝ) * (p : ℝ) ^ e * (p : ℝ) ^ e ≤ (p : ℝ) ^ e * (p : ℝ) ^ e * (p : ℝ) ^ e := by
              gcongr
          _ ≤ (R.natAbs : ℝ) * (R.natAbs : ℝ) * (R.natAbs : ℝ) := by gcongr
          _ = (R.natAbs : ℝ) ^ 3 := by ring
      have h9 : (p : ℝ) * (p : ℝ) ^ e ≤ (R.natAbs : ℝ) ^ 3 := by
        calc (p : ℝ) * (p : ℝ) ^ e ≤ (p : ℝ) * (p : ℝ) ^ e * (p : ℝ) ^ e := by
              have : (1 : ℝ) ≤ (p : ℝ) ^ e := hp1.trans hpple
              nlinarith [mul_pos hp0 hpe0]
          _ ≤ (R.natAbs : ℝ) ^ 3 := h8
      rw [h6, h7] at h2
      calc (cnt f n (p ^ k) : ℝ)
          ≤ (p : ℝ) * (p : ℝ) ^ e * ((p : ℝ) ^ e * ((n : ℝ) / (p : ℝ) ^ k) + 1) := h2
        _ = (p : ℝ) * (p : ℝ) ^ e * (p : ℝ) ^ e * ((n : ℝ) / (p : ℝ) ^ k)
              + (p : ℝ) * (p : ℝ) ^ e := by ring
        _ ≤ (R.natAbs : ℝ) ^ 3 * ((n : ℝ) / (p : ℝ) ^ k) + (R.natAbs : ℝ) ^ 3 :=
            add_le_add (mul_le_mul_of_nonneg_right h8 hfrac) h9
        _ = (R.natAbs : ℝ) ^ 3 * ((n : ℝ) / (p : ℝ) ^ k + 1) := by ring
  · -- good prime
    have hpR' : ¬ (p : ℤ) ^ (0 + 1) ∣ R := by simpa using hpR
    have h1 : cnt f n (p ^ k) ≤ rho f p * (n / p ^ k + 1) := by
      unfold cnt rho
      apply card_le_mul_of_fibers (pow_pos hp.pos _) _
        (fun x hx => (Finset.mem_Icc.1 (Finset.mem_filter.1 hx).1).2) (fun x => x % p)
      · intro x hx
        have hx' := Finset.mem_filter.1 hx
        refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.mod_lt _ hp.pos), ?_⟩
        apply dvd_eval_mod f x
        have h1 : (p : ℤ) ∣ ((p ^ k : ℕ) : ℤ) := by
          push_cast
          exact dvd_pow_self _ (by omega)
        exact h1.trans hx'.2
      · intro x hx y hy hxy
        have hx' := (Finset.mem_filter.1 hx).2
        have hy' := (Finset.mem_filter.1 hy).2
        push_cast at hx' hy'
        have h3 : (p : ℤ) ^ (0 + 1) ∣ (y : ℤ) - x := by
          have := Nat.modEq_iff_dvd.1 (show x ≡ y [MOD p] from hxy)
          simpa using this
        have h4 := lifting f u v R hR hp 0 k (by omega) hpR' x y hx' hy' h3
        have h5 : x ≡ y [MOD p ^ k] := by
          apply Nat.modEq_iff_dvd.2
          push_cast
          simpa using h4
        exact h5
    have h2 : (cnt f n (p ^ k) : ℝ) ≤ ((rho f p * (n / p ^ k + 1) : ℕ) : ℝ) := by
      exact_mod_cast h1
    refine h2.trans ?_
    push_cast
    have h4 : ((n / p ^ k : ℕ) : ℝ) ≤ (n : ℝ) / ((p ^ k : ℕ) : ℝ) := Nat.cast_div_le
    push_cast at h4
    have h5 : (rho f p : ℝ) ≤ (f.natDegree : ℝ) + (R.natAbs : ℝ) ^ 3 := by
      have : (rho f p : ℝ) ≤ (f.natDegree : ℝ) := by exact_mod_cast rho_le f hf hd hp
      have : (0 : ℝ) ≤ (R.natAbs : ℝ) ^ 3 := by positivity
      linarith
    apply mul_le_mul h5 (by linarith) (by positivity) (by positivity)

/-- Cauchy-Schwarz: many collisions of a map into a small set. -/
lemma card_sq_le_card_mul_collisions {α β : Type*} [DecidableEq α] [DecidableEq β]
    (B : Finset α) (T : Finset β) (φ : α → β) (h : ∀ x ∈ B, φ x ∈ T) :
    B.card ^ 2 ≤ T.card * ((B ×ˢ B).filter (fun x => φ x.1 = φ x.2)).card := by
  have h1 : B.card = ∑ t ∈ T, (B.filter (fun a => φ a = t)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x hx => h x hx)
  have h2 : ((B ×ˢ B).filter (fun x => φ x.1 = φ x.2)).card
      = ∑ t ∈ T, (B.filter (fun a => φ a = t)).card ^ 2 := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x : α × α => φ x.1) (t := T)]
    · refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [sq, ← Finset.card_product]
      congr 1
      ext ⟨a, b⟩
      simp only [mem_filter, mem_product]
      constructor
      · rintro ⟨⟨⟨ha, hb⟩, hab⟩, hat⟩
        exact ⟨⟨ha, hat⟩, ⟨hb, hab ▸ hat⟩⟩
      · rintro ⟨⟨ha, hat⟩, ⟨hb, hbt⟩⟩
        exact ⟨⟨⟨ha, hb⟩, hat.trans hbt.symm⟩, hat⟩
    · intro x hx
      exact h _ (Finset.mem_product.1 (Finset.mem_filter.1 hx).1).1
  rw [h1, h2]
  exact sq_sum_le_card_mul_sum_sq

lemma dvd_G (f : ℤ[X]) {p : ℕ} (a b r : ℤ) (h1 : (p : ℤ) ∣ a - r * b)
    (h2 : (p : ℤ) ∣ f.eval r) : (p : ℤ) ∣ G f a b := by
  have key : ((G f a b : ℤ) : ZMod p)
      = (b : ZMod p) ^ f.natDegree * ((f.eval r : ℤ) : ZMod p) := by
    have ha : (a : ZMod p) = (r : ZMod p) * (b : ZMod p) := by
      have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h1
      push_cast at h3
      linear_combination h3
    rw [eval_eq_sum_range]
    unfold G
    push_cast
    rw [ha, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i ≤ f.natDegree := by
      have := Finset.mem_range.1 hi
      omega
    have h3 : (b : ZMod p) ^ f.natDegree
        = (b : ZMod p) ^ i * (b : ZMod p) ^ (f.natDegree - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hi']
    rw [h3, mul_pow]
    ring
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
  rw [key, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h2, mul_zero]

lemma card_Dp_le (N p : ℕ) :
    (((range N ×ˢ range N) ×ˢ (range N ×ˢ range N)).filter
      (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.1 % p = x.2.1 % p ∧ x.1.2 % p = x.2.2 % p)).card
      ≤ N ^ 2 * (N / p + 1) ^ 2 := by
  have h0 : (((range N ×ˢ range N) ×ˢ (range N ×ˢ range N)).filter
      (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.1 % p = x.2.1 % p ∧ x.1.2 % p = x.2.2 % p)).card
      ≤ ((range N ×ˢ range N) ×ˢ (range (N / p + 1) ×ˢ range (N / p + 1))).card := by
    apply Finset.card_le_card_of_injOn
      (fun x : (ℕ × ℕ) × (ℕ × ℕ) => (x.1, (x.2.1 / p, x.2.2 / p)))
    · intro x hx
      have hx' := Finset.mem_filter.1 (Finset.mem_coe.1 hx)
      have h1 := Finset.mem_product.1 hx'.1
      have h2 := Finset.mem_product.1 h1.2
      have h3 := Finset.mem_range.1 h2.1
      have h4 := Finset.mem_range.1 h2.2
      refine Finset.mem_coe.2 (Finset.mem_product.2 ⟨h1.1, Finset.mem_product.2 ⟨?_, ?_⟩⟩)
      · exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right h3.le))
      · exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right h4.le))
    · intro x hx y hy hxy
      have hx' := (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
      have hy' := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨h1, h2, h3⟩ := hxy
      have e1 := Nat.div_add_mod x.2.1 p
      have e2 := Nat.div_add_mod y.2.1 p
      have e3 := Nat.div_add_mod x.2.2 p
      have e4 := Nat.div_add_mod y.2.2 p
      have m1 : x.2.1 % p = y.2.1 % p := by rw [← hx'.1, ← hy'.1, h1]
      have m2 : x.2.2 % p = y.2.2 % p := by rw [← hx'.2, ← hy'.2, h1]
      have r1 : x.2.1 = y.2.1 := by rw [← e1, ← e2, h2, m1]
      have r2 : x.2.2 = y.2.2 := by rw [← e3, ← e4, h3, m2]
      exact Prod.ext h1 (Prod.ext r1 r2)
  refine h0.trans (le_of_eq ?_)
  simp only [Finset.card_product, Finset.card_range]
  ring

lemma card_X_ge (f : ℤ[X]) {p : ℕ} (hp : p.Prime) (N : ℕ) :
    (rho f p : ℝ) * ((N : ℝ) ^ 4 / p - 2 * (N : ℝ) ^ 4 / (p : ℝ) ^ 2 - 2 * (N : ℝ) ^ 2)
      ≤ ((((range N ×ˢ range N) ×ˢ (range N ×ˢ range N)).filter
          (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1 ≠ x.2 ∧
            (p : ℤ) ∣ G f ((x.1.1 : ℤ) - x.2.1) ((x.1.2 : ℤ) - x.2.2))).card : ℝ) := by
  classical
  have := Fact.mk hp
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  set BB := (range N ×ˢ range N) ×ˢ (range N ×ˢ range N) with hBB
  set X := BB.filter (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1 ≠ x.2 ∧
            (p : ℤ) ∣ G f ((x.1.1 : ℤ) - x.2.1) ((x.1.2 : ℤ) - x.2.2)) with hX
  set Dp := BB.filter
      (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.1 % p = x.2.1 % p ∧ x.1.2 % p = x.2.2 % p) with hDp
  set A : ℕ → Finset ((ℕ × ℕ) × (ℕ × ℕ)) := fun r => BB.filter
      (fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
        (p : ℤ) ∣ ((x.1.1 : ℤ) - x.2.1) - (r : ℤ) * ((x.1.2 : ℤ) - x.2.2)) with hA
  set roots := (range p).filter (fun r : ℕ => (p : ℤ) ∣ f.eval (r : ℤ)) with hroots
  -- Step 1: Cauchy-Schwarz
  have step1 : ∀ r : ℕ, N ^ 4 ≤ p * (A r).card := by
    intro r
    have h1 := card_sq_le_card_mul_collisions (range N ×ˢ range N) (Finset.univ : Finset (ZMod p))
      (fun u : ℕ × ℕ => ((u.1 : ZMod p) - (r : ZMod p) * (u.2 : ZMod p))) (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ, ZMod.card, Finset.card_product, Finset.card_range] at h1
    have h2 : (((range N ×ˢ range N) ×ˢ (range N ×ˢ range N)).filter
        (fun x : (ℕ × ℕ) × (ℕ × ℕ) => ((x.1.1 : ZMod p) - (r : ZMod p) * (x.1.2 : ZMod p))
          = ((x.2.1 : ZMod p) - (r : ZMod p) * (x.2.2 : ZMod p)))).card ≤ (A r).card := by
      apply Finset.card_le_card
      intro x hx
      have hx' := Finset.mem_filter.1 hx
      refine Finset.mem_filter.2 ⟨hx'.1, ?_⟩
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
      push_cast
      linear_combination hx'.2
    calc N ^ 4 = (N * N) ^ 2 := by ring
      _ ≤ p * _ := h1
      _ ≤ p * (A r).card := Nat.mul_le_mul_left _ h2
  -- Step 2: A r \ Dp ⊆ X for roots r
  have step2 : ∀ r ∈ roots, A r \ Dp ⊆ X := by
    intro r hr x hx
    have hr' := (Finset.mem_filter.1 hr).2
    have hx1 := Finset.mem_sdiff.1 hx
    have hxA := Finset.mem_filter.1 hx1.1
    refine Finset.mem_filter.2 ⟨hxA.1, ?_, dvd_G f _ _ _ hxA.2 hr'⟩
    intro heq
    apply hx1.2
    refine Finset.mem_filter.2 ⟨hxA.1, ?_, ?_⟩ <;> rw [heq]
  -- Step 3: disjointness
  have step3 : ∀ r ∈ roots, ∀ r' ∈ roots, r ≠ r' → Disjoint (A r \ Dp) (A r' \ Dp) := by
    intro r hr r' hr' hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    have hx1 := Finset.mem_sdiff.1 hx
    have hx2 := Finset.mem_sdiff.1 hx'
    have hxA := Finset.mem_filter.1 hx1.1
    have hxA' := Finset.mem_filter.1 hx2.1
    apply hx1.2
    have hrlt := Finset.mem_range.1 (Finset.mem_filter.1 hr).1
    have hrlt' := Finset.mem_range.1 (Finset.mem_filter.1 hr').1
    have h1 : (p : ℤ) ∣ ((r : ℤ) - r') * ((x.1.2 : ℤ) - x.2.2) := by
      have h2 := dvd_sub hxA'.2 hxA.2
      have h3 : ((x.1.1 : ℤ) - x.2.1) - (r' : ℤ) * ((x.1.2 : ℤ) - x.2.2)
          - (((x.1.1 : ℤ) - x.2.1) - (r : ℤ) * ((x.1.2 : ℤ) - x.2.2))
          = ((r : ℤ) - r') * ((x.1.2 : ℤ) - x.2.2) := by ring
      rwa [h3] at h2
    have h4 : ¬ (p : ℤ) ∣ ((r : ℤ) - r') := by
      intro h5
      apply hne
      have h6 : r' ≡ r [MOD p] := Nat.modEq_iff_dvd.2 h5
      have h7 : r' % p = r % p := h6
      rw [Nat.mod_eq_of_lt hrlt, Nat.mod_eq_of_lt hrlt'] at h7
      exact h7.symm
    have h5 : (p : ℤ) ∣ ((x.1.2 : ℤ) - x.2.2) := (hpz.dvd_or_dvd h1).resolve_left h4
    have h6 : (p : ℤ) ∣ ((x.1.1 : ℤ) - x.2.1) := by
      have h7 := dvd_add hxA.2 (Dvd.dvd.mul_left h5 (r : ℤ))
      simpa using h7
    refine Finset.mem_filter.2 ⟨hxA.1, ?_, ?_⟩
    · exact (Nat.modEq_iff_dvd.2 h6).symm
    · exact (Nat.modEq_iff_dvd.2 h5).symm
  -- Step 4: sum over roots
  have step4 : ∑ r ∈ roots, (A r \ Dp).card ≤ X.card := by
    rw [← Finset.card_biUnion (fun r hr r' hr' hne => step3 r hr r' hr' hne)]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨r, hr, hxr⟩ := Finset.mem_biUnion.1 hx
    exact step2 r hr hxr
  -- Step 6: bound on Dp
  have step6 : Dp.card ≤ N ^ 2 * (N / p + 1) ^ 2 := card_Dp_le N p
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hDp' : (Dp.card : ℝ) ≤ 2 * (N : ℝ) ^ 4 / (p : ℝ) ^ 2 + 2 * (N : ℝ) ^ 2 := by
    have h1 : (Dp.card : ℝ) ≤ ((N ^ 2 * (N / p + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast step6
    refine h1.trans ?_
    push_cast
    have h2 : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ) := Nat.cast_div_le
    have h3 : (0 : ℝ) ≤ ((N / p : ℕ) : ℝ) := Nat.cast_nonneg _
    have h4 : (((N / p : ℕ) : ℝ) + 1) ^ 2 ≤ 2 * ((N : ℝ) / (p : ℝ)) ^ 2 + 2 := by
      nlinarith [sq_nonneg (((N / p : ℕ) : ℝ) - 1), mul_le_mul h2 h2 h3 (le_trans h3 h2)]
    calc (N : ℝ) ^ 2 * (((N / p : ℕ) : ℝ) + 1) ^ 2
        ≤ (N : ℝ) ^ 2 * (2 * ((N : ℝ) / (p : ℝ)) ^ 2 + 2) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 2 * (N : ℝ) ^ 4 / (p : ℝ) ^ 2 + 2 * (N : ℝ) ^ 2 := by
          field_simp
  -- each root contributes
  have hroot : ∀ r ∈ roots, (N : ℝ) ^ 4 / p - 2 * (N : ℝ) ^ 4 / (p : ℝ) ^ 2 - 2 * (N : ℝ) ^ 2
      ≤ ((A r \ Dp).card : ℝ) := by
    intro r _
    have h1 : ((N ^ 4 : ℕ) : ℝ) ≤ ((p * (A r).card : ℕ) : ℝ) := by exact_mod_cast step1 r
    push_cast at h1
    have h2 : (N : ℝ) ^ 4 / p ≤ ((A r).card : ℝ) := by
      rw [div_le_iff₀ hp0]
      linarith
    have h3 : ((A r).card : ℝ) ≤ ((A r \ Dp).card : ℝ) + (Dp.card : ℝ) := by
      exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := A r) (t := Dp))
    linarith
  have hsum : (rho f p : ℝ) * ((N : ℝ) ^ 4 / p - 2 * (N : ℝ) ^ 4 / (p : ℝ) ^ 2 - 2 * (N : ℝ) ^ 2)
      ≤ ∑ r ∈ roots, ((A r \ Dp).card : ℝ) := by
    have h1 := Finset.sum_le_sum hroot
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    exact h1
  refine hsum.trans ?_
  exact_mod_cast step4

/-- the sum of `log p` over distinct primes dividing a nonzero integer is at most `log |z|` -/
lemma sum_log_le_log_natAbs (z : ℤ) (hz : z ≠ 0) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ (p : ℤ) ∣ z) :
    ∑ p ∈ s, Real.log (p : ℝ) ≤ Real.log (z.natAbs : ℝ) := by
  have h1 : s ⊆ z.natAbs.primeFactors := by
    intro p hp
    have h := hs p hp
    exact Nat.mem_primeFactors.2 ⟨h.1, Int.natCast_dvd.1 h.2, Int.natAbs_ne_zero.2 hz⟩
  have h2 : ∏ p ∈ s, p ≤ z.natAbs := by
    apply Nat.le_of_dvd (Int.natAbs_pos.2 hz)
    exact (Finset.prod_dvd_prod_of_subset _ _ _ h1).trans (Nat.prod_primeFactors_dvd _)
  have h3 : ∑ p ∈ s, Real.log (p : ℝ) = Real.log ((∏ p ∈ s, p : ℕ) : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (hs p hp).1.ne_zero
  rw [h3]
  apply Real.log_le_log
  · have h4 : 0 < ∏ p ∈ s, p := Finset.prod_pos (fun p hp => (hs p hp).1.pos)
    exact_mod_cast h4
  · exact_mod_cast h2

lemma sum_log_div_sq_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ) ^ 2 ≤ C := by
  have hnn : ∀ k : ℕ, 0 ≤ Real.log k / (k : ℝ) ^ 2 := fun k =>
    div_nonneg (Real.log_natCast_nonneg k) (by positivity)
  have hsum : Summable (fun k : ℕ => Real.log k / (k : ℝ) ^ 2) := by
    have h1 : Summable (fun k : ℕ => 2 * ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
      (Real.summable_nat_rpow_inv.2 (by norm_num)).mul_left 2
    refine Summable.of_nonneg_of_le hnn (fun k => ?_) h1
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      have h2 : Real.log k ≤ (k : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
        Real.log_le_rpow_div hk'.le (by norm_num)
      have h3 : (k : ℝ) ^ 2 = (k : ℝ) ^ (3 / 2 : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hk', ← Real.rpow_natCast]
        norm_num
      have h5 : (0 : ℝ) < (k : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hk' _
      have h6 : (0 : ℝ) < (k : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hk' _
      rw [h3, div_le_iff₀ (mul_pos h5 h6)]
      have h4 : 2 * ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹ * ((k : ℝ) ^ (3 / 2 : ℝ) * (k : ℝ) ^ (1 / 2 : ℝ))
          = 2 * (k : ℝ) ^ (1 / 2 : ℝ) := by
        field_simp
      rw [h4]
      linarith
  exact ⟨∑' k : ℕ, Real.log k / (k : ℝ) ^ 2, tsum_nonneg hnn,
    fun n => hsum.sum_le_tsum _ (fun k _ => hnn k)⟩

/-- the key saving: the weighted number of roots modulo primes is at most `(d/2) log n + O(1)` -/
lemma saving (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      ∑ p ∈ Nat.primesLE n, (rho f p : ℝ) * (Real.log p / p)
        ≤ (f.natDegree : ℝ) / 2 * Real.log n + C := by
  obtain ⟨C₂, hC₂0, hC₂⟩ := sum_log_div_sq_le
  have hL1 : 1 ≤ Lf f := Lf_pos f hf.ne_zero
  refine ⟨Real.log (Lf f) + f.natDegree * Real.log 2 + 2 * f.natDegree * C₂
    + 2 * f.natDegree * Real.log 4, ?_⟩
  intro n hn
  set N := Nat.sqrt n + 1 with hN
  have hN1 : 1 ≤ N := by omega
  have hnN : n ≤ N ^ 2 := (Nat.lt_succ_sqrt' n).le
  have hN4 : N ^ 2 ≤ 4 * n := by
    have h1 := Nat.sqrt_le' n
    have h2 : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.2 (by omega)
    nlinarith
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnNr : (n : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hnN
  have hN4r : (N : ℝ) ^ 2 ≤ 4 * n := by exact_mod_cast hN4
  have hd0 : (0 : ℝ) ≤ (f.natDegree : ℝ) := Nat.cast_nonneg _
  set BB := (range N ×ˢ range N) ×ˢ (range N ×ˢ range N) with hBB
  have hBBcard : (BB.card : ℝ) = (N : ℝ) ^ 4 := by
    simp only [hBB, Finset.card_product, Finset.card_range]
    push_cast
    ring
  set M : ℝ := (Lf f : ℝ) * (N : ℝ) ^ f.natDegree with hM
  have hLr : (1 : ℝ) ≤ (Lf f : ℝ) := by exact_mod_cast hL1
  have hM1 : 1 ≤ M := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ f.natDegree := one_le_pow₀ hNr
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ M := mul_le_mul hLr h1 (by norm_num) (by linarith)
  set g : (ℕ × ℕ) × (ℕ × ℕ) → ℝ := fun x =>
    Real.log ((G f ((x.1.1 : ℤ) - x.2.1) ((x.1.2 : ℤ) - x.2.2)).natAbs : ℝ) with hg
  -- (a) upper bound for the sum of logs
  have ha : ∑ x ∈ BB, g x ≤ (N : ℝ) ^ 4 * Real.log M := by
    have h1 : ∀ x ∈ BB, g x ≤ Real.log M := by
      intro x hx
      have hx1 := Finset.mem_product.1 hx
      have hx2 := Finset.mem_product.1 hx1.1
      have hx3 := Finset.mem_product.1 hx1.2
      have a1 := Finset.mem_range.1 hx2.1
      have a2 := Finset.mem_range.1 hx2.2
      have a3 := Finset.mem_range.1 hx3.1
      have a4 := Finset.mem_range.1 hx3.2
      have hab1 : |(x.1.1 : ℤ) - x.2.1| ≤ (N : ℤ) := by
        rw [abs_le]; constructor <;> omega
      have hab2 : |(x.1.2 : ℤ) - x.2.2| ≤ (N : ℤ) := by
        rw [abs_le]; constructor <;> omega
      have h2 := G_abs_le f _ _ N hab1 hab2
      rw [Int.abs_eq_natAbs] at h2
      have h3 : ((G f ((x.1.1 : ℤ) - x.2.1) ((x.1.2 : ℤ) - x.2.2)).natAbs : ℝ) ≤ M := by
        rw [hM]
        exact_mod_cast h2
      rcases Nat.eq_zero_or_pos (G f ((x.1.1 : ℤ) - x.2.1) ((x.1.2 : ℤ) - x.2.2)).natAbs
        with h0 | h0
      · simp only [hg, h0, Nat.cast_zero, Real.log_zero]
        exact Real.log_nonneg hM1
      · exact Real.log_le_log (by exact_mod_cast h0) h3
    calc ∑ x ∈ BB, g x ≤ ∑ x ∈ BB, Real.log M := Finset.sum_le_sum h1
      _ = (N : ℝ) ^ 4 * Real.log M := by rw [Finset.sum_const, nsmul_eq_mul, hBBcard]
  -- (b) lower bound: double counting over primes
  have hb : ∑ p ∈ Nat.primesLE n, ((BB.filter (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1 ≠ x.2 ∧
        (p : ℤ) ∣ G f ((x.1.1 : ℤ) - x.2.1) ((x.1.2 : ℤ) - x.2.2))).card : ℝ) * Real.log p
      ≤ ∑ x ∈ BB, g x := by
    have h1 : ∀ p : ℕ, ((BB.filter (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1 ≠ x.2 ∧
        (p : ℤ) ∣ G f ((x.1.1 : ℤ) - x.2.1) ((x.1.2 : ℤ) - x.2.2))).card : ℝ) * Real.log p
        = ∑ x ∈ BB, (if (x.1 ≠ x.2 ∧
        (p : ℤ) ∣ G f ((x.1.1 : ℤ) - x.2.1) ((x.1.2 : ℤ) - x.2.2)) then Real.log p else 0) := by
      intro p
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    simp_rw [h1]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro x _
    rw [← Finset.sum_filter]
    by_cases hx12 : x.1 = x.2
    · have h2 : (Nat.primesLE n).filter (fun p : ℕ => x.1 ≠ x.2 ∧
          (p : ℤ) ∣ G f ((x.1.1 : ℤ) - x.2.1) ((x.1.2 : ℤ) - x.2.2)) = ∅ := by
        apply Finset.filter_eq_empty_iff.2
        intro p _ h
        exact h.1 hx12
      rw [h2, Finset.sum_empty]
      exact Real.log_natCast_nonneg _
    · apply sum_log_le_log_natAbs
      · apply G_ne_zero f hf hd
        by_contra hcon
        push Not at hcon
        apply hx12
        have e1 : x.1.1 = x.2.1 := by have := hcon.1; omega
        have e2 : x.1.2 = x.2.2 := by have := hcon.2; omega
        exact Prod.ext e1 e2
      · intro p hp
        have hp' := Finset.mem_filter.1 hp
        exact ⟨(Nat.mem_primesLE.1 hp'.1).2, hp'.2.2⟩
  -- (c) per-prime inequality
  have hc : ∀ p ∈ Nat.primesLE n,
      (N : ℝ) ^ 4 * ((rho f p : ℝ) * (Real.log p / p))
        ≤ ((BB.filter (fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1 ≠ x.2 ∧
        (p : ℤ) ∣ G f ((x.1.1 : ℤ) - x.2.1) ((x.1.2 : ℤ) - x.2.2))).card : ℝ) * Real.log p
          + 2 * (N : ℝ) ^ 4 * f.natDegree * (Real.log p / (p : ℝ) ^ 2)
          + 2 * (N : ℝ) ^ 2 * f.natDegree * Real.log p := by
    intro p hp
    have hpp := (Nat.mem_primesLE.1 hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hl : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
    have h1 := mul_le_mul_of_nonneg_right (card_X_ge f hpp N) hl
    have hrho : (rho f p : ℝ) ≤ (f.natDegree : ℝ) := by exact_mod_cast rho_le f hf hd hpp
    have hrho0 : (0 : ℝ) ≤ (rho f p : ℝ) := Nat.cast_nonneg _
    have e1 : (rho f p : ℝ) * ((N : ℝ) ^ 4 / p - 2 * (N : ℝ) ^ 4 / (p : ℝ) ^ 2 - 2 * (N : ℝ) ^ 2)
        * Real.log p
        = (N : ℝ) ^ 4 * ((rho f p : ℝ) * (Real.log p / p))
          - 2 * (N : ℝ) ^ 4 * (rho f p : ℝ) * (Real.log p / (p : ℝ) ^ 2)
          - 2 * (N : ℝ) ^ 2 * (rho f p : ℝ) * Real.log p := by
      field_simp
    have t2 : (0 : ℝ) ≤ Real.log p / (p : ℝ) ^ 2 := div_nonneg hl (by positivity)
    have e2 : 2 * (N : ℝ) ^ 4 * (rho f p : ℝ) * (Real.log p / (p : ℝ) ^ 2)
        ≤ 2 * (N : ℝ) ^ 4 * f.natDegree * (Real.log p / (p : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ t2
      apply mul_le_mul_of_nonneg_left hrho (by positivity)
    have e3 : 2 * (N : ℝ) ^ 2 * (rho f p : ℝ) * Real.log p
        ≤ 2 * (N : ℝ) ^ 2 * f.natDegree * Real.log p := by
      apply mul_le_mul_of_nonneg_right _ hl
      apply mul_le_mul_of_nonneg_left hrho (by positivity)
    rw [e1] at h1
    linarith
  -- (d) sum over primes
  have hd' := Finset.sum_le_sum hc
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum] at hd'
  have htheta : ∑ p ∈ Nat.primesLE n, Real.log (p : ℝ) ≤ Real.log 4 * n := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)
  have hsq := hC₂ n
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h10 : (N : ℝ) ^ 4 * ∑ p ∈ Nat.primesLE n, (rho f p : ℝ) * (Real.log p / p)
      ≤ (N : ℝ) ^ 4 * (Real.log M + 2 * f.natDegree * C₂ + 2 * f.natDegree * Real.log 4) := by
    have h11 : 2 * (N : ℝ) ^ 4 * f.natDegree * ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ) ^ 2
        ≤ 2 * (N : ℝ) ^ 4 * f.natDegree * C₂ :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have h12 : 2 * (N : ℝ) ^ 2 * f.natDegree * ∑ p ∈ Nat.primesLE n, Real.log (p : ℝ)
        ≤ 2 * (N : ℝ) ^ 2 * f.natDegree * (Real.log 4 * (N : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact htheta.trans (mul_le_mul_of_nonneg_left hnNr hlog4)
    nlinarith [hb, ha, hd', h11, h12]
  have h13 : ∑ p ∈ Nat.primesLE n, (rho f p : ℝ) * (Real.log p / p)
      ≤ Real.log M + 2 * f.natDegree * C₂ + 2 * f.natDegree * Real.log 4 :=
    le_of_mul_le_mul_left h10 (by positivity)
  -- (e) log M
  have h14 : Real.log M = Real.log (Lf f) + f.natDegree * Real.log N := by
    rw [hM, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have h15 : 2 * Real.log N ≤ 2 * Real.log 2 + Real.log n := by
    have h16 : Real.log ((N : ℝ) ^ 2) ≤ Real.log (4 * n) :=
      Real.log_le_log (by positivity) hN4r
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity)] at h16
    have h17 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    push_cast at h16
    linarith
  have h18 : (f.natDegree : ℝ) * Real.log N
      ≤ (f.natDegree : ℝ) / 2 * Real.log n + f.natDegree * Real.log 2 := by
    have := mul_le_mul_of_nonneg_left h15 hd0
    linarith
  linarith

lemma eval_natAbs_le (f : ℤ[X]) (n m : ℕ) (hm : m ∈ Icc 1 n) :
    (f.eval (m : ℤ)).natAbs ≤ Lf f * n ^ f.natDegree := by
  have hm' := Finset.mem_Icc.1 hm
  have h1 := G_abs_le f (m : ℤ) 1 n
    (by rw [abs_of_nonneg (by positivity)]; exact_mod_cast hm'.2)
    (by rw [abs_one]; exact_mod_cast (hm'.1.trans hm'.2))
  rw [G_one, Int.abs_eq_natAbs] at h1
  exact_mod_cast h1

lemma eval_lower (f : ℤ[X]) (hf0 : f ≠ 0) (m : ℕ) (hm : 1 ≤ m) :
    (m : ℤ) ^ f.natDegree - (Lf f : ℤ) * (m : ℤ) ^ (f.natDegree - 1) ≤ |f.eval (m : ℤ)| := by
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := by positivity
  have hm1 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  rw [eval_eq_sum_range, Finset.sum_range_succ]
  have h1 : |∑ i ∈ range f.natDegree, f.coeff i * (m : ℤ) ^ i|
      ≤ (Lf f : ℤ) * (m : ℤ) ^ (f.natDegree - 1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    unfold Lf
    push_cast
    rw [Finset.sum_range_succ, add_mul, Finset.sum_mul]
    have h2 : ∑ i ∈ range f.natDegree, |f.coeff i * (m : ℤ) ^ i|
        ≤ ∑ i ∈ range f.natDegree, |f.coeff i| * (m : ℤ) ^ (f.natDegree - 1) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_pow, abs_of_nonneg hm0]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply pow_le_pow_right₀ hm1
      have := Finset.mem_range.1 hi
      omega
    have h3 : 0 ≤ |f.coeff f.natDegree| * (m : ℤ) ^ (f.natDegree - 1) := by positivity
    linarith
  have h2 : (m : ℤ) ^ f.natDegree ≤ |f.coeff f.natDegree * (m : ℤ) ^ f.natDegree| := by
    rw [abs_mul, abs_pow, abs_of_nonneg hm0]
    have h3 : 1 ≤ |f.coeff f.natDegree| := Int.one_le_abs (leadingCoeff_ne_zero.2 hf0)
    have h4 : (0 : ℤ) ≤ (m : ℤ) ^ f.natDegree := by positivity
    nlinarith
  have h3 : |f.coeff f.natDegree * (m : ℤ) ^ f.natDegree|
      ≤ |∑ i ∈ range f.natDegree, f.coeff i * (m : ℤ) ^ i + f.coeff f.natDegree * (m : ℤ) ^ f.natDegree|
        + |∑ i ∈ range f.natDegree, f.coeff i * (m : ℤ) ^ i| := by
    have h4 := abs_sub (∑ i ∈ range f.natDegree, f.coeff i * (m : ℤ) ^ i
      + f.coeff f.natDegree * (m : ℤ) ^ f.natDegree) (∑ i ∈ range f.natDegree, f.coeff i * (m : ℤ) ^ i)
    simpa using h4
  linarith

lemma pow_le_mul_natAbs (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (m : ℕ)
    (hm : 1 ≤ m) :
    m ^ f.natDegree ≤ (2 * Lf f) ^ f.natDegree * (f.eval (m : ℤ)).natAbs := by
  have hne : (f.eval (m : ℤ)).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (eval_ne_zero f hf hd m)
  have hL1 := Lf_pos f hf.ne_zero
  by_cases hmL : m ≤ 2 * Lf f
  · calc m ^ f.natDegree ≤ (2 * Lf f) ^ f.natDegree := Nat.pow_le_pow_left hmL _
      _ = (2 * Lf f) ^ f.natDegree * 1 := (mul_one _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.2 hne)
  · push Not at hmL
    have h1 := eval_lower f hf.ne_zero m hm
    rw [Int.abs_eq_natAbs] at h1
    have h2 : (m : ℤ) ^ f.natDegree = (m : ℤ) * (m : ℤ) ^ (f.natDegree - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h3 : (m : ℤ) ^ f.natDegree ≤ 2 * ((f.eval (m : ℤ)).natAbs : ℤ) := by
      have h5 : (0 : ℤ) ≤ (m : ℤ) ^ (f.natDegree - 1) := by positivity
      have hmL' : (2 * (Lf f : ℤ)) < m := by exact_mod_cast hmL
      nlinarith
    have h4 : m ^ f.natDegree ≤ 2 * (f.eval (m : ℤ)).natAbs := by exact_mod_cast h3
    have h5 : 2 ≤ (2 * Lf f) ^ f.natDegree := by
      calc 2 ≤ 2 * Lf f := by omega
        _ = (2 * Lf f) ^ 1 := (pow_one _).symm
        _ ≤ (2 * Lf f) ^ f.natDegree := Nat.pow_le_pow_right (by omega) (by omega)
    calc m ^ f.natDegree ≤ 2 * (f.eval (m : ℤ)).natAbs := h4
      _ ≤ (2 * Lf f) ^ f.natDegree * (f.eval (m : ℤ)).natAbs := Nat.mul_le_mul_right _ h5

lemma sum_log_ge (n : ℕ) : (n : ℝ) * Real.log n - n ≤ ∑ m ∈ Icc 1 n, Real.log (m : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have h1 : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
        have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
        rw [Real.log_div (by positivity) (by positivity)] at h2
        have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
        linarith
      have h2 : (n : ℝ) * Real.log ((n : ℝ) + 1) - (n : ℝ) * Real.log n ≤ 1 := by
        rw [← mul_sub]
        calc (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ (n : ℝ) * (1 / n) :=
              mul_le_mul_of_nonneg_left h1 hn'.le
          _ = 1 := by field_simp
      push_cast
      linarith

lemma log_prod_ge (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (n : ℕ) :
    (f.natDegree : ℝ) * (n * Real.log n - n)
        - n * Real.log (((2 * Lf f) ^ f.natDegree : ℕ) : ℝ)
      ≤ Real.log ((∏ m ∈ Icc 1 n, (f.eval (m : ℤ)).natAbs : ℕ) : ℝ) := by
  have hL1 := Lf_pos f hf.ne_zero
  rw [Nat.cast_prod, Real.log_prod (fun m _ => by
    exact_mod_cast Int.natAbs_ne_zero.2 (eval_ne_zero f hf hd m))]
  have h1 : ∀ m ∈ Icc 1 n, (f.natDegree : ℝ) * Real.log m
      - Real.log (((2 * Lf f) ^ f.natDegree : ℕ) : ℝ)
      ≤ Real.log ((f.eval (m : ℤ)).natAbs : ℝ) := by
    intro m hm
    have hm1 := (Finset.mem_Icc.1 hm).1
    have h2 := pow_le_mul_natAbs f hf hd m hm1
    have h3 : ((m ^ f.natDegree : ℕ) : ℝ)
        ≤ (((2 * Lf f) ^ f.natDegree * (f.eval (m : ℤ)).natAbs : ℕ) : ℝ) := by
      exact_mod_cast h2
    have hmpos : (0 : ℝ) < ((m ^ f.natDegree : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))
    have h4 := Real.log_le_log hmpos h3
    have hk0 : (((2 * Lf f) ^ f.natDegree : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast pow_ne_zero _ (by omega)
    have ha0 : (((f.eval (m : ℤ)).natAbs : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Int.natAbs_ne_zero.2 (eval_ne_zero f hf hd m)
    rw [Nat.cast_mul, Real.log_mul hk0 ha0, Nat.cast_pow, Real.log_pow] at h4
    linarith
  have h5 := Finset.sum_le_sum h1
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at h5
  have h6 := sum_log_ge n
  have h7 : (f.natDegree : ℝ) * ((n : ℝ) * Real.log n - n)
      ≤ (f.natDegree : ℝ) * ∑ m ∈ Icc 1 n, Real.log (m : ℝ) :=
    mul_le_mul_of_nonneg_left h6 (Nat.cast_nonneg _)
  simp only [Nat.add_sub_cancel] at h5
  linarith

lemma factorization_prod_eq (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (n : ℕ)
    {p : ℕ} (hp : p.Prime) (K : ℕ)
    (hK : ∀ m ∈ Icc 1 n, (f.eval (m : ℤ)).natAbs < p ^ K) :
    (∏ m ∈ Icc 1 n, (f.eval (m : ℤ)).natAbs).factorization p
      = ∑ k ∈ Ico 1 K, cnt f n (p ^ k) := by
  rw [Nat.factorization_prod_apply
    (fun (m : ℕ) _ => Int.natAbs_ne_zero.2 (eval_ne_zero f hf hd (m : ℤ)))]
  have h1 : ∀ m ∈ Icc 1 n, (f.eval (m : ℤ)).natAbs.factorization p
      = ∑ k ∈ Ico 1 K, (if ((p ^ k : ℕ) : ℤ) ∣ f.eval (m : ℤ) then 1 else 0) := by
    intro m hm
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hp
      (Int.natAbs_pos.2 (eval_ne_zero f hf hd m)) (hK m hm), Finset.card_filter]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [Int.natCast_dvd]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold cnt
  rw [Finset.card_filter]

lemma factorization_le_large (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (n : ℕ)
    (hLn : Lf f ≤ n) {p : ℕ} (hp : p.Prime) (hpn : n < p) :
    (∏ m ∈ Icc 1 n, (f.eval (m : ℤ)).natAbs).factorization p ≤ f.natDegree * f.natDegree := by
  have hK : ∀ m ∈ Icc 1 n, (f.eval (m : ℤ)).natAbs < p ^ (f.natDegree + 1) := by
    intro m hm
    calc (f.eval (m : ℤ)).natAbs ≤ Lf f * n ^ f.natDegree := eval_natAbs_le f n m hm
      _ ≤ n * n ^ f.natDegree := Nat.mul_le_mul_right _ hLn
      _ = n ^ (f.natDegree + 1) := by ring
      _ < p ^ (f.natDegree + 1) := Nat.pow_lt_pow_left hpn (by omega)
  rw [factorization_prod_eq f hf hd n hp _ hK]
  calc ∑ k ∈ Ico 1 (f.natDegree + 1), cnt f n (p ^ k)
      ≤ ∑ k ∈ Ico 1 (f.natDegree + 1), f.natDegree := by
        apply Finset.sum_le_sum
        intro k hk
        have hk1 := (Finset.mem_Ico.1 hk).1
        calc cnt f n (p ^ k) ≤ cnt f n p := cnt_pow_le_cnt f p n k hk1
          _ ≤ rho f p * (n / p + 1) := cnt_prime_le f hp n
          _ = rho f p := by rw [Nat.div_eq_of_lt hpn]; simp
          _ ≤ f.natDegree := rho_le f hf hd hp
    _ = f.natDegree * f.natDegree := by simp

lemma pi_mul_log_le (n : ℕ) (hn : 2 ≤ n) :
    ((Nat.primesLE n).card : ℝ) * Real.log n ≤ (2 * Real.log 4 + 2) * n := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h1 := Chebyshev.pi_le_log4_mul_div hn1
  rw [Nat.floor_natCast, Real.log_sqrt hn0.le] at h1
  rw [Nat.primesLE_card_eq_primeCounting]
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have hsq : Real.log n ≤ 2 * √(n : ℝ) := by
    have h2 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hn0)
    rw [Real.log_sqrt hn0.le] at h2
    linarith
  have h3 : (Nat.primeCounting n : ℝ) * Real.log n
      ≤ (Real.log 4 * n / (Real.log n / 2) + √(n : ℝ)) * Real.log n :=
    mul_le_mul_of_nonneg_right h1 hlog.le
  have h4 : (Real.log 4 * n / (Real.log n / 2) + √(n : ℝ)) * Real.log n
      = 2 * Real.log 4 * n + √(n : ℝ) * Real.log n := by
    field_simp
  have h5 : √(n : ℝ) * Real.log n ≤ 2 * n := by
    calc √(n : ℝ) * Real.log n ≤ √(n : ℝ) * (2 * √(n : ℝ)) :=
          mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
      _ = 2 * (√(n : ℝ) * √(n : ℝ)) := by ring
      _ = 2 * n := by rw [Real.mul_self_sqrt hn0.le]
  linarith

/-- bound for the exponent of a prime in the product of the values -/
lemma factorization_le_small (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) (B : ℕ)
    (_hB : f.natDegree ≤ B)
    (hcnt : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ,
      (cnt f n (p ^ k) : ℝ) ≤ B * ((n : ℝ) / (p : ℝ) ^ k + 1))
    (n : ℕ) {p : ℕ} (hp : p.Prime) :
    (((∏ m ∈ Icc 1 n, (f.eval (m : ℤ)).natAbs).factorization p : ℕ) : ℝ)
      ≤ (rho f p : ℝ) * ((n : ℝ) / p) + f.natDegree + 2 * B * n / (p : ℝ) ^ 2
        + B * (Nat.log p (Lf f * n ^ f.natDegree) : ℝ) := by
  set H := Lf f * n ^ f.natDegree with hH
  set K := Nat.log p H + 1 with hK
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  rw [factorization_prod_eq f hf hd n hp K (fun m hm =>
    lt_of_le_of_lt (eval_natAbs_le f n m hm) (Nat.lt_pow_succ_log_self hp.one_lt H))]
  push_cast
  -- split off the term k = 1
  have hsplit : ∑ k ∈ Ico 1 K, (cnt f n (p ^ k) : ℝ)
      ≤ (cnt f n p : ℝ) + ∑ k ∈ Ico 2 K, (cnt f n (p ^ k) : ℝ) := by
    rcases Nat.lt_or_ge 1 K with h | h
    · rw [Finset.sum_eq_sum_Ico_succ_bot h, pow_one]
    · rw [Finset.Ico_eq_empty_of_le h, Finset.sum_empty]
      have h1 : (0 : ℝ) ≤ (cnt f n p : ℝ) := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ ∑ k ∈ Ico 2 K, (cnt f n (p ^ k) : ℝ) :=
        Finset.sum_nonneg (fun k _ => Nat.cast_nonneg _)
      linarith
  -- the term k = 1
  have hk1 : (cnt f n p : ℝ) ≤ (rho f p : ℝ) * ((n : ℝ) / p) + f.natDegree := by
    have h1 : (cnt f n p : ℝ) ≤ ((rho f p * (n / p + 1) : ℕ) : ℝ) := by
      exact_mod_cast cnt_prime_le f hp n
    have h2 : ((n / p : ℕ) : ℝ) ≤ (n : ℝ) / (p : ℝ) := Nat.cast_div_le
    have h3 : (rho f p : ℝ) ≤ (f.natDegree : ℝ) := by exact_mod_cast rho_le f hf hd hp
    have h4 : (0 : ℝ) ≤ (rho f p : ℝ) := Nat.cast_nonneg _
    push_cast at h1
    have h5 : (rho f p : ℝ) * (((n / p : ℕ) : ℝ) + 1)
        ≤ (rho f p : ℝ) * ((n : ℝ) / p + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) h4
    linarith
  -- the terms k ≥ 2
  have hk2 : ∑ k ∈ Ico 2 K, (cnt f n (p ^ k) : ℝ)
      ≤ 2 * B * n / (p : ℝ) ^ 2 + B * (Nat.log p H : ℝ) := by
    have h1 : ∑ k ∈ Ico 2 K, (cnt f n (p ^ k) : ℝ)
        ≤ ∑ k ∈ Ico 2 K, ((B : ℝ) * n * ((p : ℝ)⁻¹) ^ k + B) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_Ico.1 hk
      have h2 := hcnt p hp k (by omega) n
      have h3 : (B : ℝ) * ((n : ℝ) / (p : ℝ) ^ k + 1) = (B : ℝ) * n * ((p : ℝ)⁻¹) ^ k + B := by
        rw [inv_pow]
        field_simp
      linarith
    have hinv0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
    have hinv1 : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hp2
    have hgeo : ∑ k ∈ Ico 2 K, ((p : ℝ)⁻¹) ^ k ≤ 2 * ((p : ℝ)⁻¹) ^ 2 := by
      have h4 := geom_sum_Ico_le_of_lt_one (m := 2) (n := K) hinv0 (by linarith)
      refine h4.trans ?_
      rw [div_le_iff₀ (by linarith)]
      have h5 : (0 : ℝ) ≤ ((p : ℝ)⁻¹) ^ 2 := by positivity
      nlinarith
    have hcard : ((Ico 2 K).card : ℝ) ≤ (Nat.log p H : ℝ) := by
      rw [Nat.card_Ico]
      have : K - 2 ≤ Nat.log p H := by omega
      exact_mod_cast this
    refine h1.trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    have h6 : (B : ℝ) * n * ∑ k ∈ Ico 2 K, ((p : ℝ)⁻¹) ^ k
        ≤ (B : ℝ) * n * (2 * ((p : ℝ)⁻¹) ^ 2) :=
      mul_le_mul_of_nonneg_left hgeo (by positivity)
    have h7 : (B : ℝ) * n * (2 * ((p : ℝ)⁻¹) ^ 2) = 2 * B * n / (p : ℝ) ^ 2 := by
      rw [inv_pow]
      field_simp
    have h8 : ((Ico 2 K).card : ℝ) * (B : ℝ) ≤ (B : ℝ) * (Nat.log p H : ℝ) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hcard hB0
    linarith
  linarith

lemma log_mul_log_le (p H : ℕ) (hp : 1 < p) (hH : H ≠ 0) :
    (Nat.log p H : ℝ) * Real.log p ≤ Real.log H := by
  have h1 : p ^ Nat.log p H ≤ H := Nat.pow_log_le_self p hH
  have h2 : ((p ^ Nat.log p H : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
  have h3 : (0 : ℝ) < ((p ^ Nat.log p H : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))
  have h4 := Real.log_le_log h3 h2
  rwa [Nat.cast_pow, Real.log_pow] at h4

/-- the contribution of the primes up to `n` -/
lemma small_part (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      ∑ p ∈ Nat.primesLE n,
        (((∏ m ∈ Icc 1 n, (f.eval (m : ℤ)).natAbs).factorization p : ℕ) : ℝ) * Real.log p
        ≤ (f.natDegree : ℝ) / 2 * (n * Real.log n) + C * n := by
  obtain ⟨B, hB, hcnt⟩ := cnt_pow_le f hf hd
  obtain ⟨C₃, hsav⟩ := saving f hf hd
  obtain ⟨C₂, hC₂0, hC₂⟩ := sum_log_div_sq_le
  have hL1 := Lf_pos f hf.ne_zero
  refine ⟨C₃ + f.natDegree * Real.log 4 + 2 * B * C₂ + B * Real.log (Lf f)
    + B * f.natDegree * (2 * Real.log 4 + 2), ?_⟩
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hd0 : (0 : ℝ) ≤ (f.natDegree : ℝ) := Nat.cast_nonneg _
  have hLr : (1 : ℝ) ≤ (Lf f : ℝ) := by exact_mod_cast hL1
  have hlogL : 0 ≤ Real.log (Lf f) := Real.log_nonneg hLr
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  set H := Lf f * n ^ f.natDegree with hH
  have hH0 : H ≠ 0 := by
    rw [hH]
    exact mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
  have hlogH : Real.log (H : ℝ) = Real.log (Lf f) + f.natDegree * Real.log n := by
    rw [hH, Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  -- per prime
  have hper : ∀ p ∈ Nat.primesLE n,
      (((∏ m ∈ Icc 1 n, (f.eval (m : ℤ)).natAbs).factorization p : ℕ) : ℝ) * Real.log p
        ≤ (n : ℝ) * ((rho f p : ℝ) * (Real.log p / p)) + f.natDegree * Real.log p
          + 2 * B * n * (Real.log p / (p : ℝ) ^ 2) + B * Real.log H := by
    intro p hp
    have hpp := (Nat.mem_primesLE.1 hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hl : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
    have h1 := mul_le_mul_of_nonneg_right (factorization_le_small f hf hd B hB hcnt n hpp) hl
    have h2 := log_mul_log_le p H hpp.one_lt hH0
    have e1 : ((rho f p : ℝ) * ((n : ℝ) / p) + f.natDegree + 2 * B * n / (p : ℝ) ^ 2
        + B * (Nat.log p H : ℝ)) * Real.log p
        = (n : ℝ) * ((rho f p : ℝ) * (Real.log p / p)) + f.natDegree * Real.log p
          + 2 * B * n * (Real.log p / (p : ℝ) ^ 2)
          + B * ((Nat.log p H : ℝ) * Real.log p) := by
      field_simp
    rw [e1] at h1
    have h3 : (B : ℝ) * ((Nat.log p H : ℝ) * Real.log p) ≤ B * Real.log H :=
      mul_le_mul_of_nonneg_left h2 hB0
    linarith
  have hsum := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hsum
  have htheta : ∑ p ∈ Nat.primesLE n, Real.log (p : ℝ) ≤ Real.log 4 * n := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)
  have hsv := hsav n (by omega)
  have hsq := hC₂ n
  have hpi := pi_mul_log_le n hn
  have hpin : ((Nat.primesLE n).card : ℝ) ≤ n := by
    have h1 : (Nat.primesLE n).card ≤ (Icc 1 n).card := by
      apply Finset.card_le_card
      intro p hp
      have hp' := Nat.mem_primesLE.1 hp
      exact Finset.mem_Icc.2 ⟨hp'.2.one_le, hp'.1⟩
    rw [Nat.card_Icc] at h1
    have h2 : (Nat.primesLE n).card ≤ n := by omega
    exact_mod_cast h2
  have hcard0 : (0 : ℝ) ≤ ((Nat.primesLE n).card : ℝ) := Nat.cast_nonneg _
  -- assemble
  have t1 : (n : ℝ) * ∑ p ∈ Nat.primesLE n, (rho f p : ℝ) * (Real.log p / p)
      ≤ (n : ℝ) * ((f.natDegree : ℝ) / 2 * Real.log n + C₃) :=
    mul_le_mul_of_nonneg_left hsv hn0.le
  have t2 : (f.natDegree : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log (p : ℝ)
      ≤ (f.natDegree : ℝ) * (Real.log 4 * n) := mul_le_mul_of_nonneg_left htheta hd0
  have t3 : 2 * (B : ℝ) * n * ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ) ^ 2
      ≤ 2 * (B : ℝ) * n * C₂ := mul_le_mul_of_nonneg_left hsq (by positivity)
  have t4 : ((Nat.primesLE n).card : ℝ) * ((B : ℝ) * Real.log H)
      ≤ (B : ℝ) * Real.log (Lf f) * n + B * f.natDegree * ((2 * Real.log 4 + 2) * n) := by
    rw [hlogH]
    have h1 : ((Nat.primesLE n).card : ℝ) * Real.log (Lf f) ≤ n * Real.log (Lf f) :=
      mul_le_mul_of_nonneg_right hpin hlogL
    have h2 : (B : ℝ) * (((Nat.primesLE n).card : ℝ) * Real.log (Lf f))
        ≤ (B : ℝ) * (n * Real.log (Lf f)) := mul_le_mul_of_nonneg_left h1 hB0
    have h3 : (B : ℝ) * f.natDegree * (((Nat.primesLE n).card : ℝ) * Real.log n)
        ≤ (B : ℝ) * f.natDegree * ((2 * Real.log 4 + 2) * n) :=
      mul_le_mul_of_nonneg_left hpi (by positivity)
    nlinarith
  nlinarith

/-- every prime factor of a nonzero natural number is at most its greatest prime factor -/
lemma le_maxPrimeFac_of_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (h : p ∣ n) :
    p ≤ Nat.maxPrimeFac n := by
  have hmem : p ∈ n.primeFactorsList := (Nat.mem_primeFactorsList hn).2 ⟨hp, h⟩
  have hne : n.primeFactorsList ≠ [] := List.ne_nil_of_mem hmem
  have h1 : n ≠ 1 := by
    rintro rfl
    simp at hmem
  have h2 : p ≤ n.primeFactorsList.getLast hne :=
    (Nat.primeFactorsList_sorted n).pairwise.rel_getLast hmem
  unfold Nat.maxPrimeFac
  rw [if_neg h1, List.getLastI_eq_getLast?_getD, List.getLast?_eq_getLast_of_ne_nil hne]
  exact h2

lemma key_bound (f : ℤ[X]) (hf : Irreducible f) (hd : 2 ≤ f.natDegree) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → Lf f ≤ n →
      (f.natDegree : ℝ) / 2 * (n * Real.log n) - C * n
        ≤ (f.natDegree : ℝ) ^ 2 * Real.log 4 * (Erdos976.F f n : ℝ) := by
  obtain ⟨C₄, hsmall⟩ := small_part f hf hd
  refine ⟨C₄ + f.natDegree + Real.log (((2 * Lf f) ^ f.natDegree : ℕ) : ℝ), ?_⟩
  intro n hn hLn
  set Z := ∏ m ∈ Icc 1 n, (f.eval (m : ℤ)).natAbs with hZ
  have hZ0 : Z ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun m _ => Int.natAbs_ne_zero.2 (eval_ne_zero f hf hd m))
  have hF : Erdos976.F f n = Z.maxPrimeFac := by
    unfold Erdos976.F
    congr 1
    rw [hZ]
    exact map_prod Int.natAbsHom _ _
  have hlow := log_prod_ge f hf hd n
  have hlog : Real.log (Z : ℝ)
      = ∑ p ∈ Z.primeFactors, (Z.factorization p : ℝ) * Real.log p := by
    rw [Real.log_nat_eq_sum_factorization]
    rfl
  rw [← Finset.sum_filter_add_sum_filter_not Z.primeFactors (fun p => p ≤ n)] at hlog
  have h1 : ∑ p ∈ Z.primeFactors.filter (fun p => p ≤ n),
      (Z.factorization p : ℝ) * Real.log p
      ≤ ∑ p ∈ Nat.primesLE n, (Z.factorization p : ℝ) * Real.log p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      have hp' := Finset.mem_filter.1 hp
      exact Nat.mem_primesLE.2 ⟨hp'.2, (Nat.mem_primeFactors.1 hp'.1).1⟩
    · intro p _ _
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have h2 : ∑ p ∈ Z.primeFactors.filter (fun p => ¬ p ≤ n),
      (Z.factorization p : ℝ) * Real.log p
      ≤ (f.natDegree : ℝ) ^ 2 * Real.log 4 * (Z.maxPrimeFac : ℝ) := by
    have h3 : ∀ p ∈ Z.primeFactors.filter (fun p => ¬ p ≤ n),
        (Z.factorization p : ℝ) * Real.log p ≤ (f.natDegree : ℝ) ^ 2 * Real.log p := by
      intro p hp
      have hp' := Finset.mem_filter.1 hp
      have hpp := (Nat.mem_primeFactors.1 hp'.1).1
      have h4 := factorization_le_large f hf hd n hLn hpp (by omega)
      apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg _)
      have h5 : (Z.factorization p : ℝ) ≤ ((f.natDegree * f.natDegree : ℕ) : ℝ) := by
        exact_mod_cast h4
      push_cast at h5
      rw [sq]
      exact h5
    calc ∑ p ∈ Z.primeFactors.filter (fun p => ¬ p ≤ n), (Z.factorization p : ℝ) * Real.log p
        ≤ ∑ p ∈ Z.primeFactors.filter (fun p => ¬ p ≤ n),
            (f.natDegree : ℝ) ^ 2 * Real.log p := Finset.sum_le_sum h3
      _ = (f.natDegree : ℝ) ^ 2
            * ∑ p ∈ Z.primeFactors.filter (fun p => ¬ p ≤ n), Real.log (p : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (f.natDegree : ℝ) ^ 2 * ∑ p ∈ Nat.primesLE Z.maxPrimeFac, Real.log (p : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            have hp' := Finset.mem_filter.1 hp
            have hpf := Nat.mem_primeFactors.1 hp'.1
            exact Nat.mem_primesLE.2 ⟨le_maxPrimeFac_of_dvd hZ0 hpf.1 hpf.2.1, hpf.1⟩
          · intro p _ _
            exact Real.log_natCast_nonneg _
      _ = (f.natDegree : ℝ) ^ 2 * Chebyshev.theta (Z.maxPrimeFac : ℝ) := by
          rw [Chebyshev.theta_eq_sum_primesLE_log]
      _ ≤ (f.natDegree : ℝ) ^ 2 * (Real.log 4 * Z.maxPrimeFac) := by
          apply mul_le_mul_of_nonneg_left
            (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)) (by positivity)
      _ = (f.natDegree : ℝ) ^ 2 * Real.log 4 * (Z.maxPrimeFac : ℝ) := by ring
  have h4 := hsmall n hn
  rw [hF]
  linarith

end OMA.Helpers

theorem OMA.solution : type_of% @Erdos976.erdos_976.variants.nagell_ricci := by
  intro f hf hd
  obtain ⟨C, hC⟩ := OMA.Helpers.key_bound f hf hd
  have hd0 : (0 : ℝ) < f.natDegree := by exact_mod_cast (by omega : 0 < f.natDegree)
  have hev : ∀ᶠ n : ℕ in Filter.atTop, 4 * C / f.natDegree ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  rw [Asymptotics.isBigO_iff]
  refine ⟨4 * f.natDegree * Real.log 4, ?_⟩
  filter_upwards [hev, Filter.eventually_ge_atTop 2,
    Filter.eventually_ge_atTop (OMA.Helpers.Lf f)] with n h1 h2 h3
  have h4 := hC n h2 h3
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  rw [Real.norm_of_nonneg (mul_nonneg hn0.le hlog), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have h5 : C * n ≤ (f.natDegree : ℝ) / 4 * (n * Real.log n) := by
    have h6 := (div_le_iff₀ hd0).1 h1
    nlinarith
  have h7 : (f.natDegree : ℝ) / 4 * ((n : ℝ) * Real.log n)
      ≤ (f.natDegree : ℝ) / 4 * (4 * f.natDegree * Real.log 4 * (Erdos976.F f n : ℝ)) := by
    have h8 : (f.natDegree : ℝ) / 4 * (4 * f.natDegree * Real.log 4 * (Erdos976.F f n : ℝ))
        = (f.natDegree : ℝ) ^ 2 * Real.log 4 * (Erdos976.F f n : ℝ) := by ring
    rw [h8]
    linarith
  exact le_of_mul_le_mul_left h7 (by positivity)
