import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R1

/-!
# Step H2 of the reduction AgohGiuga.agoh_giuga.variants.giuga.R1

Giuga (1950): if n is a strong Giuga number and p is a prime factor of n, then p divides
n / p - 1. Write n = p m. Modulo p the sum of i ^ (n - 1) over 0 < i < n is m times the sum of
x ^ (n - 1) over the field ZMod p, which is -1 when p - 1 divides n - 1 and 0 otherwise. Since p
divides 1 plus the sum, the second case would give 1 = 0, and the first gives m = 1 modulo p.
Only the upstream definition `AgohGiuga.IsStrongGiuga` is used.
-/

namespace OMA.Helpers

theorem sum_range_eq_univ (p : ℕ) [Fact p.Prime] (e : ℕ) :
    ∑ i ∈ Finset.range p, ((i : ZMod p)) ^ e = ∑ x : ZMod p, x ^ e := by
  refine Finset.sum_nbij' (fun i => (i : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intro i _; exact Finset.mem_univ _
  · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro i hi
    exact ZMod.val_cast_of_lt (Finset.mem_range.mp hi)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro i _; rfl

theorem sum_univ_pow (p : ℕ) [hp : Fact p.Prime] (e : ℕ) (he : 0 < e) :
    ∑ x : ZMod p, x ^ e = if p - 1 ∣ e then -1 else 0 := by
  classical
  have hU := FiniteField.sum_pow_units (ZMod p) e
  rw [ZMod.card] at hU
  rw [← hU]
  let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ x, Units.val_injective⟩
  have hmap : Finset.univ.map φ = Finset.univ \ {0} := by
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Finset.mem_singleton]
    constructor
    · rintro ⟨u, rfl⟩
      exact u.ne_zero
    · intro hx
      exact ⟨Units.mk0 x hx, rfl⟩
  rw [← Finset.sum_sdiff ({0} : Finset (ZMod p)).subset_univ, Finset.sum_singleton,
    zero_pow he.ne', add_zero, ← hmap, Finset.sum_map]
  rfl

theorem sum_range_mul (p : ℕ) (e m : ℕ) :
    ∑ i ∈ Finset.range (p * m), ((i : ZMod p)) ^ e =
      (m : ZMod p) * ∑ i ∈ Finset.range p, ((i : ZMod p)) ^ e := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have : ∀ x : ℕ, (((p * m + x : ℕ) : ZMod p)) = (x : ZMod p) := by
      intro x
      push_cast
      simp
    simp only [this]
    push_cast
    ring

theorem sum_Ioo_eq_range (p N e : ℕ) (he : 0 < e) :
    ∑ i ∈ Finset.Ioo 0 N, ((i : ZMod p)) ^ e = ∑ i ∈ Finset.range N, ((i : ZMod p)) ^ e := by
  apply Finset.sum_subset
  · intro i hi
    rw [Finset.mem_Ioo] at hi
    exact Finset.mem_range.mpr hi.2
  · intro i hi hni
    rw [Finset.mem_Ioo] at hni
    have : i = 0 := by
      rw [Finset.mem_range] at hi
      omega
    subst this
    simp [zero_pow he.ne']

theorem giuga_prime_dvd (n : ℕ) (hn : AgohGiuga.IsStrongGiuga n) :
    ∀ p ∈ n.primeFactors, p ∣ (n / p - 1) := by
  intro p hp
  obtain ⟨hcomp, hdvd⟩ := hn
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpn := Nat.dvd_of_mem_primeFactors hp
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨m, rfl⟩ := hpn
  rw [Nat.mul_div_cancel_left m hpp.pos]
  have hn1 : 1 < p * m := hcomp.1
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; omega
    · exact h
  have he : 0 < p * m - 1 := by omega
  have h1 : p ∣ 1 + ∑ i ∈ Finset.Ioo 0 (p * m), i ^ (p * m - 1) :=
    (dvd_mul_right p m).trans hdvd
  rw [← ZMod.natCast_eq_zero_iff] at h1
  push_cast at h1
  rw [sum_Ioo_eq_range p _ _ he, sum_range_mul, sum_range_eq_univ, sum_univ_pow p _ he] at h1
  split_ifs at h1 with hd
  · rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hm]
    push_cast
    linear_combination -h1
  · simp at h1

end OMA.Helpers

theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R1.H2 :=
  fun n hn => OMA.Helpers.giuga_prime_dvd n hn
