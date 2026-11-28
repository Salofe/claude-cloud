import OMAStatements.S_oeis_a285052
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a285052

theorem idem_unique {R : Type*} [Monoid R] {x e f : R} {k m : ℕ}
    (he : IsIdempotentElem e) (hk : 0 < k) (hxk : x ^ k = e)
    (hf : IsIdempotentElem f) (hm : 0 < m) (hxm : x ^ m = f) : e = f := by
  calc e = e ^ m := (he.pow_eq hm.ne').symm
    _ = x ^ (k * m) := by rw [pow_mul, hxk]
    _ = x ^ (m * k) := by rw [mul_comm]
    _ = f ^ k := by rw [pow_mul, hxm]
    _ = f := hf.pow_eq hk.ne'

theorem triples_eq (n : ℕ) : triples n =
    {t | IsIdempotentElem t.1 ∧ IsIdempotentElem t.2.1 ∧ t.2.2 = t.1 * t.2.1} := by
  ext ⟨e1, e2, e3⟩
  simp only [triples, idempotentPower, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, b, ⟨h1, k, hk, hak⟩, ⟨h2, l, hl, hbl⟩, ⟨h3, m, hm, habm⟩⟩
    refine ⟨h1, h2, ?_⟩
    have hp : (a * b) ^ (k * l) = e1 * e2 := by
      rw [mul_pow, pow_mul, hak, mul_comm k l, pow_mul, hbl, h1.pow_eq hl.ne', h2.pow_eq hk.ne']
    exact (idem_unique (h1.mul h2) (Nat.mul_pos hk hl) hp h3 hm habm).symm
  · rintro ⟨h1, h2, h3⟩
    refine ⟨e1, e2, ⟨h1, 1, one_pos, pow_one _⟩, ⟨h2, 1, one_pos, pow_one _⟩, ?_⟩
    subst h3
    exact ⟨h1.mul h2, 1, one_pos, pow_one _⟩

/-- Idempotents of a ring. -/
abbrev Idem (R : Type*) [Mul R] := {e : R // IsIdempotentElem e}

def idemEquivOfRingEquiv {R S : Type*} [Semiring R] [Semiring S] (f : R ≃+* S) :
    Idem R ≃ Idem S :=
  f.toEquiv.subtypeEquiv (fun e => by
    simp only [IsIdempotentElem, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
    rw [← map_mul, f.injective.eq_iff])

def idemProdEquiv (R S : Type*) [Mul R] [Mul S] : Idem (R × S) ≃ Idem R × Idem S :=
  (Equiv.subtypeEquivRight (fun e => by
    simp only [IsIdempotentElem, Prod.ext_iff, Prod.fst_mul, Prod.snd_mul])).trans
    (Equiv.subtypeProdEquivProd (p := fun a : R => a * a = a) (q := fun b : S => b * b = b))

theorem idem_primePow (p k : ℕ) (hp : p.Prime) (hk : 0 < k) (e : ZMod (p ^ k)) :
    IsIdempotentElem e ↔ e = 0 ∨ e = 1 := by
  have : NeZero (p ^ k) := ⟨(pow_pos hp.pos k).ne'⟩
  constructor
  · intro he
    by_cases hd : p ∣ e.val
    · left
      have h1 : e ^ k = 0 := by
        rw [← ZMod.natCast_zmod_val e, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
        exact pow_dvd_pow_of_dvd hd k
      rw [← he.pow_eq hk.ne', h1]
    · right
      have hu : IsUnit e := by
        rw [← ZMod.natCast_zmod_val e, ZMod.isUnit_iff_coprime]
        exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hd).symm
      exact (IsIdempotentElem.iff_eq_one_of_isUnit hu).1 he
  · rintro (h | h) <;> subst h
    · exact IsIdempotentElem.zero
    · exact IsIdempotentElem.one

theorem card_idem (n : ℕ) (hn : 0 < n) : Nat.card (Idem (ZMod n)) = 2 ^ n.primeFactors.card := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => exact absurd hn (lt_irrefl 0)
  | one =>
    simp only [Nat.primeFactors_one, Finset.card_empty, pow_zero]
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨⟨0, IsIdempotentElem.zero⟩⟩⟩
  | prime_pow p k hp hk =>
    rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.card_singleton, pow_one]
    have : Fact (1 < p ^ k) := ⟨Nat.one_lt_pow hk.ne' hp.one_lt⟩
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨0, IsIdempotentElem.zero⟩, ⟨1, IsIdempotentElem.one⟩, ?_, ?_⟩
    · intro h
      exact zero_ne_one (congrArg Subtype.val h)
    · ext ⟨e, he⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      rcases (idem_primePow p k hp hk e).1 he with h | h
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.card_congr ((idemEquivOfRingEquiv (ZMod.chineseRemainder hab)).trans
      (idemProdEquiv _ _)), Nat.card_prod, iha (by omega), ihb (by omega),
      Nat.primeFactors_mul (by omega) (by omega),
      Finset.card_union_of_disjoint hab.disjoint_primeFactors, pow_add]

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a285052.main := by
  intro n hn
  rw [triples_eq]
  have e : ↥{t : ZMod n × ZMod n × ZMod n |
      IsIdempotentElem t.1 ∧ IsIdempotentElem t.2.1 ∧ t.2.2 = t.1 * t.2.1} ≃
      Idem (ZMod n) × Idem (ZMod n) :=
    { toFun := fun t => (⟨t.1.1, t.2.1⟩, ⟨t.1.2.1, t.2.2.1⟩)
      invFun := fun p => ⟨(p.1.1, p.2.1, p.1.1 * p.2.1), p.1.2, p.2.2, rfl⟩
      left_inv := by
        rintro ⟨⟨e1, e2, e3⟩, h1, h2, h3⟩
        simp only at h3
        subst h3
        rfl
      right_inv := by
        rintro ⟨⟨e1, h1⟩, ⟨e2, h2⟩⟩
        rfl }
  rw [Nat.card_congr e, Nat.card_prod, card_idem n hn, ← mul_pow]
  norm_num
