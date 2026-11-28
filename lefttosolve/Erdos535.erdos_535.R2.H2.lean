import OMAReductions.R_Erdos535_erdos_535_R2

/-!
# Step H2 of the reduction Erdos535.erdos_535.R2

Class map: g n i = min (v_i(n)) (log2 N) for i = 0, ..., t. The truncation at log2 N is never
reached on 1..N, because 2 ^ v <= p ^ v <= n <= N for every prime p, so two members of one
class have equal exponents at every prime p <= t.

Code: enc n consists of the even numbers 2 * pair p j for the primes p > t and
1 <= j <= v_p(n), padded to exactly K elements by odd numbers 2 * pair n i + 1. The even
part of enc a ∩ enc b is {2 * pair p j : t < p, 1 <= j <= min (v_p a) (v_p b)}, so equal
intersections give equal min (v_p a) (v_p b) for every p > t. Together with the small primes
this fixes the factorization of gcd a b, hence gcd a b itself.
-/

namespace OMA.Helpers

/-- Codes of the prime powers `p ^ j` with `t < p` and `1 ≤ j ≤ v_p(n)`. -/
def bigCode (t n : ℕ) : Finset ℕ :=
  (n.primeFactors.filter (t < ·)).biUnion
    (fun p => (Finset.Icc 1 (n.factorization p)).image (fun j => 2 * Nat.pair p j))

/-- Odd padding codes, private to `n`. -/
def padCode (n m : ℕ) : Finset ℕ :=
  (Finset.range m).image (fun i => 2 * Nat.pair n i + 1)

/-- The `K`-element code of `n`. -/
def encode (t K n : ℕ) : Finset ℕ :=
  bigCode t n ∪ padCode n (K - ∑ p ∈ n.primeFactors.filter (t < ·), n.factorization p)

theorem card_bigCode (t n : ℕ) :
    (bigCode t n).card = ∑ p ∈ n.primeFactors.filter (t < ·), n.factorization p := by
  unfold bigCode
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro p _
    rw [Finset.card_image_of_injective, Nat.card_Icc, Nat.add_sub_cancel]
    intro j j' h
    simp only at h
    have h' : Nat.pair p j = Nat.pair p j' := by omega
    exact (Nat.pair_eq_pair.mp h').2
  · intro p _ q _ hpq
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j', _, hj'⟩ := Finset.mem_image.mp hx'
    have h' : Nat.pair q j' = Nat.pair p j := by omega
    exact hpq (Nat.pair_eq_pair.mp h').1.symm

theorem card_padCode (n m : ℕ) : (padCode n m).card = m := by
  unfold padCode
  rw [Finset.card_image_of_injective, Finset.card_range]
  intro i i' h
  have h' : Nat.pair n i = Nat.pair n i' := by simp only at h; omega
  exact (Nat.pair_eq_pair.mp h').2

theorem card_encode (t K n : ℕ)
    (h : ∑ p ∈ n.primeFactors.filter (t < ·), n.factorization p ≤ K) :
    (encode t K n).card = K := by
  unfold encode
  rw [Finset.card_union_of_disjoint, card_bigCode, card_padCode]
  · omega
  · rw [Finset.disjoint_left]
    intro x hx hx'
    unfold bigCode at hx
    unfold padCode at hx'
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx'
    omega

theorem mem_encode (t K n p j : ℕ) :
    2 * Nat.pair p j ∈ encode t K n ↔ t < p ∧ 1 ≤ j ∧ j ≤ n.factorization p := by
  unfold encode bigCode padCode
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image,
    Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro (⟨q, ⟨_, hq⟩, i, ⟨hi1, hi2⟩, hqi⟩ | ⟨i, _, hi⟩)
    · have h' : Nat.pair q i = Nat.pair p j := by omega
      obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp h'
      exact ⟨hq, hi1, hi2⟩
    · omega
  · rintro ⟨hp, hj1, hj2⟩
    left
    refine ⟨p, ⟨?_, hp⟩, j, ⟨hj1, hj2⟩, rfl⟩
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    omega

theorem factorization_le_log {N n : ℕ} (hn : n ∈ Finset.Icc 1 N) (p : ℕ) :
    n.factorization p ≤ Nat.log 2 N := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
  by_cases hp : p.Prime
  · apply Nat.le_log_of_pow_le Nat.one_lt_two
    calc 2 ^ n.factorization p ≤ p ^ n.factorization p :=
          Nat.pow_le_pow_left hp.two_le _
      _ ≤ n := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n p)
      _ ≤ N := h2
  · rw [Nat.factorization_eq_zero_of_not_prime n hp]
    exact Nat.zero_le _

theorem min_eq_of_iff {x y z w : ℕ}
    (h : ∀ j, 1 ≤ j → (j ≤ x ∧ j ≤ y ↔ j ≤ z ∧ j ≤ w)) : min x y = min z w := by
  have h1 := h (min x y)
  have h2 := h (min z w)
  by_cases hx : 1 ≤ min x y <;> by_cases hz : 1 ≤ min z w
  · have a1 := (h1 hx).mp ⟨min_le_left _ _, min_le_right _ _⟩
    have a2 := (h2 hz).mpr ⟨min_le_left _ _, min_le_right _ _⟩
    omega
  · have a1 := (h1 hx).mp ⟨min_le_left _ _, min_le_right _ _⟩
    omega
  · have a2 := (h2 hz).mpr ⟨min_le_left _ _, min_le_right _ _⟩
    omega
  · omega

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : OMA.R_Erdos535_erdos_535_R2.H2 := by
  unfold OMA.R_Erdos535_erdos_535_R2.H2
  intro t K N hK
  refine ⟨fun n i => ⟨min (n.factorization i) (Nat.log 2 N), by omega⟩, encode t K,
    fun n hn => card_encode t K n (hK n hn), ?_⟩
  intro a ha b hb c hc d hd hab hac had henc
  have hne : ∀ n ∈ Finset.Icc 1 N, n ≠ 0 := fun n hn => by
    have := (Finset.mem_Icc.mp hn).1; omega
  -- small primes: members of one class have equal exponents
  have small : ∀ p, p ≤ t → ∀ x ∈ Finset.Icc 1 N, ∀ y ∈ Finset.Icc 1 N,
      (fun i : Fin (t + 1) => (⟨min (x.factorization i) (Nat.log 2 N), by omega⟩ :
        Fin (Nat.log 2 N + 1))) =
      (fun i : Fin (t + 1) => (⟨min (y.factorization i) (Nat.log 2 N), by omega⟩ :
        Fin (Nat.log 2 N + 1))) →
      x.factorization p = y.factorization p := by
    intro p hp x hx y hy hxy
    have h := congrArg Fin.val (congrFun hxy ⟨p, by omega⟩)
    simp only at h
    have := factorization_le_log hx p
    have := factorization_le_log hy p
    omega
  apply Nat.eq_of_factorization_eq (Nat.gcd_ne_zero_left (hne a ha))
    (Nat.gcd_ne_zero_left (hne c hc))
  intro p
  rw [Nat.factorization_gcd (hne a ha) (hne b hb), Nat.factorization_gcd (hne c hc) (hne d hd),
    Finsupp.inf_apply, Finsupp.inf_apply]
  by_cases hp : p ≤ t
  · have e1 := small p hp a ha b hb hab
    have e2 := small p hp a ha c hc hac
    have e3 := small p hp a ha d hd had
    rw [← e1, ← e2, ← e3]
  · -- large primes: the even codes in the intersection record the minimum exponent
    apply min_eq_of_iff
    intro j hj
    have h := congrArg (fun s => 2 * Nat.pair p j ∈ s) henc
    simp only [Finset.mem_inter, mem_encode] at h
    have hp' : t < p := by omega
    constructor
    · intro hx
      have := h.mp ⟨⟨hp', hj, hx.1⟩, ⟨hp', hj, hx.2⟩⟩
      exact ⟨this.1.2.2, this.2.2.2⟩
    · intro hx
      have := h.mpr ⟨⟨hp', hj, hx.1⟩, ⟨hp', hj, hx.2⟩⟩
      exact ⟨this.1.2.2, this.2.2.2⟩
