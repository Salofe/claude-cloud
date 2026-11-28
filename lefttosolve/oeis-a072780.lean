import OMAStatements.S_oeis_a072780
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a072780 ArithmeticFunction

def S (n : ℕ) : ℤ := (ArithmeticFunction.sigma 2 n : ℤ)

def T (n : ℕ) : ℤ := (Nat.totient n : ℤ) * (ArithmeticFunction.sigma 1 n : ℤ)

theorem a_eq (n : ℕ) : a n = S n + T n - 2 * (n : ℤ) ^ 2 := rfl

theorem S_one : S 1 = 1 := by simp [S]

theorem T_one : T 1 = 1 := by simp [T]

theorem a_one : a 1 = 0 := by rw [a_eq, S_one, T_one]; norm_num

theorem S_pos (n : ℕ) (hn : n ≠ 0) : 0 < S n := by
  unfold S
  exact_mod_cast sigma_pos 2 n hn

theorem S_pp (p k : ℕ) (hp : p.Prime) :
    S (p ^ (k + 1)) = ∑ j ∈ Finset.range (k + 2), (p : ℤ) ^ (j * 2) := by
  unfold S
  rw [sigma_apply_prime_pow hp]
  push_cast
  rfl

theorem T_pp (p k : ℕ) (hp : p.Prime) :
    T (p ^ (k + 1)) = (p : ℤ) ^ (2 * k + 2) - (p : ℤ) ^ k := by
  unfold T
  rw [Nat.totient_prime_pow_succ hp, sigma_one_apply_prime_pow hp]
  push_cast
  rw [Nat.cast_sub hp.one_le]
  push_cast
  have h := geom_sum_mul (p : ℤ) (k + 1 + 1)
  calc (p : ℤ) ^ k * ((p : ℤ) - 1) * ∑ i ∈ Finset.range (k + 1 + 1), (p : ℤ) ^ i
      = (p : ℤ) ^ k * ((∑ i ∈ Finset.range (k + 1 + 1), (p : ℤ) ^ i) * ((p : ℤ) - 1)) := by ring
    _ = (p : ℤ) ^ k * ((p : ℤ) ^ (k + 1 + 1) - 1) := by rw [h]
    _ = (p : ℤ) ^ (2 * k + 2) - (p : ℤ) ^ k := by ring

theorem S_prime (p : ℕ) (hp : p.Prime) : S p = 1 + (p : ℤ) ^ 2 := by
  have h := S_pp p 0 hp
  rw [pow_one] at h
  rw [h]
  simp [Finset.sum_range_succ]

theorem T_prime (p : ℕ) (hp : p.Prime) : T p = (p : ℤ) ^ 2 - 1 := by
  have h := T_pp p 0 hp
  rw [pow_one] at h
  rw [h]
  simp

theorem S_pp_ge (p k : ℕ) (hp : p.Prime) :
    0 ≤ S (p ^ (k + 1)) - (p : ℤ) ^ (2 * k + 2) - (p : ℤ) ^ k ∧
    (1 ≤ k → 3 ≤ S (p ^ (k + 1)) - (p : ℤ) ^ (2 * k + 2) - (p : ℤ) ^ k) ∧
    (k = 0 → S (p ^ (k + 1)) - (p : ℤ) ^ (2 * k + 2) - (p : ℤ) ^ k = 0) := by
  have h3 : 1 ≤ k → 3 ≤ S (p ^ (k + 1)) - (p : ℤ) ^ (2 * k + 2) - (p : ℤ) ^ k := by
    intro hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [S_pp p (j + 1) hp, Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 : (1 : ℤ) ≤ ∑ x ∈ Finset.range (j + 1), (p : ℤ) ^ (x * 2) := by
      have := Finset.single_le_sum (f := fun x => (p : ℤ) ^ (x * 2))
        (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.succ_pos j))
      simpa using this
    have hu : (2 : ℤ) ≤ (p : ℤ) ^ (j + 1) := by
      have : 2 ≤ p ^ (j + 1) := by
        calc 2 ≤ p := hp.two_le
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ (j + 1) := Nat.pow_le_pow_right hp.pos (by omega)
      exact_mod_cast this
    have e1 : (p : ℤ) ^ ((j + 1) * 2) = ((p : ℤ) ^ (j + 1)) ^ 2 := by ring
    have e2 : (p : ℤ) ^ ((j + 1 + 1) * 2) = (p : ℤ) ^ (2 * (j + 1) + 2) := by ring_nf
    rw [e1, e2]
    nlinarith
  have h0 : k = 0 → S (p ^ (k + 1)) - (p : ℤ) ^ (2 * k + 2) - (p : ℤ) ^ k = 0 := by
    rintro rfl
    rw [pow_one, S_prime p hp]
    ring
  refine ⟨?_, h3, h0⟩
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [h0 hk]
  · linarith [h3 hk]

theorem S_mul (a b : ℕ) (h : Nat.Coprime a b) : S (a * b) = S a * S b := by
  unfold S
  rw [isMultiplicative_sigma.map_mul_of_coprime h]
  push_cast
  ring

theorem T_mul (a b : ℕ) (h : Nat.Coprime a b) : T (a * b) = T a * T b := by
  unfold T
  rw [isMultiplicative_sigma.map_mul_of_coprime h, Nat.totient_mul h]
  push_cast
  ring

theorem cop (p k m : ℕ) (hp : p.Prime) (hm : ¬ p ∣ m) : Nat.Coprime (p ^ (k + 1)) m :=
  ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm).pow_left _

theorem a_decomp (p k m : ℕ) (hp : p.Prime) (hm : ¬ p ∣ m) :
    a (p ^ (k + 1) * m) =
      (S (p ^ (k + 1)) - (p : ℤ) ^ (2 * k + 2) - (p : ℤ) ^ k) * S m +
        (p : ℤ) ^ (2 * k + 2) * a m + (p : ℤ) ^ k * (S m - T m) := by
  rw [a_eq, a_eq, S_mul _ _ (cop p k m hp hm), T_mul _ _ (cop p k m hp hm), T_pp p k hp]
  push_cast
  ring

theorem T_sub (p k m : ℕ) (hp : p.Prime) (hm : ¬ p ∣ m) :
    S (p ^ (k + 1) * m) - T (p ^ (k + 1) * m) =
      (S (p ^ (k + 1)) - (p : ℤ) ^ (2 * k + 2) + (p : ℤ) ^ k) * S m +
        ((p : ℤ) ^ (2 * k + 2) - (p : ℤ) ^ k) * (S m - T m) := by
  rw [S_mul _ _ (cop p k m hp hm), T_mul _ _ (cop p k m hp hm), T_pp p k hp]
  ring

/-- Decomposition of `n ≥ 2` as `p ^ (k+1) * m` with `p` prime, `p ∤ m`, `1 ≤ m < n`. -/
theorem decomp (n : ℕ) (hn : 2 ≤ n) :
    ∃ p k m : ℕ, p.Prime ∧ ¬ p ∣ m ∧ n = p ^ (k + 1) * m ∧ 1 ≤ m ∧ m < n := by
  have hp : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
  obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) (Nat.minFac n)
    hp.ne_one
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at he; omega
    · exact h
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := by
    rcases e with _ | k
    · exfalso
      apply hm
      rw [pow_zero, one_mul] at he
      rw [← he]
      exact Nat.minFac_dvd n
    · exact ⟨k, rfl⟩
  refine ⟨Nat.minFac n, k, m, hp, hm, he, hm1, ?_⟩
  have h2 : 2 ≤ (Nat.minFac n) ^ (k + 1) := by
    calc 2 ≤ Nat.minFac n := hp.two_le
      _ = Nat.minFac n ^ 1 := (pow_one _).symm
      _ ≤ Nat.minFac n ^ (k + 1) := Nat.pow_le_pow_right hp.pos (by omega)
  rw [he]
  nlinarith

theorem base (n : ℕ) : 1 ≤ n → 0 ≤ a n ∧ (2 ≤ n → T n < S n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n = 1 := by omega
    subst this
    exact ⟨by rw [a_one], fun h => absurd h (by norm_num)⟩
  obtain ⟨p, k, m, hp, hpm, rfl, hm1, hmn⟩ := decomp n h
  obtain ⟨iha, ihT⟩ := ih m hmn hm1
  have hTS : 0 ≤ S m - T m := by
    rcases Nat.lt_or_ge m 2 with h' | h'
    · have : m = 1 := by omega
      subst this
      rw [S_one, T_one]; norm_num
    · linarith [ihT h']
  have hSm := S_pos m (by omega)
  obtain ⟨hs0, -, -⟩ := S_pp_ge p k hp
  have hB : (0 : ℤ) < (p : ℤ) ^ k := by have := hp.pos; positivity
  have hA : (p : ℤ) ^ k < (p : ℤ) ^ (2 * k + 2) := by
    apply pow_lt_pow_right₀ (by exact_mod_cast hp.one_lt) (by omega)
  refine ⟨?_, fun _ => ?_⟩
  · rw [a_decomp p k m hp hpm]
    have := mul_nonneg hs0 hSm.le
    have := mul_nonneg (by positivity : (0 : ℤ) ≤ (p : ℤ) ^ (2 * k + 2)) iha
    have := mul_nonneg hB.le hTS
    linarith
  · have h := T_sub p k m hp hpm
    have h1 : 0 < (S (p ^ (k + 1)) - (p : ℤ) ^ (2 * k + 2) + (p : ℤ) ^ k) * S m := by
      apply mul_pos _ hSm
      linarith
    have h2 := mul_nonneg (by linarith : (0 : ℤ) ≤ (p : ℤ) ^ (2 * k + 2) - (p : ℤ) ^ k) hTS
    linarith

theorem zero_iff (n : ℕ) (hn : 1 ≤ n) : a n = 0 ↔ n = 1 ∨ Nat.Prime n := by
  constructor
  · intro h0
    rcases Nat.lt_or_ge n 2 with h | h
    · left; omega
    right
    obtain ⟨p, k, m, hp, hpm, rfl, hm1, hmn⟩ := decomp n h
    obtain ⟨iha, ihT⟩ := base m hm1
    have hTS : 0 ≤ S m - T m := by
      rcases Nat.lt_or_ge m 2 with h' | h'
      · have : m = 1 := by omega
        subst this
        rw [S_one, T_one]; norm_num
      · linarith [ihT h']
    have hSm := S_pos m (by omega)
    obtain ⟨hs0, hs3, -⟩ := S_pp_ge p k hp
    have hB : (0 : ℤ) < (p : ℤ) ^ k := by have := hp.pos; positivity
    rw [a_decomp p k m hp hpm] at h0
    have t1 := mul_nonneg hs0 hSm.le
    have t2 := mul_nonneg (by positivity : (0 : ℤ) ≤ (p : ℤ) ^ (2 * k + 2)) iha
    have t3 := mul_nonneg hB.le hTS
    have z3 : (p : ℤ) ^ k * (S m - T m) = 0 := by linarith
    have z1 : (S (p ^ (k + 1)) - (p : ℤ) ^ (2 * k + 2) - (p : ℤ) ^ k) * S m = 0 := by linarith
    have hm : m = 1 := by
      by_contra hne
      have := ihT (by omega)
      have : (p : ℤ) ^ k * (S m - T m) > 0 := mul_pos hB (by linarith)
      linarith
    have hk : k = 0 := by
      by_contra hne
      have := hs3 (by omega)
      have : 0 < (S (p ^ (k + 1)) - (p : ℤ) ^ (2 * k + 2) - (p : ℤ) ^ k) * S m :=
        mul_pos (by linarith) hSm
      linarith
    subst hm hk
    simpa using hp
  · rintro (rfl | hp)
    · exact a_one
    · have h := a_decomp n 0 1 hp (by
        intro hd; exact hp.one_lt.ne' (Nat.dvd_one.mp hd))
      rw [pow_one, mul_one] at h
      rw [h, a_one, S_one, T_one, S_prime n hp]
      ring

theorem two_iff (n : ℕ) (hn : 1 ≤ n) :
    a n = 2 ↔ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ n = p * q := by
  constructor
  · intro h2
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by omega
      subst this
      rw [a_one] at h2; norm_num at h2
    obtain ⟨p, k, m, hp, hpm, rfl, hm1, hmn⟩ := decomp n h
    obtain ⟨iha, ihT⟩ := base m hm1
    have hTS : 0 ≤ S m - T m := by
      rcases Nat.lt_or_ge m 2 with h' | h'
      · have : m = 1 := by omega
        subst this
        rw [S_one, T_one]; norm_num
      · linarith [ihT h']
    have hSm := S_pos m (by omega)
    obtain ⟨hs0, hs3, hs00⟩ := S_pp_ge p k hp
    have hB : (0 : ℤ) < (p : ℤ) ^ k := by have := hp.pos; positivity
    have hA4 : (4 : ℤ) ≤ (p : ℤ) ^ (2 * k + 2) := by
      have : 4 ≤ p ^ (2 * k + 2) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ p ^ 2 := Nat.pow_le_pow_left hp.two_le 2
          _ ≤ p ^ (2 * k + 2) := Nat.pow_le_pow_right hp.pos (by omega)
      exact_mod_cast this
    rw [a_decomp p k m hp hpm] at h2
    have t1 := mul_nonneg hs0 hSm.le
    have t3 := mul_nonneg hB.le hTS
    have ham : a m = 0 := by
      by_contra hne
      have : 1 ≤ a m := by omega
      have : 4 ≤ (p : ℤ) ^ (2 * k + 2) * a m := by nlinarith
      linarith
    rw [ham, mul_zero, add_zero] at h2
    rcases (zero_iff m hm1).mp ham with rfl | hq
    · rw [S_one, T_one, sub_self, mul_zero, add_zero, mul_one] at h2
      rcases Nat.eq_zero_or_pos k with hk | hk
      · rw [hs00 hk] at h2; norm_num at h2
      · have := hs3 hk; linarith
    · rw [S_prime m hq, T_prime m hq] at h2
      have hk : k = 0 := by
        by_contra hne
        have : (2 : ℤ) ≤ (p : ℤ) ^ k := by
          have : 2 ≤ p ^ k := by
            calc 2 ≤ p := hp.two_le
              _ = p ^ 1 := (pow_one p).symm
              _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos (by omega)
          exact_mod_cast this
        have : 0 ≤ (S (p ^ (k + 1)) - (p : ℤ) ^ (2 * k + 2) - (p : ℤ) ^ k) *
            (1 + (m : ℤ) ^ 2) := mul_nonneg hs0 (by positivity)
        nlinarith
      subst hk
      refine ⟨p, m, hp, hq, ?_, by rw [zero_add, pow_one]⟩
      rintro rfl
      exact hpm (dvd_refl p)
  · rintro ⟨p, q, hp, hq, hpq, rfl⟩
    have hpq' : ¬ p ∣ q := fun hd => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd)
    have h := a_decomp p 0 q hp hpq'
    rw [zero_add, pow_one] at h
    rw [h, S_prime p hp, (zero_iff q hq.one_lt.le).mpr (Or.inr hq),
      S_prime q hq, T_prime q hq]
    ring

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a072780.main :=
  ⟨fun n hn => ⟨(base n hn).1, zero_iff n hn⟩, fun n hn => two_iff n hn⟩
