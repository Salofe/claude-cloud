import OMAReductions.R_Erdos700_erdos_700_parts_ii_R1
import Mathlib

-- Step H2 of reduction Erdos700.erdos_700.parts.ii.R1 (Chebyshev plus pigeonhole).
-- With u = 2^j, X = u^4 and Y = 4 u^2: Chebyshev (2^X <= (X+1) lcm(1..X) <= (X+1) X^pi(X)) gives
-- more than (u^3 + 1)(j + 1) primes in [Y, X]. Blocks of length u give a block with j + 2 primes.
-- A set without p < q < r, q - p < r - q, halves its distance to the maximum at every element,
-- so j + 2 elements need spread at least 2^j = u; hence the block contains such a triple, and
-- 2 (r - p)^2 < 2 u^2 < Y <= p.

namespace OMA.Helpers

/-- Halving: a set with no triple p < q < r with q - p < r - q is exponentially spread out. -/
theorem halving : ∀ (k : ℕ) (S : Finset ℕ) (a m : ℕ), a ∈ S → m ∈ S →
    (∀ x ∈ S, a ≤ x ∧ x ≤ m) → k + 2 ≤ S.card →
    (∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p < q → q < r → r - q ≤ q - p) → 2 ^ k ≤ m - a := by
  intro k
  induction k with
  | zero =>
    intro S a m ha hm hb hc _
    obtain ⟨x, hx, hxa⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) a
    have := hb x hx
    have : a < x := lt_of_le_of_ne (hb x hx).1 (Ne.symm hxa)
    simp only [pow_zero]
    omega
  | succ k ih =>
    intro S a m ha hm hb hcS hc
    set S' := S.erase a with hS'
    have hcard : k + 2 ≤ S'.card := by
      rw [Finset.card_erase_of_mem ha]; omega
    have hne : S'.Nonempty := Finset.card_pos.1 (by omega)
    set a' := S'.min' hne with ha'
    have ha'S' : a' ∈ S' := Finset.min'_mem S' hne
    have ha'S : a' ∈ S := Finset.mem_of_mem_erase ha'S'
    have ha'ne : a' ≠ a := Finset.ne_of_mem_erase ha'S'
    have haa' : a < a' := lt_of_le_of_ne (hb a' ha'S).1 (Ne.symm ha'ne)
    obtain ⟨x, hx, hxa⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) a
    have hxa' : a < x := lt_of_le_of_ne (hb x hx).1 (Ne.symm hxa)
    have hma : m ≠ a := by have := (hb x hx).2; omega
    have hmS' : m ∈ S' := Finset.mem_erase.2 ⟨hma, hm⟩
    have hb' : ∀ y ∈ S', a' ≤ y ∧ y ≤ m := fun y hy =>
      ⟨Finset.min'_le S' y hy, (hb y (Finset.mem_of_mem_erase hy)).2⟩
    have hc' : ∀ p ∈ S', ∀ q ∈ S', ∀ r ∈ S', p < q → q < r → r - q ≤ q - p :=
      fun p hp q hq r hr => hc p (Finset.mem_of_mem_erase hp) q (Finset.mem_of_mem_erase hq) r
        (Finset.mem_of_mem_erase hr)
    have hIH := ih S' a' m ha'S' hmS' hb' hcard hc'
    obtain ⟨y, hy, hya⟩ := Finset.exists_mem_ne (by omega : 1 < S'.card) a'
    have hay : a' < y := lt_of_le_of_ne (hb' y hy).1 (Ne.symm hya)
    have hym : y ≤ m := (hb' y hy).2
    have htri := hc a ha a' ha'S m hm haa' (by omega)
    rw [pow_succ]
    omega

theorem chebyshev_nat (n : ℕ) (hn : n ≠ 0) : 2 ^ n ≤ (n + 1) * n ^ (Nat.primesLE n).card := by
  calc 2 ^ n ≤ (n + 1) * Nat.lcmUpto n := Chebyshev.two_pow_le_mul_lcmUpto n
    _ ≤ (n + 1) * n ^ (Nat.primesLE n).card := by
      gcongr
      rw [Nat.lcmUpto_eq_prod_pow_log]
      exact Finset.prod_le_pow_card _ _ _ fun p _ => Nat.pow_log_le_self p hn

theorem pow_ge_sq (j : ℕ) (hj : 12 ≤ j) : 8 * (j + 1) ^ 2 ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    rw [pow_succ 2 j]
    have h1 : 8 * (j + 1 + 1) ^ 2 ≤ 2 * (8 * (j + 1) ^ 2) := by nlinarith
    omega

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos700_erdos_700_parts_ii_R1.H2 := by
  intro N
  obtain ⟨j, hj⟩ : ∃ j, j = N + 12 := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = 2 ^ j := ⟨_, rfl⟩
  have hju : 8 * (j + 1) ^ 2 ≤ u := hu ▸ OMA.Helpers.pow_ge_sq j (by omega)
  have hupos : 0 < u := by rw [hu]; positivity
  obtain ⟨X, hX⟩ : ∃ X, X = u ^ 4 := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = 4 * u ^ 2 := ⟨_, rfl⟩
  have hXpow : X = 2 ^ (4 * j) := by rw [hX, hu, ← pow_mul, mul_comm]
  have hX0 : X ≠ 0 := by rw [hX]; positivity
  have hcheb := OMA.Helpers.chebyshev_nat X hX0
  obtain ⟨π0, hπ0⟩ : ∃ π0, π0 = (Nat.primesLE X).card := ⟨_, rfl⟩
  rw [← hπ0] at hcheb
  have hπ : 2 ^ X ≤ 2 ^ (4 * j + 1 + 4 * j * π0) := by
    calc 2 ^ X ≤ (X + 1) * X ^ π0 := hcheb
      _ ≤ 2 ^ (4 * j + 1) * (2 ^ (4 * j)) ^ π0 := by
        gcongr
        · rw [hXpow, pow_succ]; have : 1 ≤ 2 ^ (4 * j) := Nat.one_le_two_pow; omega
        · rw [hXpow]
      _ = 2 ^ (4 * j + 1 + 4 * j * π0) := by rw [← pow_mul, ← pow_add]
  have hπ' : X ≤ 4 * j + 1 + 4 * j * π0 := (Nat.pow_le_pow_iff_right (by norm_num)).1 hπ
  obtain ⟨P, hP⟩ : ∃ P : Finset ℕ, P = (Nat.primesLE X).filter (fun p => Y ≤ p) := ⟨_, rfl⟩
  have hPcard : π0 ≤ P.card + Y := by
    have h1 := Finset.card_filter_add_card_filter_not (s := Nat.primesLE X) (fun p => Y ≤ p)
    rw [← hP, ← hπ0] at h1
    have h2 : ((Nat.primesLE X).filter (fun p => ¬ Y ≤ p)).card ≤ Y := by
      calc ((Nat.primesLE X).filter (fun p => ¬ Y ≤ p)).card ≤ (Finset.range Y).card := by
            apply Finset.card_le_card
            intro p hp
            simp only [Finset.mem_filter, not_le] at hp
            exact Finset.mem_range.2 hp.2
        _ = Y := Finset.card_range Y
    omega
  have hu4 : X = u * u ^ 3 := by rw [hX]; ring
  have hcount : (Finset.range (u ^ 3 + 1)).card * (j + 1) < P.card := by
    rw [Finset.card_range]
    have key : 4 * j * ((u ^ 3 + 1) * (j + 1) + Y) < 4 * j * π0 := by
      have hYle : 4 * j * Y + 4 * (j + 1) ^ 2 + 4 * j + 1 ≤ u ^ 3 := by
        rw [hY]
        have h2 : 8 * (j + 1) ^ 2 * u ^ 2 ≤ u * u ^ 2 := Nat.mul_le_mul_right _ hju
        have h3 : u * u ^ 2 = u ^ 3 := by ring
        have h4 : 1 ≤ u ^ 2 := Nat.one_le_pow _ _ hupos
        have h5 : 8 * (j + 1) ^ 2 * u ^ 2 = 16 * j * u ^ 2 + (8 * j ^ 2 + 8) * u ^ 2 := by ring
        have h6 : 4 * (j + 1) ^ 2 + 4 * j + 1 ≤ (8 * j ^ 2 + 8) * 1 := by nlinarith
        have h7 : (8 * j ^ 2 + 8) * 1 ≤ (8 * j ^ 2 + 8) * u ^ 2 := Nat.mul_le_mul_left _ h4
        have h8 : 4 * j * (4 * u ^ 2) = 16 * j * u ^ 2 := by ring
        linarith
      have hmain : 8 * (j + 1) ^ 2 * u ^ 3 ≤ X := by rw [hu4]; exact Nat.mul_le_mul_right _ hju
      have hA : 4 * j * ((u ^ 3 + 1) * (j + 1) + Y) =
          4 * j * (j + 1) * u ^ 3 + 4 * j * (j + 1) + 4 * j * Y := by ring
      have hB : 8 * (j + 1) ^ 2 * u ^ 3 =
          4 * j * (j + 1) * u ^ 3 + (4 * j ^ 2 + 12 * j + 8) * u ^ 3 := by ring
      have hC : u ^ 3 ≤ (4 * j ^ 2 + 12 * j + 8) * u ^ 3 := Nat.le_mul_of_pos_left _ (by positivity)
      have hD : 4 * j * (j + 1) < 4 * (j + 1) ^ 2 := by nlinarith
      rw [hA]
      linarith
    have := Nat.lt_of_mul_lt_mul_left key
    omega
  have hmaps : ∀ p ∈ P, (fun p => (p - Y) / u) p ∈ Finset.range (u ^ 3 + 1) := by
    intro p hp
    rw [hP, Finset.mem_filter, Nat.mem_primesLE] at hp
    apply Finset.mem_range.2
    apply Nat.lt_add_one_iff.2
    apply Nat.div_le_of_le_mul
    omega
  obtain ⟨c, -, hc⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hcount
  obtain ⟨F, hF⟩ : ∃ F : Finset ℕ, F = P.filter (fun p => (p - Y) / u = c) := ⟨_, rfl⟩
  rw [← hF] at hc
  have hFne : F.Nonempty := Finset.card_pos.1 (by omega)
  have hFmem : ∀ x ∈ F, x.Prime ∧ Y ≤ x ∧ (x - Y) / u = c := by
    intro x hx
    rw [hF, Finset.mem_filter, hP, Finset.mem_filter, Nat.mem_primesLE] at hx
    exact ⟨hx.1.1.2, hx.1.2, hx.2⟩
  have hspread : ∀ x ∈ F, ∀ y ∈ F, x - y < u := by
    intro x hx y hy
    obtain ⟨-, hxY, hxc⟩ := hFmem x hx
    obtain ⟨-, hyY, hyc⟩ := hFmem y hy
    have e1 := Nat.div_add_mod (x - Y) u
    have e2 := Nat.div_add_mod (y - Y) u
    have r1 := Nat.mod_lt (x - Y) hupos
    have r2 := Nat.mod_lt (y - Y) hupos
    rw [hxc] at e1
    rw [hyc] at e2
    generalize u * c = w at e1 e2
    omega
  by_contra hno
  push Not at hno
  have hnt : ∀ p ∈ F, ∀ q ∈ F, ∀ r ∈ F, p < q → q < r → r - q ≤ q - p := by
    intro p hp q hq r hr hpq hqr
    by_contra hlt
    push Not at hlt
    obtain ⟨hpp, hpY, -⟩ := hFmem p hp
    obtain ⟨hqp, -, -⟩ := hFmem q hq
    obtain ⟨hrp, -, -⟩ := hFmem r hr
    have hsp := hspread r hr p hp
    have hNp : N < p := by
      have h1 : j < u := hu ▸ Nat.lt_two_pow_self
      have h2 : u ≤ Y := by rw [hY]; nlinarith
      omega
    have hsmall : 2 * (r - p) ^ 2 < p := by
      have : (r - p) ^ 2 < u ^ 2 := Nat.pow_lt_pow_left hsp (by norm_num)
      omega
    exact absurd hsmall (not_lt.2 (hno p q r hNp hpp hqp hrp hpq hqr hlt))
  have hlo := Finset.min'_mem F hFne
  have hhi := Finset.max'_mem F hFne
  have hh := OMA.Helpers.halving j F (F.min' hFne) (F.max' hFne) hlo hhi
    (fun x hx => ⟨Finset.min'_le F x hx, Finset.le_max' F x hx⟩) (by omega) hnt
  have := hspread _ hhi _ hlo
  omega
