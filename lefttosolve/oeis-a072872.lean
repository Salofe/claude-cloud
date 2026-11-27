import OMAStatements.S_oeis_a072872
import Mathlib

namespace OMA.Helpers

/-- Trial division by `d, d + 2, d + 4, ...` with fuel `f`; `true` means no divisor was found
below the square root. -/
def td (n f : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => false)
    (fun _ ih d => cond (Nat.blt n (d * d)) true (cond (Nat.beq (n % d) 0) false (ih (d + 2)))) f

/-- A kernel-friendly primality test. -/
def isP (n : ℕ) : Bool := Nat.beq n 2 || (Nat.ble 2 n && !Nat.beq (n % 2) 0 && td n n 3)

theorem td_zero (n d : ℕ) : td n 0 d = false := rfl

theorem td_succ (n f d : ℕ) : td n (f + 1) d =
    cond (Nat.blt n (d * d)) true (cond (Nat.beq (n % d) 0) false (td n f (d + 2))) := rfl

theorem beq_false_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hc : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hc) h

theorem ne_of_beq_false {a b : ℕ} (h : Nat.beq a b = false) : a ≠ b := by
  intro e
  rw [e, Nat.beq_refl] at h
  exact Bool.noConfusion h

theorem blt_false_of_not {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hc : Nat.blt a b
  · rfl
  · exact absurd (Nat.le_of_ble_eq_true hc) h

theorem td_sound (n : ℕ) : ∀ f d, td n f d = true →
    ∀ m, d ≤ m → m * m ≤ n → m % 2 = d % 2 → ¬ m ∣ n := by
  intro f
  induction f with
  | zero => intro d h; simp [td_zero] at h
  | succ f ih =>
    intro d h m hdm hmm hpar hdvd
    rw [td_succ] at h
    by_cases h1 : n < d * d
    · have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · rw [blt_false_of_not h1] at h
      by_cases h2 : n % d = 0
      · have hb2 : Nat.beq (n % d) 0 = true := by rw [h2]; rfl
        rw [hb2] at h
        exact Bool.noConfusion h
      · rw [beq_false_of_ne h2] at h
        simp only [cond_false] at h
        rcases Nat.eq_or_lt_of_le hdm with rfl | hlt
        · exact h2 (Nat.mod_eq_zero_of_dvd hdvd)
        · exact ih (d + 2) h m (by omega) hmm (by omega) hdvd

theorem isP_sound (n : ℕ) (h : isP n = true) : n.Prime := by
  unfold isP at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with h | ⟨⟨h2, hodd⟩, htd⟩
  · have : n = 2 := Nat.eq_of_beq_eq_true h
    subst this
    exact Nat.prime_two
  · have h2' : 2 ≤ n := Nat.le_of_ble_eq_true h2
    have hodd' : n % 2 ≠ 0 := ne_of_beq_false hodd
    rw [Nat.prime_def_le_sqrt]
    refine ⟨h2', fun m hm hms hdvd => ?_⟩
    rw [Nat.le_sqrt] at hms
    rcases Nat.mod_two_eq_zero_or_one m with he | ho
    · exact hodd' (Nat.mod_eq_zero_of_dvd ((Nat.dvd_of_mod_eq_zero he).trans hdvd))
    · have hm3 : 3 ≤ m := by omega
      exact td_sound n n 3 htd m hm3 hms (by omega) hdvd

/-- `kc F = true` means that no `k` with `1 ≤ k ≤ F` has `2^((k-1) % 1518 + 1) ≡ k (mod 6298)`. -/
def kc (F : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun f ih => cond (Nat.beq (2 ^ (f % 1518 + 1) % 6298) ((f + 1) % 6298)) false ih) F

theorem kc_succ (f : ℕ) : kc (f + 1) =
    cond (Nat.beq (2 ^ (f % 1518 + 1) % 6298) ((f + 1) % 6298)) false (kc f) := rfl

theorem kc_sound : ∀ F, kc F = true → ∀ k, 1 ≤ k → k ≤ F →
    2 ^ ((k - 1) % 1518 + 1) % 6298 ≠ k % 6298 := by
  intro F
  induction F with
  | zero => intro _ k hk hkF; omega
  | succ f ih =>
    intro h k hk hkF
    rw [kc_succ] at h
    by_cases hb : 2 ^ (f % 1518 + 1) % 6298 = (f + 1) % 6298
    · have : Nat.beq (2 ^ (f % 1518 + 1) % 6298) ((f + 1) % 6298) = true := by rw [hb]; exact Nat.beq_refl _
      rw [this] at h
      exact Bool.noConfusion h
    · rw [beq_false_of_ne hb] at h
      simp only [cond_false] at h
      rcases Nat.eq_or_lt_of_le hkF with rfl | hlt
      · simpa using hb
      · exact ih h k hk (by omega)

theorem two_mul_period_gen (M n : ℕ) (h0 : 2 * 2 ^ M ≡ 2 [MOD n]) (q : ℕ) :
    2 * (2 ^ M) ^ q ≡ 2 [MOD n] := by
  induction q with
  | zero => simp [Nat.ModEq]
  | succ q ih =>
    calc 2 * (2 ^ M) ^ (q + 1) = (2 * (2 ^ M) ^ q) * 2 ^ M := by ring
      _ ≡ 2 * 2 ^ M [MOD n] := ih.mul_right _
      _ ≡ 2 [MOD n] := h0

theorem two_mul_period (q : ℕ) : 2 * (2 ^ 1518) ^ q ≡ 2 [MOD 6298] :=
  two_mul_period_gen 1518 6298 (by decide +kernel) q

theorem pow_split (M q s : ℕ) : 2 ^ (M * q + (s + 1)) = 2 ^ s * (2 * (2 ^ M) ^ q) := by
  rw [pow_add, pow_mul, pow_succ]
  ring

theorem pow_period (k : ℕ) (hk : 1 ≤ k) :
    2 ^ k % 6298 = 2 ^ ((k - 1) % 1518 + 1) % 6298 := by
  have hk' : k = 1518 * ((k - 1) / 1518) + ((k - 1) % 1518 + 1) := by
    have := Nat.div_add_mod (k - 1) 1518
    omega
  have key : 2 ^ k ≡ 2 ^ ((k - 1) % 1518 + 1) [MOD 6298] := by
    rw [hk', pow_split]
    have h3 := (two_mul_period ((k - 1) / 1518)).mul_left (2 ^ ((k - 1) % 1518))
    rw [← pow_succ] at h3
    have e : 1518 * ((k - 1) / 1518) + ((k - 1) % 1518 + 1) - 1 = (k - 1) := by omega
    rw [e]
    exact h3
  exact key

theorem no_good (k : ℕ) (hk : 1 ≤ k) (hkF : k ≤ 65000) (hkc : kc 65000 = true) :
    ¬ 6298 ∣ 2 ^ k - k := by
  intro hd
  have hle : k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
  have hmod : k ≡ 2 ^ k [MOD 6298] := (Nat.modEq_iff_dvd' hle).2 hd
  have := kc_sound 65000 hkc k hk hkF
  apply this
  rw [← pow_period k hk]
  exact hmod.symm

theorem kc_true : kc 65000 = true := by decide +kernel

theorem c0 : Nat.count (fun k => isP (0 + k) = true) 5000 = 669 := by decide +kernel
theorem c1 : Nat.count (fun k => isP (5000 + k) = true) 5000 = 560 := by decide +kernel
theorem c2 : Nat.count (fun k => isP (10000 + k) = true) 5000 = 525 := by decide +kernel
theorem c3 : Nat.count (fun k => isP (15000 + k) = true) 5000 = 508 := by decide +kernel
theorem c4 : Nat.count (fun k => isP (20000 + k) = true) 5000 = 500 := by decide +kernel
theorem c5 : Nat.count (fun k => isP (25000 + k) = true) 5000 = 483 := by decide +kernel
theorem c6 : Nat.count (fun k => isP (30000 + k) = true) 5000 = 487 := by decide +kernel
theorem c7 : Nat.count (fun k => isP (35000 + k) = true) 5000 = 471 := by decide +kernel
theorem c8 : Nat.count (fun k => isP (40000 + k) = true) 5000 = 472 := by decide +kernel
theorem c9 : Nat.count (fun k => isP (45000 + k) = true) 5000 = 458 := by decide +kernel
theorem c10 : Nat.count (fun k => isP (50000 + k) = true) 5000 = 457 := by decide +kernel
theorem c11 : Nat.count (fun k => isP (55000 + k) = true) 5000 = 467 := by decide +kernel
theorem c12 : Nat.count (fun k => isP (60000 + k) = true) 5000 = 436 := by decide +kernel

theorem count_step (a : ℕ) : Nat.count (fun k => isP k = true) (a + 5000) =
    Nat.count (fun k => isP k = true) a + Nat.count (fun k => isP (a + k) = true) 5000 :=
  Nat.count_add _ a 5000

theorem count_isP : Nat.count (fun k => isP k = true) 65000 = 6493 := by
  have e0 : Nat.count (fun k => isP k = true) 0 = 0 := Nat.count_zero _
  have s1 := count_step 0
  have s2 := count_step 5000
  have s3 := count_step 10000
  have s4 := count_step 15000
  have s5 := count_step 20000
  have s6 := count_step 25000
  have s7 := count_step 30000
  have s8 := count_step 35000
  have s9 := count_step 40000
  have s10 := count_step 45000
  have s11 := count_step 50000
  have s12 := count_step 55000
  have s13 := count_step 60000
  norm_num only at s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13
  rw [c0] at s1
  rw [c1] at s2
  rw [c2] at s3
  rw [c3] at s4
  rw [c4] at s5
  rw [c5] at s6
  rw [c6] at s7
  rw [c7] at s8
  rw [c8] at s9
  rw [c9] at s10
  rw [c10] at s11
  rw [c11] at s12
  rw [c12] at s13
  omega

theorem nth_prime_lt : Nat.nth Nat.Prime 6297 < 65000 := by
  apply Nat.nth_lt_of_lt_count
  have h := Nat.count_mono_left (p := fun k => isP k = true) (q := Nat.Prime) (n := 65000)
    (fun k _ hk => isP_sound k hk)
  rw [count_isP] at h
  omega

end OMA.Helpers

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a072872.main) := by
  intro h
  obtain ⟨k, hk, hlt⟩ := h 6298 (by norm_num)
  have hgood : OMA.S_oeis_a072872.Good 6298 k := hk.1
  have hlt' : k < 65000 := by
    have := OMA.Helpers.nth_prime_lt
    have e : (6298 - 1 : ℕ) = 6297 := rfl
    rw [e] at hlt
    omega
  exact OMA.Helpers.no_good k hgood.1 hlt'.le OMA.Helpers.kc_true hgood.2
