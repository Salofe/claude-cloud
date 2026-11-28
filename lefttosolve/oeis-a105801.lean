import OMAStatements.S_oeis_a105801
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a105801

theorem orbit_succ (n : ℕ) : orbit (1, 2) (n + 1) =
    ((orbit (1, 2) n).2, next (orbit (1, 2) n).1 (orbit (1, 2) n).2) := rfl

theorem next_even {x y : ℕ} (h : (x + y) % 2 = 0) : next x y = (x + y) / 2 := by
  simp [next, h]

theorem next_odd {x y : ℕ} (h : (x + y) % 2 = 1) : next x y = 3 * (x + y) + 1 := by
  simp [next, h]

theorem next_dvd {j x y : ℕ} (hx : 3 ^ j ∣ 5 * x + 1) (hy : 3 ^ j ∣ 5 * y + 1) :
    3 ^ j ∣ 5 * next x y + 1 := by
  rcases Nat.mod_two_eq_zero_or_one (x + y) with h | h
  · rw [next_even h]
    have hs : 3 ^ j ∣ (5 * ((x + y) / 2) + 1) * 2 := by
      have e : (5 * ((x + y) / 2) + 1) * 2 = (5 * x + 1) + (5 * y + 1) := by omega
      rw [e]; exact dvd_add hx hy
    exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left j (by norm_num)) hs
  · rw [next_odd h]
    have e : 5 * (3 * (x + y) + 1) + 1 = 3 * ((5 * x + 1) + (5 * y + 1)) := by ring
    rw [e]; exact Dvd.dvd.mul_left (dvd_add hx hy) 3

theorem next_odd_dvd {j x y : ℕ} (h : (x + y) % 2 = 1) (hx : 3 ^ j ∣ 5 * x + 1)
    (hy : 3 ^ j ∣ 5 * y + 1) : 3 ^ (j + 1) ∣ 5 * next x y + 1 := by
  rw [next_odd h]
  obtain ⟨c, hc⟩ := dvd_add hx hy
  refine ⟨c, ?_⟩
  have e : 5 * (3 * (x + y) + 1) + 1 = 3 * ((5 * x + 1) + (5 * y + 1)) := by ring
  rw [e, hc, pow_succ]
  ring

/-- Both entries of the state at time `n` are congruent to `-1/5` modulo `3 ^ j`. -/
def Q (j n : ℕ) : Prop := 3 ^ j ∣ 5 * (orbit (1, 2) n).1 + 1 ∧ 3 ^ j ∣ 5 * (orbit (1, 2) n).2 + 1

theorem Q_succ {j n : ℕ} (h : Q j n) : Q j (n + 1) := by
  rw [Q, orbit_succ]
  exact ⟨h.2, next_dvd h.1 h.2⟩

theorem Q_mono {j n : ℕ} (h : Q j n) : ∀ m, n ≤ m → Q j m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact Q_succ ih

/-- The first entry is even and the two entries differ. -/
def good (n : ℕ) : Prop := (orbit (1, 2) n).1 % 2 = 0 ∧ (orbit (1, 2) n).1 ≠ (orbit (1, 2) n).2

theorem key : ∀ d n, good n →
    (orbit (1, 2) n).1 - (orbit (1, 2) n).2 + ((orbit (1, 2) n).2 - (orbit (1, 2) n).1) = d →
    ∃ n', n < n' ∧ good n' ∧ ∀ j, Q j n → Q (j + 1) n' := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro n hg hd
  obtain ⟨hx, hne⟩ := hg
  rcases Nat.mod_two_eq_zero_or_one ((orbit (1, 2) n).1 + (orbit (1, 2) n).2) with h | h
  · have h1 : orbit (1, 2) (n + 1) = ((orbit (1, 2) n).2,
        ((orbit (1, 2) n).1 + (orbit (1, 2) n).2) / 2) := by
      rw [orbit_succ, next_even h]
    have hg1 : good (n + 1) := by
      rw [good, h1]; constructor <;> dsimp only <;> omega
    obtain ⟨n', hn', hg', hQ⟩ := ih _ (by rw [← hd, h1]; dsimp only; omega) (n + 1) hg1 rfl
    exact ⟨n', by omega, hg', fun j hj => hQ j (Q_succ hj)⟩
  · have h1 : orbit (1, 2) (n + 1) = ((orbit (1, 2) n).2,
        3 * ((orbit (1, 2) n).1 + (orbit (1, 2) n).2) + 1) := by
      rw [orbit_succ, next_odd h]
    have h2' : ((orbit (1, 2) n).2 + (3 * ((orbit (1, 2) n).1 + (orbit (1, 2) n).2) + 1)) % 2
        = 1 := by omega
    have h2 : orbit (1, 2) (n + 2) = (3 * ((orbit (1, 2) n).1 + (orbit (1, 2) n).2) + 1,
        3 * ((orbit (1, 2) n).2 + (3 * ((orbit (1, 2) n).1 + (orbit (1, 2) n).2) + 1)) + 1) := by
      rw [orbit_succ, h1]; dsimp only; rw [next_odd h2']
    refine ⟨n + 2, by omega, ?_, ?_⟩
    · rw [good, h2]; constructor <;> dsimp only <;> omega
    · intro j hj
      obtain ⟨hjx, hjy⟩ := hj
      have hz : 3 ^ (j + 1) ∣ 5 * next (orbit (1, 2) n).1 (orbit (1, 2) n).2 + 1 :=
        next_odd_dvd h hjx hjy
      rw [next_odd h] at hz
      have hy' : 3 ^ (j + 1) ∣ 5 * next (orbit (1, 2) n).2
          (3 * ((orbit (1, 2) n).1 + (orbit (1, 2) n).2) + 1) + 1 :=
        next_odd_dvd h2' hjy (Nat.dvd_trans (pow_dvd_pow 3 (Nat.le_succ j)) hz)
      rw [next_odd h2'] at hy'
      rw [Q, h2]
      exact ⟨hz, hy'⟩

theorem levels : ∀ j, ∃ m, good m ∧ Q j m := by
  intro j
  induction j with
  | zero => exact ⟨1, by unfold good; decide, by simp [Q]⟩
  | succ j ih =>
    obtain ⟨m, hg, hQ⟩ := ih
    obtain ⟨n', _, hg', hQ'⟩ := key _ m hg rfl
    exact ⟨n', hg', hQ' j hQ⟩

theorem mod_eq {k a b : ℕ} (ha : 3 ^ k ∣ 5 * a + 1) (hb : 3 ^ k ∣ 5 * b + 1) :
    a % 3 ^ k = b % 3 ^ k := by
  have h1 : 5 * a + 1 ≡ 5 * b + 1 [MOD 3 ^ k] :=
    ((Nat.modEq_zero_iff_dvd).2 ha).trans ((Nat.modEq_zero_iff_dvd).2 hb).symm
  have h2 : 5 * a ≡ 5 * b [MOD 3 ^ k] := Nat.ModEq.add_right_cancel' 1 h1
  exact Nat.ModEq.cancel_left_of_coprime (Nat.Coprime.pow_left k (by norm_num)) h2

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a105801.main := by
  intro k _
  obtain ⟨m, _, hQ⟩ := levels k
  refine ⟨m + 1, (OMA.S_oeis_a105801.orbit (1, 2) m).1 % 3 ^ k, ?_⟩
  intro n hn
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  exact mod_eq (Q_mono hQ n' (by omega)).1 hQ.1
