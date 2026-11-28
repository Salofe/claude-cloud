import OMAStatements.S_oeis_a262231
import Mathlib

namespace OMA.Helpers.A262231

open OMA.S_oeis_a262231

theorem sel_iff (n : ℕ) :
    selected n ↔ (2 ≤ n ∧ ∀ k : ℕ, k < n → selected k → ¬ (k + 1) ∣ n) := by
  rw [selected]

theorem not_sel_lt_two {k : ℕ} (hk : k < 2) : ¬ selected k := by
  rw [sel_iff]
  omega

theorem sel_two : selected 2 := by
  rw [sel_iff]
  refine ⟨le_refl 2, fun k hk hs => ?_⟩
  exact absurd hs (not_sel_lt_two hk)

theorem not_sel_three_dvd {n : ℕ} (h3 : 3 ∣ n) (hn : 2 < n) : ¬ selected n := by
  rw [sel_iff]
  rintro ⟨_, h⟩
  exact h 2 hn sel_two h3

theorem sel_prime {q : ℕ} (hq : q.Prime) (h : ¬ selected (q - 1)) : selected q := by
  rw [sel_iff]
  refine ⟨hq.two_le, fun k hk hs hd => ?_⟩
  rcases (Nat.dvd_prime hq).1 hd with h1 | h1
  · exact not_sel_lt_two (by omega) hs
  · have : k = q - 1 := by omega
    exact h (this ▸ hs)

end OMA.Helpers.A262231

open OMA.Helpers.A262231 OMA.S_oeis_a262231 in
theorem OMA.solution : type_of% @OMA.S_oeis_a262231.main := by
  intro htp N
  obtain ⟨p, hNp, hp, hp2⟩ := htp (N + 4)
  have h3 : 3 ∣ p + 1 := by
    have h1 : ¬ 3 ∣ p := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h
      omega
    have h2 : ¬ 3 ∣ p + 2 := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp2).1 h
      omega
    omega
  have hb : selected (p + 2) :=
    sel_prime hp2 (by
      have : p + 2 - 1 = p + 1 := by omega
      rw [this]
      exact not_sel_three_dvd h3 (by omega))
  by_cases ha : selected p
  · exact ⟨p, p + 2, by omega, by omega, by omega, ha, hb⟩
  · have ha' : selected (p - 1) := by
      by_contra hc
      exact ha (sel_prime hp hc)
    exact ⟨p - 1, p + 2, by omega, by omega, by omega, ha', hb⟩
