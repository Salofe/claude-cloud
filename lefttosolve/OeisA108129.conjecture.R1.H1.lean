import OMAReductions.R_OeisA108129_conjecture_R1

-- Step H1 of reduction OeisA108129.conjecture.R1: 509203 is a Riesel number.
-- Covering set 3, 5, 7, 13, 17, 241: each divides 2 ^ 24 - 1, and for every residue of m mod 24
-- one of them divides 509203 * 2 ^ m - 1, which exceeds 241.

namespace OMA.Helpers

theorem aux (p r q : ℕ) (h1 : 2 ^ 24 % p = 1 % p) (h2 : 509203 * 2 ^ r % p = 1 % p) :
    p ∣ 509203 * 2 ^ r * (2 ^ 24) ^ q - 1 := by
  have hN : 509203 * 2 ^ r * (2 ^ 24) ^ q ≡ 1 [MOD p] := by
    have h3 : (2 ^ 24) ^ q ≡ 1 ^ q [MOD p] := Nat.ModEq.pow q h1
    rw [one_pow] at h3
    have h4 := Nat.ModEq.mul (show 509203 * 2 ^ r ≡ 1 [MOD p] from h2) h3
    simpa using h4
  have hle : 1 ≤ 509203 * 2 ^ r * (2 ^ 24) ^ q := Nat.one_le_iff_ne_zero.mpr (by positivity)
  exact (Nat.modEq_iff_dvd' hle).mp hN.symm

theorem key (m : ℕ) (hm : m ≠ 0) : ¬ (509203 * 2 ^ m - 1).Prime := by
  intro hp
  have hm' : 509203 * 2 ^ m - 1 = 509203 * 2 ^ (m % 24) * (2 ^ 24) ^ (m / 24) - 1 := by
    rw [mul_assoc, ← pow_mul, ← pow_add, Nat.mod_add_div]
  have hbig : 241 < 509203 * 2 ^ m - 1 := by
    have : 2 ≤ 2 ^ m := Nat.le_self_pow hm 2
    omega
  have hex : ∃ p, p.Prime ∧ p ≤ 241 ∧ p ∣ 509203 * 2 ^ m - 1 := by
    rw [hm']
    have hr : m % 24 < 24 := Nat.mod_lt _ (by norm_num)
    generalize m % 24 = r at hr
    generalize m / 24 = q
    interval_cases r
    · exact ⟨3, by norm_num, by norm_num, aux 3 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨5, by norm_num, by norm_num, aux 5 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨3, by norm_num, by norm_num, aux 3 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨241, by norm_num, by norm_num, aux 241 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨3, by norm_num, by norm_num, aux 3 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨5, by norm_num, by norm_num, aux 5 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨3, by norm_num, by norm_num, aux 3 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨13, by norm_num, by norm_num, aux 13 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨3, by norm_num, by norm_num, aux 3 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨5, by norm_num, by norm_num, aux 5 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨3, by norm_num, by norm_num, aux 3 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨7, by norm_num, by norm_num, aux 7 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨3, by norm_num, by norm_num, aux 3 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨5, by norm_num, by norm_num, aux 5 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨3, by norm_num, by norm_num, aux 3 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨17, by norm_num, by norm_num, aux 17 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨3, by norm_num, by norm_num, aux 3 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨5, by norm_num, by norm_num, aux 5 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨3, by norm_num, by norm_num, aux 3 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨13, by norm_num, by norm_num, aux 13 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨3, by norm_num, by norm_num, aux 3 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨5, by norm_num, by norm_num, aux 5 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨3, by norm_num, by norm_num, aux 3 _ q (by norm_num) (by norm_num)⟩
    · exact ⟨7, by norm_num, by norm_num, aux 7 _ q (by norm_num) (by norm_num)⟩
  obtain ⟨p, hpp, hp241, hpd⟩ := hex
  rcases hp.eq_one_or_self_of_dvd p hpd with h | h
  · exact hpp.one_lt.ne' h
  · omega

end OMA.Helpers

theorem OMA.solution : OMA.R_OeisA108129_conjecture_R1.H1 := by
  unfold OMA.R_OeisA108129_conjecture_R1.H1 OeisA108129.a
  rw [if_neg (by norm_num), dif_neg]
  rintro ⟨m, hm, hp⟩
  exact OMA.Helpers.key m hm (by norm_num at hp ⊢; exact hp)
