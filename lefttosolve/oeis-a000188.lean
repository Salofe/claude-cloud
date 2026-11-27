import OMAStatements.S_oeis_a000188
import Mathlib

namespace OMA.Helpers

theorem a188_dvd_sq_iff {a b x : ℕ} (hb : 0 < b) (ha : Squarefree a) :
    b ^ 2 * a ∣ x * x ↔ a * b ∣ x := by
  constructor
  · intro h
    have hbx : b ∣ x := by
      have h1 : b ^ 2 ∣ x ^ 2 := by
        rw [sq x]; exact Dvd.dvd.trans (Dvd.intro a rfl) h
      exact (Nat.pow_dvd_pow_iff (by norm_num)).mp h1
    obtain ⟨y, rfl⟩ := hbx
    have h2 : a ∣ y ^ 2 := by
      have h3 : b ^ 2 * a ∣ b ^ 2 * (y ^ 2) := by
        have : b * y * (b * y) = b ^ 2 * y ^ 2 := by ring
        rw [← this]; exact h
      exact (Nat.mul_dvd_mul_iff_left (by positivity)).mp h3
    have hay : a ∣ y := (ha.dvd_pow_iff_dvd (by norm_num)).mp h2
    obtain ⟨c, rfl⟩ := hay
    exact ⟨c, by ring⟩
  · rintro ⟨c, rfl⟩
    exact ⟨a * c * c, by ring⟩

theorem a188_square_iff {a b k : ℕ} (ha0 : 0 < a) (hb : 0 < b) (ha : Squarefree a) :
    IsSquare (b ^ 2 * a * k) ↔ ∃ e, k = a * e * e := by
  constructor
  · rintro ⟨r, hr⟩
    have hbr : b ∣ r := by
      have h1 : b ^ 2 ∣ r ^ 2 := by
        rw [sq r, ← hr]; exact Dvd.intro (a * k) (by ring)
      exact (Nat.pow_dvd_pow_iff (by norm_num)).mp h1
    obtain ⟨s, rfl⟩ := hbr
    have h2 : a * k = s ^ 2 := by
      have h3 : b ^ 2 * (a * k) = b ^ 2 * s ^ 2 := by rw [← mul_assoc, hr]; ring
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h3
    have has : a ∣ s := (ha.dvd_pow_iff_dvd (by norm_num)).mp (Dvd.intro k h2)
    obtain ⟨e, rfl⟩ := has
    refine ⟨e, ?_⟩
    have h4 : a * k = a * (a * e * e) := by rw [h2]; ring
    exact Nat.eq_of_mul_eq_mul_left ha0 h4
  · rintro ⟨e, rfl⟩
    exact ⟨b * a * e, by ring⟩

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a000188.main := by
  intro n hn
  obtain ⟨a, b, ha0, hb0, hn', hsq⟩ := Nat.sq_mul_squarefree_of_pos hn
  subst hn'
  have hL : (Finset.range (b ^ 2 * a)).filter (fun x => x * x % (b ^ 2 * a) = 0) =
      (Finset.range b).image (fun i => a * b * i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    rw [← Nat.dvd_iff_mod_eq_zero, a188_dvd_sq_iff hb0 hsq]
    constructor
    · rintro ⟨hx, c, rfl⟩
      refine ⟨c, ?_, rfl⟩
      by_contra hc
      push_neg at hc
      have : a * b * b ≤ a * b * c := Nat.mul_le_mul_left _ hc
      have h2 : b ^ 2 * a = a * b * b := by ring
      omega
    · rintro ⟨c, hc, rfl⟩
      refine ⟨?_, c, rfl⟩
      have h1 : a * b * c < a * b * b := Nat.mul_lt_mul_of_pos_left hc (by positivity)
      have h2 : b ^ 2 * a = a * b * b := by ring
      omega
  have hR : (Finset.Icc 1 (b ^ 2 * a)).filter (fun k => IsSquare (b ^ 2 * a * k)) =
      (Finset.Icc 1 b).image (fun e => a * e * e) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    rw [a188_square_iff ha0 hb0 hsq]
    constructor
    · rintro ⟨⟨hk1, hk2⟩, e, rfl⟩
      refine ⟨e, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos e with he | he
        · subst he; simp at hk1
        · exact he
      · by_contra he
        push_neg at he
        have h1 : b * b < e * e := Nat.mul_self_lt_mul_self he
        have h3 : a * (b * b) < a * (e * e) := Nat.mul_lt_mul_of_pos_left h1 ha0
        have h2 : b ^ 2 * a = a * (b * b) := by ring
        have h4 : a * e * e = a * (e * e) := by ring
        omega
    · rintro ⟨e, ⟨he1, he2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, e, rfl⟩
      · have : 1 ≤ e * e := Nat.one_le_iff_ne_zero.mpr (by positivity)
        have h4 : a * e * e = a * (e * e) := by ring
        have : 1 * 1 ≤ a * (e * e) := Nat.mul_le_mul ha0 this
        omega
      · have h1 : e * e ≤ b * b := Nat.mul_self_le_mul_self he2
        have h3 : a * (e * e) ≤ a * (b * b) := Nat.mul_le_mul_left _ h1
        have h2 : b ^ 2 * a = a * (b * b) := by ring
        have h4 : a * e * e = a * (e * e) := by ring
        omega
  rw [hL, hR, Finset.card_image_of_injective, Finset.card_image_of_injective]
  · simp
  · intro e e' h
    simp only at h
    have h1 : a * (e * e) = a * (e' * e') := by rw [← mul_assoc, ← mul_assoc]; exact h
    exact Nat.mul_self_inj.mp (Nat.eq_of_mul_eq_mul_left ha0 h1)
  · intro c c' h
    simp only at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
