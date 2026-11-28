import OMAStatements.S_oeis_a000126
import Mathlib

namespace OMA.Helpers

open OMA.S_oeis_a000126

theorem a126_mem_succ (n x : ℕ) :
    x ∈ laymanSet (n + 2) ↔ ∃ y ∈ laymanSet (n + 1), y + 1 = x ∨ 2 * y + 1 = x := by
  simp only [laymanSet, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨y, hy, h⟩ | ⟨y, hy, h⟩)
    · exact ⟨y, hy, Or.inl h⟩
    · exact ⟨y, hy, Or.inr h⟩
  · rintro ⟨y, hy, h | h⟩
    · exact Or.inl ⟨y, hy, h⟩
    · exact Or.inr ⟨y, hy, h⟩

theorem a126_add_one {n y : ℕ} (h : y ∈ laymanSet n) : y + 1 ∈ laymanSet (n + 1) := by
  rcases n with _ | n
  · simp [laymanSet] at h
  · exact (a126_mem_succ n _).2 ⟨y, h, Or.inl rfl⟩

theorem a126_two_mul {n y : ℕ} (h : y ∈ laymanSet n) : 2 * y + 1 ∈ laymanSet (n + 1) := by
  rcases n with _ | n
  · simp [laymanSet] at h
  · exact (a126_mem_succ n _).2 ⟨y, h, Or.inr rfl⟩

theorem a126_ge : ∀ n x : ℕ, x ∈ laymanSet n → n ≤ x
  | 0, _, _ => Nat.zero_le _
  | 1, x, h => by simp [laymanSet] at h; omega
  | n + 2, x, h => by
    obtain ⟨y, hy, h1 | h1⟩ := (a126_mem_succ n x).1 h
    · have := a126_ge (n + 1) y hy; omega
    · have := a126_ge (n + 1) y hy; omega

theorem a126_self : ∀ n : ℕ, 1 ≤ n → n ∈ laymanSet n
  | 0, h => absurd h (by norm_num)
  | 1, _ => by simp [laymanSet]
  | n + 2, _ => a126_add_one (a126_self (n + 1) (by omega))

theorem a126_interval : ∀ n : ℕ, 1 ≤ n → ∀ x, n ≤ x → x < 2 * n → x ∈ laymanSet n
  | 0, h => absurd h (by norm_num)
  | 1, _ => by
    intro x hx1 hx2
    have : x = 1 := by omega
    subst this; simp [laymanSet]
  | n + 2, _ => by
    intro x hx1 hx2
    by_cases hx : x ≤ 2 * n + 2
    · have h1 : x - 1 ∈ laymanSet (n + 1) :=
        a126_interval (n + 1) (by omega) (x - 1) (by omega) (by omega)
      have h2 := a126_add_one h1
      have h3 : x - 1 + 1 = x := by omega
      rw [h3] at h2; exact h2
    · have h1 := a126_two_mul (a126_self (n + 1) (by omega))
      have h3 : 2 * (n + 1) + 1 = x := by omega
      rw [h3] at h1; exact h1

theorem a126_persist : ∀ n x : ℕ, x ∈ laymanSet n → x ≠ n → x ∈ laymanSet (n + 1)
  | 0, _, h, _ => by simp [laymanSet] at h
  | 1, x, h, hx => by simp [laymanSet] at h; omega
  | n + 2, x, h, hx => by
    obtain ⟨y, hy, h1 | h1⟩ := (a126_mem_succ n x).1 h
    · have hyn : y ≠ n + 1 := by omega
      have := a126_add_one (a126_persist (n + 1) y hy hyn)
      rw [h1] at this; exact this
    · by_cases hyn : y = n + 1
      · have h2 : 2 * n + 2 ∈ laymanSet (n + 2) :=
          a126_interval (n + 2) (by omega) _ (by omega) (by omega)
        have := a126_add_one h2
        have h3 : 2 * n + 2 + 1 = x := by omega
        rw [h3] at this; exact this
      · have := a126_two_mul (a126_persist (n + 1) y hy hyn)
        rw [h1] at this; exact this

theorem a126_half : ∀ n x : ℕ, n < x → 2 * x + 1 ∈ laymanSet (n + 1) → x ∈ laymanSet n
  | 0, x, hx, h => by simp [laymanSet] at h; omega
  | 1, x, hx, h => by
    obtain ⟨y, hy, h1 | h1⟩ := (a126_mem_succ 0 _).1 h <;> simp [laymanSet] at hy <;> omega
  | n + 2, x, hx, h => by
    obtain ⟨y, hy, h1 | h1⟩ := (a126_mem_succ (n + 1) _).1 h
    · have hy2 : y = 2 * x := by omega
      subst hy2
      obtain ⟨z, hz, h2 | h2⟩ := (a126_mem_succ n _).1 hy
      · have hz2 : z = 2 * (x - 1) + 1 := by omega
        rw [hz2] at hz
        have h3 := a126_half n (x - 1) (by omega) hz
        have h4 := a126_add_one h3
        have h5 : x - 1 + 1 = x := by omega
        rw [h5] at h4
        exact a126_persist (n + 1) x h4 (by omega)
      · omega
    · have : y = x := by omega
      subst this; exact hy

theorem a126_inter (n : ℕ) :
    (laymanSet (n + 2)).image (fun x => x + 1) ∩ (laymanSet (n + 2)).image (fun x => 2 * x + 1) =
      ((laymanSet n).erase n).image (fun x => 2 * x + 3) := by
  ext y
  simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, ⟨v, hv, hv2⟩⟩
    have hvge := a126_ge _ _ hv
    have hu2 : u = 2 * v := by omega
    subst hu2
    obtain ⟨w, hw, h1 | h1⟩ := (a126_mem_succ n _).1 hu
    · have hw2 : w = 2 * (v - 1) + 1 := by omega
      rw [hw2] at hw
      have hx := a126_half n (v - 1) (by omega) hw
      exact ⟨v - 1, ⟨by omega, hx⟩, by omega⟩
    · omega
  · rintro ⟨x, ⟨hxn, hx⟩, rfl⟩
    refine ⟨⟨2 * x + 2, ?_, by ring⟩, ⟨x + 1, ?_, by ring⟩⟩
    · have := a126_add_one (a126_two_mul hx)
      have h3 : 2 * x + 1 + 1 = 2 * x + 2 := by ring
      rw [h3] at this; exact this
    · exact a126_add_one (a126_persist n x hx hxn)

theorem a126_rec (n : ℕ) (hn : 1 ≤ n) :
    (laymanSet (n + 3)).card + (laymanSet n).card = 2 * (laymanSet (n + 2)).card + 1 := by
  have hU : laymanSet (n + 3) = (laymanSet (n + 2)).image (fun x => x + 1) ∪
      (laymanSet (n + 2)).image (fun x => 2 * x + 1) := rfl
  have key := Finset.card_union_add_card_inter ((laymanSet (n + 2)).image (fun x => x + 1))
    ((laymanSet (n + 2)).image (fun x => 2 * x + 1))
  rw [← hU, a126_inter n, Finset.card_image_of_injective _ (fun a b h => by simpa using h),
    Finset.card_image_of_injective _ (fun a b h => by simpa using h),
    Finset.card_image_of_injective _ (fun a b h => by simpa using h),
    Finset.card_erase_of_mem (a126_self n hn)] at key
  have hpos : 1 ≤ (laymanSet n).card :=
    Finset.card_pos.mpr ⟨n, a126_self n hn⟩
  omega

theorem a126_main : ∀ n : ℕ, 1 ≤ n → (laymanSet n).card + (n + 1) = Nat.fib (n + 3)
  | 0, h => absurd h (by norm_num)
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | n + 4, _ => by
    have h1 := a126_main (n + 1) (by omega)
    have h3 := a126_main (n + 3) (by omega)
    have hr := a126_rec (n + 1) (by omega)
    have f1 : Nat.fib (n + 7) = Nat.fib (n + 5) + Nat.fib (n + 6) := Nat.fib_add_two
    have f2 : Nat.fib (n + 6) = Nat.fib (n + 4) + Nat.fib (n + 5) := Nat.fib_add_two
    have f3 : Nat.fib (n + 5) = Nat.fib (n + 3) + Nat.fib (n + 4) := Nat.fib_add_two
    simp only [show n + 1 + 3 = n + 4 from rfl, show n + 1 + 2 = n + 3 from rfl] at hr
    simp only [show n + 1 + 3 = n + 4 from rfl] at h1
    simp only [show n + 3 + 3 = n + 6 from rfl] at h3
    show (laymanSet (n + 4)).card + (n + 4 + 1) = Nat.fib (n + 7)
    omega

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a000126.main := by
  intro n hn
  have := OMA.Helpers.a126_main n hn
  unfold OMA.S_oeis_a000126.a
  omega
