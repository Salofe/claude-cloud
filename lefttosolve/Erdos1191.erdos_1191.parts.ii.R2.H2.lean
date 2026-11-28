import OMAReductions.R_Erdos1191_erdos_1191_parts_ii_R2
import Mathlib

/-!
# Step H2 of the reduction Erdos1191.erdos_1191.parts.ii.R2

An additive label code with polynomial loss. Write a in binary and cut the bits into blocks
at the positions 0, 0, 2^4, 2^8, 2^16, ... (block t starts at bit 2^(2^t) for t at least 2).
The code enc a places block t at a fixed position and leaves above it a gap of 32 * 2^t bits.
The gap above block t - 1 receives, besides the carry bit of pair sums, a label code of the
form (j + 1) + H (j + 1)^2 for every number whose top bit j lies in block t; here H depends only
on t and exceeds twice every j + 1 of that block, so a sum of two such codes determines the pair
of labels. Since every digit of a pair sum stays below its width, enc a + enc b determines the
blockwise sums of a and b (hence a + b) and the gap contents (hence the unordered pair of
labels). The gaps below bit j have total width 32 (2^t - 1) with 2^(2^t) at most j, so
enc a is at most 2^j (j + 2)^33.
-/

namespace OMA.Helpers

open Finset

/-- Gap positions in the binary expansion: no gap inside the first block, then 2^(2^t). -/
def gq (t : ℕ) : ℕ := if t < 2 then 0 else 2 ^ 2 ^ t

theorem gq_of_two_le {t : ℕ} (ht : 2 ≤ t) : gq t = 2 ^ 2 ^ t := by
  unfold gq; rw [if_neg (by omega)]

theorem gq_le_succ (t : ℕ) : gq t ≤ gq (t + 1) := by
  unfold gq
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact Nat.zero_le _
  · omega
  · exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem gq_mono : Monotone gq := monotone_nat_of_le_succ gq_le_succ

theorem lt_gq {t : ℕ} (ht : 2 ≤ t) : t < gq t := by
  rw [gq_of_two_le ht]
  exact (Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right (by norm_num) Nat.lt_two_pow_self)

theorem exists_blk (j : ℕ) : ∃ T, j < gq (T + 1) :=
  ⟨j + 1, (Nat.lt_succ_self j).trans ((Nat.lt_succ_self _).trans (lt_gq (by omega)))⟩

/-- The index of the block containing bit j. -/
def lvl (j : ℕ) : ℕ := Nat.find (exists_blk j)

theorem lvl_spec (j : ℕ) : j < gq (lvl j + 1) := Nat.find_spec (exists_blk j)

theorem lvl_pos (j : ℕ) : 1 ≤ lvl j := by
  by_contra h
  have h0 : lvl j = 0 := by omega
  have := lvl_spec j
  rw [h0] at this
  simp [gq] at this

theorem gq_lvl_le (j : ℕ) : gq (lvl j) ≤ j := by
  have h := Nat.find_min (exists_blk j) (m := lvl j - 1)
    (show lvl j - 1 < lvl j by have := lvl_pos j; omega)
  rw [Nat.sub_add_cancel (lvl_pos j)] at h
  omega

theorem lvl_le (j : ℕ) : lvl j ≤ j + 1 :=
  Nat.find_min' (exists_blk j) (m := j + 1)
    ((Nat.lt_succ_self j).trans ((Nat.lt_succ_self _).trans (lt_gq (by omega))))

/-- Base of the Sidon label code of block lvl j. -/
def hb (j : ℕ) : ℕ := 2 ^ 2 ^ (lvl j + 2)

/-- Label code: pair sums inside one block determine the pair. -/
def code (j : ℕ) : ℕ := (j + 1) + hb j * (j + 1) ^ 2

theorem succ_le_top (j : ℕ) : j + 1 ≤ 2 ^ 2 ^ (lvl j + 1) := by
  have h := lvl_spec j
  rw [gq_of_two_le (by have := lvl_pos j; omega)] at h
  omega

theorem two_mul_succ_lt_hb (j : ℕ) : 2 * (j + 1) < hb j := by
  have h := succ_le_top j
  unfold hb
  have e : 2 ^ (lvl j + 2) = 2 ^ (lvl j + 1) + 2 ^ (lvl j + 1) := by rw [pow_succ]; ring
  have h1 : 1 < 2 ^ (lvl j + 1) := Nat.one_lt_two_pow (by omega)
  calc 2 * (j + 1) ≤ 2 * 2 ^ 2 ^ (lvl j + 1) := by omega
    _ < 2 ^ 2 ^ (lvl j + 1) * 2 ^ 2 ^ (lvl j + 1) := by
        apply Nat.mul_lt_mul_of_pos_right _ (by positivity)
        calc 2 = 2 ^ 1 := by norm_num
          _ < 2 ^ 2 ^ (lvl j + 1) := Nat.pow_lt_pow_right (by norm_num) h1
    _ = 2 ^ 2 ^ (lvl j + 2) := by rw [← pow_add, e]

theorem sq_succ_le_hb (j : ℕ) : (j + 1) ^ 2 ≤ hb j := by
  have h := succ_le_top j
  unfold hb
  calc (j + 1) ^ 2 ≤ (2 ^ 2 ^ (lvl j + 1)) ^ 2 := Nat.pow_le_pow_left h 2
    _ = 2 ^ 2 ^ (lvl j + 2) := by rw [← pow_mul, pow_succ 2 (lvl j + 1)]

theorem code_pos (j : ℕ) : 0 < code j := by unfold code; omega

theorem code_lt (j : ℕ) : code j < 2 ^ (2 ^ (lvl j + 3) + 1) := by
  have h1 := two_mul_succ_lt_hb j
  have h2 := sq_succ_le_hb j
  have e : 2 ^ (2 ^ (lvl j + 3) + 1) = 2 * (hb j * hb j) := by
    unfold hb
    rw [← pow_add, ← two_mul, pow_succ 2 (lvl j + 2), mul_comm (2 ^ (lvl j + 2)) 2,
      pow_succ, mul_comm]
  rw [e]
  unfold code
  have h3 : hb j * (j + 1) ^ 2 ≤ hb j * hb j := Nat.mul_le_mul_left _ h2
  have h4 : 1 ≤ hb j := by omega
  nlinarith

theorem code_inj (j k : ℕ) (hl : lvl j = lvl k) (h : code j = code k) : j = k := by
  have hh : hb j = hb k := by unfold hb; rw [hl]
  unfold code at h
  rw [hh] at h
  have hpos : 0 < hb k := by unfold hb; positivity
  rcases lt_trichotomy j k with hjk | hjk | hjk
  · have : (j + 1) ^ 2 < (k + 1) ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
    have := Nat.mul_lt_mul_of_pos_left this hpos
    omega
  · exact hjk
  · have : (k + 1) ^ 2 < (j + 1) ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
    have := Nat.mul_lt_mul_of_pos_left this hpos
    omega

theorem decode_pair (B r s r' s' : ℕ) (hr : r < B) (hr' : r' < B)
    (h : r + B * s = r' + B * s') : r = r' ∧ s = s' := by
  have h1 : r = r' := by
    have := congrArg (· % B) h
    simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] using this
  subst h1
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_left_cancel h)⟩

theorem sidon_sq (X Y U V H : ℕ) (hXY : X + Y < H) (hUV : U + V < H)
    (h : X + Y + H * (X ^ 2 + Y ^ 2) = U + V + H * (U ^ 2 + V ^ 2)) :
    (X = U ∧ Y = V) ∨ (X = V ∧ Y = U) := by
  obtain ⟨hs, hq⟩ := decode_pair H _ _ _ _ hXY hUV h
  have hs' : (X : ℤ) + Y = U + V := by exact_mod_cast hs
  have hq' : (X : ℤ) ^ 2 + Y ^ 2 = U ^ 2 + V ^ 2 := by exact_mod_cast hq
  have hY : (Y : ℤ) = U + V - X := by linarith
  rw [hY] at hq'
  have hprod : 2 * (((X : ℤ) - U) * ((X : ℤ) - V)) = 0 := by linear_combination hq'
  have hprod' : ((X : ℤ) - U) * ((X : ℤ) - V) = 0 := by linarith
  rcases mul_eq_zero.1 hprod' with h1 | h1
  · left; constructor <;> omega
  · right; constructor <;> omega

theorem code_sidon (i₁ i₂ i₃ i₄ : ℕ) (h2 : lvl i₁ = lvl i₂) (h3 : lvl i₁ = lvl i₃)
    (h4 : lvl i₁ = lvl i₄) (h : code i₁ + code i₂ = code i₃ + code i₄) :
    (i₁ = i₃ ∧ i₂ = i₄) ∨ (i₁ = i₄ ∧ i₂ = i₃) := by
  have e2 : hb i₂ = hb i₁ := by unfold hb; rw [h2]
  have e3 : hb i₃ = hb i₁ := by unfold hb; rw [h3]
  have e4 : hb i₄ = hb i₁ := by unfold hb; rw [h4]
  have b1 := two_mul_succ_lt_hb i₁
  have b2 := two_mul_succ_lt_hb i₂
  have b3 := two_mul_succ_lt_hb i₃
  have b4 := two_mul_succ_lt_hb i₄
  rw [e2] at b2
  rw [e3] at b3
  rw [e4] at b4
  unfold code at h
  rw [e2, e3, e4] at h
  have key := sidon_sq (i₁ + 1) (i₂ + 1) (i₃ + 1) (i₄ + 1) (hb i₁) (by omega) (by omega)
    (by linarith [h])
  omega

/-- Label code written in gap t by a number with label j. -/
def kap (t j : ℕ) : ℕ := if t + 1 = lvl j then code j else 0

theorem kap_lt (t j : ℕ) : kap t j < 2 ^ (2 ^ (t + 4) + 1) := by
  unfold kap
  split_ifs with h
  · have := code_lt j
    rwa [← h] at this
  · positivity

theorem label_decode (i₁ i₂ i₃ i₄ : ℕ)
    (h : ∀ t, kap t i₁ + kap t i₂ = kap t i₃ + kap t i₄) :
    (i₁ = i₃ ∧ i₂ = i₄) ∨ (i₁ = i₄ ∧ i₂ = i₃) := by
  have hk : ∀ t i, kap t i = if t = lvl i - 1 then code i else 0 := by
    intro t i
    have := lvl_pos i
    unfold kap
    by_cases ht : t = lvl i - 1
    · rw [if_pos (by omega), if_pos ht]
    · rw [if_neg (by omega), if_neg ht]
  simp only [hk] at h
  have c₁ := code_pos i₁
  have c₂ := code_pos i₂
  have c₃ := code_pos i₃
  have c₄ := code_pos i₄
  have p₁ := lvl_pos i₁
  have p₂ := lvl_pos i₂
  have p₃ := lvl_pos i₃
  have p₄ := lvl_pos i₄
  by_cases h12 : lvl i₁ = lvl i₂
  · have h3 : lvl i₃ = lvl i₁ := by
      by_contra hne
      have := h (lvl i₃ - 1)
      split_ifs at this <;> omega
    have h4 : lvl i₄ = lvl i₁ := by
      by_contra hne
      have := h (lvl i₄ - 1)
      split_ifs at this <;> omega
    have := h (lvl i₁ - 1)
    split_ifs at this <;> first
      | omega
      | exact code_sidon i₁ i₂ i₃ i₄ h12 h3.symm h4.symm this
  · have e1 := h (lvl i₁ - 1)
    have e2 := h (lvl i₂ - 1)
    split_ifs at e1 e2 <;> first
      | omega
      | (left; exact ⟨code_inj _ _ (by omega) (by omega), code_inj _ _ (by omega) (by omega)⟩)
      | (right; exact ⟨code_inj _ _ (by omega) (by omega), code_inj _ _ (by omega) (by omega)⟩)

/-- Position of block t in the code. -/
def gP (t : ℕ) : ℕ := gq t + 32 * (2 ^ t - 1)

/-- Length of block t. -/
def glen (t : ℕ) : ℕ := gq (t + 1) - gq t

theorem gP_succ (t : ℕ) : gP (t + 1) = gP t + glen t + 32 * 2 ^ t := by
  unfold gP glen
  have h1 := gq_le_succ t
  have h2 : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ]; ring
  have h3 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  rw [h2]
  generalize 2 ^ t = m at *
  omega

theorem gP_le_succ (t : ℕ) : gP t ≤ gP (t + 1) := by rw [gP_succ]; omega

/-- Block t of the binary expansion of a. -/
def blk (t a : ℕ) : ℕ := a / 2 ^ gq t % 2 ^ glen t

/-- Digit t of the code: block t, then the gap above it holding the carry bit and a label code. -/
def dig (t a : ℕ) : ℕ := blk t a + 2 ^ (glen t + 1) * kap t (Nat.log 2 a)

/-- The additive label code. -/
def enc (a : ℕ) : ℕ := ∑ t ∈ range (a + 2), 2 ^ gP t * dig t a

theorem recon (N a : ℕ) : ∑ t ∈ range N, 2 ^ gq t * blk t a = a % 2 ^ gq N := by
  induction N with
  | zero => simp [gq, Nat.mod_one]
  | succ N ih =>
    rw [sum_range_succ, ih]
    have e : 2 ^ gq (N + 1) = 2 ^ gq N * 2 ^ glen N := by
      rw [← pow_add]; unfold glen; congr 1; have := gq_le_succ N; omega
    rw [e, Nat.mod_mul]
    rfl

theorem mr_lt (P : ℕ → ℕ) (hP : ∀ t, P t ≤ P (t + 1)) (d : ℕ → ℕ) (N : ℕ)
    (hd : ∀ t < N, d t < 2 ^ (P (t + 1) - P t)) :
    ∑ t ∈ range N, 2 ^ P t * d t < 2 ^ P N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have h1 := ih (fun t ht => hd t (by omega))
    have h2 := hd N (by omega)
    have e : 2 ^ P (N + 1) = 2 ^ P N * 2 ^ (P (N + 1) - P N) := by
      rw [← pow_add]; congr 1; have := hP N; omega
    rw [e]
    have h3 : 2 ^ P N * (d N + 1) ≤ 2 ^ P N * 2 ^ (P (N + 1) - P N) :=
      Nat.mul_le_mul_left _ h2
    nlinarith

theorem mr_inj (P : ℕ → ℕ) (hP : ∀ t, P t ≤ P (t + 1)) (d d' : ℕ → ℕ) (N : ℕ)
    (hd : ∀ t < N, d t < 2 ^ (P (t + 1) - P t)) (hd' : ∀ t < N, d' t < 2 ^ (P (t + 1) - P t))
    (h : ∑ t ∈ range N, 2 ^ P t * d t = ∑ t ∈ range N, 2 ^ P t * d' t) :
    ∀ t < N, d t = d' t := by
  induction N with
  | zero => intro t ht; omega
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ] at h
    have l1 := mr_lt P hP d N (fun t ht => hd t (by omega))
    have l2 := mr_lt P hP d' N (fun t ht => hd' t (by omega))
    obtain ⟨hs, hN⟩ := decode_pair _ _ _ _ _ l1 l2 h
    intro t ht
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
    · exact ih (fun t ht => hd t (by omega)) (fun t ht => hd' t (by omega)) hs t ht
    · rw [ht]; exact hN

theorem blk_lt (t a : ℕ) : blk t a < 2 ^ glen t := Nat.mod_lt _ (by positivity)

theorem blk_pair_lt (t a b : ℕ) : blk t a + blk t b < 2 ^ (glen t + 1) := by
  have := blk_lt t a
  have := blk_lt t b
  rw [pow_succ]
  omega

theorem dig_pair_lt (t a b : ℕ) : dig t a + dig t b < 2 ^ (gP (t + 1) - gP t) := by
  rw [gP_succ, show gP t + glen t + 32 * 2 ^ t - gP t = glen t + 32 * 2 ^ t by omega]
  have hb := blk_pair_lt t a b
  have k1 := kap_lt t (Nat.log 2 a)
  have k2 := kap_lt t (Nat.log 2 b)
  have hexp : glen t + 1 + (2 ^ (t + 4) + 1) + 1 ≤ glen t + 32 * 2 ^ t := by
    have e : 2 ^ (t + 4) = 16 * 2 ^ t := by rw [pow_add]; ring
    have : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    omega
  calc dig t a + dig t b
        = (blk t a + blk t b) + 2 ^ (glen t + 1) * (kap t (Nat.log 2 a) + kap t (Nat.log 2 b)) := by
          unfold dig; ring
    _ < 2 ^ (glen t + 1) + 2 ^ (glen t + 1) * (kap t (Nat.log 2 a) + kap t (Nat.log 2 b)) := by
          omega
    _ = 2 ^ (glen t + 1) * (1 + kap t (Nat.log 2 a) + kap t (Nat.log 2 b)) := by ring
    _ ≤ 2 ^ (glen t + 1) * (2 * 2 ^ (2 ^ (t + 4) + 1)) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 ^ (glen t + 1 + (2 ^ (t + 4) + 1) + 1) := by ring
    _ ≤ 2 ^ (glen t + 32 * 2 ^ t) := Nat.pow_le_pow_right (by norm_num) hexp

theorem dig_lt (t a : ℕ) : dig t a < 2 ^ (gP (t + 1) - gP t) :=
  lt_of_le_of_lt (Nat.le_add_right _ _) (dig_pair_lt t a a)

theorem lt_two_pow_gq {z N : ℕ} (h : z + 2 ≤ N) : z < 2 ^ gq N :=
  (show z < N by omega).trans ((lt_gq (by omega)).trans Nat.lt_two_pow_self)

theorem sum_range_eq_of_zero (f : ℕ → ℕ) {M N : ℕ} (hMN : M ≤ N)
    (hz : ∀ t, M ≤ t → f t = 0) : ∑ t ∈ range N, f t = ∑ t ∈ range M, f t := by
  symm
  apply sum_subset (range_subset_range.2 hMN)
  intro t _ ht
  exact hz t (by simpa using ht)

theorem enc_eq (a N : ℕ) (h : a + 2 ≤ N) : enc a = ∑ t ∈ range N, 2 ^ gP t * dig t a := by
  unfold enc
  symm
  apply sum_range_eq_of_zero _ h
  intro t ht
  have h1 : a < 2 ^ gq t := lt_two_pow_gq ht
  have h2 := lvl_le (Nat.log 2 a)
  have h3 := Nat.log_le_self 2 a
  simp only [dig, blk, kap, Nat.div_eq_of_lt h1, Nat.zero_mod, zero_add]
  rw [if_neg (by omega), mul_zero, mul_zero]

theorem enc_sum (a b u v : ℕ) (h : enc a + enc b = enc u + enc v) :
    a + b = u + v ∧ ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨
      (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u)) := by
  set N := a + b + u + v + 2 with hN
  rw [enc_eq a N (by omega), enc_eq b N (by omega), enc_eq u N (by omega),
    enc_eq v N (by omega), ← sum_add_distrib, ← sum_add_distrib] at h
  simp only [← mul_add] at h
  have hd := mr_inj gP gP_le_succ (fun t => dig t a + dig t b) (fun t => dig t u + dig t v) N
    (fun t _ => dig_pair_lt t a b) (fun t _ => dig_pair_lt t u v) h
  have hsplit : ∀ t < N, blk t a + blk t b = blk t u + blk t v ∧
      kap t (Nat.log 2 a) + kap t (Nat.log 2 b) = kap t (Nat.log 2 u) + kap t (Nat.log 2 v) := by
    intro t ht
    have e := hd t ht
    simp only [dig] at e
    apply decode_pair (2 ^ (glen t + 1)) _ _ _ _ (blk_pair_lt t a b) (blk_pair_lt t u v)
    calc blk t a + blk t b + 2 ^ (glen t + 1) * (kap t (Nat.log 2 a) + kap t (Nat.log 2 b))
        = blk t a + 2 ^ (glen t + 1) * kap t (Nat.log 2 a) +
          (blk t b + 2 ^ (glen t + 1) * kap t (Nat.log 2 b)) := by ring
      _ = blk t u + 2 ^ (glen t + 1) * kap t (Nat.log 2 u) +
          (blk t v + 2 ^ (glen t + 1) * kap t (Nat.log 2 v)) := e
      _ = _ := by ring
  constructor
  · have ra := recon N a
    have rb := recon N b
    have ru := recon N u
    have rv := recon N v
    rw [Nat.mod_eq_of_lt (lt_two_pow_gq (by omega))] at ra rb ru rv
    rw [← ra, ← rb, ← ru, ← rv, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro t ht
    rw [← mul_add, ← mul_add, (hsplit t (mem_range.1 ht)).1]
  · apply label_decode
    intro t
    by_cases ht : t < N
    · exact (hsplit t ht).2
    · have z : ∀ z, z ≤ a + b + u + v → kap t (Nat.log 2 z) = 0 := by
        intro z hz
        unfold kap
        have := lvl_le (Nat.log 2 z)
        have := Nat.log_le_self 2 z
        rw [if_neg (by omega)]
      rw [z a (by omega), z b (by omega), z u (by omega), z v (by omega)]

theorem enc_size (j a : ℕ) (ha : a ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1))) :
    1 ≤ enc a ∧ enc a ≤ 2 ^ j * (j + 2) ^ 33 := by
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 ha
  have hlog : Nat.log 2 a = j := Nat.log_eq_of_pow_le_of_lt_pow h1 h2
  have hT1 := lvl_pos j
  have hTlo := gq_lvl_le j
  have hThi := lvl_spec j
  have hja : j ≤ a := (Nat.lt_two_pow_self).le.trans h1
  have hTa : lvl j + 1 ≤ a + 2 := by have := lvl_le j; omega
  have hzero : ∀ t, lvl j + 1 ≤ t → 2 ^ gP t * dig t a = 0 := by
    intro t ht
    have hlt : a < 2 ^ gq t := lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num)
      ((show j + 1 ≤ gq (lvl j + 1) by omega).trans (gq_mono ht)))
    simp only [dig, blk, kap, Nat.div_eq_of_lt hlt, Nat.zero_mod, zero_add, hlog]
    rw [if_neg (by omega), mul_zero, mul_zero]
  have hE : enc a = ∑ t ∈ range (lvl j), 2 ^ gP t * dig t a + 2 ^ gP (lvl j) * dig (lvl j) a := by
    unfold enc
    rw [sum_range_eq_of_zero _ hTa hzero, sum_range_succ]
  have hlow := mr_lt gP gP_le_succ (fun t => dig t a) (lvl j) (fun t _ => dig_lt t a)
  have hdT : dig (lvl j) a = a / 2 ^ gq (lvl j) := by
    simp only [dig, kap, hlog]
    rw [if_neg (by omega), mul_zero, add_zero]
    unfold blk
    apply Nat.mod_eq_of_lt
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    calc a < 2 ^ (j + 1) := h2
      _ ≤ 2 ^ (glen (lvl j) + gq (lvl j)) := Nat.pow_le_pow_right (by norm_num)
          (by unfold glen; have := gq_le_succ (lvl j); omega)
  have hq1 : 1 ≤ a / 2 ^ gq (lvl j) := by
    rw [Nat.one_le_div_iff (by positivity)]
    exact (Nat.pow_le_pow_right (by norm_num) hTlo).trans h1
  have hq2 : a / 2 ^ gq (lvl j) < 2 ^ (j + 1 - gq (lvl j)) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel (by omega)]
    exact h2
  rw [hE, hdT]
  constructor
  · have : 1 ≤ 2 ^ gP (lvl j) * (a / 2 ^ gq (lvl j)) :=
      Nat.mul_le_mul (Nat.one_le_two_pow) hq1
    omega
  · have hb : ∑ t ∈ range (lvl j), 2 ^ gP t * dig t a + 2 ^ gP (lvl j) * (a / 2 ^ gq (lvl j)) <
        2 ^ (gP (lvl j) + (j + 1 - gq (lvl j))) := by
      rw [pow_add]
      calc ∑ t ∈ range (lvl j), 2 ^ gP t * dig t a + 2 ^ gP (lvl j) * (a / 2 ^ gq (lvl j))
          < 2 ^ gP (lvl j) + 2 ^ gP (lvl j) * (a / 2 ^ gq (lvl j)) := by omega
        _ = 2 ^ gP (lvl j) * (a / 2 ^ gq (lvl j) + 1) := by ring
        _ ≤ 2 ^ gP (lvl j) * 2 ^ (j + 1 - gq (lvl j)) := Nat.mul_le_mul_left _ hq2
    have hexp : gP (lvl j) + (j + 1 - gq (lvl j)) = j + (1 + 32 * (2 ^ lvl j - 1)) := by
      unfold gP; omega
    have hpow : 2 ^ (1 + 32 * (2 ^ lvl j - 1)) ≤ (j + 2) ^ 33 := by
      have hp1 : 1 ≤ 2 ^ lvl j := Nat.one_le_two_pow
      rcases Nat.lt_or_ge (lvl j) 2 with hl | hl
      · have hl1 : lvl j = 1 := by omega
        rw [hl1]
        calc 2 ^ (1 + 32 * (2 ^ 1 - 1)) = 2 ^ 33 := by norm_num
          _ ≤ (j + 2) ^ 33 := Nat.pow_le_pow_left (by omega) 33
      · rw [gq_of_two_le hl] at hTlo
        calc 2 ^ (1 + 32 * (2 ^ lvl j - 1)) ≤ 2 ^ (2 ^ lvl j * 33) :=
              Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = (2 ^ 2 ^ lvl j) ^ 33 := pow_mul _ _ _
          _ ≤ (j + 2) ^ 33 := Nat.pow_le_pow_left (by omega) 33
    calc _ ≤ 2 ^ (j + (1 + 32 * (2 ^ lvl j - 1))) := by rw [← hexp]; exact hb.le
      _ = 2 ^ j * 2 ^ (1 + 32 * (2 ^ lvl j - 1)) := pow_add _ _ _
      _ ≤ 2 ^ j * (j + 2) ^ 33 := Nat.mul_le_mul_left _ hpow

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos1191_erdos_1191_parts_ii_R2.H2 :=
  ⟨OMA.Helpers.enc, 33, OMA.Helpers.enc_sum, OMA.Helpers.enc_size⟩
