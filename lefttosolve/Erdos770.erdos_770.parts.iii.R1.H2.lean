import OMAReductions.R_Erdos770_erdos_770_parts_iii_R1
import Mathlib

/-!
# Step H2 of the reduction Erdos770.erdos_770.parts.iii.R1

For every prime `q < 2 ^ 17` and every proper subgroup `H` of `(ZMod q)ˣ` there is a unit
`a ∉ H` whose representative `a.val` is at most `21 / 5 * (log q) ^ 2`.

Approach (only Mathlib and our own helper definitions are used):

* For `q = 2` the unit group is trivial, so no proper subgroup exists.
* For odd `q` we exhibit a primitive root `g` with `2 ≤ g ≤ 2 * (log₂ q) ^ 2` and `g < q`.
  An element of order `q - 1` generates the whole unit group, so it lies outside every proper
  subgroup (`not_mem_of_orderOf`).  The bound `2 k ^ 2 ≤ 21 / 5 * (log q) ^ 2` for
  `2 ^ k ≤ q` follows from `log 2 > 0.6931471803` (`real_bound`).
* The primitive roots are found by a Boolean checker `chk`, evaluated by the kernel
  (`decide +kernel`) on all odd numbers `3 ≤ n < 2 ^ 17` in sixteen chunks.  For each `n` it
  either finds a proper divisor among `3, 5, 7`, or a Fermat witness `2 ^ (n - 1) % n ≠ 1`, or
  it factors `n - 1` by trial division and searches `g = 2, 3, …` such that
  `g ^ ((n - 1) / ℓ) % n ≠ 1` for every prime factor `ℓ` of `n - 1`.
  `chk_sound` proves that a successful check of a prime `n` yields `g` of order `n - 1`
  (via `orderOf_eq_of_pow_and_pow_div_prime` and Fermat's little theorem).
* The loops are written with `Nat.rec` and fuel, and modular powers use two kernel-accelerated
  `Nat.pow` calls of moderate size (`pw`), so that the whole kernel computation takes well
  under a minute.
-/


namespace OMA.Helpers

/-- Boolean selection; one delta step and one iota step in the kernel. -/
def bsel {α : Sort _} (c : Bool) (x y : α) : α := Bool.rec y x c

theorem bsel_true {α : Sort _} (x y : α) : bsel true x y = x := rfl
theorem bsel_false {α : Sort _} (x y : α) : bsel false x y = y := rfl

theorem beq_t {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h
theorem beq_f {a b : ℕ} (h : Nat.beq a b = false) : a ≠ b := Nat.ne_of_beq_eq_false h
theorem blt_t {a b : ℕ} (h : Nat.blt a b = true) : a < b := by simpa using h
theorem blt_f {a b : ℕ} (h : Nat.blt a b = false) : b ≤ a := by
  have : ¬ a < b := fun h' => by rw [(Nat.blt_eq).mpr h'] at h; exact Bool.noConfusion h
  omega

/-- `b ^ e % m`, computed with two kernel-accelerated powers of moderate size. -/
def pw (b e m : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.pow b 256) m) (Nat.div e 256))
    (Nat.pow b (Nat.mod e 256))) m

theorem pw_eq (b e m : ℕ) : pw b e m = b ^ e % m := by
  show ((b ^ 256 % m) ^ (e / 256) * b ^ (e % 256)) % m = b ^ e % m
  conv_rhs => rw [← Nat.div_add_mod e 256, pow_add, pow_mul]
  rw [Nat.mul_mod, ← Nat.pow_mod, ← Nat.mul_mod]

/-- Divide `m` by `d` as long as it is divisible (at most `f` times). -/
noncomputable def stripLoop (d f : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun m => m)
    (fun _ ih m => bsel (Nat.beq (Nat.mod m d) 0) (ih (Nat.div m d)) m) f

theorem stripLoop_zero (d m : ℕ) : stripLoop d 0 m = m := rfl

theorem stripLoop_succ (d f m : ℕ) :
    stripLoop d (f + 1) m = bsel (Nat.beq (Nat.mod m d) 0) (stripLoop d f (Nat.div m d)) m := rfl

theorem stripLoop_spec (d f : ℕ) : ∀ m, ∃ k, stripLoop d f m * d ^ k = m := by
  induction f with
  | zero => intro m; exact ⟨0, by simp [stripLoop_zero]⟩
  | succ f ih =>
    intro m
    rw [stripLoop_succ]
    cases h : Nat.beq (Nat.mod m d) 0
    · exact ⟨0, by simp [bsel_false]⟩
    · rw [bsel_true]
      obtain ⟨k, hk⟩ := ih (Nat.div m d)
      refine ⟨k + 1, ?_⟩
      have h' : m % d = 0 := beq_t h
      have hd : d ∣ m := Nat.dvd_of_mod_eq_zero h'
      rw [pow_succ, ← mul_assoc, hk]
      exact Nat.div_mul_cancel hd

/-- Trial division by `d, d + 2, …`; returns the found divisors pushed on `acc`
(a final `1` signals that the fuel ran out). -/
noncomputable def facLoop (f : ℕ) : ℕ → ℕ → List ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → List ℕ → List ℕ) (fun _ _ acc => 1 :: acc)
    (fun _ ih d m acc => bsel (Nat.blt m (Nat.mul d d))
       (bsel (Nat.beq m 1) acc (m :: acc))
       (bsel (Nat.beq (Nat.mod m d) 0) (ih d (Nat.div m d) (d :: acc))
         (ih (Nat.add d 2) m acc))) f

theorem facLoop_zero (d m : ℕ) (acc : List ℕ) : facLoop 0 d m acc = 1 :: acc := rfl

theorem facLoop_succ (f d m : ℕ) (acc : List ℕ) :
    facLoop (f + 1) d m acc = bsel (Nat.blt m (Nat.mul d d))
       (bsel (Nat.beq m 1) acc (m :: acc))
       (bsel (Nat.beq (Nat.mod m d) 0) (facLoop f d (Nat.div m d) (d :: acc))
         (facLoop f (Nat.add d 2) m acc)) := rfl

/-- If every prime factor of `m` is at least `d` and `m < d * d`, every prime factor of `m`
equals `m`. -/
theorem eq_of_dvd_of_lt_sq {d m p : ℕ} (hm0 : m ≠ 0) (hmd : m < d * d)
    (hall : ∀ q, q.Prime → q ∣ m → d ≤ q) (hp : p.Prime) (hpm : p ∣ m) : p = m := by
  obtain ⟨t, rfl⟩ := hpm
  have ht0 : t ≠ 0 := by rintro rfl; simp at hm0
  by_cases ht1 : t = 1
  · subst ht1; simp
  · exfalso
    obtain ⟨q, hq, hqt⟩ := Nat.exists_prime_and_dvd ht1
    have h1 : d ≤ p := hall p hp (dvd_mul_right p t)
    have h2 : d ≤ q := hall q hq (Dvd.dvd.mul_left hqt p)
    have h3 : q ≤ t := Nat.le_of_dvd (Nat.pos_of_ne_zero ht0) hqt
    have : d * d ≤ p * t := Nat.mul_le_mul h1 (h2.trans h3)
    omega

theorem facLoop_spec (f : ℕ) : ∀ d m (acc : List ℕ), ¬ 2 ∣ m → d % 2 = 1 →
    (∀ p, p.Prime → p ∣ m → d ≤ p) →
    (∀ x ∈ acc, x ∈ facLoop f d m acc) ∧
      (∀ p, p.Prime → p ∣ m → p ∈ facLoop f d m acc ∨ 1 ∈ facLoop f d m acc) := by
  induction f with
  | zero =>
    intro d m acc _ _ _
    rw [facLoop_zero]
    exact ⟨fun x hx => List.mem_cons_of_mem _ hx, fun _ _ _ => Or.inr List.mem_cons_self⟩
  | succ f ih =>
    intro d m acc hm2 hd2 hall
    have hm0 : m ≠ 0 := by rintro rfl; exact hm2 (dvd_zero 2)
    rw [facLoop_succ]
    cases h1 : Nat.blt m (Nat.mul d d)
    · rw [bsel_false]
      have h1' : d * d ≤ m := blt_f h1
      cases h2 : Nat.beq (Nat.mod m d) 0
      · rw [bsel_false]
        have h2' : m % d ≠ 0 := beq_f h2
        have hdm : ¬ d ∣ m := fun h => h2' (Nat.mod_eq_zero_of_dvd h)
        apply ih (Nat.add d 2) m acc hm2 (by show (d + 2) % 2 = 1; omega)
        intro p hp hpm
        have hpd := hall p hp hpm
        have hpne : p ≠ d := by rintro rfl; exact hdm hpm
        have hp2 : p ≠ 2 := by rintro rfl; exact hm2 hpm
        have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
        show d + 2 ≤ p
        omega
      · rw [bsel_true]
        have h2' : m % d = 0 := beq_t h2
        have hdm : d ∣ m := Nat.dvd_of_mod_eq_zero h2'
        have hd0 : 0 < d := by omega
        have hsub : m / d ∣ m := Nat.div_dvd_of_dvd hdm
        obtain ⟨ih1, ih2⟩ := ih d (Nat.div m d) (d :: acc)
          (fun h => hm2 (h.trans hsub)) hd2 (fun p hp hpm => hall p hp (hpm.trans hsub))
        refine ⟨fun x hx => ih1 x (List.mem_cons_of_mem _ hx), ?_⟩
        intro p hp hpm
        have hm' : m = d * (m / d) := (Nat.mul_div_cancel' hdm).symm
        rw [hm'] at hpm
        rcases (Nat.Prime.dvd_mul hp).1 hpm with hpd | hpd
        · have := hall p hp (hm' ▸ hpm)
          have := Nat.le_of_dvd hd0 hpd
          have hpd' : p = d := by omega
          subst hpd'
          exact Or.inl (ih1 p List.mem_cons_self)
        · exact ih2 p hp hpd
    · rw [bsel_true]
      have h1' : m < d * d := blt_t h1
      cases h3 : Nat.beq m 1
      · rw [bsel_false]
        have h3' : m ≠ 1 := beq_f h3
        refine ⟨fun x hx => List.mem_cons_of_mem _ hx, ?_⟩
        intro p hp hpm
        left
        rw [eq_of_dvd_of_lt_sq hm0 h1' hall hp hpm]
        exact List.mem_cons_self
      · rw [bsel_true]
        have h3' : m = 1 := beq_t h3
        refine ⟨fun x hx => hx, ?_⟩
        intro p hp hpm
        subst h3'
        exact absurd (Nat.le_of_dvd one_pos hpm) (by have := hp.two_le; omega)

/-- `testAll n M g L` checks `g ^ (M / x) % n ≠ 1` for every `x ∈ L`. -/
noncomputable def testAll (n M g : ℕ) (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x _ ih => bsel (Nat.beq (pw g (Nat.div M x) n) 1) false ih) L

theorem testAll_spec (n M g : ℕ) (L : List ℕ) (h : testAll n M g L = true) :
    ∀ x ∈ L, g ^ (M / x) % n ≠ 1 := by
  induction L with
  | nil => intro x hx; simp at hx
  | cons y L ih =>
    have hstep : testAll n M g (y :: L) =
        bsel (Nat.beq (pw g (Nat.div M y) n) 1) false (testAll n M g L) := rfl
    rw [hstep] at h
    cases h1 : Nat.beq (pw g (Nat.div M y) n) 1
    · rw [h1, bsel_false] at h
      have h1' : pw g (M / y) n ≠ 1 := beq_f h1
      rw [pw_eq] at h1'
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h1'
      · exact ih h x hx
    · rw [h1, bsel_true] at h
      exact absurd h (by simp)

/-- Search for `g ≤ cap` with `g < n` passing `testAll`, starting from `g`. -/
noncomputable def search (n M cap : ℕ) (L : List ℕ) (f : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => false)
    (fun _ ih g => bsel (Nat.blt cap g) false
      (bsel (bsel (Nat.blt g n) (testAll n M g L) false) true (ih (Nat.add g 1)))) f

theorem search_spec (n M cap : ℕ) (L : List ℕ) (f : ℕ) : ∀ g, search n M cap L f g = true →
    ∃ g', g ≤ g' ∧ g' ≤ cap ∧ g' < n ∧ testAll n M g' L = true := by
  induction f with
  | zero => intro g h; exact absurd h (by simp [search])
  | succ f ih =>
    intro g h
    have hstep : search n M cap L (f + 1) g = bsel (Nat.blt cap g) false
        (bsel (bsel (Nat.blt g n) (testAll n M g L) false) true (search n M cap L f (Nat.add g 1))) :=
      rfl
    rw [hstep] at h
    cases h1 : Nat.blt cap g
    · rw [h1, bsel_false] at h
      have h1' : g ≤ cap := blt_f h1
      cases h2 : Nat.blt g n
      · rw [h2, bsel_false, bsel_false] at h
        obtain ⟨g', hg1, hg2⟩ := ih (Nat.add g 1) h
        exact ⟨g', by change g + 1 ≤ g' at hg1; omega, hg2⟩
      · rw [h2, bsel_true] at h
        have h2' : g < n := blt_t h2
        cases h3 : testAll n M g L
        · rw [h3, bsel_false] at h
          obtain ⟨g', hg1, hg2⟩ := ih (Nat.add g 1) h
          exact ⟨g', by change g + 1 ≤ g' at hg1; omega, hg2⟩
        · exact ⟨g, le_rfl, h1', h2', h3⟩
    · rw [h1, bsel_true] at h
      exact absurd h (by simp)

/-- `p` is a proper divisor of `n`. -/
def sv (n p : ℕ) : Bool := bsel (Nat.beq (Nat.mod n p) 0) (Nat.blt p n) false

theorem sv_spec {n p : ℕ} (h : sv n p = true) : p ∣ n ∧ p < n := by
  unfold sv at h
  cases h1 : Nat.beq (Nat.mod n p) 0
  · rw [h1, bsel_false] at h; exact absurd h (by simp)
  · rw [h1, bsel_true] at h
    have h1' : n % p = 0 := beq_t h1
    exact ⟨Nat.dvd_of_mod_eq_zero h1', blt_t h⟩

/-- The check for one odd number `n ≥ 3`: either `n` is visibly composite, or `n - 1` is
factored by trial division and some `g ≤ 2 (log₂ n)²` passes the primitive root test. -/
noncomputable def chk (n : ℕ) : Bool :=
  bsel (sv n 3) true (bsel (sv n 5) true (bsel (sv n 7) true
    (bsel (Nat.beq (pw 2 (Nat.sub n 1) n) 1)
      (bsel (Nat.beq (Nat.mod (stripLoop 2 17 (Nat.sub n 1)) 2) 1)
        (search n (Nat.sub n 1) (Nat.mul 2 (Nat.pow (Nat.log2 n) 2))
          (2 :: facLoop 200 3 (stripLoop 2 17 (Nat.sub n 1)) []) 600 2) false)
      true)))

theorem not_sv_of_prime {n p : ℕ} (hn : n.Prime) (hp : 2 ≤ p) : sv n p = false := by
  cases h : sv n p
  · rfl
  · obtain ⟨h1, h2⟩ := sv_spec h
    rcases hn.eq_one_or_self_of_dvd p h1 with h3 | h3 <;> omega

theorem fermat_nat {n a : ℕ} (hn : n.Prime) (ha : ¬ n ∣ a) : a ^ (n - 1) % n = 1 := by
  have := Fact.mk hn
  have h1 : ((a : ZMod n)) ^ (n - 1) = 1 := by
    apply ZMod.pow_card_sub_one_eq_one
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have h2 : ((a ^ (n - 1) : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by push_cast; exact h1
  rw [ZMod.natCast_eq_natCast_iff'] at h2
  rw [h2]
  exact Nat.mod_eq_of_lt hn.one_lt

theorem chk_sound (n : ℕ) (hn : n.Prime) (h3 : 3 ≤ n) (h : chk n = true) :
    ∃ g : ℕ, 2 ≤ g ∧ g ≤ 2 * Nat.log2 n ^ 2 ∧ g < n ∧ orderOf (g : ZMod n) = n - 1 := by
  have := Fact.mk hn
  unfold chk at h
  rw [not_sv_of_prime hn (by norm_num), not_sv_of_prime hn (by norm_num),
    not_sv_of_prime hn (by norm_num), bsel_false, bsel_false, bsel_false] at h
  have hodd : ¬ n ∣ 2 := by
    intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
  have hf : Nat.beq (pw 2 (Nat.sub n 1) n) 1 = true := by
    rw [Nat.beq_eq, pw_eq]
    exact fermat_nat hn hodd
  rw [hf, bsel_true] at h
  set M := n - 1 with hM
  set r := stripLoop 2 17 (Nat.sub n 1) with hr
  cases h4 : Nat.beq (Nat.mod r 2) 1
  · rw [h4, bsel_false] at h; exact absurd h (by simp)
  rw [h4, bsel_true] at h
  have hr2 : ¬ 2 ∣ r := by
    have : r % 2 = 1 := beq_t h4
    omega
  obtain ⟨g, hg2, hgcap, hgn, htest⟩ := search_spec _ _ _ _ _ 2 h
  have htest' := testAll_spec _ _ _ _ htest
  refine ⟨g, hg2, by simpa using hgcap, hgn, ?_⟩
  -- every prime factor of `M` occurs in the list
  obtain ⟨k, hk⟩ := stripLoop_spec 2 17 (Nat.sub n 1)
  have hspec := facLoop_spec 200 3 r [] hr2 (by norm_num) (fun p hp _ => by
    have := hp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · exfalso
      have : p = 2 := by omega
      subst this
      exact hr2 ‹_›
    · exact h)
  have hgcop : ¬ n ∣ g := by
    intro hd; have := Nat.le_of_dvd (by omega) hd; omega
  have hferm := fermat_nat hn hgcop
  have hmem : ∀ p, p.Prime → p ∣ M → g ^ (M / p) % n ≠ 1 := by
    intro p hp hpM
    have hnot1 : (1 : ℕ) ∉ 2 :: facLoop 200 3 r [] := by
      intro h1
      have := htest' 1 h1
      rw [Nat.div_one] at this
      exact this hferm
    apply htest' p
    by_cases hp2 : p = 2
    · subst hp2; exact List.mem_cons_self
    · have hpr : p ∣ r := by
        have hpM' : p ∣ r * 2 ^ k := by rw [hk]; exact hpM
        rcases (Nat.Prime.dvd_mul hp).1 hpM' with h | h
        · exact h
        · exfalso
          have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
          exact hp2 this
      rcases hspec.2 p hp hpr with h | h
      · exact List.mem_cons_of_mem _ h
      · exact absurd (List.mem_cons_of_mem _ h) hnot1
  apply orderOf_eq_of_pow_and_pow_div_prime (by omega)
  · have : ((g ^ M : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
      rw [ZMod.natCast_eq_natCast_iff', hferm, Nat.mod_eq_of_lt hn.one_lt]
    push_cast at this
    exact this
  · intro p hp hpM hpow
    apply hmem p hp hpM
    have : ((g ^ (M / p) : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by push_cast; exact hpow
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hn.one_lt] at this
    exact this

/-- Run `chk` on `n, n + 2, …, n + 2 (f - 1)`. -/
noncomputable def allChk (f : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun _ ih n => bsel (chk n) (ih (Nat.add n 2)) false) f

theorem allChk_spec (f : ℕ) : ∀ n, allChk f n = true → ∀ i < f, chk (n + 2 * i) = true := by
  induction f with
  | zero => intro n _ i hi; omega
  | succ f ih =>
    intro n h i hi
    have hstep : allChk (f + 1) n = bsel (chk n) (allChk f (Nat.add n 2)) false := rfl
    rw [hstep] at h
    cases h1 : chk n
    · rw [h1, bsel_false] at h; exact absurd h (by simp)
    · rw [h1, bsel_true] at h
      rcases i with _ | i
      · simpa using h1
      · have := ih (Nat.add n 2) h i (by omega)
        rw [show n + 2 * (i + 1) = Nat.add n 2 + 2 * i by show _ = n + 2 + 2 * i; ring]
        exact this

theorem chunk0 : allChk 4096 3 = true := by decide +kernel

theorem chunk1 : allChk 4096 8195 = true := by decide +kernel

theorem chunk2 : allChk 4096 16387 = true := by decide +kernel

theorem chunk3 : allChk 4096 24579 = true := by decide +kernel

theorem chunk4 : allChk 4096 32771 = true := by decide +kernel

theorem chunk5 : allChk 4096 40963 = true := by decide +kernel

theorem chunk6 : allChk 4096 49155 = true := by decide +kernel

theorem chunk7 : allChk 4096 57347 = true := by decide +kernel

theorem chunk8 : allChk 4096 65539 = true := by decide +kernel

theorem chunk9 : allChk 4096 73731 = true := by decide +kernel

theorem chunk10 : allChk 4096 81923 = true := by decide +kernel

theorem chunk11 : allChk 4096 90115 = true := by decide +kernel

theorem chunk12 : allChk 4096 98307 = true := by decide +kernel

theorem chunk13 : allChk 4096 106499 = true := by decide +kernel

theorem chunk14 : allChk 4096 114691 = true := by decide +kernel

theorem chunk15 : allChk 4095 122883 = true := by decide +kernel

theorem chk_of_chunk {f n : ℕ} (h : allChk f n = true) (q : ℕ) (h1 : n ≤ q) (h2 : q < n + 2 * f)
    (h3 : (q - n) % 2 = 0) : chk q = true := by
  have := allChk_spec f n h ((q - n) / 2) (by omega)
  rwa [show n + 2 * ((q - n) / 2) = q by omega] at this

theorem chk_all (q : ℕ) (h3 : 3 ≤ q) (hq : q < 131072) (hodd : q % 2 = 1) : chk q = true := by
  rcases Nat.lt_or_ge q 8195 with h0 | h0
  · exact chk_of_chunk chunk0 q (by omega) (by omega) (by omega)
  rcases Nat.lt_or_ge q 16387 with h1 | h1
  · exact chk_of_chunk chunk1 q (by omega) (by omega) (by omega)
  rcases Nat.lt_or_ge q 24579 with h2 | h2
  · exact chk_of_chunk chunk2 q (by omega) (by omega) (by omega)
  rcases Nat.lt_or_ge q 32771 with h3 | h3
  · exact chk_of_chunk chunk3 q (by omega) (by omega) (by omega)
  rcases Nat.lt_or_ge q 40963 with h4 | h4
  · exact chk_of_chunk chunk4 q (by omega) (by omega) (by omega)
  rcases Nat.lt_or_ge q 49155 with h5 | h5
  · exact chk_of_chunk chunk5 q (by omega) (by omega) (by omega)
  rcases Nat.lt_or_ge q 57347 with h6 | h6
  · exact chk_of_chunk chunk6 q (by omega) (by omega) (by omega)
  rcases Nat.lt_or_ge q 65539 with h7 | h7
  · exact chk_of_chunk chunk7 q (by omega) (by omega) (by omega)
  rcases Nat.lt_or_ge q 73731 with h8 | h8
  · exact chk_of_chunk chunk8 q (by omega) (by omega) (by omega)
  rcases Nat.lt_or_ge q 81923 with h9 | h9
  · exact chk_of_chunk chunk9 q (by omega) (by omega) (by omega)
  rcases Nat.lt_or_ge q 90115 with h10 | h10
  · exact chk_of_chunk chunk10 q (by omega) (by omega) (by omega)
  rcases Nat.lt_or_ge q 98307 with h11 | h11
  · exact chk_of_chunk chunk11 q (by omega) (by omega) (by omega)
  rcases Nat.lt_or_ge q 106499 with h12 | h12
  · exact chk_of_chunk chunk12 q (by omega) (by omega) (by omega)
  rcases Nat.lt_or_ge q 114691 with h13 | h13
  · exact chk_of_chunk chunk13 q (by omega) (by omega) (by omega)
  rcases Nat.lt_or_ge q 122883 with h14 | h14
  · exact chk_of_chunk chunk14 q (by omega) (by omega) (by omega)
  exact chk_of_chunk chunk15 q (by omega) (by omega) (by omega)

theorem not_mem_of_orderOf {q : ℕ} [Fact q.Prime] (u : (ZMod q)ˣ) (hu : orderOf u = q - 1)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) : u ∉ H := by
  intro huH
  apply hH
  have h1 : Subgroup.zpowers u ≤ H := Subgroup.zpowers_le.2 huH
  have h2 : Subgroup.zpowers u = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hu, Nat.card_eq_fintype_card, ZMod.card_units]
  rw [h2] at h1
  exact top_le_iff.1 h1

theorem real_bound (q k : ℕ) (hq : 2 ^ k ≤ q) : 2 * (k : ℝ) ^ 2 ≤ 21 / 5 * Real.log q ^ 2 := by
  have hq0 : (0 : ℝ) < q := by
    have : 0 < 2 ^ k := Nat.pos_of_ne_zero (by positivity)
    exact_mod_cast (lt_of_lt_of_le this hq)
  have h1 : (k : ℝ) * Real.log 2 ≤ Real.log q := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast hq
  have h2 := Real.log_two_gt_d9
  have h3 : 0 ≤ (k : ℝ) * Real.log 2 := by positivity
  have h4 : ((k : ℝ) * Real.log 2) ^ 2 ≤ Real.log q ^ 2 := pow_le_pow_left₀ h3 h1 2
  have h5 : (10 / 21 : ℝ) ≤ Real.log 2 ^ 2 := by nlinarith
  have h6 : (k : ℝ) ^ 2 * (10 / 21) ≤ (k : ℝ) ^ 2 * Real.log 2 ^ 2 :=
    mul_le_mul_of_nonneg_left h5 (sq_nonneg _)
  nlinarith

theorem h2_core : ∀ q : ℕ, q.Prime → q < 2 ^ 17 → ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
    ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ 21 / 5 * Real.log q ^ 2 := by
  intro q hq hq17 H hH
  have := Fact.mk hq
  rcases hq.eq_two_or_odd' with rfl | hodd
  · exfalso
    have h1 : (1 : (ZMod 2)ˣ) ∉ H := not_mem_of_orderOf 1 (by simp) H hH
    exact h1 H.one_mem
  · have hq2 : q % 2 = 1 := Nat.odd_iff.mp hodd
    have h3 : 3 ≤ q := by have := hq.two_le; omega
    obtain ⟨g, hg2, hgcap, hgq, hord⟩ :=
      chk_sound q hq h3 (chk_all q h3 (by norm_num at hq17; omega) hq2)
    have hcop : Nat.Coprime g q := by
      rw [Nat.coprime_comm, hq.coprime_iff_not_dvd]
      intro hd; have := Nat.le_of_dvd (by omega) hd; omega
    refine ⟨ZMod.unitOfCoprime g hcop, ?_, ?_⟩
    · apply not_mem_of_orderOf _ _ H hH
      rw [← orderOf_units, ZMod.coe_unitOfCoprime]
      exact hord
    · rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hgq]
      have hk := real_bound q (Nat.log2 q) (Nat.log2_self_le hq.ne_zero)
      have : (g : ℝ) ≤ 2 * (Nat.log2 q : ℝ) ^ 2 := by exact_mod_cast hgcap
      linarith

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos770_erdos_770_parts_iii_R1.H2 := by
  intro q hq hq17 H hH
  exact OMA.Helpers.h2_core q hq hq17 H hH
