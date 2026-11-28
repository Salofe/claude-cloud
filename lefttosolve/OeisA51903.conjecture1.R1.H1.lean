import OMAReductions.R_OeisA51903_conjecture1_R1

/-!
# Step H1 of the reduction OeisA51903.conjecture1.R1

Claim: if `1 < n` and the totient of `n` divides `n - 1`, then the largest exponent in the
prime factorisation of `n` (the sequence A051903) equals one.

Proof.
* If `p` is prime and `p * p ∣ n`, write `n = p * (p * k)`. The totient is multiplicative in
  the form `φ (p * m) = p * φ m` whenever `p ∣ m`, so `p ∣ φ n`.
* Under the Lehmer congruence such a `p` divides both `n - 1` and `n`, hence divides `1`,
  which is impossible. So `n` is squarefree.
* A squarefree `n` has a duplicate-free list of prime factors, so each prime factor occurs
  exactly once and the list of multiplicities is a list of ones; it is nonempty as `1 < n`.
* The right fold of `max` starting from `0` over a nonempty list of ones is `1`.
-/

namespace OMA.Helpers

/-- A prime whose square divides `n` divides the totient of `n`. -/
theorem a51903_prime_dvd_totient_of_sq_dvd {p n : ℕ} (hp : p.Prime) (h : p * p ∣ n) :
    p ∣ n.totient := by
  obtain ⟨k, rfl⟩ := h
  rw [mul_assoc, Nat.totient_mul_of_prime_of_dvd hp (dvd_mul_right p k)]
  exact dvd_mul_right p _

/-- The Lehmer congruence `φ n ∣ n - 1` forces `n` to be squarefree. -/
theorem a51903_squarefree_of_lehmer {n : ℕ} (hn : 1 < n) (h : n.totient ∣ n - 1) :
    Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have h1 : p ∣ n - 1 := (a51903_prime_dvd_totient_of_sq_dvd hp hpp).trans h
  have h2 : p ∣ n - 1 + 1 := by
    rw [Nat.sub_add_cancel hn.le]
    exact (dvd_mul_right p p).trans hpp
  exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp h2))

/-- The right fold of `max` from `0` over a nonempty list of ones is one. -/
theorem a51903_foldr_max_of_all_one :
    ∀ l : List ℕ, l ≠ [] → (∀ x ∈ l, x = 1) → l.foldr max 0 = 1
  | [], hne, _ => absurd rfl hne
  | [a], _, h => by
    rw [List.foldr_cons, List.foldr_nil, h a (List.mem_singleton_self a)]
    rfl
  | a :: b :: t, _, h => by
    rw [List.foldr_cons,
      a51903_foldr_max_of_all_one (b :: t) (List.cons_ne_nil b t)
        (fun x hx => h x (List.mem_cons_of_mem a hx)),
      h a List.mem_cons_self]
    rfl

end OMA.Helpers

theorem OMA.solution : OMA.R_OeisA51903_conjecture1_R1.H1 := by
  intro n hn hφ
  have hnd : n.primeFactorsList.Nodup :=
    (Nat.squarefree_iff_nodup_primeFactorsList (by omega)).mp
      (OMA.Helpers.a51903_squarefree_of_lehmer hn hφ)
  unfold OeisA51903.a
  apply OMA.Helpers.a51903_foldr_max_of_all_one
  · rw [Ne, List.map_eq_nil_iff]
    exact (Nat.primeFactorsList_ne_nil n).mpr hn
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact List.count_eq_one_of_mem hnd hp
