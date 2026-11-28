import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H2_R1

/-!
# Step H1 of the reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1.H2.R1

Exponent e = 458 of 3 is impossible, so the bound holds with A = 0 (vacuously).

3 ^ 458 + 1 = 2 * 5 * 19039061 * Q, where Q is a prime of 211 digits. Since 3 is the only odd prime
whose square divides n, every odd prime factor of 3 ^ 458 + 1 other than 3 is a simple prime of n
(it divides the unitary divisor sum 2 n). So Q is a simple prime of n. But 5 divides both
3 ^ 458 + 1 and Q + 1, so 5 ^ 2 divides the unitary divisor sum 2 n, while 5 is a simple prime:
contradiction. This uses the balance equation and its consequences (kill_at, facts) proved in the
reduction files.

The primality of Q is certified by a Lucas (Pratt) certificate tree: for each prime p of the tree,
p - 1 is fully factored and a witness a of order p - 1 is given. The modular powers are computed by
the kernel with a repeated-squaring function pw, proved correct below (pw_spec).
-/

namespace OMA.Helpers

/-- Modular exponentiation by repeated squaring, with a fuel argument for structural recursion:
`pw m f b e = b ^ e % m` as soon as `e < 2 ^ f`. -/
def pw (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1 % m
  | f + 1, b, e =>
    if e = 0 then 1 % m
    else if e % 2 = 1 then pw m f (b * b % m) (e / 2) * b % m
    else pw m f (b * b % m) (e / 2)

theorem pw_spec (m : ℕ) : ∀ f b e, e < 2 ^ f → pw m f b e = b ^ e % m := by
  intro f
  induction f with
  | zero =>
    intro b e he
    have : e = 0 := by simpa using he
    subst this
    simp [pw]
  | succ f ih =>
    intro b e he
    have he2 : e / 2 < 2 ^ f := by rw [pow_succ] at he; omega
    have key := ih (b * b % m) (e / 2) he2
    have hpow : (b * b % m) ^ (e / 2) % m = b ^ (2 * (e / 2)) % m := by
      rw [← Nat.pow_mod, pow_mul, sq]
    by_cases h0 : e = 0
    · subst h0
      simp [pw]
    · by_cases h1 : e % 2 = 1
      · have hsplit : e = 2 * (e / 2) + 1 := by omega
        simp only [pw, h0, h1, if_false, if_true, key, hpow]
        conv_rhs => rw [hsplit, pow_succ]
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      · have hsplit : e = 2 * (e / 2) := by omega
        simp only [pw, h0, h1, if_false, key, hpow]
        rw [← hsplit]

/-- A Lucas certificate: `p - 1` is the product of the list `L`, `a` has order dividing `p - 1`,
and `a ^ ((p - 1) / q) ≠ 1` for every `q` in `L`. All computations are modulo `p`. -/
def cert (p a : ℕ) (L : List ℕ) : Bool :=
  decide (1 < p) && (p - 1 == L.prod) && (pw p p a (p - 1) == 1) &&
    L.all (fun q => pw p p a ((p - 1) / q) != 1)

theorem prime_of_cert (p a : ℕ) (L : List ℕ) (hc : cert p a L = true)
    (hL : ∀ q ∈ L, q.Prime) : p.Prime := by
  simp only [cert, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨⟨hp, hprod⟩, hfull⟩, hall⟩ := hc
  have hfuel : ∀ e, e ≤ p - 1 → pw p p a e = a ^ e % p := fun e he =>
    pw_spec p p a e (lt_of_le_of_lt he (lt_of_lt_of_le (by omega) p.lt_two_pow_self.le))
  have hcast : ∀ e, (a : ZMod p) ^ e = ((a ^ e % p : ℕ) : ZMod p) := by
    intro e
    rw [ZMod.natCast_mod, Nat.cast_pow]
  refine lucas_primality p (a : ZMod p) ?_ ?_
  · rw [hcast, ← hfuel _ le_rfl, hfull, Nat.cast_one]
  · intro q hq hqd h
    rw [hprod] at hqd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hqd
    have hqx' : q = x := (Nat.prime_dvd_prime_iff_eq hq (hL x hx)).mp hqx
    subst hqx'
    have h1 := hall q hx
    have hle : (p - 1) / q ≤ p - 1 := Nat.div_le_self _ _
    rw [hcast, ← hfuel _ hle] at h
    have hlt : pw p p a ((p - 1) / q) < p := by
      rw [hfuel _ hle]
      exact Nat.mod_lt _ (by omega)
    have h2 := (ZMod.natCast_eq_natCast_iff' (pw p p a ((p - 1) / q)) 1 p).mp (by rw [h, Nat.cast_one])
    rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hp] at h2
    exact h1 h2

theorem allP_nil : ∀ q ∈ ([] : List ℕ), q.Prime := by simp

theorem allP_cons {x : ℕ} {L : List ℕ} (hx : x.Prime) (hL : ∀ q ∈ L, q.Prime) :
    ∀ q ∈ x :: L, q.Prime := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | h
  · exact hx
  · exact hL q h

theorem prime_55375561 : Nat.Prime 55375561 :=
  prime_of_cert 55375561 11
    [2, 2, 2, 3, 3, 5, 193, 797]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) allP_nil))))))))

theorem prime_292010161 : Nat.Prime 292010161 :=
  prime_of_cert 292010161 17
    [2, 2, 2, 2, 3, 5, 13, 173, 541]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) allP_nil)))))))))

theorem prime_6260041 : Nat.Prime 6260041 :=
  prime_of_cert 6260041 13
    [2, 2, 2, 3, 3, 5, 17389]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) allP_nil)))))))

theorem prime_24551880803 : Nat.Prime 24551880803 :=
  prime_of_cert 24551880803 2
    [2, 37, 53, 6260041]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_6260041 allP_nil))))

theorem prime_49103761607 : Nat.Prime 49103761607 :=
  prime_of_cert 49103761607 5
    [2, 24551880803]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons prime_24551880803 allP_nil))

theorem prime_665303323 : Nat.Prime 665303323 :=
  prime_of_cert 665303323 2
    [2, 3, 1151, 96337]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) allP_nil))))

theorem prime_619078048117961 : Nat.Prime 619078048117961 :=
  prime_of_cert 619078048117961 3
    [2, 2, 2, 5, 43, 541, 665303323]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_665303323 allP_nil)))))))

theorem prime_1868284339168339 : Nat.Prime 1868284339168339 :=
  prime_of_cert 1868284339168339 2
    [2, 3, 3, 3, 7, 7, 13, 37, 6197, 236879]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) allP_nil))))))))))

theorem prime_286529816279694857749513 : Nat.Prime 286529816279694857749513 :=
  prime_of_cert 286529816279694857749513 11
    [2, 2, 2, 3, 709, 9013, 1868284339168339]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_1868284339168339 allP_nil)))))))

theorem prime_18653681 : Nat.Prime 18653681 :=
  prime_of_cert 18653681 6
    [2, 2, 2, 2, 5, 431, 541]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) allP_nil)))))))

theorem prime_32009716597 : Nat.Prime 32009716597 :=
  prime_of_cert 32009716597 2
    [2, 2, 3, 11, 13, 18653681]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_18653681 allP_nil))))))

theorem prime_2496757894567 : Nat.Prime 2496757894567 :=
  prime_of_cert 2496757894567 5
    [2, 3, 13, 32009716597]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_32009716597 allP_nil))))

theorem prime_1521374455475455781 : Nat.Prime 1521374455475455781 :=
  prime_of_cert 1521374455475455781 2
    [2, 2, 5, 30467, 2496757894567]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_2496757894567 allP_nil)))))

theorem prime_1901803 : Nat.Prime 1901803 :=
  prime_of_cert 1901803 2
    [2, 3, 7, 45281]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) allP_nil))))

theorem prime_39879028822393 : Nat.Prime 39879028822393 :=
  prime_of_cert 39879028822393 5
    [2, 2, 2, 3, 3, 3, 193, 503, 1901803]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_1901803 allP_nil)))))))))

theorem prime_14072073163 : Nat.Prime 14072073163 :=
  prime_of_cert 14072073163 2
    [2, 3, 7, 7039, 47599]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) allP_nil)))))

theorem prime_31141357188987371 : Nat.Prime 31141357188987371 :=
  prime_of_cert 31141357188987371 2
    [2, 5, 13, 29, 587, 14072073163]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_14072073163 allP_nil))))))

theorem prime_29416937523401 : Nat.Prime 29416937523401 :=
  prime_of_cert 29416937523401 3
    [2, 2, 2, 5, 5, 7, 239, 5273, 16673]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) allP_nil)))))))))

theorem prime_142319143738214039 : Nat.Prime 142319143738214039 :=
  prime_of_cert 142319143738214039 7
    [2, 41, 59, 29416937523401]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_29416937523401 allP_nil))))

theorem prime_284638287476428079 : Nat.Prime 284638287476428079 :=
  prime_of_cert 284638287476428079 17
    [2, 142319143738214039]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons prime_142319143738214039 allP_nil))

theorem prime_1710959 : Nat.Prime 1710959 :=
  prime_of_cert 1710959 17
    [2, 71, 12049]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) allP_nil)))

theorem prime_776076771549846271 : Nat.Prime 776076771549846271 :=
  prime_of_cert 776076771549846271 3
    [2, 3, 5, 7, 641, 977, 3449, 1710959]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_1710959 allP_nil))))))))

theorem prime_8535292333505209288459 : Nat.Prime 8535292333505209288459 :=
  prime_of_cert 8535292333505209288459 2
    [2, 3, 3, 13, 47, 776076771549846271]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_776076771549846271 allP_nil))))))

theorem prime_10934839 : Nat.Prime 10934839 :=
  prime_of_cert 10934839 13
    [2, 3, 3, 3, 3, 67499]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) allP_nil))))))

theorem prime_328045171 : Nat.Prime 328045171 :=
  prime_of_cert 328045171 2
    [2, 3, 5, 10934839]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_10934839 allP_nil))))

theorem prime_35363356825689644743 : Nat.Prime 35363356825689644743 :=
  prime_of_cert 35363356825689644743 5
    [2, 3, 3, 61, 499, 196751, 328045171]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_328045171 allP_nil)))))))

theorem prime_4931632289483375097279809 : Nat.Prime 4931632289483375097279809 :=
  prime_of_cert 4931632289483375097279809 3
    [2, 2, 2, 2, 2, 2, 2179, 35363356825689644743]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_35363356825689644743 allP_nil))))))))

theorem prime_88769381210700751751036563 : Nat.Prime 88769381210700751751036563 :=
  prime_of_cert 88769381210700751751036563 2
    [2, 3, 3, 4931632289483375097279809]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_4931632289483375097279809 allP_nil))))

theorem prime_3883848086440037310497051322544183 : Nat.Prime 3883848086440037310497051322544183 :=
  prime_of_cert 3883848086440037310497051322544183 3
    [2, 3, 3, 7, 347239, 88769381210700751751036563]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_88769381210700751751036563 allP_nil))))))

theorem prime_2938403877747137219284354089380826550354938422035201475099792317258946933632118590181850731 : Nat.Prime 2938403877747137219284354089380826550354938422035201475099792317258946933632118590181850731 :=
  prime_of_cert 2938403877747137219284354089380826550354938422035201475099792317258946933632118590181850731 2
    [2, 5, 31141357188987371, 284638287476428079, 8535292333505209288459, 3883848086440037310497051322544183]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_31141357188987371 (allP_cons prime_284638287476428079 (allP_cons prime_8535292333505209288459 (allP_cons prime_3883848086440037310497051322544183 allP_nil))))))

theorem prime_68970680968988137598347931772763984981852545863721949540826705746146307928219198256064312676941049562890465273 : Nat.Prime 68970680968988137598347931772763984981852545863721949540826705746146307928219198256064312676941049562890465273 :=
  prime_of_cert 68970680968988137598347931772763984981852545863721949540826705746146307928219198256064312676941049562890465273 3
    [2, 2, 2, 29, 43, 59, 39879028822393, 2938403877747137219284354089380826550354938422035201475099792317258946933632118590181850731]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_39879028822393 (allP_cons prime_2938403877747137219284354089380826550354938422035201475099792317258946933632118590181850731 allP_nil))))))))

theorem prime_1049302322029657087263636853427239717061483168620014582746869687897650603407478424436347449898616761159136772402905959988275932131 : Nat.Prime 1049302322029657087263636853427239717061483168620014582746869687897650603407478424436347449898616761159136772402905959988275932131 :=
  prime_of_cert 1049302322029657087263636853427239717061483168620014582746869687897650603407478424436347449898616761159136772402905959988275932131 2
    [2, 5, 1521374455475455781, 68970680968988137598347931772763984981852545863721949540826705746146307928219198256064312676941049562890465273]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_1521374455475455781 (allP_cons prime_68970680968988137598347931772763984981852545863721949540826705746146307928219198256064312676941049562890465273 allP_nil))))

theorem prime_1608582317417214810130635352535801824283625580080564742616555593796775363039054605362655017772160887748612499490552428161762482617917902416636558184042356827836981572487811361331057 : Nat.Prime 1608582317417214810130635352535801824283625580080564742616555593796775363039054605362655017772160887748612499490552428161762482617917902416636558184042356827836981572487811361331057 :=
  prime_of_cert 1608582317417214810130635352535801824283625580080564742616555593796775363039054605362655017772160887748612499490552428161762482617917902416636558184042356827836981572487811361331057 3
    [2, 2, 2, 2, 11, 49103761607, 619078048117961, 286529816279694857749513, 1049302322029657087263636853427239717061483168620014582746869687897650603407478424436347449898616761159136772402905959988275932131]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_49103761607 (allP_cons prime_619078048117961 (allP_cons prime_286529816279694857749513 (allP_cons prime_1049302322029657087263636853427239717061483168620014582746869687897650603407478424436347449898616761159136772402905959988275932131 allP_nil)))))))))

theorem prime_1745376548298255875979192507374504750088219827931938208827516973981765722860972555354002702289104895588612885757598083846275425844450388650127389943613904875063115406417706454079369576338460190775339499104522829 : Nat.Prime 1745376548298255875979192507374504750088219827931938208827516973981765722860972555354002702289104895588612885757598083846275425844450388650127389943613904875063115406417706454079369576338460190775339499104522829 :=
  prime_of_cert 1745376548298255875979192507374504750088219827931938208827516973981765722860972555354002702289104895588612885757598083846275425844450388650127389943613904875063115406417706454079369576338460190775339499104522829 2
    [2, 2, 229, 331, 9923, 22303, 55375561, 292010161, 1608582317417214810130635352535801824283625580080564742616555593796775363039054605362655017772160887748612499490552428161762482617917902416636558184042356827836981572487811361331057]
    (by decide +kernel)
    (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons (by norm_num) (allP_cons prime_55375561 (allP_cons prime_292010161 (allP_cons prime_1608582317417214810130635352535801824283625580080564742616555593796775363039054605362655017772160887748612499490552428161762482617917902416636558184042356827836981572487811361331057 allP_nil)))))))))

theorem kill458 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ 458) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 458 * ∏ p ∈ P, p) :
    False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 458 → c ∈ ({3} : Finset ℕ) :=
    OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.prime_dvd_prime_pow (by norm_num)
  obtain ⟨-, -, -, -, -, -, S7, S8⟩ := OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.facts hP hK E
  have hQ : 1745376548298255875979192507374504750088219827931938208827516973981765722860972555354002702289104895588612885757598083846275425844450388650127389943613904875063115406417706454079369576338460190775339499104522829 ∈ P :=
    S7 1745376548298255875979192507374504750088219827931938208827516973981765722860972555354002702289104895588612885757598083846275425844450388650127389943613904875063115406417706454079369576338460190775339499104522829 prime_1745376548298255875979192507374504750088219827931938208827516973981765722860972555354002702289104895588612885757598083846275425844450388650127389943613904875063115406417706454079369576338460190775339499104522829 (by norm_num) (by simp) ⟨190390610, by decide +kernel⟩
  exact S8 5 (by norm_num) (by norm_num) (by simp) ⟨66460661142039879632752561757292291563438745370811350812195668292348500970518302001421468086094215485020463274649882263664704910906934921966966069814503390729048066145653009318621632410904200436486652038320911034447138, by decide +kernel⟩
    1745376548298255875979192507374504750088219827931938208827516973981765722860972555354002702289104895588612885757598083846275425844450388650127389943613904875063115406417706454079369576338460190775339499104522829 hQ ⟨349075309659651175195838501474900950017643965586387641765503394796353144572194511070800540457820979117722577151519616769255085168890077730025477988722780975012623081283541290815873915267692038155067899820904566, by decide +kernel⟩

end OMA.Helpers

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H2_R1.H1 := by
  refine ⟨0, fun n h hiff he _ => ?_⟩
  exact (OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H2_R1.kill_at h hiff
    (fun _ _ hP E => OMA.Helpers.kill458 hP (by rw [he] at E; exact E))).elim
