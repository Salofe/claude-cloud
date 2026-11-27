import OMAReductions.R_SternPrime_isSternPrime_iff_R1

-- Step H2 of reduction SternPrime.isSternPrime_iff.R1: the eight known Stern primes are Stern primes.
-- This is the finite verification already carried out upstream in
-- SternPrime.isSternPrime_known_examples (a kernel computation); we transport it from the
-- list form to the set form of the step.

theorem OMA.solution : OMA.R_SternPrime_isSternPrime_iff_R1.H2 := by
  intro q hq
  apply SternPrime.isSternPrime_known_examples
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
