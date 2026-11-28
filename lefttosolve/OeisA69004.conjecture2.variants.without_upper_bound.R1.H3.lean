import OMAReductions.R_OeisA69004_conjecture2_variants_without_upper_bound_R1

/-!
# Step H3 of the reduction OeisA69004.conjecture2.variants.without_upper_bound.R1

The three claimed equalities pi(2) = a(2), pi(10) = a(10) and 5 a(12) = pi(12) are finite
computations, checked by the kernel.
-/

theorem OMA.solution : OMA.R_OeisA69004_conjecture2_variants_without_upper_bound_R1.H3 := by
  unfold OMA.R_OeisA69004_conjecture2_variants_without_upper_bound_R1.H3 OeisA69004.a
  decide +kernel
