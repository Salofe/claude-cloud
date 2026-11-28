import OMAReductions.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1

-- Step H1 of reduction SumOfThreeCubes.isSumOfThreeCubes_iff_mod_9.R1: the elementary direction.
-- A cube is 0 or 1 or -1 modulo 9, so a sum of three cubes is never 4 or 5 modulo 9; this is
-- SumOfThreeCubes.mod_9_of_isSumOfThreeCubes upstream.

theorem OMA.solution : OMA.R_SumOfThreeCubes_isSumOfThreeCubes_iff_mod_9_R1.H1 :=
  fun n hn => SumOfThreeCubes.mod_9_of_isSumOfThreeCubes n hn
