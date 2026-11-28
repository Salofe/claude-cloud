import OMAStatements.S_oeis_a207110

/-!
Proof of the two conjectures of OEIS A207110 (n X 7 binary arrays avoiding 0 0 0 and 0 1 1
horizontally and 0 0 1 and 1 1 0 vertically).

An array is good iff every row avoids the horizontal patterns (`RowOK`) and every three
consecutive rows `x, y, z` satisfy the vertical condition `V x y z` (`avoids_iff`). Removing the
first row gives a transfer recursion for the number `T m x y` of ways to continue the rows `x, y`
by `m` more rows: `T (m + 1) x y = Sum_{z, RowOK x and V x y z} T m y z`, and
`a (n + 2) = Sum_{x, y} T n x y`.

Exactly 25 rows satisfy `RowOK`; they are coded by `Fin 25` (`vrow`, codes in `codes`), and on
codes the condition `RowOK x and V x y z` becomes a bit test `Vt` (columns where `x` and `y`
agree must keep their value in `z`), checked once on all triples. For each pair of codes `(u, v)`,
`T m (vrow u) (vrow v) = Sum_{k < 8} tab u v k * choose m k` with an explicit table of Newton
coefficients `tab`: the case `m = 0` is `tab u v 0 = 1`, and the step follows from Pascal's rule
and the finite check `tab u v k + tab u v (k + 1) = Sum_{w, Vt u v w} tab v w k` (with
`tab u v 8 = 0`). Summing over the 625 pairs,
`a (n + 2) = 625 + 2774 C(n,1) + 5338 C(n,2) + 5454 C(n,3) + 3172 C(n,4) + 1066 C(n,5)
+ 202 C(n,6) + 18 C(n,7)`, a polynomial of degree 7 which also gives `a 1 = 25`. The recurrence
(an eighth difference) and the generating function follow.
-/

namespace OMA.Helpers

open OMA.S_oeis_a207110

def a207110_codes : List ℕ := [18, 20, 21, 36, 37, 41, 42, 73, 74, 82, 84, 85, 100, 101, 105, 106, 114, 116, 117, 121, 122, 124, 125, 126, 127]

/-- Newton coefficients: `tab[u][v][k]`. -/
def a207110_tabL : List (List (List ℕ)) := [
  [[1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 4, 5, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 7, 14, 11, 3, 0, 0, 0], [1, 12, 40, 57, 37, 9, 0, 0], [1, 10, 24, 24, 11, 2, 0, 0], [1, 6, 9, 5, 1, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 8, 19, 18, 6, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 8, 19, 19, 8, 1, 0, 0], [1, 14, 51, 81, 62, 21, 2, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 5, 10, 10, 5, 1, 0, 0]],
  [[1, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 4, 5, 2, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 4, 5, 2, 0, 0, 0, 0], [1, 4, 5, 2, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 9, 20, 16, 4, 0, 0, 0], [1, 15, 55, 86, 66, 25, 4, 0], [1, 13, 39, 49, 30, 9, 1, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 8, 22, 28, 17, 4, 0, 0], [1, 8, 19, 19, 8, 1, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 7, 15, 13, 4, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 9, 26, 34, 21, 5, 0, 0]],
  [[1, 2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 6, 9, 4, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 7, 14, 11, 3, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 9, 20, 16, 4, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 9, 19, 16, 6, 1, 0, 0], [1, 24, 111, 217, 221, 126, 39, 5], [1, 8, 19, 18, 6, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 14, 54, 93, 80, 33, 5, 0], [1, 7, 15, 13, 4, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 9, 26, 34, 21, 5, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0]],
  [[1, 2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 6, 12, 10, 3, 0, 0, 0], [1, 4, 5, 2, 0, 0, 0, 0], [1, 7, 13, 9, 2, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 9, 20, 16, 4, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 10, 29, 36, 20, 4, 0, 0], [1, 8, 17, 15, 6, 1, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 7, 15, 13, 4, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 9, 26, 34, 21, 5, 0, 0]],
  [[1, 4, 5, 2, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 4, 5, 2, 0, 0, 0, 0], [1, 9, 23, 23, 8, 0, 0, 0], [1, 12, 39, 53, 32, 7, 0, 0], [1, 9, 20, 16, 4, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 7, 12, 6, 0, 0, 0, 0], [1, 6, 12, 10, 3, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 6, 10, 6, 1, 0, 0, 0], [1, 16, 61, 98, 77, 30, 5, 0], [1, 7, 15, 13, 4, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 9, 26, 34, 21, 5, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0]],
  [[1, 2, 1, 0, 0, 0, 0, 0], [1, 4, 5, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 10, 27, 31, 16, 3, 0, 0], [1, 15, 54, 84, 64, 23, 3, 0], [1, 9, 20, 18, 7, 1, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 6, 12, 10, 3, 0, 0, 0], [1, 10, 27, 30, 14, 2, 0, 0], [1, 6, 10, 6, 1, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 9, 23, 25, 12, 2, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0]],
  [[1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 6, 9, 4, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 6, 9, 5, 1, 0, 0, 0], [1, 13, 37, 44, 26, 8, 1, 0], [1, 24, 109, 206, 199, 106, 31, 4], [1, 3, 2, 0, 0, 0, 0, 0], [1, 7, 12, 6, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 8, 17, 15, 6, 1, 0, 0], [1, 16, 57, 84, 59, 20, 3, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 9, 23, 25, 12, 2, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0]],
  [[1, 3, 3, 1, 0, 0, 0, 0], [1, 4, 5, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 6, 12, 10, 3, 0, 0, 0], [1, 4, 5, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 7, 14, 11, 3, 0, 0, 0], [1, 10, 24, 24, 11, 2, 0, 0], [1, 6, 9, 5, 1, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 9, 23, 25, 12, 2, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0]],
  [[1, 2, 1, 0, 0, 0, 0, 0], [1, 4, 5, 2, 0, 0, 0, 0], [1, 7, 14, 11, 3, 0, 0, 0], [1, 4, 5, 2, 0, 0, 0, 0], [1, 9, 23, 23, 8, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 9, 19, 16, 6, 1, 0, 0], [1, 17, 59, 84, 58, 20, 3, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 9, 23, 25, 12, 2, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0]],
  [[1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 7, 13, 9, 2, 0, 0, 0], [1, 12, 39, 53, 32, 7, 0, 0], [1, 10, 27, 31, 16, 3, 0, 0], [1, 6, 9, 5, 1, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 4, 5, 2, 0, 0, 0, 0], [1, 7, 16, 15, 5, 0, 0, 0], [1, 7, 13, 9, 2, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 6, 10, 6, 1, 0, 0, 0], [1, 11, 30, 33, 15, 2, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0]],
  [[1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 9, 20, 16, 4, 0, 0, 0], [1, 15, 54, 84, 64, 23, 3, 0], [1, 13, 37, 44, 26, 8, 1, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 10, 27, 31, 16, 3, 0, 0], [1, 9, 20, 18, 7, 1, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 6, 12, 10, 3, 0, 0, 0], [1, 6, 10, 6, 1, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 7, 15, 13, 4, 0, 0, 0]],
  [[1, 5, 7, 3, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 9, 20, 16, 4, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 9, 20, 18, 7, 1, 0, 0], [1, 24, 109, 206, 199, 106, 31, 4], [1, 1, 0, 0, 0, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 6, 9, 5, 1, 0, 0, 0], [1, 17, 61, 92, 69, 26, 4, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 11, 32, 39, 21, 4, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 7, 15, 13, 4, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0]],
  [[1, 7, 14, 11, 3, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 9, 20, 16, 4, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 4, 5, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 7, 14, 11, 3, 0, 0, 0], [1, 6, 9, 5, 1, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 7, 15, 13, 4, 0, 0, 0]],
  [[1, 12, 40, 57, 37, 9, 0, 0], [1, 9, 20, 16, 4, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 7, 12, 6, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 7, 16, 15, 5, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 4, 5, 2, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 12, 34, 39, 20, 4, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 7, 15, 13, 4, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0]],
  [[1, 10, 24, 24, 11, 2, 0, 0], [1, 15, 55, 86, 66, 25, 4, 0], [1, 9, 19, 16, 6, 1, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 7, 13, 9, 2, 0, 0, 0], [1, 10, 27, 31, 16, 3, 0, 0], [1, 6, 9, 5, 1, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 4, 5, 2, 0, 0, 0, 0], [1, 7, 13, 9, 2, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 7, 13, 9, 2, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0]],
  [[1, 6, 9, 5, 1, 0, 0, 0], [1, 13, 39, 49, 30, 9, 1, 0], [1, 24, 111, 217, 221, 126, 39, 5], [1, 3, 2, 0, 0, 0, 0, 0], [1, 7, 12, 6, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 9, 20, 18, 7, 1, 0, 0], [1, 17, 61, 92, 69, 26, 4, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 6, 9, 5, 1, 0, 0, 0], [1, 12, 32, 34, 16, 3, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 7, 13, 9, 2, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0]],
  [[1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 8, 19, 18, 6, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 6, 12, 10, 3, 0, 0, 0], [1, 6, 12, 10, 3, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 7, 14, 11, 3, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 4, 5, 2, 0, 0, 0, 0], [1, 4, 5, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 8, 15, 10, 2, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0]],
  [[1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 10, 27, 30, 14, 2, 0, 0], [1, 8, 17, 15, 6, 1, 0, 0], [1, 10, 24, 24, 11, 2, 0, 0], [1, 9, 19, 16, 6, 1, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 7, 13, 9, 2, 0, 0, 0], [1, 6, 9, 5, 1, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 4, 5, 2, 0, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0]],
  [[1, 8, 19, 18, 6, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 6, 10, 6, 1, 0, 0, 0], [1, 16, 57, 84, 59, 20, 3, 0], [1, 6, 9, 5, 1, 0, 0, 0], [1, 17, 59, 84, 58, 20, 3, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 12, 32, 34, 16, 3, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 8, 16, 12, 3, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0]],
  [[1, 4, 6, 4, 1, 0, 0, 0], [1, 8, 22, 28, 17, 4, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 10, 29, 36, 20, 4, 0, 0], [1, 6, 10, 6, 1, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 6, 12, 10, 3, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 7, 14, 11, 3, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 4, 5, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 5, 6, 2, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0]],
  [[1, 3, 3, 1, 0, 0, 0, 0], [1, 8, 19, 19, 8, 1, 0, 0], [1, 14, 54, 93, 80, 33, 5, 0], [1, 8, 17, 15, 6, 1, 0, 0], [1, 16, 61, 98, 77, 30, 5, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 6, 10, 6, 1, 0, 0, 0], [1, 11, 32, 39, 21, 4, 0, 0], [1, 6, 9, 5, 1, 0, 0, 0], [1, 12, 34, 39, 20, 4, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 8, 16, 12, 3, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 6, 2, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0]],
  [[1, 8, 19, 19, 8, 1, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 7, 15, 13, 4, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 7, 15, 13, 4, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 6, 10, 6, 1, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 4, 4, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0]],
  [[1, 14, 51, 81, 62, 21, 2, 0], [1, 7, 15, 13, 4, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 7, 15, 13, 4, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 9, 23, 25, 12, 2, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 9, 23, 25, 12, 2, 0, 0], [1, 11, 30, 33, 15, 2, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 7, 13, 9, 2, 0, 0, 0], [1, 8, 15, 10, 2, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 5, 6, 2, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0]],
  [[1, 4, 6, 4, 1, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 9, 26, 34, 21, 5, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 9, 26, 34, 21, 5, 0, 0], [1, 9, 23, 25, 12, 2, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 9, 23, 25, 12, 2, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 7, 15, 13, 4, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 7, 15, 13, 4, 0, 0, 0], [1, 7, 13, 9, 2, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 5, 6, 2, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0]],
  [[1, 5, 10, 10, 5, 1, 0, 0], [1, 9, 26, 34, 21, 5, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 9, 26, 34, 21, 5, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 4, 6, 4, 1, 0, 0, 0], [1, 7, 15, 13, 4, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 7, 15, 13, 4, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 3, 3, 1, 0, 0, 0, 0], [1, 5, 7, 3, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 2, 1, 0, 0, 0, 0, 0], [1, 3, 2, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

def a207110_code (u : Fin 25) : ℕ := a207110_codes.getD u.val 0

def a207110_tab (u v : Fin 25) (k : ℕ) : ℕ := ((a207110_tabL.getD u.val []).getD v.val []).getD k 0

def a207110_Vt (u v w : Fin 25) : Bool :=
  Nat.land (Nat.xor (a207110_code v) (a207110_code w))
    (127 - Nat.xor (a207110_code u) (a207110_code v)) == 0

def a207110_S (u v : Fin 25) (k : ℕ) : ℕ :=
  ((List.finRange 25).map (fun w => if a207110_Vt u v w then a207110_tab v w k else 0)).sum

set_option maxRecDepth 100000 in
theorem a207110_check : ∀ u v : Fin 25, ∀ k : Fin 8,
    a207110_tab u v k + a207110_tab u v (k + 1) = a207110_S u v k := by
  decide +kernel

/-- A row of the array. -/
abbrev a207110_Row := Fin 7 → Fin 2

/-- The row with code `u` (bits of the code, most significant first). -/
def a207110_vrow (u : Fin 25) : a207110_Row :=
  fun j => ⟨a207110_code u / 2 ^ (6 - j.val) % 2, Nat.mod_lt _ (by norm_num)⟩

/-- The horizontal condition on one row. -/
def a207110_RowOK (r : a207110_Row) : Prop :=
  ∀ j : Fin 5,
    ((r ⟨j.val, by omega⟩ : ℕ), (r ⟨j.val + 1, by omega⟩ : ℕ), (r ⟨j.val + 2, by omega⟩ : ℕ))
      ≠ (0, 0, 0) ∧
    ((r ⟨j.val, by omega⟩ : ℕ), (r ⟨j.val + 1, by omega⟩ : ℕ), (r ⟨j.val + 2, by omega⟩ : ℕ))
      ≠ (0, 1, 1)

instance (r : a207110_Row) : Decidable (a207110_RowOK r) := by
  unfold a207110_RowOK
  infer_instance

/-- The vertical condition on three consecutive rows. -/
def a207110_V (x y z : a207110_Row) : Prop :=
  ∀ j : Fin 7, ((x j : ℕ), (y j : ℕ), (z j : ℕ)) ≠ (0, 0, 1) ∧
    ((x j : ℕ), (y j : ℕ), (z j : ℕ)) ≠ (1, 1, 0)

instance (x y z : a207110_Row) : Decidable (a207110_V x y z) := by
  unfold a207110_V
  infer_instance

/-- Every row satisfies the horizontal condition and every three consecutive rows the vertical
one. -/
def a207110_Good {m : ℕ} (A : Fin m → a207110_Row) : Prop :=
  (∀ i, a207110_RowOK (A i)) ∧
    ∀ (i : ℕ) (h : i + 2 < m),
      a207110_V (A ⟨i, by omega⟩) (A ⟨i + 1, by omega⟩) (A ⟨i + 2, h⟩)

theorem a207110_get_eq {m : ℕ} (A : Fin m → a207110_Row) {i j : ℕ} (hi : i < m) (hj : j < 7) :
    get A i j = (A ⟨i, hi⟩ ⟨j, hj⟩ : ℕ) := dif_pos ⟨hi, hj⟩

theorem a207110_avoids_iff {m : ℕ} (A : Fin m → a207110_Row) :
    avoids A = true ↔ a207110_Good A := by
  unfold avoids a207110_Good a207110_RowOK a207110_V
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i hi j => ?_⟩
    · have hj := j.isLt
      have := h1 i.val i.isLt j.val (by omega)
      rwa [a207110_get_eq A i.isLt (by omega), a207110_get_eq A i.isLt (by omega),
        a207110_get_eq A i.isLt (by omega)] at this
    · have hj := j.isLt
      have := h2 i (by omega) j.val hj
      rwa [a207110_get_eq A (by omega) hj, a207110_get_eq A (by omega) hj,
        a207110_get_eq A hi hj] at this
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_⟩
    · have := h1 ⟨i, hi⟩ ⟨j, by omega⟩
      rwa [a207110_get_eq A hi (by omega), a207110_get_eq A hi (by omega),
        a207110_get_eq A hi (by omega)]
    · have := h2 i (by omega) ⟨j, hj⟩
      rwa [a207110_get_eq A (by omega) hj, a207110_get_eq A (by omega) hj,
        a207110_get_eq A (by omega) hj]

theorem a207110_good_cons {m : ℕ} (x : a207110_Row) (B : Fin (m + 2) → a207110_Row) :
    a207110_Good (Fin.cons x B : Fin (m + 3) → a207110_Row) ↔
      a207110_RowOK x ∧ a207110_V x (B ⟨0, by omega⟩) (B ⟨1, by omega⟩) ∧ a207110_Good B := by
  constructor
  · rintro ⟨h1, h2⟩
    have h20 := h2 0 (by omega)
    exact ⟨h1 0, h20, fun i => h1 i.succ, fun i hi => h2 (i + 1) (by omega)⟩
  · rintro ⟨hx, hv, h1, h2⟩
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hx
      · simpa using h1 i
    · cases i with
      | zero => exact hv
      | succ i => exact h2 i (by omega)

/-- The number of ways to continue the rows `x, y` by `m` more rows. -/
noncomputable def a207110_T (m : ℕ) (x y : a207110_Row) : ℕ := by
  classical
  exact ∑ B : Fin m → a207110_Row,
    if a207110_Good (Fin.cons x (Fin.cons y B) : Fin (m + 2) → a207110_Row) then 1 else 0

theorem a207110_T_zero (x y : a207110_Row) :
    a207110_T 0 x y = if a207110_RowOK x ∧ a207110_RowOK y then 1 else 0 := by
  classical
  unfold a207110_T
  rw [Fintype.sum_unique]
  refine if_congr ⟨fun h => ⟨h.1 0, h.1 1⟩, fun h => ⟨fun i => ?_, fun i hi => ?_⟩⟩ rfl rfl
  · refine Fin.cases ?_ (fun i => ?_) i
    · simpa using h.1
    · refine Fin.cases ?_ (fun i => i.elim0) i
      simpa using h.2
  · omega

theorem a207110_T_succ (m : ℕ) (x y : a207110_Row) :
    a207110_T (m + 1) x y =
      ∑ z : a207110_Row, if a207110_RowOK x ∧ a207110_V x y z then a207110_T m y z else 0 := by
  classical
  unfold a207110_T
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => a207110_Row).symm _
    (fun p => if a207110_Good (Fin.cons x (Fin.cons y (Fin.cons p.1 p.2)) :
      Fin (m + 3) → a207110_Row) then 1 else 0) (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hv : a207110_RowOK x ∧ a207110_V x y z
  · rw [if_pos hv]
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    rw [a207110_good_cons]
    exact ⟨fun h => h.2.2, fun h => ⟨hv.1, hv.2, h⟩⟩
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [a207110_good_cons]
    exact fun h => hv ⟨h.1, h.2.1⟩

theorem a207110_T_bad (m : ℕ) (x y : a207110_Row) (h : ¬ (a207110_RowOK x ∧ a207110_RowOK y)) :
    a207110_T m x y = 0 := by
  classical
  unfold a207110_T
  refine Finset.sum_eq_zero fun B _ => if_neg fun hg => h ⟨hg.1 0, hg.1 1⟩

theorem a207110_a_eq (n : ℕ) :
    a (n + 2) = ((∑ x : a207110_Row, ∑ y : a207110_Row, a207110_T n x y : ℕ) : ℤ) := by
  classical
  have h1 : (Finset.univ.filter (fun A : Fin (n + 2) → Fin 7 → Fin 2 => avoids A)).card =
      ∑ A : Fin (n + 2) → a207110_Row, if a207110_Good A then 1 else 0 := by
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun A _ => if_congr (a207110_avoids_iff A) rfl rfl
  unfold a
  rw [h1]
  apply congrArg (Nat.cast : ℕ → ℤ)
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => a207110_Row).symm _
    (fun p => if a207110_Good (Fin.cons p.1 p.2 : Fin (n + 2) → a207110_Row) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => a207110_Row).symm _
    (fun p => if a207110_Good (Fin.cons x (Fin.cons p.1 p.2) : Fin (n + 2) → a207110_Row)
      then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  rfl

theorem a207110_vrow_inj : Function.Injective a207110_vrow := by
  decide +kernel

theorem a207110_rowOK_iff : ∀ r : a207110_Row, a207110_RowOK r ↔ ∃ u, a207110_vrow u = r := by
  decide +kernel

theorem a207110_sum_rows (f : a207110_Row → ℕ) (hf : ∀ x, ¬ a207110_RowOK x → f x = 0) :
    ∑ x, f x = ∑ u : Fin 25, f (a207110_vrow u) := by
  classical
  rw [← Finset.sum_filter_of_ne (p := a207110_RowOK) (fun x _ hx => by
    by_contra h
    exact hx (hf x h))]
  have e : Finset.univ.filter a207110_RowOK = Finset.univ.map ⟨a207110_vrow, a207110_vrow_inj⟩ := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    exact a207110_rowOK_iff r
  rw [e, Finset.sum_map]
  rfl

theorem a207110_vrow_ok : ∀ u, a207110_RowOK (a207110_vrow u) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem a207110_V_iff : ∀ u v w : Fin 25,
    (a207110_RowOK (a207110_vrow u) ∧
      a207110_V (a207110_vrow u) (a207110_vrow v) (a207110_vrow w)) ↔ a207110_Vt u v w = true := by
  decide +kernel

theorem a207110_tab_zero : ∀ u v : Fin 25, a207110_tab u v 0 = 1 := by
  decide +kernel

theorem a207110_tab_eight (u v : Fin 25) : a207110_tab u v 8 = 0 := by
  revert u v
  decide +kernel

theorem a207110_T_step (m : ℕ) (u v : Fin 25) :
    a207110_T (m + 1) (a207110_vrow u) (a207110_vrow v) =
      ∑ w : Fin 25, if a207110_Vt u v w then
        a207110_T m (a207110_vrow v) (a207110_vrow w) else 0 := by
  classical
  rw [a207110_T_succ, a207110_sum_rows]
  · refine Finset.sum_congr rfl fun w _ => if_congr (a207110_V_iff u v w) rfl rfl
  · intro z hz
    split_ifs
    · exact a207110_T_bad m _ _ (fun h => hz h.2)
    · rfl

theorem a207110_T_closed (m : ℕ) : ∀ u v : Fin 25,
    a207110_T m (a207110_vrow u) (a207110_vrow v) =
      ∑ k ∈ Finset.range 8, a207110_tab u v k * m.choose k := by
  induction m with
  | zero =>
    intro u v
    rw [a207110_T_zero, if_pos ⟨a207110_vrow_ok u, a207110_vrow_ok v⟩]
    simp [Finset.sum_range_succ, a207110_tab_zero]
  | succ m ih =>
    intro u v
    rw [a207110_T_step]
    simp only [ih]
    have e1 : ∀ w : Fin 25, (if a207110_Vt u v w then
        ∑ k ∈ Finset.range 8, a207110_tab v w k * m.choose k else 0) =
        ∑ k ∈ Finset.range 8, (if a207110_Vt u v w then a207110_tab v w k else 0) * m.choose k := by
      intro w
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun w _ => e1 w, Finset.sum_comm]
    have e2 : ∀ k ∈ Finset.range 8,
        ∑ w : Fin 25, (if a207110_Vt u v w then a207110_tab v w k else 0) * m.choose k =
        (a207110_tab u v k + a207110_tab u v (k + 1)) * m.choose k := by
      intro k hk
      rw [← Finset.sum_mul]
      have hc : a207110_tab u v k + a207110_tab u v (k + 1) = a207110_S u v k :=
        a207110_check u v ⟨k, Finset.mem_range.mp hk⟩
      have hS : (∑ w : Fin 25, if a207110_Vt u v w then a207110_tab v w k else 0) =
          a207110_S u v k := by
        rw [a207110_S, Fin.sum_univ_def]
      rw [hS, ← hc]
    rw [Finset.sum_congr rfl e2]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_succ_succ',
      Nat.choose_zero_right]
    rw [a207110_tab_eight]
    ring

theorem a207110_D : ∀ k : Fin 8, (∑ u : Fin 25, ∑ v : Fin 25, a207110_tab u v k) =
    [625, 2774, 5338, 5454, 3172, 1066, 202, 18].getD k 0 := by
  simp only [Fin.sum_univ_def]
  decide +kernel

theorem a207110_sum_closed (n : ℕ) :
    (∑ x : a207110_Row, ∑ y : a207110_Row, a207110_T n x y) =
      ∑ k ∈ Finset.range 8, (∑ u : Fin 25, ∑ v : Fin 25, a207110_tab u v k) * n.choose k := by
  rw [a207110_sum_rows (fun x => ∑ y, a207110_T n x y)
    (fun x hx => Finset.sum_eq_zero fun y _ => a207110_T_bad n x y (fun h => hx h.1))]
  rw [Finset.sum_congr rfl fun u _ => a207110_sum_rows (fun y => a207110_T n (a207110_vrow u) y)
    (fun y hy => a207110_T_bad n _ y (fun h => hy h.2))]
  simp only [a207110_T_closed, Finset.sum_mul]
  calc (∑ u : Fin 25, ∑ v : Fin 25, ∑ k ∈ Finset.range 8, a207110_tab u v k * n.choose k)
      = ∑ u : Fin 25, ∑ k ∈ Finset.range 8, ∑ v : Fin 25, a207110_tab u v k * n.choose k :=
        Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ = ∑ k ∈ Finset.range 8, ∑ u : Fin 25, ∑ v : Fin 25, a207110_tab u v k * n.choose k :=
        Finset.sum_comm

theorem a207110_a_add_two (n : ℕ) :
    a (n + 2) = 625 + 2774 * n.choose 1 + 5338 * n.choose 2 + 5454 * n.choose 3
      + 3172 * n.choose 4 + 1066 * n.choose 5 + 202 * n.choose 6 + 18 * n.choose 7 := by
  rw [a207110_a_eq, a207110_sum_closed]
  have d0 : (∑ u : Fin 25, ∑ v : Fin 25, a207110_tab u v 0) = 625 := a207110_D 0
  have d1 : (∑ u : Fin 25, ∑ v : Fin 25, a207110_tab u v 1) = 2774 := a207110_D 1
  have d2 : (∑ u : Fin 25, ∑ v : Fin 25, a207110_tab u v 2) = 5338 := a207110_D 2
  have d3 : (∑ u : Fin 25, ∑ v : Fin 25, a207110_tab u v 3) = 5454 := a207110_D 3
  have d4 : (∑ u : Fin 25, ∑ v : Fin 25, a207110_tab u v 4) = 3172 := a207110_D 4
  have d5 : (∑ u : Fin 25, ∑ v : Fin 25, a207110_tab u v 5) = 1066 := a207110_D 5
  have d6 : (∑ u : Fin 25, ∑ v : Fin 25, a207110_tab u v 6) = 202 := a207110_D 6
  have d7 : (∑ u : Fin 25, ∑ v : Fin 25, a207110_tab u v 7) = 18 := a207110_D 7
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, d0, d1, d2, d3, d4, d5, d6, d7,
    Nat.choose_zero_right]
  push_cast
  ring

theorem a207110_choose (n : ℕ) :
    ((n.choose 1 : ℕ) : ℚ) = n ∧
    ((n.choose 2 : ℕ) : ℚ) = n * (n - 1) / 2 ∧
    ((n.choose 3 : ℕ) : ℚ) = n * (n - 1) * (n - 2) / 6 ∧
    ((n.choose 4 : ℕ) : ℚ) = n * (n - 1) * (n - 2) * (n - 3) / 24 ∧
    ((n.choose 5 : ℕ) : ℚ) = n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 120 ∧
    ((n.choose 6 : ℕ) : ℚ) = n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) / 720 ∧
    ((n.choose 7 : ℕ) : ℚ) =
      n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) * (n - 6) / 5040 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih
    rw [Nat.choose_succ_succ' n 0, Nat.choose_succ_succ' n 1, Nat.choose_succ_succ' n 2,
      Nat.choose_succ_succ' n 3, Nat.choose_succ_succ' n 4, Nat.choose_succ_succ' n 5,
      Nat.choose_succ_succ' n 6]
    push_cast
    rw [h1, h2, h3, h4, h5, h6, h7, Nat.choose_zero_right]
    push_cast
    refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, by ring⟩

/-- The polynomial giving `a n` for `n ≥ 1` (in terms of `m = n - 2`). -/
def a207110_P (m : ℚ) : ℚ :=
  625 + 2774 * m + 5338 * (m * (m - 1) / 2) + 5454 * (m * (m - 1) * (m - 2) / 6)
    + 3172 * (m * (m - 1) * (m - 2) * (m - 3) / 24)
    + 1066 * (m * (m - 1) * (m - 2) * (m - 3) * (m - 4) / 120)
    + 202 * (m * (m - 1) * (m - 2) * (m - 3) * (m - 4) * (m - 5) / 720)
    + 18 * (m * (m - 1) * (m - 2) * (m - 3) * (m - 4) * (m - 5) * (m - 6) / 5040)

theorem a207110_a_one : a 1 = 25 := by
  decide +kernel

theorem a207110_poly (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = a207110_P ((n : ℚ) - 2) := by
  rcases n with _ | _ | m
  · omega
  · rw [a207110_a_one]
    unfold a207110_P
    norm_num
  · rw [a207110_a_add_two]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := a207110_choose m
    push_cast
    rw [h1, h2, h3, h4, h5, h6, h7]
    unfold a207110_P
    ring

theorem a207110_rec (n : ℕ) (hn : 9 ≤ n) :
    (a n : ℚ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4)
      + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  rw [a207110_poly n (by omega), a207110_poly (n - 1) (by omega), a207110_poly (n - 2) (by omega),
    a207110_poly (n - 3) (by omega), a207110_poly (n - 4) (by omega),
    a207110_poly (n - 5) (by omega), a207110_poly (n - 6) (by omega),
    a207110_poly (n - 7) (by omega), a207110_poly (n - 8) (by omega)]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  rw [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega,
    show m + 9 - 3 = m + 6 by omega, show m + 9 - 4 = m + 5 by omega,
    show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega,
    show m + 9 - 7 = m + 2 by omega, show m + 9 - 8 = m + 1 by omega]
  unfold a207110_P
  push_cast
  ring

theorem a207110_val (n : ℕ) (hn : 1 ≤ n) (v : ℚ) (h : a207110_P ((n : ℚ) - 2) = v) :
    (a n : ℚ) = v := by
  rw [a207110_poly n hn, h]

end OMA.Helpers

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a207110.main := by
  refine ⟨?_, OMA.Helpers.a207110_rec⟩
  set p : PowerSeries ℚ :=
    PowerSeries.mk (fun n => if n < 1 then 0 else (OMA.S_oeis_a207110.a n : ℚ)) with hp
  have e1 : p * (1 - X) ^ 8 =
      p - PowerSeries.C (8 : ℚ) * (p * X ^ 1) + PowerSeries.C (28 : ℚ) * (p * X ^ 2)
        - PowerSeries.C (56 : ℚ) * (p * X ^ 3) + PowerSeries.C (70 : ℚ) * (p * X ^ 4)
        - PowerSeries.C (56 : ℚ) * (p * X ^ 5) + PowerSeries.C (28 : ℚ) * (p * X ^ 6)
        - PowerSeries.C (8 : ℚ) * (p * X ^ 7) + p * X ^ 8 := by
    simp only [map_ofNat]
    ring
  have e2 : (X * (25 + 425 * X - 901 * X ^ 2 + 419 * X ^ 3 + 249 * X ^ 4 - 269 * X ^ 5
      + 79 * X ^ 6 - 9 * X ^ 7) : PowerSeries ℚ) =
      PowerSeries.C (25 : ℚ) * X ^ 1 + PowerSeries.C (425 : ℚ) * X ^ 2
        - PowerSeries.C (901 : ℚ) * X ^ 3 + PowerSeries.C (419 : ℚ) * X ^ 4
        + PowerSeries.C (249 : ℚ) * X ^ 5 - PowerSeries.C (269 : ℚ) * X ^ 6
        + PowerSeries.C (79 : ℚ) * X ^ 7 - PowerSeries.C (9 : ℚ) * X ^ 8 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', hp, PowerSeries.coeff_mk]
  have v1 := OMA.Helpers.a207110_val 1 (by norm_num) 25 (by unfold OMA.Helpers.a207110_P; norm_num)
  have v2 := OMA.Helpers.a207110_val 2 (by norm_num) 625
    (by unfold OMA.Helpers.a207110_P; norm_num)
  have v3 := OMA.Helpers.a207110_val 3 (by norm_num) 3399
    (by unfold OMA.Helpers.a207110_P; norm_num)
  have v4 := OMA.Helpers.a207110_val 4 (by norm_num) 11511
    (by unfold OMA.Helpers.a207110_P; norm_num)
  have v5 := OMA.Helpers.a207110_val 5 (by norm_num) 30415
    (by unfold OMA.Helpers.a207110_P; norm_num)
  have v6 := OMA.Helpers.a207110_val 6 (by norm_num) 68737
    (by unfold OMA.Helpers.a207110_P; norm_num)
  have v7 := OMA.Helpers.a207110_val 7 (by norm_num) 139341
    (by unfold OMA.Helpers.a207110_P; norm_num)
  have v8 := OMA.Helpers.a207110_val 8 (by norm_num) 260597
    (by unfold OMA.Helpers.a207110_P; norm_num)
  by_cases hk : k < 9
  · interval_cases k <;> simp [v1, v2, v3, v4, v5, v6, v7, v8] <;> norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 9 := ⟨k - 9, by omega⟩
    have hr := OMA.Helpers.a207110_rec (j + 9) (by omega)
    simp only [show ¬ (j + 9 < 1) by omega, if_false, show 1 ≤ j + 9 by omega,
      show 2 ≤ j + 9 by omega, show 3 ≤ j + 9 by omega, show 4 ≤ j + 9 by omega,
      show 5 ≤ j + 9 by omega, show 6 ≤ j + 9 by omega, show 7 ≤ j + 9 by omega,
      show 8 ≤ j + 9 by omega, if_true, show ¬ (j + 9 = 1) by omega,
      show ¬ (j + 9 = 2) by omega, show ¬ (j + 9 = 3) by omega, show ¬ (j + 9 = 4) by omega,
      show ¬ (j + 9 = 5) by omega, show ¬ (j + 9 = 6) by omega, show ¬ (j + 9 = 7) by omega,
      show ¬ (j + 9 = 8) by omega, show ¬ (j + 9 - 1 < 1) by omega,
      show ¬ (j + 9 - 2 < 1) by omega, show ¬ (j + 9 - 3 < 1) by omega,
      show ¬ (j + 9 - 4 < 1) by omega, show ¬ (j + 9 - 5 < 1) by omega,
      show ¬ (j + 9 - 6 < 1) by omega, show ¬ (j + 9 - 7 < 1) by omega,
      show ¬ (j + 9 - 8 < 1) by omega]
    rw [hr]
    ring
