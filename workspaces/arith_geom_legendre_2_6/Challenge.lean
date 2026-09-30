import ChallengeDeps

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_legendre_2_6

theorem legendre_2_6 (a b c : ℤ)
    (ha : SquarefreeInt a) (hb : SquarefreeInt b) (hc : SquarefreeInt c)
    (hcoprime : PairwiseCoprime3 a b c)
    (hsign : SignsNotAllSame a b c) :
    HasNonzeroRationalSolution a b c ↔ LegendreCongruencesSolvable a b c := by
  sorry
