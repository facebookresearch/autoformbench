import Mathlib

open scoped BigOperators Pointwise















namespace Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_7_1_10_freiman


abbrev Interval (L : ℕ) : Type :=
  ↑(Finset.Icc 1 L)


structure GeneralizedArithmeticProgression where
  dimension : ℕ
  lengths : Fin dimension → ℕ
  base : ℤ
  steps : Fin dimension → ℤ


abbrev GeneralizedArithmeticProgression.Domain (P : GeneralizedArithmeticProgression) : Type :=
  ∀ i : Fin P.dimension, Interval (P.lengths i)


def GeneralizedArithmeticProgression.toFun (P : GeneralizedArithmeticProgression) :
    P.Domain → ℤ :=
  fun x => P.base + ∑ i, ((x i).1 : ℤ) * P.steps i


def GeneralizedArithmeticProgression.carrier (P : GeneralizedArithmeticProgression) : Set ℤ :=
  Set.range P.toFun


def GeneralizedArithmeticProgression.volume (P : GeneralizedArithmeticProgression) : ℕ :=
  ∏ i, P.lengths i



end Autoform_Graph_Theory_and_Additive_Combinatorics_graph_theory_theorem_7_1_10_freiman
