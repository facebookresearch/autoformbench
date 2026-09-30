import ChallengeDeps
import Submission

open Autoform_Buildings_and_Classical_Groups_buildings_negativeCurvatureInequality

universe uV uP uι uW

variable {ι : Type uι} [Fintype ι]
variable {M : CoxeterMatrix ι}
variable {W : Type uW} [Group W]
variable (X : AffineBuildingWithCanonicalMetric ι M W)

theorem negativeCurvatureInequality {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (x y z : X.Point) :
    dist z (X.affineCombination t x y) ^ 2 ≤
      t * dist z x ^ 2 + (1 - t) * dist z y ^ 2 -
        t * (1 - t) * dist x y ^ 2 := by
  apply Submission.negativeCurvatureInequality <;> assumption
