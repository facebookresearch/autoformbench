import ChallengeDeps
import Submission.Helpers

open CategoryTheory
open AlgebraicGeometry
open Autoform_Algebraic_Geometry_I_alg_geom_chow_lemma.AlgebraicGeometryI.ChowLemma

universe u


theorem chow_lemma (K : Type u) [Field K] [IsAlgClosed K]
    (X : Scheme) (πX : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper πX] :
    ∃ (Xtilde : Scheme) (πtilde : Xtilde ⟶ Spec (CommRingCat.of K))
      (f : Xtilde ⟶ X),
      IsIntegral Xtilde ∧
      IsProjectiveVarietyOver K Xtilde πtilde ∧
      IsBirationalMorphismOver πtilde πX f := by
  sorry

