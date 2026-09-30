import ChallengeDeps
import Submission

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_birationalEquivalent_iff_functionFields_isomorphic

variable {k : Type*} [Field k]

theorem birationalEquivalent_iff_functionFields_isomorphic (X Y : AffineVarietyOver k) :
    BirationalEquivalent X Y ↔ FunctionFieldsIsomorphic X Y := by
  exact Submission.birationalEquivalent_iff_functionFields_isomorphic X Y
