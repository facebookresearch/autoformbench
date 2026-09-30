import ChallengeDeps
import Submission

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_geometric_group_law_23_19_divisorClass
open scoped BigOperators

universe u

theorem geometric_group_law_23_19_divisorClass {k : Type u} [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (O P Q R S : W.toProjective.Point)
    (hO : IsPointAtInfinity O)
    (hR : IsThirdIntersectionPointOnSecantTangent W P Q R)
    (hS : IsGeometricNegation W O R S) :
    P + Q = S := by
  exact Submission.geometric_group_law_23_19_divisorClass W O P Q R S hO hR hS
