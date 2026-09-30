import ChallengeDeps
import Submission

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_rabin_3_7

theorem rabin_3_7 (F : Type*) [Field F] [Fintype F]
    (hq_odd : Odd (Fintype.card F))
    {α β : F} (hαβ : α ≠ β) :
    (RabinDifferentTypeDeltas F α β).card = finiteFieldHalfExponent F := by
  exact Submission.rabin_3_7 F hq_odd hαβ
