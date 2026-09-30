


import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Prod
import Mathlib.Data.Finsupp.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Submission.Helpers
import ChallengeDeps






















namespace Submission

open _root_.Autoform_Noncommutative_Algebra_noncomm_alg_proposition_8_5_universal.FgProjectiveModule
open _root_.Autoform_Noncommutative_Algebra_noncomm_alg_proposition_8_5_universal
open _root_.Autoform_Noncommutative_Algebra_noncomm_alg_proposition_8_5_universal.TraceRelationIndex
open _root_.Autoform_Noncommutative_Algebra_noncomm_alg_proposition_8_5_universal.TraceMap
open _root_.Autoform_Noncommutative_Algebra_noncomm_alg_proposition_8_5_universal.TraceGenerator
universe u v w

namespace Autoform_Noncommutative_Algebra_noncomm_alg_proposition_8_5_universal

noncomputable section







attribute [instance] FgProjectiveModule.isAddCommGroup
attribute [instance] FgProjectiveModule.isModule
attribute [instance] FgProjectiveModule.isFinite
attribute [instance] FgProjectiveModule.isProjective


























theorem proposition_8_5
    (R : Type u) [Ring R] :
    Nonempty (PresentedTraceGroup R ≃+ Cocenter R) := by
  sorry






theorem proposition_8_5_universal
    (R : Type u) [Ring R] :
    ∃ τ : TraceMap R (Cocenter R),
      IsUniversalTraceTarget.{u, u, w} R (Cocenter R) τ := by
  sorry

end

end Autoform_Noncommutative_Algebra_noncomm_alg_proposition_8_5_universal

end Submission
