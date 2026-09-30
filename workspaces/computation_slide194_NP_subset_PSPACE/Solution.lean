import Mathlib.Computability.Language
import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Submission
import ChallengeDeps


































open Asymptotics
open Turing

universe u

namespace Autoform_Introduction_to_the_Theory_of_Computation_computation_slide194_NP_subset_PSPACE





namespace LocatedCfg

variable {Γ Λ : Type u} [Inhabited Γ]



end LocatedCfg





attribute [instance]
  DTM0.gammaInhabited DTM0.gammaFintype DTM0.gammaDecEq
  DTM0.stateInhabited DTM0.stateFintype DTM0.stateDecEq

namespace DTM0

variable {α : Type u}





















end DTM0



namespace DTM0

variable {α : Type u}





end DTM0









attribute [instance]
  NTM0.gammaInhabited NTM0.gammaFintype NTM0.gammaDecEq
  NTM0.stateInhabited NTM0.stateFintype NTM0.stateDecEq

namespace NTM0

variable {α : Type u}















end NTM0













section Slide194Statements

variable {α : Type u} [Fintype α] [DecidableEq α]









theorem slide194_relationships
    (t : ℕ → ℕ) (ht : ∀ n : ℕ, n ≤ t n) :
    (TIME α t ⊆ SPACE α t) ∧
      (SPACE α t ⊆ TIME_twoPowO α t) ∧
      (TIME_twoPowO α t = TIME_expUnion α t) := Submission.Autoform_Introduction_to_the_Theory_of_Computation_computation_slide194_NP_subset_PSPACE.slide194_relationships t ht




theorem slide194_P_subset_PSPACE :
    P α ⊆ PSPACE α := Submission.Autoform_Introduction_to_the_Theory_of_Computation_computation_slide194_NP_subset_PSPACE.slide194_P_subset_PSPACE





theorem slide194_NP_subset_PSPACE :
    NP α ⊆ PSPACE α := Submission.Autoform_Introduction_to_the_Theory_of_Computation_computation_slide194_NP_subset_PSPACE.slide194_NP_subset_PSPACE

end Slide194Statements

end Autoform_Introduction_to_the_Theory_of_Computation_computation_slide194_NP_subset_PSPACE
