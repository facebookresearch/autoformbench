import Mathlib

noncomputable section

open Set Metric MeromorphicOn
open scoped BigOperators

namespace Autoform_Functions_of_a_Complex_Variable_complex_var_Rouche

abbrev ClosedUnitDisc : Type :=
  { z : ℂ // ‖z‖ ≤ (1 : ℝ) }

def openUnitDisc : Set ClosedUnitDisc :=
  { z : ClosedUnitDisc | ‖(z : ℂ)‖ < (1 : ℝ) }

def circleToClosedUnitDisc (ζ : Circle) : ClosedUnitDisc :=
  ⟨(ζ : ℂ), by
    exact le_of_eq (Circle.norm_coe ζ)
  ⟩











structure FilledCurve where
  map : ClosedUnitDisc → ℂ
  continuous_map : Continuous map
  injective_map : Function.Injective map

instance instCoeFunFilledCurve : CoeFun FilledCurve (fun _ => ClosedUnitDisc → ℂ) where
  coe J := J.map


def filled (J : FilledCurve) : Set ℂ :=
  Set.range J.map





def interior (J : FilledCurve) : Set ℂ :=
  J.map '' openUnitDisc

def boundaryMap (J : FilledCurve) : Circle → ℂ :=
  fun ζ : Circle => J.map (circleToClosedUnitDisc ζ)

def curve (J : FilledCurve) : Set ℂ :=
  Set.range (boundaryMap J)

instance instCompactSpaceClosedUnitDisc : CompactSpace ClosedUnitDisc := by
  rw [← isCompact_univ_iff]
  rw [Subtype.isCompact_iff]
  convert (isCompact_closedBall (0 : ℂ) (1 : ℝ)) using 1
  ext z
  simp [ClosedUnitDisc, Metric.closedBall, dist_eq_norm]

theorem isCompact_filled (J : FilledCurve) : IsCompact (filled J) := by
  simpa [filled] using isCompact_range J.continuous_map

def IsRegion (Ω : Set ℂ) : Prop :=
  IsOpen Ω ∧ IsPreconnected Ω

def zeroCount {Ω : Set ℂ}
    (D : Function.locallyFinsuppWithin Ω ℤ) (inside : Finset ℂ) : ℤ :=
  ∑ a ∈ inside, (D a)⁺

def divisorSupportOn {Ω : Set ℂ}
    (D : Function.locallyFinsuppWithin Ω ℤ)
    (K : Set ℂ) (hKΩ : K ⊆ Ω) (hK : IsCompact K) : Finset ℂ :=
  ((D.restrict hKΩ).finiteSupport hK).toFinset

def divisorSupportIn {Ω : Set ℂ}
    (D : Function.locallyFinsuppWithin Ω ℤ)
    (K A : Set ℂ) (hKΩ : K ⊆ Ω) (hK : IsCompact K) : Finset ℂ := by
  classical
  exact (divisorSupportOn D K hKΩ hK).filter (fun z => z ∈ A)

def zeroCountIn {Ω : Set ℂ}
    (D : Function.locallyFinsuppWithin Ω ℤ)
    (K A : Set ℂ) (hKΩ : K ⊆ Ω) (hK : IsCompact K) : ℤ :=
  zeroCount D (divisorSupportIn D K A hKΩ hK)





end Autoform_Functions_of_a_Complex_Variable_complex_var_Rouche

end
