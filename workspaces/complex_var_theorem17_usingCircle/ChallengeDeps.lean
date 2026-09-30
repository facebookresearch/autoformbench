import Mathlib

noncomputable section

open Set Metric
open scoped BigOperators

namespace Autoform_Functions_of_a_Complex_Variable_complex_var_theorem17_usingCircle

def twoPiI : ℂ :=
  (2 : ℂ) * (Real.pi : ℂ) * Complex.I

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

namespace FilledCurve

instance instCoeFunFilledCurve : CoeFun FilledCurve (fun _ => ClosedUnitDisc → ℂ) where
  coe J := J.map


def filled (J : FilledCurve) : Set ℂ :=
  Set.range J.map





def interior (J : FilledCurve) : Set ℂ :=
  J.map '' openUnitDisc

def boundaryMap (J : FilledCurve) : Circle → ℂ :=
  fun ζ : Circle => J.map (circleToClosedUnitDisc ζ)

def curve (J : FilledCurve) : Set ℂ :=
  Set.range J.boundaryMap






def boundaryParam (J : FilledCurve) (t : ℝ) : ℂ :=
  J.boundaryMap (Circle.exp t)








def HasSmoothBoundary (J : FilledCurve) : Prop :=
  ContDiffOn ℝ 1
    (fun t : ℝ => J.boundaryParam t)
    (Set.Icc (0 : ℝ) (2 * Real.pi))










def boundaryIntegral (J : FilledCurve) (f : ℂ → ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..(2 * Real.pi),
    f (J.boundaryParam t) *
      deriv (fun u : ℝ => J.boundaryParam u) t


def BoundaryIntegrable (J : FilledCurve) (f : ℂ → ℂ) : Prop :=
  IntervalIntegrable
    (fun t : ℝ =>
      f (J.boundaryParam t) *
        deriv (fun u : ℝ => J.boundaryParam u) t)
    MeasureTheory.volume
    (0 : ℝ)
    (2 * Real.pi)




def windingIndex (J : FilledCurve) (w : ℂ) : ℂ :=
  twoPiI⁻¹ * J.boundaryIntegral (fun z : ℂ => (z - w)⁻¹)





def PositivelyOriented (J : FilledCurve) : Prop :=
  ∀ w : ℂ, w ∈ J.interior →
    J.BoundaryIntegrable (fun z : ℂ => (z - w)⁻¹) ∧
      J.windingIndex w = 1

end FilledCurve

def IsRegion (Ω : Set ℂ) : Prop :=
  IsOpen Ω ∧ IsPreconnected Ω









def IsolatedSingularitiesIn (Ω S : Set ℂ) : Prop :=
  S ⊆ Ω ∧
    ∀ z : ℂ, z ∈ Ω →
      ∃ ε : ℝ, 0 < ε ∧
        (Metric.ball z ε \ ({z} : Set ℂ)) ⊆ Ω \ S








structure ResidueCircle (Ω S : Set ℂ) (a : ℂ) where
  r : ℝ
  r_pos : 0 < r
  puncturedClosedBall_subset_regular :
    Metric.closedBall a r \ ({a} : Set ℂ) ⊆ Ω \ S






def residue {Ω S : Set ℂ} (f : ℂ → ℂ) (a : ℂ)
    (C : ResidueCircle Ω S a) : ℂ :=
  twoPiI⁻¹ * (∮ z in C(a, C.r), f z)







def residueSum {Ω S : Set ℂ} (f : ℂ → ℂ)
    (interiorSings : Finset ℂ)
    (C : ∀ a : ℂ, a ∈ interiorSings → ResidueCircle Ω S a) : ℂ :=
  ∑ a ∈ interiorSings.attach,
    residue f a.1 (C a.1 a.2)



end Autoform_Functions_of_a_Complex_Variable_complex_var_theorem17_usingCircle

end
