import Mathlib

set_option autoImplicit false

namespace Autoform_Introduction_to_PDEs_pde_proposition_1_0_1










noncomputable def sphericalAverage
    (h : EuclideanSpace ℝ (Fin 3) → ℝ)
    (r : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  MeasureTheory.average
    (MeasureTheory.Measure.toSphere
      (MeasureTheory.volume :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
    (fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
      h (x + r • ω.1))





noncomputable def modifiedSphericalAverage
    (h : EuclideanSpace ℝ (Fin 3) → ℝ)
    (r : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  r * sphericalAverage h r x



end Autoform_Introduction_to_PDEs_pde_proposition_1_0_1
