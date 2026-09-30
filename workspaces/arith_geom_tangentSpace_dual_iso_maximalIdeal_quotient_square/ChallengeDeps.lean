import Mathlib























noncomputable section

open scoped BigOperators

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_tangentSpace_dual_iso_maximalIdeal_quotient_square








def directionalDerivativeAt
    {k ι : Type*} [Field k] [Fintype ι]
    (P v : ι → k) (f : MvPolynomial ι k) : k :=
  ∑ i, v i * MvPolynomial.eval P (MvPolynomial.pderiv i f)















def PointLiesOnAffineVariety
    {k ι : Type*} [Field k]
    (I : Ideal (MvPolynomial ι k)) (P : ι → k) : Prop :=
  ∀ f : MvPolynomial ι k, f ∈ I → MvPolynomial.eval P f = 0
















end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_tangentSpace_dual_iso_maximalIdeal_quotient_square

end