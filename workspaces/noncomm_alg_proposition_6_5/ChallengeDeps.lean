import Mathlib




















universe u v

namespace Autoform_Noncommutative_Algebra_noncomm_alg_proposition_6_5











structure ProjectiveSurjection
    (R : Type u) [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M] where
  P : Type (max u v)
  [P_addCommGroup : AddCommGroup P]
  [P_module : Module R P]
  [P_projective : Module.Projective R P]
  quotientMap : P →ₗ[R] M
  quotientMap_surjective : Function.Surjective quotientMap

attribute [instance] ProjectiveSurjection.P_addCommGroup
attribute [instance] ProjectiveSurjection.P_module
attribute [instance] ProjectiveSurjection.P_projective



end Autoform_Noncommutative_Algebra_noncomm_alg_proposition_6_5
