import Mathlib














namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_rabin_3_7



def finiteFieldHalfExponent (F : Type*) [Fintype F] : ℕ :=
  (Fintype.card F - 1) / 2





def DifferentType (F : Type*) [Field F] [Fintype F] (x y : F) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ x ^ (finiteFieldHalfExponent F) ≠ y ^ (finiteFieldHalfExponent F)





noncomputable def RabinDifferentTypeDeltas
    (F : Type*) [Field F] [Fintype F] (α β : F) : Finset F := by
  classical
  exact Finset.univ.filter fun δ : F => DifferentType F (α + δ) (β + δ)



end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_rabin_3_7
