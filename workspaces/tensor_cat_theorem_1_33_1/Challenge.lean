import ChallengeDeps





import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic

open Autoform_Tensor_Categories_tensor_cat_theorem_1_33_1
noncomputable section

open scoped TensorProduct

namespace Autoform_Tensor_Categories_tensor_cat_theorem_1_33_1



attribute [scoped instance 100] LieRing.ofAssociativeRing

universe uK uH uG uL














theorem ueaComulPrimitive_map_add
    (k : Type uK) (L : Type uL)
    [CommRing k] [LieRing L] [LieAlgebra k L] (x y : L) :
    ((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) (x + y)) ⊗ₜ[k] (1 : UEA k L)
        + (1 : UEA k L) ⊗ₜ[k]
            ((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) (x + y))
      = (((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) x) ⊗ₜ[k] (1 : UEA k L)
            + (1 : UEA k L) ⊗ₜ[k]
                ((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) x))
        + (((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) y) ⊗ₜ[k] (1 : UEA k L)
            + (1 : UEA k L) ⊗ₜ[k]
                ((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) y)) := by
  
  sorry





theorem ueaComulPrimitive_map_smul
    (k : Type uK) (L : Type uL)
    [CommRing k] [LieRing L] [LieAlgebra k L] (a : k) (x : L) :
    ((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) (a • x)) ⊗ₜ[k] (1 : UEA k L)
        + (1 : UEA k L) ⊗ₜ[k]
            ((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) (a • x))
      = (RingHom.id k) a •
          (((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) x) ⊗ₜ[k] (1 : UEA k L)
            + (1 : UEA k L) ⊗ₜ[k]
                ((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) x)) := by
  
  sorry





theorem ueaComulPrimitive_map_lie
    (k : Type uK) (L : Type uL)
    [CommRing k] [LieRing L] [LieAlgebra k L] (x y : L) :
    ((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) ⁅x, y⁆) ⊗ₜ[k] (1 : UEA k L)
        + (1 : UEA k L) ⊗ₜ[k]
            ((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) ⁅x, y⁆)
      = ⁅((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) x) ⊗ₜ[k] (1 : UEA k L)
            + (1 : UEA k L) ⊗ₜ[k]
                ((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) x),
          ((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) y) ⊗ₜ[k] (1 : UEA k L)
            + (1 : UEA k L) ⊗ₜ[k]
                ((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) y)⁆ := by
  
  sorry























noncomputable def ueaComulPrimitive
    (k : Type uK) (L : Type uL)
    [CommRing k] [LieRing L] [LieAlgebra k L] :
    L →ₗ⁅k⁆ (UEA k L ⊗[k] UEA k L) where
  toFun x :=
    ((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) x) ⊗ₜ[k] (1 : UEA k L)
      + (1 : UEA k L) ⊗ₜ[k]
          ((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) x)
  map_add' x y := ueaComulPrimitive_map_add k L x y
  map_smul' a x := ueaComulPrimitive_map_smul k L a x
  map_lie' {x y} := ueaComulPrimitive_map_lie k L x y







noncomputable def ueaComulAlgHom
    (k : Type uK) (L : Type uL)
    [CommRing k] [LieRing L] [LieAlgebra k L] :
    UEA k L →ₐ[k] (UEA k L ⊗[k] UEA k L) :=
  (UniversalEnvelopingAlgebra.lift k) (ueaComulPrimitive k L)






noncomputable def ueaComul
    (k : Type uK) (L : Type uL)
    [CommRing k] [LieRing L] [LieAlgebra k L] :
    UEA k L →ₗ[k] (UEA k L ⊗[k] UEA k L) :=
  (ueaComulAlgHom k L).toLinearMap




theorem ueaAntipodePrimitiveOp_map_add
    (k : Type uK) (L : Type uL)
    [CommRing k] [LieRing L] [LieAlgebra k L] (x y : L) :
    MulOpposite.op
        (-((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) (x + y)))
      = MulOpposite.op
            (-((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) x))
        + MulOpposite.op
            (-((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) y)) := by
  sorry





theorem ueaAntipodePrimitiveOp_map_smul
    (k : Type uK) (L : Type uL)
    [CommRing k] [LieRing L] [LieAlgebra k L] (a : k) (x : L) :
    MulOpposite.op
        (-((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) (a • x)))
      = (RingHom.id k) a •
          MulOpposite.op
            (-((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) x)) := by
  sorry





theorem ueaAntipodePrimitiveOp_map_lie
    (k : Type uK) (L : Type uL)
    [CommRing k] [LieRing L] [LieAlgebra k L] (x y : L) :
    MulOpposite.op
        (-((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) ⁅x, y⁆))
      = ⁅MulOpposite.op
            (-((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) x)),
          MulOpposite.op
            (-((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) y))⁆ := by
  
  
  sorry













noncomputable def ueaAntipodePrimitiveOp
    (k : Type uK) (L : Type uL)
    [CommRing k] [LieRing L] [LieAlgebra k L] :
    L →ₗ⁅k⁆ (UEA k L)ᵐᵒᵖ where
  toFun x :=
    MulOpposite.op
      (-((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L) x))
  map_add' x y := ueaAntipodePrimitiveOp_map_add k L x y
  map_smul' a x := ueaAntipodePrimitiveOp_map_smul k L a x
  map_lie' {x y} := ueaAntipodePrimitiveOp_map_lie k L x y






noncomputable def ueaAntipodeToOpAlgHom
    (k : Type uK) (L : Type uL)
    [CommRing k] [LieRing L] [LieAlgebra k L] :
    UEA k L →ₐ[k] (UEA k L)ᵐᵒᵖ :=
  (UniversalEnvelopingAlgebra.lift k) (ueaAntipodePrimitiveOp k L)




theorem ueaAntipode_map_add
    (k : Type uK) (L : Type uL)
    [CommRing k] [LieRing L] [LieAlgebra k L] (a b : UEA k L) :
    MulOpposite.unop ((ueaAntipodeToOpAlgHom k L) (a + b))
      = MulOpposite.unop ((ueaAntipodeToOpAlgHom k L) a)
        + MulOpposite.unop ((ueaAntipodeToOpAlgHom k L) b) := by
  sorry





theorem ueaAntipode_map_smul
    (k : Type uK) (L : Type uL)
    [CommRing k] [LieRing L] [LieAlgebra k L] (c : k) (a : UEA k L) :
    MulOpposite.unop ((ueaAntipodeToOpAlgHom k L) (c • a))
      = (RingHom.id k) c • MulOpposite.unop ((ueaAntipodeToOpAlgHom k L) a) := by
  sorry































noncomputable def ueaAntipode
    (k : Type uK) (L : Type uL)
    [CommRing k] [LieRing L] [LieAlgebra k L] :
    UEA k L →ₗ[k] UEA k L where
  toFun a := MulOpposite.unop ((ueaAntipodeToOpAlgHom k L) a)
  map_add' a b := ueaAntipode_map_add k L a b
  map_smul' c a := ueaAntipode_map_smul k L c a









noncomputable def skewComulSingleLinear
    {k : Type uK} {G : Type uG} {L : Type uL}
    [CommRing k] [Group G] [LieRing L] [LieAlgebra k L]
    (ρ : LieAction k G L) (g : G) :
    UEA k L →ₗ[k]
      (SkewGroupAlgebra k G L ρ ⊗[k] SkewGroupAlgebra k G L ρ) :=
  (TensorProduct.map
      (singleLinear ρ g)
      (singleLinear ρ g)).comp
    (ueaComul k L)








noncomputable def skewComul
    {k : Type uK} {G : Type uG} {L : Type uL}
    [CommRing k] [Group G] [LieRing L] [LieAlgebra k L]
    (ρ : LieAction k G L) :
    SkewGroupAlgebra k G L ρ →ₗ[k]
      (SkewGroupAlgebra k G L ρ ⊗[k] SkewGroupAlgebra k G L ρ) :=
  Finsupp.lsum k fun g : G => skewComulSingleLinear ρ g








noncomputable def skewAntipodeSingleLinear
    {k : Type uK} {G : Type uG} {L : Type uL}
    [CommRing k] [Group G] [LieRing L] [LieAlgebra k L]
    (ρ : LieAction k G L) (g : G) :
    UEA k L →ₗ[k] SkewGroupAlgebra k G L ρ :=
  (singleLinear ρ g⁻¹).comp
    ((ueaMapAlgHom (k := k) (L := L) (ρ.act g)).toLinearMap.comp
      (ueaAntipode k L))







noncomputable def skewAntipode
    {k : Type uK} {G : Type uG} {L : Type uL}
    [CommRing k] [Group G] [LieRing L] [LieAlgebra k L]
    (ρ : LieAction k G L) :
    SkewGroupAlgebra k G L ρ →ₗ[k] SkewGroupAlgebra k G L ρ :=
  Finsupp.lsum k fun g : G => skewAntipodeSingleLinear ρ g
















structure CartierKostantEquiv
    (k : Type uK) (H : Type uH)
    (G : Type uG) (L : Type uL)
    [Field k] [Ring H] [HopfAlgebra k H]
    [Group G] [LieRing L] [LieAlgebra k L]
    (ρ : LieAction k G L) : Type _ where
  toLinearEquiv : H ≃ₗ[k] SkewGroupAlgebra k G L ρ

  map_one :
    toLinearEquiv 1 = skewOne ρ

  map_mul :
    ∀ x y : H,
      toLinearEquiv (x * y)
        = skewMul ρ (toLinearEquiv x) (toLinearEquiv y)

  map_comul :
    ∀ x : H,
      TensorProduct.map toLinearEquiv.toLinearMap toLinearEquiv.toLinearMap
          (CoalgebraStruct.comul x)
        = skewComul ρ (toLinearEquiv x)

  map_counit :
    ∀ x : H,
      skewCounit ρ (toLinearEquiv x)
        = CoalgebraStruct.counit x

  map_antipode :
    ∀ x : H,
      toLinearEquiv ((HopfAlgebraStruct.antipode k : H →ₗ[k] H) x)
        = skewAntipode ρ (toLinearEquiv x)












theorem theorem_1_33_1
    (k : Type uK) [Field k] [IsAlgClosed k] [CharZero k]
    (H : Type uH) [Ring H] [HopfAlgebra k H]
    [HasBijectiveAntipode k H]
    [Coalgebra.IsCocomm k H] :
    ∃ (G : Type uH) (_ : Group G)
      (L : Type uH) (_ : LieRing L) (_ : LieAlgebra k L)
      (ρ : LieAction k G L),
        Nonempty (CartierKostantEquiv k H G L ρ) := by
  sorry

end Autoform_Tensor_Categories_tensor_cat_theorem_1_33_1

end