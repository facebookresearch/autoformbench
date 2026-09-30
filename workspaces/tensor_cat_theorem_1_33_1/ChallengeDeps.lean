import Mathlib

noncomputable section

open scoped TensorProduct

namespace Autoform_Tensor_Categories_tensor_cat_theorem_1_33_1



attribute [scoped instance 100] LieRing.ofAssociativeRing

universe uK uH uG uL








class HasBijectiveAntipode
    (k : Type uK) (H : Type uH)
    [CommSemiring k] [Semiring H] [HopfAlgebra k H] : Prop where
  antipode_bijective :
    Function.Bijective ⇑(HopfAlgebraStruct.antipode k : H →ₗ[k] H)






abbrev UEA
    (k : Type uK) (L : Type uL)
    [CommRing k] [LieRing L] [LieAlgebra k L] : Type (max uK uL) :=
  UniversalEnvelopingAlgebra k L












structure LieAction
    (k : Type uK) (G : Type uG) (L : Type uL)
    [CommRing k] [Group G] [LieRing L] [LieAlgebra k L] where
  act : G → (L ≃ₗ⁅k⁆ L)
  act_one : act 1 = LieEquiv.refl
  act_mul : ∀ g h : G, act (g * h) = (act g) ∘ (act h)







noncomputable def ueaMapAlgHom
    {k : Type uK} {L : Type uL}
    [CommRing k] [LieRing L] [LieAlgebra k L]
    (e : L ≃ₗ⁅k⁆ L) :
    UEA k L →ₐ[k] UEA k L :=
  (UniversalEnvelopingAlgebra.lift k)
    ((UniversalEnvelopingAlgebra.ι k : L →ₗ⁅k⁆ UEA k L).comp
      (e : L →ₗ⁅k⁆ L))















noncomputable def ueaCounitPrimitive
    (k : Type uK) (L : Type uL)
    [CommRing k] [LieRing L] [LieAlgebra k L] :
    L →ₗ⁅k⁆ k where
  toFun _ := 0
  map_add' := by
    intro x y
    simp
  map_smul' := by
    intro a x
    simp
  map_lie' := by
    intro x y
    simp






noncomputable def ueaCounitAlgHom
    (k : Type uK) (L : Type uL)
    [CommRing k] [LieRing L] [LieAlgebra k L] :
    UEA k L →ₐ[k] k :=
  (UniversalEnvelopingAlgebra.lift k) (ueaCounitPrimitive k L)






noncomputable def ueaCounit
    (k : Type uK) (L : Type uL)
    [CommRing k] [LieRing L] [LieAlgebra k L] :
    UEA k L →ₗ[k] k :=
  (ueaCounitAlgHom k L).toLinearMap
























abbrev SkewGroupAlgebra
    (k : Type uK) (G : Type uG) (L : Type uL)
    [CommRing k] [Group G] [LieRing L] [LieAlgebra k L]
    (_ρ : LieAction k G L) : Type (max uG (max uK uL)) :=
  G →₀ UEA k L







noncomputable def singleLinear
    {k : Type uK} {G : Type uG} {L : Type uL}
    [CommRing k] [Group G] [LieRing L] [LieAlgebra k L]
    (ρ : LieAction k G L) (g : G) :
    UEA k L →ₗ[k] SkewGroupAlgebra k G L ρ :=
  Finsupp.lsingle g






noncomputable def ueaAction
    {k : Type uK} {G : Type uG} {L : Type uL}
    [CommRing k] [Group G] [LieRing L] [LieAlgebra k L]
    (ρ : LieAction k G L) (g : G) :
    UEA k L →ₐ[k] UEA k L :=
  ueaMapAlgHom (k := k) (L := L) (ρ.act g)







noncomputable def skewOne
    {k : Type uK} {G : Type uG} {L : Type uL}
    [CommRing k] [Group G] [LieRing L] [LieAlgebra k L]
    (ρ : LieAction k G L) :
    SkewGroupAlgebra k G L ρ :=
  Finsupp.single (1 : G) (1 : UEA k L)












noncomputable def skewMul
    {k : Type uK} {G : Type uG} {L : Type uL}
    [CommRing k] [Group G] [LieRing L] [LieAlgebra k L]
    (ρ : LieAction k G L)
    (x y : SkewGroupAlgebra k G L ρ) :
    SkewGroupAlgebra k G L ρ :=
  x.sum fun g a =>
    y.sum fun h b =>
      Finsupp.single (g * h) ((ueaAction ρ h⁻¹ a) * b)










noncomputable def skewCounit
    {k : Type uK} {G : Type uG} {L : Type uL}
    [CommRing k] [Group G] [LieRing L] [LieAlgebra k L]
    (ρ : LieAction k G L) :
    SkewGroupAlgebra k G L ρ →ₗ[k] k :=
  Finsupp.lsum k fun _g : G => ueaCounit k L






end Autoform_Tensor_Categories_tensor_cat_theorem_1_33_1

end