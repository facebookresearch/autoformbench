/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import ChallengeDeps

open Autoform_Algebraic_Geometry_I_alg_geom_affine_factorial_isLocallyFactorial




































noncomputable section

namespace Autoform_Algebraic_Geometry_I_alg_geom_affine_factorial_isLocallyFactorial

universe u


















def principalCartierDivisorSubgroup
    (R : Type u) [CommRing R] [IsDomain R] :
    Subgroup (AffineCartierDivisorMulGroup R) :=
  (toPrincipalIdeal R (FractionRing R)).range










abbrev AffineCartierClassGroup
    (R : Type u) [CommRing R] [IsDomain R] : Type u :=
  AffineCartierDivisorMulGroup R ⧸ principalCartierDivisorSubgroup R








def classGroupEquivAffineCartierClassGroup
    (R : Type u) [CommRing R] [IsDomain R] :
    ClassGroup R ≃* AffineCartierClassGroup R :=
  ClassGroup.equiv (R := R) (FractionRing R)









theorem heightOnePrime_isUnit_asFractionalIdeal
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hR : AffineLocallyFactorial R) (P : HeightOnePrime R) :
    IsUnit ((P.1 : Ideal R) :
      FractionalIdeal (nonZeroDivisors R) (FractionRing R)) := by
  sorry








def heightOnePrimeCartierDivisor
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hR : AffineLocallyFactorial R) (P : HeightOnePrime R) :
    AffineCartierDivisorMulGroup R :=
  (heightOnePrime_isUnit_asFractionalIdeal R hR P).unit



@[simp]
theorem coe_heightOnePrimeCartierDivisor
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hR : AffineLocallyFactorial R) (P : HeightOnePrime R) :
    ((heightOnePrimeCartierDivisor R hR P : AffineCartierDivisorMulGroup R) :
        FractionalIdeal (nonZeroDivisors R) (FractionRing R)) =
      ((P.1 : Ideal R) : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) := by
  exact (heightOnePrime_isUnit_asFractionalIdeal R hR P).unit_spec




def heightOnePrimeToCartierDivisor
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hR : AffineLocallyFactorial R) :
    HeightOnePrime R → AffineCartierDivisorGroup R :=
  fun P => Additive.ofMul (heightOnePrimeCartierDivisor R hR P)









def weilToCartierDivisor
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hR : AffineLocallyFactorial R) :
    WeilDivisorGroup R →+ AffineCartierDivisorGroup R :=
  FreeAbelianGroup.lift (heightOnePrimeToCartierDivisor R hR)





@[simp]
theorem weilToCartierDivisor_of
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hR : AffineLocallyFactorial R) (P : HeightOnePrime R) :
    weilToCartierDivisor R hR (FreeAbelianGroup.of P) =
      Additive.ofMul (heightOnePrimeCartierDivisor R hR P) := by
  simp [weilToCartierDivisor, heightOnePrimeToCartierDivisor]








theorem affine_locallyFactorial_weilToCartierDivisor_bijective
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hR : AffineLocallyFactorial R) :
    Function.Bijective (weilToCartierDivisor R hR) := by
  sorry







def affine_locallyFactorial_weilDivisor_equiv_cartierDivisor
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hR : AffineLocallyFactorial R) :
    WeilDivisorGroup R ≃+ AffineCartierDivisorGroup R :=
  AddEquiv.ofBijective
    (weilToCartierDivisor R hR)
    (affine_locallyFactorial_weilToCartierDivisor_bijective R hR)






theorem affine_factorial_isLocallyFactorial
    (R : Type u) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] :
    AffineLocallyFactorial R := by
  sorry







def affine_factorial_weilDivisor_equiv_cartierDivisor
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [UniqueFactorizationMonoid R] :
    WeilDivisorGroup R ≃+ AffineCartierDivisorGroup R :=
  affine_locallyFactorial_weilDivisor_equiv_cartierDivisor R
    (affine_factorial_isLocallyFactorial R)













def affine_picardGroup_equiv_cartierDivisors_mod_principal
    (R : Type u) [CommRing R] [IsDomain R] :
    CommRing.Pic R ≃* AffineCartierClassGroup R :=
  (ClassGroup.equivPic R).symm.trans
    (classGroupEquivAffineCartierClassGroup R)

end Autoform_Algebraic_Geometry_I_alg_geom_affine_factorial_isLocallyFactorial
