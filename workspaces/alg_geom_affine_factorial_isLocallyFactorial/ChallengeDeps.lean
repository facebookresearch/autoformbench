/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib





































noncomputable section

namespace Autoform_Algebraic_Geometry_I_alg_geom_affine_factorial_isLocallyFactorial

universe u








def HeightOnePrime (R : Type u) [CommRing R] : Type u :=
  { p : Ideal R // p.IsPrime ∧ p.height = 1 }








abbrev WeilDivisorGroup (R : Type u) [CommRing R] : Type u :=
  FreeAbelianGroup (HeightOnePrime R)








def AffineLocallyFactorial
    (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∀ (p : Ideal R) (hp : p.IsPrime),
    letI : p.IsPrime := hp
    UniqueFactorizationMonoid (Localization.AtPrime p)








abbrev AffineCartierDivisorMulGroup
    (R : Type u) [CommRing R] [IsDomain R] : Type u :=
  (FractionalIdeal (nonZeroDivisors R) (FractionRing R))ˣ







abbrev AffineCartierDivisorGroup
    (R : Type u) [CommRing R] [IsDomain R] : Type u :=
  Additive (AffineCartierDivisorMulGroup R)





