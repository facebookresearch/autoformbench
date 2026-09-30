/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import ChallengeDeps

open Autoform_Algebraic_Geometry_I_alg_geom_bezout_plane_projective_curves




























open scoped BigOperators

universe u

namespace Autoform_Algebraic_Geometry_I_alg_geom_bezout_plane_projective_curves

noncomputable section

variable {k : Type u} [Field k]










theorem vanishesAt_scaling_forward
    (C : PlaneProjectiveCurve k)
    (a b : { v : Fin 3 → k // v ≠ 0 }) (t : k)
    (ht : (a : Fin 3 → k) = t • (b : Fin 3 → k))
    (ha : (MvPolynomial.eval (a : Fin 3 → k)) C.poly = 0) :
    (MvPolynomial.eval (b : Fin 3 → k)) C.poly = 0 := by
  sorry








theorem vanishesAt_scaling_reverse
    (C : PlaneProjectiveCurve k)
    (a b : { v : Fin 3 → k // v ≠ 0 }) (t : k)
    (ht : (a : Fin 3 → k) = t • (b : Fin 3 → k))
    (hb : (MvPolynomial.eval (b : Fin 3 → k)) C.poly = 0) :
    (MvPolynomial.eval (a : Fin 3 → k)) C.poly = 0 := by
  sorry

namespace PlaneProjectiveCurve







end PlaneProjectiveCurve






namespace PlaneProjectiveCurve









noncomputable def VanishesAt
    (C : PlaneProjectiveCurve k)
    (p : Projectivization k (Fin 3 → k)) : Prop :=
  Projectivization.lift
    (fun v : { v : Fin 3 → k // v ≠ 0 } =>
      (MvPolynomial.eval v.1) C.poly = 0)
    (fun a b t ht =>
      propext
        ⟨fun ha => vanishesAt_scaling_forward C a b t ht ha,
         fun hb => vanishesAt_scaling_reverse C a b t ht hb⟩)
    p
end PlaneProjectiveCurve

namespace PlaneProjectiveCurve






def zeroLocus (C : PlaneProjectiveCurve k) :
    Set (Projectivization k (Fin 3 → k)) :=
  { p | C.VanishesAt p }
end PlaneProjectiveCurve



theorem chartIndex_ne_zero
    (p : Projectivization k (Fin 3 → k)) :
    p.rep (chartIndex p) ≠ 0 :=
  Classical.choose_spec (exists_coord_ne_zero p)

















noncomputable def affinePointIdeal
    (p : Projectivization k (Fin 3 → k)) :
    Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span
    (Set.range
      (fun j : Fin 3 =>
        MvPolynomial.X j - MvPolynomial.C (normalizedCoord p j)))






theorem affinePointIdeal_isPrime
    (p : Projectivization k (Fin 3 → k)) :
    (affinePointIdeal p).IsPrime := by
  sorry





















noncomputable abbrev localIntersectionAlgebra
    (C D : PlaneProjectiveCurve k)
    (p : Projectivization k (Fin 3 → k)) : Type u :=
  let P : Ideal (MvPolynomial (Fin 3) k) := affinePointIdeal p
  haveI : P.IsPrime := affinePointIdeal_isPrime p
  let R : Type u := Localization.AtPrime P
  R ⧸ Ideal.span
    ({ algebraMap (MvPolynomial (Fin 3) k) R (chartEquation p),
       algebraMap (MvPolynomial (Fin 3) k) R
         (dehomogenizeInChart (chartIndex p) C.poly),
       algebraMap (MvPolynomial (Fin 3) k) R
         (dehomogenizeInChart (chartIndex p) D.poly) } : Set R)










noncomputable def intersectionMultiplicity
    (C D : PlaneProjectiveCurve k)
    (p : Projectivization k (Fin 3 → k)) : ℕ :=
  Module.finrank k (localIntersectionAlgebra C D p)










theorem bezout_plane_projective_curves
    [IsAlgClosed k]
    (C D : PlaneProjectiveCurve k)
    (hcommon : ¬ C.HasCommonComponent D) :
    ∃ S : Finset (Projectivization k (Fin 3 → k)),
      (↑S : Set (Projectivization k (Fin 3 → k))) =
        C.zeroLocus ∩ D.zeroLocus ∧
      (∑ p ∈ S, intersectionMultiplicity C D p) =
        C.degree * D.degree := by
  sorry

end

end Autoform_Algebraic_Geometry_I_alg_geom_bezout_plane_projective_curves
