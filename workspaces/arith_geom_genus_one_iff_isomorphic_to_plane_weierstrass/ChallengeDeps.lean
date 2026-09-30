/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib





























noncomputable section

open scoped BigOperators

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_genus_one_iff_isomorphic_to_plane_weierstrass


structure NormalizedDiscreteValuation (F : Type*) [Field F] where
  toFun : F → WithTop ℤ
  map_zero' : toFun 0 = ⊤
  map_one' : toFun 1 = (0 : WithTop ℤ)
  map_mul' : ∀ x y : F, toFun (x * y) = toFun x + toFun y
  map_add' : ∀ x y : F, min (toFun x) (toFun y) ≤ toFun (x + y)
  finite_ne_zero' : ∀ {x : F}, x ≠ 0 → ∃ n : ℤ, toFun x = (n : WithTop ℤ)
  exists_uniformizer' : ∃ t : F, toFun t = (1 : WithTop ℤ)

instance instCoeFunNormalizedDiscreteValuation {F : Type*} [Field F] :
    CoeFun (NormalizedDiscreteValuation F) (fun _ => F → WithTop ℤ) where
  coe v := v.toFun

namespace NormalizedDiscreteValuation

variable {F : Type*} [Field F] (v : NormalizedDiscreteValuation F)

@[simp] theorem map_zero : v 0 = ⊤ := v.map_zero'
@[simp] theorem map_one : v 1 = (0 : WithTop ℤ) := v.map_one'
theorem map_mul (x y : F) : v (x * y) = v x + v y := v.map_mul' x y
theorem map_add (x y : F) : min (v x) (v y) ≤ v (x + y) := v.map_add' x y

end NormalizedDiscreteValuation


class IsOneVariableFunctionField
    (k F : Type*) [Field k] [Field F] [Algebra k F] : Prop where
  exists_finite_transcendence_generator :
    ∃ x : F,
      ¬ IsAlgebraic k x ∧
        FiniteDimensional (↥(IntermediateField.adjoin k ({x} : Set F))) F
  constants_algebraically_closed :
    ∀ x : F, IsAlgebraic k x → ∃ c : k, algebraMap k F c = x


structure FunctionFieldCurve (k : Type*) [Field k] where
  F : Type*
  fieldF : Field F
  algebraF : Algebra k F
  isFunctionField : IsOneVariableFunctionField k F

namespace FunctionFieldCurve

instance instFieldF {k : Type*} [Field k] (C : FunctionFieldCurve k) : Field C.F := C.fieldF
instance instAlgebraF {k : Type*} [Field k] (C : FunctionFieldCurve k) : Algebra k C.F := C.algebraF
instance instIsOneVariableFunctionFieldF {k : Type*} [Field k] (C : FunctionFieldCurve k) :
    IsOneVariableFunctionField k C.F := C.isFunctionField


abbrev Place {k : Type*} [Field k] (C : FunctionFieldCurve k) : Type _ :=
  { v : NormalizedDiscreteValuation C.F //
      ∀ c : k, c ≠ 0 → v (algebraMap k C.F c) = (0 : WithTop ℤ) }


abbrev placeValuation {k : Type*} [Field k] (C : FunctionFieldCurve k)
    (P : C.Place) : NormalizedDiscreteValuation C.F :=
  P.1


theorem place_trivial_on_constants {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (P : C.Place) :
    ∀ c : k, c ≠ 0 → C.placeValuation P (algebraMap k C.F c) = (0 : WithTop ℤ) :=
  P.2

end FunctionFieldCurve


abbrev ord {k : Type*} [Field k] (C : FunctionFieldCurve k)
    (P : C.Place) (f : C.F) : WithTop ℤ :=
  C.placeValuation P f


abbrev Divisor {k : Type*} [Field k] (C : FunctionFieldCurve k) : Type _ :=
  C.Place →₀ ℤ


abbrev WeierstrassFunctionField {k : Type*} [Field k]
    (W : WeierstrassCurve.Affine k) : Type _ :=
  W.FunctionField


def FunctionFieldIsomorphismToWeierstrass
    {k : Type*} [Field k]
    (C : FunctionFieldCurve k) (W : WeierstrassCurve.Affine k) : Prop :=
  ∃ e : C.F ≃+* WeierstrassFunctionField W,
    ∀ c : k, e (algebraMap k C.F c) = algebraMap k (WeierstrassFunctionField W) c










def IsIsomorphicToPlaneWeierstrassCurve
    {k : Type*} [Field k] (C : FunctionFieldCurve k) : Prop :=
  ∃ W : WeierstrassCurve.Affine k,
    WeierstrassCurve.IsElliptic W ∧ FunctionFieldIsomorphismToWeierstrass C W

end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_genus_one_iff_isomorphic_to_plane_weierstrass

end
