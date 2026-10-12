/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option warningAsError false














universe u v w a

namespace Autoform_Buildings_and_Classical_Groups_buildings_leftOperator_comp_rightOperator






structure GenericData (R : Type u) [CommRing R] (ι : Type v)
    (M : CoxeterMatrix ι) (W : Type w) [Group W] where
  coxeter : CoxeterSystem M W
  a : ι → R
  b : ι → R
  a_eq_of_conj_simple :
    ∀ ⦃s t : ι⦄ ⦃x : W⦄,
      coxeter.simple s = x * coxeter.simple t * x⁻¹ → a s = a t
  b_eq_of_conj_simple :
    ∀ ⦃s t : ι⦄ ⦃x : W⦄,
      coxeter.simple s = x * coxeter.simple t * x⁻¹ → b s = b t

variable {R : Type u} [CommRing R]
variable {ι : Type v} {M : CoxeterMatrix ι}
variable {W : Type w} [Group W]


abbrev EndomorphismRing (A : Type a) [AddCommGroup A] [Module R A] :=
  Module.End R A





noncomputable def leftOnBasis (D : GenericData R ι M W)
    {A : Type a} [AddCommGroup A] [Module R A]
    (T : Module.Basis W R A) (s : ι) (x : W) : A :=
  if D.coxeter.length (D.coxeter.simple s * x) > D.coxeter.length x then
    T (D.coxeter.simple s * x)
  else
    D.a s • T x + D.b s • T (D.coxeter.simple s * x)





noncomputable def rightOnBasis (D : GenericData R ι M W)
    {A : Type a} [AddCommGroup A] [Module R A]
    (T : Module.Basis W R A) (t : ι) (x : W) : A :=
  if D.coxeter.length (x * D.coxeter.simple t) > D.coxeter.length x then
    T (x * D.coxeter.simple t)
  else
    D.a t • T x + D.b t • T (x * D.coxeter.simple t)



noncomputable def leftOperator (D : GenericData R ι M W)
    {A : Type a} [AddCommGroup A] [Module R A]
    (T : Module.Basis W R A) (s : ι) : EndomorphismRing (R := R) A :=
  (Module.Basis.constr T R) (fun x : W => leftOnBasis D T s x)



noncomputable def rightOperator (D : GenericData R ι M W)
    {A : Type a} [AddCommGroup A] [Module R A]
    (T : Module.Basis W R A) (t : ι) : EndomorphismRing (R := R) A :=
  (Module.Basis.constr T R) (fun x : W => rightOnBasis D T t x)



end Autoform_Buildings_and_Classical_Groups_buildings_leftOperator_comp_rightOperator
