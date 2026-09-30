/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
























noncomputable section

open CategoryTheory Module
open scoped MonoidalCategory

universe u v w t

namespace Autoform_Tensor_Categories_tensor_cat_theorem_1_53_1










def EssentialEpi {C : Type u} [Category.{v} C] {P X : C} (π : P ⟶ X) : Prop :=
  Epi π ∧
    ∀ ⦃Y : C⦄ (i : Y ⟶ P), Mono i → Epi (i ≫ π) → IsIso i









structure ProjectiveCover {C : Type u} [Category.{v} C] (P X : C) where
  π : P ⟶ X
  projective : Projective P
  essential_epi : EssentialEpi π

namespace ProjectiveCover

variable {C : Type u} [Category.{v} C] {P X : C} (c : ProjectiveCover P X)

end ProjectiveCover










class HomFinite (k : Type w) [Field k] (C : Type u)
    [Category.{v} C] [Preadditive C] [Linear k C] : Prop where
  hom_finite : ∀ X Y : C, FiniteDimensional k (X ⟶ Y)

attribute [instance] HomFinite.hom_finite













def HasFiniteLengthObjects (C : Type u) [Category.{v} C] : Prop :=
  ∀ X : C, IsArtinianObject X ∧ IsNoetherianObject X













def IsSemisimpleAbelianCategory (C : Type u) [Category.{v} C] : Prop :=
  ∀ X : C, Projective X












structure TensorUnitEndEquiv (k : Type w) [Field k] (C : Type u)
    [Category.{v} C] [Preadditive C] [Linear k C] [MonoidalCategory C] where
  unitEnd : End (𝟙_ C) ≃ₗ[k] k











structure SimpleProjectiveCoverData
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C]
    (ι : Type t) where
  L : ι → C
  P : ι → C
  simple : ∀ i, Simple (L i)
  cover : ∀ i, ProjectiveCover (P i) (L i)
  complete : ∀ X : C, Simple X → ∃ i : ι, Nonempty (X ≅ L i)
  no_duplicates : ∀ i j : ι, Nonempty (L i ≅ L j) → i = j











structure FiniteTensorCategoryData
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C]
    (ι : Type t) [Fintype ι] where
  homFinite : HomFinite k C
  finiteLength : HasFiniteLengthObjects C
  unitEnd : TensorUnitEndEquiv k C
  simples : SimpleProjectiveCoverData k C ι














def identityAdditiveFunctor
    (C : Type u) [Category.{v} C] [Preadditive C] : C ⥤+ C :=
  AdditiveFunctor.of (𝟭 C)

















def cartanMatrix
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C]
    {ι : Type t}
    (S : SimpleProjectiveCoverData k C ι) : Matrix ι ι k :=
  fun i j => (Module.finrank k (S.P j ⟶ S.P i) : k)








def CartanMatrixDegenerate
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [Abelian C]
    {ι : Type t} [Fintype ι] [DecidableEq ι]
    (S : SimpleProjectiveCoverData k C ι) : Prop :=
  Matrix.det (cartanMatrix S) = 0



end Autoform_Tensor_Categories_tensor_cat_theorem_1_53_1

end