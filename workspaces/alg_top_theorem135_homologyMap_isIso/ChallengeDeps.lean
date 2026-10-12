/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
















noncomputable section

open CategoryTheory Limits

namespace Autoform_Algebraic_Topology_I_alg_top_theorem135_homologyMap_isIso

abbrev ZModCat := ModuleCat ℤ








abbrev SSetChainComplexFunctor : SSet ⥤ ChainComplex ZModCat ℕ :=
  (SSet.chainComplexFunctor ZModCat).obj (ModuleCat.of ℤ ℤ)











abbrev SingCC (X : TopCat) : ChainComplex ZModCat ℕ :=
  SSetChainComplexFunctor.obj (TopCat.toSSet.obj X)







abbrev SingularSimplexOfDegree
    (X : TopCat) (n : SimplexCategoryᵒᵖ) : Type _ :=
  (TopCat.toSSet.obj X).obj n








abbrev StandardSimplexOfDegree (n : SimplexCategoryᵒᵖ) : Type :=
  stdSimplex ℝ (Fin ((Opposite.unop n).len + 1))











noncomputable def simplexContinuousMapOf
    {X : TopCat} {n : SimplexCategoryᵒᵖ}
    (σ : SingularSimplexOfDegree X n) :
    C(StandardSimplexOfDegree n, ↑X) :=
  (TopCat.toSSetObjEquiv X n) σ








def IsCover (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X) : Prop :=
  ∀ x : ↑X, ∃ i : ι, x ∈ interior (𝒜 i)









def IsASmallSimplex
    (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X)
    {n : SimplexCategoryᵒᵖ}
    (σ : SingularSimplexOfDegree X n) : Prop :=
  ∃ i : ι,
    Set.range
      ((simplexContinuousMapOf (X := X) (n := n) σ).toFun) ⊆ 𝒜 i










abbrev ASmallSimplex
    (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X)
    (n : SimplexCategoryᵒᵖ) : Type _ :=
  {σ : SingularSimplexOfDegree X n // IsASmallSimplex X 𝒜 σ}























def ChainMapQuasiIso
    {C D : ChainComplex ZModCat ℕ} (f : C ⟶ D) : Prop :=
  ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap f n)



end Autoform_Algebraic_Topology_I_alg_top_theorem135_homologyMap_isIso

end