/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open scoped Manifold

namespace Autoform_Lie_groups_lie_algebras_lie_theorem_4_1
namespace Theorem41








structure QuotientModel
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] (d : ℕ) where
  E : Type*
  [normedAddCommGroup_E : NormedAddCommGroup E]
  [normedSpace_E : NormedSpace 𝕜 E]
  [finiteDimensional_E : FiniteDimensional 𝕜 E]
  H : Type*
  [topologicalSpace_H : TopologicalSpace H]
  I : ModelWithCorners 𝕜 E H
  finrank_E : Module.finrank 𝕜 E = d

attribute [instance]
  QuotientModel.normedAddCommGroup_E
  QuotientModel.normedSpace_E
  QuotientModel.finiteDimensional_E
  QuotientModel.topologicalSpace_H










structure SmoothLocalTrivializationAt
    {n : WithTop ℕ∞}
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {EY HY EX HX EF HF Y X : Type*}
    [NormedAddCommGroup EY] [NormedSpace 𝕜 EY] [TopologicalSpace HY]
    [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
    [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] [TopologicalSpace HF]
    [TopologicalSpace Y] [ChartedSpace HY Y]
    [TopologicalSpace X] [ChartedSpace HX X]
    (IY : ModelWithCorners 𝕜 EY HY)
    (IX : ModelWithCorners 𝕜 EX HX)
    (IF : ModelWithCorners 𝕜 EF HF)
    (F : Type*) [TopologicalSpace F] [ChartedSpace HF F]
    (p : Y → X) (x : X) : Type _ where
  base : TopologicalSpace.Opens X
  mem_base : x ∈ (base : Set X)
  source : TopologicalSpace.Opens Y
  source_eq : (source : Set Y) = p ⁻¹' (base : Set X)
  trivialization :
    Diffeomorph IY (IX.prod IF) (↥source) (↥base × F) n
  proj_fst :
    ∀ y : ↥source, ((trivialization y).1 : X) = p (y : Y)






def IsSmoothLocallyTrivialFibrationWithFiber
    {n : WithTop ℕ∞}
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {EY HY EX HX EF HF Y X : Type*}
    [NormedAddCommGroup EY] [NormedSpace 𝕜 EY] [TopologicalSpace HY]
    [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
    [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] [TopologicalSpace HF]
    [TopologicalSpace Y] [ChartedSpace HY Y]
    [TopologicalSpace X] [ChartedSpace HX X]
    (IY : ModelWithCorners 𝕜 EY HY)
    (IX : ModelWithCorners 𝕜 EX HX)
    (IF : ModelWithCorners 𝕜 EF HF)
    (F : Type*) [TopologicalSpace F] [ChartedSpace HF F]
    (p : Y → X) : Prop :=
  ∀ x : X, Nonempty (SmoothLocalTrivializationAt (n := n) IY IX IF F p x)










structure IsClosedLieSubgroup
    {n : WithTop ℕ∞}
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {EG HG EH HH G : Type*}
    [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [TopologicalSpace HG]
    [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [TopologicalSpace HH]
    (IG : ModelWithCorners 𝕜 EG HG)
    (IH : ModelWithCorners 𝕜 EH HH)
    [Group G] [TopologicalSpace G] [ChartedSpace HG G]
    (H : Subgroup G)
    [ChartedSpace HH H] : Prop where
  isClosed_carrier : IsClosed (H : Set G)
  inclusion_smoothEmbedding :
    Manifold.IsSmoothEmbedding IH IG n (fun h : H => (h : G))










def tangentSubmoduleAtOne
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {EG HG EH HH G : Type*}
    [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [TopologicalSpace HG]
    [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [TopologicalSpace HH]
    (IG : ModelWithCorners 𝕜 EG HG)
    (IH : ModelWithCorners 𝕜 EH HH)
    [Group G] [TopologicalSpace G] [ChartedSpace HG G]
    (H : Subgroup G)
    [ChartedSpace HH H] :
    Submodule 𝕜 (TangentSpace IG (1 : G)) :=
  LinearMap.range
    ((mfderiv IH IG (fun h : H => (h : G)) (1 : H)).toLinearMap)












structure HomogeneousSpaceResult
    {n : WithTop ℕ∞}
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {EG HG EH HH G : Type*}
    [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [TopologicalSpace HG]
    [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [TopologicalSpace HH]
    (IG : ModelWithCorners 𝕜 EG HG)
    (IH : ModelWithCorners 𝕜 EH HH)
    [Group G] [TopologicalSpace G] [ChartedSpace HG G] [LieGroup IG n G]
    (H : Subgroup G)
    [ChartedSpace HH H] [LieGroup IH n H]
    {d : ℕ} (Q : QuotientModel 𝕜 d) : Type _ where
  [quotientTopologicalSpace : TopologicalSpace (G ⧸ H)]
  [quotientT2Space : T2Space (G ⧸ H)]
  [quotientSecondCountableTopology : SecondCountableTopology (G ⧸ H)]
  [quotientChartedSpace : ChartedSpace Q.H (G ⧸ H)]
  [quotientSmoothManifold : IsManifold Q.I n (G ⧸ H)]
  [quotientBoundarylessManifold : BoundarylessManifold Q.I (G ⧸ H)]

  
  projection_quotientMap :
    Topology.IsQuotientMap (QuotientGroup.mk : G → G ⧸ H)

  
  projection_smooth :
    ContMDiff IG Q.I n (QuotientGroup.mk : G → G ⧸ H)

  
  projection_locally_trivial :
    IsSmoothLocallyTrivialFibrationWithFiber (n := n)
      IG Q.I IH H (QuotientGroup.mk : G → G ⧸ H)

  
  quotient_lieGroup_of_normal :
    ∀ [H.Normal], LieGroup Q.I n (G ⧸ H)

  
  tangent_at_identity_coset :
    TangentSpace Q.I (QuotientGroup.mk (1 : G) : G ⧸ H) ≃ₗ[𝕜]
      (TangentSpace IG (1 : G) ⧸ tangentSubmoduleAtOne IG IH H)

  
  tangent_at_identity_coset_comp_projection :
    tangent_at_identity_coset.toLinearMap.comp
        ((mfderiv IG Q.I (QuotientGroup.mk : G → G ⧸ H) (1 : G)).toLinearMap) =
      Submodule.mkQ (tangentSubmoduleAtOne IG IH H)



end Theorem41
end Autoform_Lie_groups_lie_algebras_lie_theorem_4_1
