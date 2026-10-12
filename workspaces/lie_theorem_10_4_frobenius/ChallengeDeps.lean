/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped Manifold ContDiff
open Module

universe u𝕜 uH uE uM

namespace Autoform_Lie_groups_lie_algebras_lie_theorem_10_4_frobenius

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {M : Type uM} [TopologicalSpace M]
variable {I : ModelWithCorners 𝕜 E H}
variable [ChartedSpace H M]
variable [IsManifold I 1 M]









abbrev VField
    (I : ModelWithCorners 𝕜 E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] : Type (max uM uE) :=
  (x : M) → TangentSpace I x






def SmoothOnVField
    (I : ModelWithCorners 𝕜 E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (s : Set M) (V : VField I M) : Prop :=
  ContMDiffOn I I.tangent ∞
    (fun x : M => (⟨x, V x⟩ : TangentBundle I M)) s


def SmoothVField
    (I : ModelWithCorners 𝕜 E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (V : VField I M) : Prop :=
  SmoothOnVField I M Set.univ V










structure SmoothDistribution
    (I : ModelWithCorners 𝕜 E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (k : ℕ) where
  fiber : (x : M) → Submodule 𝕜 (TangentSpace I x)
  local_frame :
    ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ frame : Fin k → VField I M,
        (∀ i : Fin k, SmoothOnVField I M U (frame i)) ∧
        ∀ y ∈ U, ∃ b : Basis (Fin k) 𝕜 (fiber y),
          ∀ i : Fin k, ((b i : fiber y) : TangentSpace I y) = frame i y







def VFieldContainedIn
    {k : ℕ} (D : SmoothDistribution I M k) (V : VField I M) : Prop :=
  ∀ x : M, V x ∈ D.fiber x


def VFieldContainedOn
    {k : ℕ} (D : SmoothDistribution I M k) (U : Set M) (V : VField I M) : Prop :=
  ∀ x ∈ U, V x ∈ D.fiber x









noncomputable def chartCoordDerivWithin
    (e : OpenPartialHomeomorph M H) (s : Set M) (x : M) :
    TangentSpace I x →L[𝕜] E :=
  let L : TangentSpace 𝓘(𝕜, E) ((e.extend I) x) →L[𝕜] E :=
    (NormedSpace.fromTangentSpace ((e.extend I) x)).toContinuousLinearMap
  L.comp
    (mfderivWithin I 𝓘(𝕜, E) (↑(e.extend I) : M → E) s x)










def ChartRepresentsDistribution
    [IsManifold I ∞ M]
    {k : ℕ} (D : SmoothDistribution I M k)
    (e : OpenPartialHomeomorph M H) (F : Submodule 𝕜 E) : Prop :=
  e ∈ IsManifold.maximalAtlas I ∞ M ∧
  Nonempty (Basis (Fin k) 𝕜 F) ∧
  ∀ x ∈ e.source,
    D.fiber x =
      Submodule.comap
        (chartCoordDerivWithin (I := I) e e.source x).toLinearMap
        F








def IsIntegrable
    [IsManifold I ∞ M]
    {k : ℕ} (D : SmoothDistribution I M k) : Prop :=
  ∀ x : M, ∃ e : OpenPartialHomeomorph M H, x ∈ e.source ∧
    ∃ F : Submodule 𝕜 E, ChartRepresentsDistribution D e F













def IsInvolutive
    {k : ℕ} (D : SmoothDistribution I M k) : Prop :=
  ∀ U : Set M, IsOpen U →
    ∀ V W : VField I M,
      SmoothOnVField I M U V →
      SmoothOnVField I M U W →
      VFieldContainedOn D U V →
      VFieldContainedOn D U W →
      VFieldContainedOn D U (VectorField.mlieBracket I V W)



end Autoform_Lie_groups_lie_algebras_lie_theorem_10_4_frobenius
