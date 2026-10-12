/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Category.Cat.Colimit
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.Hypercover.Zero
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Pullback
import ChallengeDeps

open Autoform_Stacks_Project_stacks_lemma18_5
universe u

open CategoryTheory
open CategoryTheory.Limits
open Opposite



noncomputable section




















namespace Autoform_Stacks_Project_stacks_lemma18_5

namespace PreZeroHypercover





end PreZeroHypercover









theorem coverage_pullback {C : Type u} [Category.{u} C] (S : StacksSite C) :
    ∀ ⦃X Y : C⦄ (f : Y ⟶ X) (R : Presieve X)
      (_ : R ∈ { R | ∃ E : PreZeroHypercover.{u} X,
          E ∈ S.coveringFamilies X ∧ R = E.presieve₀ }),
      ∃ T : Presieve Y,
        T ∈ { R | ∃ E : PreZeroHypercover.{u} Y,
            E ∈ S.coveringFamilies Y ∧ R = E.presieve₀ } ∧
          T.FactorsThruAlong R f := by
  sorry

namespace StacksSite





end StacksSite




namespace StacksSite







noncomputable def coverage {C : Type u} [Category.{u} C] (S : StacksSite C) :
    Coverage C where
  coverings X :=
    { R | ∃ E : PreZeroHypercover.{u} X,
        E ∈ S.coveringFamilies X ∧ R = E.presieve₀ }
  pullback := coverage_pullback S
end StacksSite

namespace StacksSite





noncomputable def topology {C : Type u} [Category.{u} C] (S : StacksSite C) :
    GrothendieckTopology C :=
  S.coverage.toGrothendieck
end StacksSite

theorem toMathlib
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {G : C ⥤ D} {S : StacksSite C} {T : StacksSite D}
    (h : IsContinuousForStacksSites G S T) :
    G.IsContinuous S.topology T.topology := by
  sorry






theorem sheafPushforward_isRightAdjoint
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {G : C ⥤ D} {S : StacksSite C} {T : StacksSite D}
    (h : IsContinuousForStacksSites G S T) :
    letI : G.IsContinuous S.topology T.topology := toMathlib h
    (G.sheafPushforwardContinuous
      (Type u) S.topology T.topology).IsRightAdjoint := by
  sorry



namespace IsMorphismOfSites

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {G : C ⥤ D} {S : StacksSite C} {T : StacksSite D}





end IsMorphismOfSites



variable {I : Type u} [Category.{u} I] [IsCofiltered I]

namespace Situation18_1











end Situation18_1










structure IsMorphismOfSites
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (G : C ⥤ D) (S : StacksSite C) (T : StacksSite D) : Prop where
  continuous : IsContinuousForStacksSites G S T
  leftExact :
    letI : G.IsContinuous S.topology T.topology := toMathlib continuous
    letI : (G.sheafPushforwardContinuous
      (Type u) S.topology T.topology).IsRightAdjoint :=
      sheafPushforward_isRightAdjoint continuous
    PreservesFiniteLimits (G.sheafPullback (Type u) S.topology T.topology)

namespace IsMorphismOfSites

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {G : C ⥤ D} {S : StacksSite C} {T : StacksSite D}


@[reducible] noncomputable def mathlibContinuous (h : IsMorphismOfSites G S T) :
    G.IsContinuous S.topology T.topology :=
  toMathlib h.continuous
end IsMorphismOfSites

namespace IsMorphismOfSites

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {G : C ⥤ D} {S : StacksSite C} {T : StacksSite D}


@[reducible] noncomputable def rightAdjoint (h : IsMorphismOfSites G S T) :
    letI : G.IsContinuous S.topology T.topology := h.mathlibContinuous
    (G.sheafPushforwardContinuous
      (Type u) S.topology T.topology).IsRightAdjoint :=
  sheafPushforward_isRightAdjoint h.continuous
end IsMorphismOfSites


structure Situation18_1 (I : Type u) [Category.{u} I] [IsCofiltered I] where
  
  C : Iᵒᵖ ⥤ Cat.{u, u}
  
  site : ∀ i : I, StacksSite (C.obj (op i))
  
  finiteCoverings :
    ∀ (i : I) {X : C.obj (op i)} (E : PreZeroHypercover.{u} X),
      E ∈ (site i).coveringFamilies X → Finite E.I₀
  



  transitionIsMorphism :
    ∀ {i j : I} (a : j ⟶ i),
      IsMorphismOfSites
        (C.map a.op).toFunctor
        (site i)
        (site j)

namespace Situation18_1
abbrev levelCategory (S : Situation18_1 I) (i : I) : Type u :=
  S.C.obj (op i)
end Situation18_1

namespace Situation18_1
noncomputable abbrev levelTopology (S : Situation18_1 I) (i : I) :
    GrothendieckTopology (levelCategory S i) :=
  (S.site i).topology
end Situation18_1

namespace Situation18_1

noncomputable abbrev colimitCategory (S : Situation18_1 I) :=
  colimit S.C
end Situation18_1

namespace Situation18_1

noncomputable abbrev inclusion (S : Situation18_1 I) (i : I) :
    levelCategory S i ⥤ colimitCategory S :=
  (colimit.ι S.C (op i)).toFunctor
end Situation18_1

namespace Situation18_1










noncomputable def colimitCoveringFamilies
    (S : Situation18_1 I) (X : colimitCategory S) :
    Set (PreZeroHypercover.{u} X) :=
  { E | ∃ (i : I) (Xi : levelCategory S i)
      (Ei : PreZeroHypercover.{u} Xi),
      Ei ∈ (S.site i).coveringFamilies Xi ∧
        ∃ e : (inclusion S i).obj Xi ≅ X,
          Nonempty (E ≅
              PreZeroHypercover.transportTarget (PreZeroHypercover.map (inclusion S i) Ei) e) ∧
            Finite E.I₀ }
end Situation18_1

theorem lemma18_2_site_hasIsos (S : Situation18_1 I)
    {X Y : Situation18_1.colimitCategory S} (f : Y ⟶ X) [IsIso f] :
    PreZeroHypercover.singleton f ∈ S.colimitCoveringFamilies X := by
  sorry


theorem lemma18_2_site_hasPullbacks (S : Situation18_1 I)
    {X : Situation18_1.colimitCategory S} (E : PreZeroHypercover.{u} X)
    (hE : E ∈ S.colimitCoveringFamilies X)
    {Y : Situation18_1.colimitCategory S} (f : Y ⟶ X) (i : E.I₀) :
    HasPullback (E.f i) f := by
  sorry


theorem lemma18_2_site_stableUnderBaseChange (S : Situation18_1 I)
    {X Y : Situation18_1.colimitCategory S} (E : PreZeroHypercover.{u} X)
    (hE : E ∈ S.colimitCoveringFamilies X) (f : Y ⟶ X) :
    letI : ∀ i : E.I₀, HasPullback (E.f i) f :=
      fun i => lemma18_2_site_hasPullbacks S E hE f i
    PreZeroHypercover.pullback₂ f E ∈ S.colimitCoveringFamilies Y := by
  sorry


theorem lemma18_2_site_stableUnderComposition (S : Situation18_1 I)
    {X : Situation18_1.colimitCategory S} (E : PreZeroHypercover.{u} X)
    (F : ∀ i : E.I₀, PreZeroHypercover.{u} (E.X i))
    (hE : E ∈ S.colimitCoveringFamilies X)
    (hF : ∀ i, F i ∈ S.colimitCoveringFamilies (E.X i)) :
    E.bind F ∈ S.colimitCoveringFamilies X := by
  sorry

namespace Situation18_1





end Situation18_1


namespace Situation18_1




noncomputable def lemma18_2_site (S : Situation18_1 I) :
    StacksSite (colimitCategory S) where
  coveringFamilies := colimitCoveringFamilies S
  hasIsos := lemma18_2_site_hasIsos S
  hasPullbacks := lemma18_2_site_hasPullbacks S
  stableUnderBaseChange := lemma18_2_site_stableUnderBaseChange S
  stableUnderComposition := lemma18_2_site_stableUnderComposition S
end Situation18_1

namespace Situation18_1

noncomputable abbrev colimitTopology (S : Situation18_1 I) :
    GrothendieckTopology (colimitCategory S) :=
  (lemma18_2_site S).topology
end Situation18_1


theorem inclusionIsMorphism_mapsCoverings (S : Situation18_1 I) (i : I)
    {X : Situation18_1.levelCategory S i} (E : PreZeroHypercover.{u} X)
    (hE : E ∈ (S.site i).coveringFamilies X) :
    PreZeroHypercover.map (S.inclusion i) E ∈
      S.lemma18_2_site.coveringFamilies ((S.inclusion i).obj X) := by
  sorry



theorem inclusionIsMorphism_preservesCoverPullbacks (S : Situation18_1 I) (i : I)
    {X Y : Situation18_1.levelCategory S i} (E : PreZeroHypercover.{u} X)
    (hE : E ∈ (S.site i).coveringFamilies X)
    (k : E.I₀) (f : Y ⟶ X) {P : Situation18_1.levelCategory S i}
    (fst : P ⟶ E.X k) (snd : P ⟶ Y)
    (hfst : IsPullback fst snd (E.f k) f) :
    IsPullback ((S.inclusion i).map fst) ((S.inclusion i).map snd)
      ((S.inclusion i).map (E.f k)) ((S.inclusion i).map f) := by
  sorry





theorem inclusionIsMorphism_continuous (S : Situation18_1 I) (i : I) :
    IsContinuousForStacksSites (S.inclusion i) (S.site i) S.lemma18_2_site where
  mapsCoverings := inclusionIsMorphism_mapsCoverings S i
  preservesCoverPullbacks := inclusionIsMorphism_preservesCoverPullbacks S i

theorem inclusionIsMorphism_leftExact (S : Situation18_1 I) (i : I) :
    letI : (Situation18_1.inclusion S i).IsContinuous
        (S.site i).topology S.lemma18_2_site.topology :=
      toMathlib (inclusionIsMorphism_continuous S i)
    letI : ((Situation18_1.inclusion S i).sheafPushforwardContinuous
        (Type u) (S.site i).topology S.lemma18_2_site.topology).IsRightAdjoint :=
      sheafPushforward_isRightAdjoint (inclusionIsMorphism_continuous S i)
    PreservesFiniteLimits ((Situation18_1.inclusion S i).sheafPullback
      (Type u) (S.site i).topology S.lemma18_2_site.topology) := by
  sorry

namespace Situation18_1



end Situation18_1









namespace Situation18_1













end Situation18_1


namespace Situation18_1




noncomputable def inclusionIsMorphism (S : Situation18_1 I) (i : I) :
    IsMorphismOfSites (inclusion S i) (S.site i) (lemma18_2_site S) where
  continuous := inclusionIsMorphism_continuous S i
  leftExact := inclusionIsMorphism_leftExact S i
end Situation18_1

scoped instance inclusionContinuousInstance
    (S : Situation18_1 I) (i : I) :
    (Situation18_1.inclusion S i).IsContinuous
      (Situation18_1.levelTopology S i) (Situation18_1.colimitTopology S) :=
  (Situation18_1.inclusionIsMorphism S i).mathlibContinuous

scoped instance inclusionRightAdjointInstance
    (S : Situation18_1 I) (i : I) :
    ((Situation18_1.inclusion S i).sheafPushforwardContinuous
      (Type u) (Situation18_1.levelTopology S i)
      (Situation18_1.colimitTopology S)).IsRightAdjoint :=
  (Situation18_1.inclusionIsMorphism S i).rightAdjoint

scoped instance transitionContinuousInstance
    (S : Situation18_1 I) {i j : I} (a : j ⟶ i) :
    ((S.C.map a.op).toFunctor).IsContinuous
      (Situation18_1.levelTopology S i) (Situation18_1.levelTopology S j) :=
  (S.transitionIsMorphism a).mathlibContinuous

scoped instance transitionRightAdjointInstance
    (S : Situation18_1 I) {i j : I} (a : j ⟶ i) :
    (((S.C.map a.op).toFunctor).sheafPushforwardContinuous
      (Type u) (Situation18_1.levelTopology S i)
      (Situation18_1.levelTopology S j)).IsRightAdjoint :=
  (S.transitionIsMorphism a).rightAdjoint

namespace Situation18_1

noncomputable def inclusionCompIso
    (S : Situation18_1 I) {i j : I} (a : j ⟶ i) :
    (S.C.map a.op).toFunctor ⋙ inclusion S j ≅ inclusion S i :=
  eqToIso (by
    simpa only [inclusion, Cat.Hom.comp_toFunctor] using
      congrArg
        (fun q : S.C.obj (op i) ⟶ colimit S.C => q.toFunctor)
        (colimit.w S.C a.op))
end Situation18_1

namespace Situation18_1

noncomputable def pushforwardCompIso
    (S : Situation18_1 I) {i j : I} (a : j ⟶ i) :
    (inclusion S j).sheafPushforwardContinuous
        (Type u) (levelTopology S j) (colimitTopology S) ⋙
      ((S.C.map a.op).toFunctor).sheafPushforwardContinuous
        (Type u) (levelTopology S i) (levelTopology S j) ≅
    (inclusion S i).sheafPushforwardContinuous
      (Type u) (levelTopology S i) (colimitTopology S) :=
  Functor.sheafPushforwardContinuousComp'
    (inclusionCompIso S a) (Type u)
    (levelTopology S i) (levelTopology S j) (colimitTopology S)
end Situation18_1

namespace Situation18_1

noncomputable def pullbackCompIso
    (S : Situation18_1 I) {i j : I} (a : j ⟶ i) :
    ((S.C.map a.op).toFunctor).sheafPullback
        (Type u) (levelTopology S i) (levelTopology S j) ⋙
      (inclusion S j).sheafPullback
        (Type u) (levelTopology S j) (colimitTopology S) ≅
    (inclusion S i).sheafPullback
      (Type u) (levelTopology S i) (colimitTopology S) :=
  (((S.C.map a.op).toFunctor).sheafAdjunctionContinuous
      (Type u) (levelTopology S i) (levelTopology S j)).leftAdjointCompIso
    ((inclusion S j).sheafAdjunctionContinuous
      (Type u) (levelTopology S j) (colimitTopology S))
    ((inclusion S i).sheafAdjunctionContinuous
      (Type u) (levelTopology S i) (colimitTopology S))
    (pushforwardCompIso S a)
end Situation18_1

namespace Situation18_1






noncomputable def canonicalPhi
    (S : Situation18_1 I) {i j : I} (a : j ⟶ i)
    (F : Sheaf (colimitTopology S) (Type u)) :
    (((S.C.map a.op).toFunctor).sheafPullback
      (Type u) (levelTopology S i) (levelTopology S j)).obj
        (((inclusion S i).sheafPushforwardContinuous
          (Type u) (levelTopology S i) (colimitTopology S)).obj F) ⟶
      ((inclusion S j).sheafPushforwardContinuous
        (Type u) (levelTopology S j) (colimitTopology S)).obj F :=
  ((((S.C.map a.op).toFunctor).sheafAdjunctionContinuous
      (Type u) (levelTopology S i) (levelTopology S j)).homEquiv _ _).symm
    ((pushforwardCompIso S a).inv.app F)
end Situation18_1

namespace Situation18_1

noncomputable def stage
    (S : Situation18_1 I) (F : Sheaf (colimitTopology S) (Type u)) (i : I) :
    Sheaf (colimitTopology S) (Type u) :=
  ((inclusion S i).sheafPullback
    (Type u) (levelTopology S i) (colimitTopology S)).obj
      (((inclusion S i).sheafPushforwardContinuous
        (Type u) (levelTopology S i) (colimitTopology S)).obj F)
end Situation18_1

namespace Situation18_1




noncomputable def transitionMap
    (S : Situation18_1 I) {i j : I} (a : j ⟶ i)
    (F : Sheaf (colimitTopology S) (Type u)) :
    stage S F i ⟶ stage S F j :=
  (pullbackCompIso S a).inv.app
      (((inclusion S i).sheafPushforwardContinuous
        (Type u) (levelTopology S i) (colimitTopology S)).obj F) ≫
    ((inclusion S j).sheafPullback
      (Type u) (levelTopology S j) (colimitTopology S)).map
        (canonicalPhi S a F)
end Situation18_1


theorem lemma18_5Diagram_map_id (S : Situation18_1 I)
    (F : Sheaf (Situation18_1.colimitTopology S) (Type u)) (X : Iᵒᵖ) :
    S.transitionMap (𝟙 X).unop F = 𝟙 (S.stage F (unop X)) := by
  sorry



theorem lemma18_5Diagram_map_comp (S : Situation18_1 I)
    (F : Sheaf (Situation18_1.colimitTopology S) (Type u))
    {X Y Z : Iᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    S.transitionMap (f ≫ g).unop F =
      S.transitionMap f.unop F ≫ S.transitionMap g.unop F := by
  sorry

namespace Situation18_1



end Situation18_1


namespace Situation18_1






noncomputable def lemma18_5Diagram
    (S : Situation18_1 I) (F : Sheaf (colimitTopology S) (Type u)) :
    Iᵒᵖ ⥤ Sheaf (colimitTopology S) (Type u) where
  obj i := stage S F i.unop
  map a := transitionMap S a.unop F
  map_id := lemma18_5Diagram_map_id S F
  map_comp := lemma18_5Diagram_map_comp S F
end Situation18_1


theorem lemma18_5Cocone_naturality (S : Situation18_1 I)
    (F : Sheaf (Situation18_1.colimitTopology S) (Type u))
    ⦃X Y : Iᵒᵖ⦄ (f : X ⟶ Y) :
    (S.lemma18_5Diagram F).map f ≫
        ((S.inclusion (unop Y)).sheafAdjunctionContinuous
          (Type u) (S.levelTopology (unop Y))
          (Situation18_1.colimitTopology S)).counit.app F =
      ((S.inclusion (unop X)).sheafAdjunctionContinuous
        (Type u) (S.levelTopology (unop X))
        (Situation18_1.colimitTopology S)).counit.app F ≫
        ((Functor.const Iᵒᵖ).obj F).map f := by
  sorry

namespace Situation18_1



end Situation18_1


namespace Situation18_1




noncomputable def lemma18_5Cocone
    (S : Situation18_1 I) (F : Sheaf (colimitTopology S) (Type u)) :
    Cocone (lemma18_5Diagram S F) where
  pt := F
  ι :=
    { app := fun i =>
        ((inclusion S i.unop).sheafAdjunctionContinuous
          (Type u) (levelTopology S i.unop) (colimitTopology S)).counit.app F
      naturality := lemma18_5Cocone_naturality S F }
end Situation18_1




theorem lemma18_5
    (S : Situation18_1 I) (F : Sheaf (Situation18_1.colimitTopology S) (Type u)) :
    Nonempty (IsColimit (S.lemma18_5Cocone F)) := by
  sorry

end Autoform_Stacks_Project_stacks_lemma18_5

end
