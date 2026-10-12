/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.Hom
import Mathlib.CategoryTheory.Types.Basic
import ChallengeDeps

open Autoform_Stacks_Project_stacks_lemma29_3
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace

universe u

namespace Autoform_Stacks_Project_stacks_lemma29_3




























noncomputable def sheafPushforwardCompIsoApp
    {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (F : X.Sheaf (Type u)) :
    (TopCat.Sheaf.pushforward (Type u) f ⋙
        TopCat.Sheaf.pushforward (Type u) g).obj F ≅
      (TopCat.Sheaf.pushforward (Type u) (f ≫ g)).obj F :=
  (fullyFaithfulSheafToPresheaf
      (Opens.grothendieckTopology ↑Z) (Type u)).preimageIso
    (TopCat.Presheaf.Pushforward.comp f g F.1).symm




theorem sheafPushforwardCompIsoApp_naturality
    {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F G : X.Sheaf (Type u)) (α : F ⟶ G) :
    (TopCat.Sheaf.pushforward (Type u) f ⋙ TopCat.Sheaf.pushforward (Type u) g).map α ≫
        (sheafPushforwardCompIsoApp f g G).hom =
      (sheafPushforwardCompIsoApp f g F).hom ≫
        (TopCat.Sheaf.pushforward (Type u) (f ≫ g)).map α := by
  sorry






















noncomputable def sheafPushforwardCompIso
    {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pushforward (Type u) f ⋙
        TopCat.Sheaf.pushforward (Type u) g ≅
      TopCat.Sheaf.pushforward (Type u) (f ≫ g) :=
  NatIso.ofComponents
    (fun F => sheafPushforwardCompIsoApp f g F)
    (fun {F G} α => sheafPushforwardCompIsoApp_naturality f g F G α)







noncomputable def sheafPullbackCompIso
    {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pullback (Type u) g ⋙
        TopCat.Sheaf.pullback (Type u) f ≅
      TopCat.Sheaf.pullback (Type u) (f ≫ g) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) g).leftAdjointCompIso
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) (f ≫ g))
    (sheafPushforwardCompIso f g)





noncomputable def pullbackSectionComp
    {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (G : Z.Sheaf (Type u)) (U : Opens Z) :
    ((TopCat.Sheaf.pullback (Type u) g).obj G).1.obj
        (op ((Opens.map g).obj U)) →
      ((TopCat.Sheaf.pullback (Type u) (f ≫ g)).obj G).1.obj
        (op ((Opens.map (f ≫ g)).obj U)) :=
  fun s => by
    let t :=
      pullbackSection f ((TopCat.Sheaf.pullback (Type u) g).obj G)
        ((Opens.map g).obj U) s
    simpa using
      (((sheafPullbackCompIso f g).hom.app G).1.app
        (op ((Opens.map f).obj ((Opens.map g).obj U))) t)





noncomputable def lemma29_3SectionMap
    {I : Type u} [Category.{u} I]
    (X : I ⥤ TopCat.{u}) (i : I)
    (G : (X.obj i).Sheaf (Type u)) (U : Opens (X.obj i))
    {a b : (Over i)ᵒᵖ} (α : a ⟶ b) :
    lemma29_3SectionsAt X i G U a.unop ⟶ lemma29_3SectionsAt X i G U b.unop :=
  TypeCat.ofHom (fun s : lemma29_3SectionsAt X i G U a.unop => by
    have h : X.map α.unop.left ≫ X.map a.unop.hom = X.map b.unop.hom := by
      rw [← X.map_comp, Over.w]
    show ((TopCat.Sheaf.pullback (Type u) (X.map b.unop.hom)).obj G).1.obj
      (op ((Opens.map (X.map b.unop.hom)).obj U))
    exact h ▸ pullbackSectionComp (X.map α.unop.left) (X.map a.unop.hom) G U s)




theorem lemma29_3SectionMap_id
    {I : Type u} [Category.{u} I]
    (X : I ⥤ TopCat.{u}) (i : I)
    (G : (X.obj i).Sheaf (Type u)) (U : Opens (X.obj i))
    (a : (Over i)ᵒᵖ) :
    lemma29_3SectionMap X i G U (𝟙 a) = 𝟙 (lemma29_3SectionsAt X i G U a.unop) := by
  sorry





theorem lemma29_3SectionMap_comp
    {I : Type u} [Category.{u} I]
    (X : I ⥤ TopCat.{u}) (i : I)
    (G : (X.obj i).Sheaf (Type u)) (U : Opens (X.obj i))
    (a b c : (Over i)ᵒᵖ) (α : a ⟶ b) (β : b ⟶ c) :
    lemma29_3SectionMap X i G U (α ≫ β) =
      lemma29_3SectionMap X i G U α ≫ lemma29_3SectionMap X i G U β := by
  sorry













noncomputable def lemma29_3SectionDiagram
    {I : Type u} [Category.{u} I]
    (X : I ⥤ TopCat.{u}) (i : I)
    (G : (X.obj i).Sheaf (Type u)) (U : Opens (X.obj i)) :
    (Over i)ᵒᵖ ⥤ Type u where
  obj a := lemma29_3SectionsAt X i G U a.unop
  map α := lemma29_3SectionMap X i G U α
  map_id a := lemma29_3SectionMap_id X i G U a
  map_comp {a b c} α β := lemma29_3SectionMap_comp X i G U a b c α β






noncomputable def lemma29_3SectionCoconeApp
    {I : Type u} [Category.{u} I]
    (X : I ⥤ TopCat.{u}) (i : I)
    (G : (X.obj i).Sheaf (Type u)) (U : Opens (X.obj i))
    (a : (Over i)ᵒᵖ) :
    lemma29_3SectionsAt X i G U a.unop ⟶
      ((TopCat.Sheaf.pullback (Type u) (limit.π X i)).obj G).1.obj
        (op ((Opens.map (limit.π X i)).obj U)) :=
  TypeCat.ofHom (fun s : lemma29_3SectionsAt X i G U a.unop => by
    have h : limit.π X a.unop.left ≫ X.map a.unop.hom = limit.π X i :=
      limit.w X a.unop.hom
    show ((TopCat.Sheaf.pullback (Type u) (limit.π X i)).obj G).1.obj
      (op ((Opens.map (limit.π X i)).obj U))
    exact h ▸ pullbackSectionComp (limit.π X a.unop.left)
      (X.map a.unop.hom) G U s)




theorem lemma29_3SectionCoconeApp_naturality
    {I : Type u} [Category.{u} I]
    (X : I ⥤ TopCat.{u}) (i : I)
    (G : (X.obj i).Sheaf (Type u)) (U : Opens (X.obj i))
    (a b : (Over i)ᵒᵖ) (α : a ⟶ b) :
    (lemma29_3SectionDiagram X i G U).map α ≫ lemma29_3SectionCoconeApp X i G U b =
      lemma29_3SectionCoconeApp X i G U a ≫
        ((Functor.const (Over i)ᵒᵖ).obj
            (((TopCat.Sheaf.pullback (Type u) (limit.π X i)).obj G).1.obj
              (op ((Opens.map (limit.π X i)).obj U)))).map α := by
  sorry









noncomputable def lemma29_3SectionCocone
    {I : Type u} [Category.{u} I]
    (X : I ⥤ TopCat.{u}) (i : I)
    (G : (X.obj i).Sheaf (Type u)) (U : Opens (X.obj i)) :
    Cocone (lemma29_3SectionDiagram X i G U) where
  pt :=
    ((TopCat.Sheaf.pullback (Type u) (limit.π X i)).obj G).1.obj
      (op ((Opens.map (limit.π X i)).obj U))
  ι :=
    { app := fun a => lemma29_3SectionCoconeApp X i G U a
      naturality := fun a b α => lemma29_3SectionCoconeApp_naturality X i G U a b α }








theorem lemma29_3
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (X : I ⥤ TopCat.{u})
    (hX : ∀ j, SpectralSpace ↑(X.obj j))
    (hmap : ∀ {j k : I} (a : j ⟶ k),
      IsSpectralMap ⇑(ConcreteCategory.hom (X.map a)))
    (i : I)
    (G : (X.obj i).Sheaf (Type u))
    (U : Opens (X.obj i))
    (hU : IsCompact (U : Set ↑(X.obj i))) :
    Nonempty (IsColimit (lemma29_3SectionCocone X i G U)) := by
  sorry

end Autoform_Stacks_Project_stacks_lemma29_3

end