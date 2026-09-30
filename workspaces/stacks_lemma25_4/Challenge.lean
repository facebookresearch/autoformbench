import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Yoneda
import ChallengeDeps

open Autoform_Stacks_Project_stacks_lemma25_4
noncomputable section

universe u v

open CategoryTheory

namespace Autoform_Stacks_Project_stacks_lemma25_4

variable {C : Type u} [Category.{v, u} C]












theorem toRestrictedHSharp_naturality
    (J : GrothendieckTopology C) (U : C)
    (G : Sheaf (J.over U) (Type (max u v)))
    (X Y : (Over U)ᵒᵖ) (f : X ⟶ Y) :
    G.obj.map f ≫
        (TypeCat.ofHom fun (_ : G.obj.obj Y) =>
          (ConcreteCategory.hom
              (((sheafificationAdjunction J (Type (max u v))).unit.app
                  (uliftYoneda.{u}.obj U)).app
                ((Over.forget U).op.obj Y)))
            (ULift.up (Opposite.unop Y).hom)) =
      (TypeCat.ofHom fun (_ : G.obj.obj X) =>
          (ConcreteCategory.hom
              (((sheafificationAdjunction J (Type (max u v))).unit.app
                  (uliftYoneda.{u}.obj U)).app
                ((Over.forget U).op.obj X)))
            (ULift.up (Opposite.unop X).hom)) ≫
        ((J.overPullback (Type (max u v)) U).obj (hSharp J U)).obj.map f := by
  sorry


















noncomputable def toRestrictedHSharp
    (J : GrothendieckTopology C) (U : C)
    (G : Sheaf (J.over U) (Type (max u v))) :
    G ⟶
      (J.overPullback (Type (max u v)) U).obj (hSharp J U) :=
  Sheaf.homEquiv.symm
    { app := fun X =>
        TypeCat.ofHom fun (_ : G.obj.obj X) =>
          (ConcreteCategory.hom
              (((sheafificationAdjunction J (Type (max u v))).unit.app
                  (uliftYoneda.{u}.obj U)).app
                ((Over.forget U).op.obj X)))
            (ULift.up (Opposite.unop X).hom)
      naturality := fun X Y f => toRestrictedHSharp_naturality J U G X Y f }














noncomputable def lowerShriekToHSharp
    (J : GrothendieckTopology C) (U : C)
    (G : Sheaf (J.over U) (Type (max u v))) :
    ((Over.forget U).sheafPullback
        (Type (max u v)) (J.over U) J).obj G ⟶
      hSharp J U :=
  (((Over.forget U).sheafAdjunctionContinuous
        (Type (max u v)) (J.over U) J).homEquiv
      G (hSharp J U)).symm
    (toRestrictedHSharp J U G)





theorem lowerShriekToHSharp_naturality
    (J : GrothendieckTopology C) (U : C)
    (G H : Sheaf (J.over U) (Type (max u v))) (f : G ⟶ H) :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map f ≫
        lowerShriekToHSharp J U H = lowerShriekToHSharp J U G := by
  sorry











noncomputable def lowerShriekToSlice
    (J : GrothendieckTopology C) (U : C) :
    Sheaf (J.over U) (Type (max u v)) ⥤
      Over (hSharp J U) :=
  ((Over.forget U).sheafPullback
      (Type (max u v)) (J.over U) J).toOver
    (hSharp J U)
    (fun G => lowerShriekToHSharp J U G)
    (fun {G H} f => lowerShriekToHSharp_naturality J U G H f)





theorem lemma25_4
    (J : GrothendieckTopology C) (U : C) :
    (lowerShriekToSlice J U).IsEquivalence := by
  sorry

end Autoform_Stacks_Project_stacks_lemma25_4

end