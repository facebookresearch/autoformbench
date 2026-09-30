import Mathlib

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace

universe u

namespace Autoform_Stacks_Project_stacks_lemma29_3
































noncomputable def pullbackSection
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    (G : Y.Sheaf (Type u)) (U : Opens Y) :
    G.1.obj (op U) →
      ((TopCat.Sheaf.pullback (Type u) f).obj G).1.obj
        (op ((Opens.map f).obj U)) :=
  fun s => by
    simpa using
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app G).1.app
        (op U) s)








noncomputable abbrev lemma29_3SectionsAt
    {I : Type u} [Category.{u} I]
    (X : I ⥤ TopCat.{u}) (i : I)
    (G : (X.obj i).Sheaf (Type u)) (U : Opens (X.obj i))
    (a : Over i) : Type u :=
  ((TopCat.Sheaf.pullback (Type u) (X.map a.hom)).obj G).1.obj
    (op ((Opens.map (X.map a.hom)).obj U))













end Autoform_Stacks_Project_stacks_lemma29_3

end