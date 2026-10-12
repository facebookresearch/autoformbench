/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

universe u v

open CategoryTheory

namespace Autoform_Stacks_Project_stacks_lemma25_4

variable {C : Type u} [Category.{v, u} C]





noncomputable def hSharp
    (J : GrothendieckTopology C) (U : C) :
    Sheaf J (Type (max u v)) :=
  (presheafToSheaf J (Type (max u v))).obj
    (uliftYoneda.{u}.obj U)










end Autoform_Stacks_Project_stacks_lemma25_4

end