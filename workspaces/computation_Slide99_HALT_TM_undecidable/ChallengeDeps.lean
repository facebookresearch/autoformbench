/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

set_option autoImplicit false
























namespace Autoform_Introduction_to_the_Theory_of_Computation_computation_Slide99_HALT_TM_undecidable






def HALT_TM : Set (Nat.Partrec.Code × Nat) :=
  {p | (p.1.eval p.2).Dom}



end Autoform_Introduction_to_the_Theory_of_Computation_computation_Slide99_HALT_TM_undecidable
