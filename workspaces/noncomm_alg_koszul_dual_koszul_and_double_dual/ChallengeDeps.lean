/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


































universe u v wι

namespace Autoform_Noncommutative_Algebra_noncomm_alg_koszul_dual_koszul_and_double_dual

noncomputable section

variable (k : Type u) [Field k]









def quadraticTensorAlgebraRelation
    (V : Type v) [AddCommGroup V] [Module k V]
    (I : Submodule k (TensorPower k 2 V)) :
    TensorAlgebra k V → TensorAlgebra k V → Prop :=
  fun a b =>
    ∃ x : TensorPower k 2 V,
      x ∈ I ∧
        a = TensorPower.toTensorAlgebra (R := k) (M := V) x ∧
          b = 0




abbrev QuadraticQuotient
    (V : Type v) [AddCommGroup V] [Module k V]
    (I : Submodule k (TensorPower k 2 V)) : Type _ :=
  RingQuot (quadraticTensorAlgebraRelation (k := k) V I)










def quadraticDualRelation
    (V : Type v) [AddCommGroup V] [Module k V]
    (I : Submodule k (TensorPower k 2 V)) :
    Submodule k (TensorPower k 2 (Module.Dual k V)) :=
  I.dualAnnihilator.comap
    (PiTensorProduct.dualDistrib
      (R := k) (M := fun _ : Fin 2 => V))








abbrev QuadraticDualQuotient
    (V : Type v) [AddCommGroup V] [Module k V]
    (I : Submodule k (TensorPower k 2 V)) : Type _ :=
  QuadraticQuotient (k := k) (Module.Dual k V)
    (quadraticDualRelation (k := k) V I)







abbrev DoubleQuadraticDualQuotient
    (V : Type v) [AddCommGroup V] [Module k V]
    (I : Submodule k (TensorPower k 2 V)) : Type _ :=
  QuadraticDualQuotient (k := k) (Module.Dual k V)
    (quadraticDualRelation (k := k) V I)













def tensorPowerTripleMul
    (V : Type v) [AddCommGroup V] [Module k V]
    {n i : ℕ} (h : i + 2 ≤ n)
    (x : TensorPower k i V)
    (y : TensorPower k 2 V)
    (z : TensorPower k (n - (i + 2)) V) :
    TensorPower k n V :=
  let xy : TensorPower k (i + 2) V :=
    (TensorPower.mulEquiv (R := k) (M := V) (n := i) (m := 2))
      (TensorProduct.tmul k x y)
  (TensorPower.cast k V (Nat.add_sub_of_le h))
    ((TensorPower.mulEquiv (R := k) (M := V)
        (n := i + 2) (m := n - (i + 2)))
      (TensorProduct.tmul k xy z))











def quadraticRelationSubspace
    (V : Type v) [AddCommGroup V] [Module k V]
    (I : Submodule k (TensorPower k 2 V))
    (n i : ℕ) :
    Submodule k (TensorPower k n V) :=
  if h : i + 2 ≤ n then
    Submodule.span k
      { t : TensorPower k n V |
        ∃ x : TensorPower k i V,
        ∃ y : I,
        ∃ z : TensorPower k (n - (i + 2)) V,
          t = tensorPowerTripleMul (k := k) V h
            x (y : TensorPower k 2 V) z }
  else
    ⊥





inductive InGeneratedSubspaceLattice
    {W : Type v} [AddCommGroup W] [Module k W]
    {ι : Type wι}
    (S : ι → Submodule k W) :
    Submodule k W → Prop
  | bot : InGeneratedSubspaceLattice S ⊥
  | top : InGeneratedSubspaceLattice S ⊤
  | basic (i : ι) : InGeneratedSubspaceLattice S (S i)
  | sup {X Y : Submodule k W} :
      InGeneratedSubspaceLattice S X →
      InGeneratedSubspaceLattice S Y →
      InGeneratedSubspaceLattice S (X ⊔ Y)
  | inf {X Y : Submodule k W} :
      InGeneratedSubspaceLattice S X →
      InGeneratedSubspaceLattice S Y →
      InGeneratedSubspaceLattice S (X ⊓ Y)




def GeneratesDistributiveSubmoduleLattice
    {W : Type v} [AddCommGroup W] [Module k W]
    {ι : Type wι}
    (S : ι → Submodule k W) : Prop :=
  ∀ X Y Z : Submodule k W,
    InGeneratedSubspaceLattice (k := k) S X →
    InGeneratedSubspaceLattice (k := k) S Y →
    InGeneratedSubspaceLattice (k := k) S Z →
      X ⊓ (Y ⊔ Z) = (X ⊓ Y) ⊔ (X ⊓ Z)











def IsKoszulQuadraticData
    (V : Type v) [AddCommGroup V] [Module k V]
    (I : Submodule k (TensorPower k 2 V)) : Prop :=
  ∀ n : ℕ,
    GeneratesDistributiveSubmoduleLattice (k := k)
      (fun i : Fin (n - 1) =>
        quadraticRelationSubspace (k := k) V I n (i : ℕ))



end

end Autoform_Noncommutative_Algebra_noncomm_alg_koszul_dual_koszul_and_double_dual
