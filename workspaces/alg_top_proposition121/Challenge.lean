/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import ChallengeDeps




import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.LinearAlgebra.Span.Basic

open Autoform_Algebraic_Topology_I_alg_top_proposition121
















noncomputable section

open CategoryTheory Limits
open scoped BigOperators

namespace Autoform_Algebraic_Topology_I_alg_top_proposition121











abbrev SingCCFunctor : TopCat ⥤ ChainComplex ZModCat ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor ZModCat).obj
    (ModuleCat.of ℤ ℤ))




























theorem linearExtendOnSimplices_simplex
    {X : TopCat} {n : ℕ} {M : ZModCat}
    (f : SingularSimplex X n → M)
    (σ : SingularSimplex X n) :
    linearExtendOnSimplices f (simplexChain σ) = f σ := by
  sorry
























theorem singularAugmentationMap_constZeroChain
    {X : TopCat} (x : ↑X) :
    singularAugmentationMap X (constZeroChain x) = (1 : ℤ) := by
  sorry















theorem coneTailPoint_property (q : ℕ)
    (t : stdSimplex ℝ (Fin ((q + 1) + 1))) :
    (fun i =>
      if coneTailMass q t = 0 then
        (stdSimplex.barycenter (X := Fin (q + 1)) :
          stdSimplex ℝ (Fin (q + 1))) i
      else
        t (Fin.succ i) / coneTailMass q t) ∈ stdSimplex ℝ (Fin (q + 1)) := by
  sorry















noncomputable def coneTailPoint (q : ℕ)
    (t : stdSimplex ℝ (Fin ((q + 1) + 1))) :
    stdSimplex ℝ (Fin (q + 1)) :=
  { val := fun i =>
      if coneTailMass q t = 0 then
        (stdSimplex.barycenter (X := Fin (q + 1)) :
          stdSimplex ℝ (Fin (q + 1))) i
      else
        t (Fin.succ i) / coneTailMass q t
    property := coneTailPoint_property q t }








theorem barycentricConePoint_property
    (n q : ℕ) (σ : SingularSimplex (StdSimplexTop n) q)
    (t : stdSimplex ℝ (Fin ((q + 1) + 1))) :
    (fun i =>
      t 0 * (simplexBarycenter n) i +
        coneTailMass q t * ((simplexMapOf σ).hom (coneTailPoint q t)) i) ∈
      stdSimplex ℝ (Fin (n + 1)) := by
  sorry


















noncomputable def barycentricConePoint
    (n q : ℕ) (σ : SingularSimplex (StdSimplexTop n) q)
    (t : stdSimplex ℝ (Fin ((q + 1) + 1))) :
    stdSimplex ℝ (Fin (n + 1)) :=
  { val := fun i =>
      t 0 * (simplexBarycenter n) i +
        coneTailMass q t * ((simplexMapOf σ).hom (coneTailPoint q t)) i
    property := barycentricConePoint_property n q σ t }








theorem barycentricConeSimplex_continuous
    (n q : ℕ) (σ : SingularSimplex (StdSimplexTop n) q) :
    Continuous (barycentricConePoint n q σ) := by
  sorry














noncomputable def barycentricConeSimplex
    (n q : ℕ) (σ : SingularSimplex (StdSimplexTop n) q) :
    SingularSimplex (StdSimplexTop n) (q + 1) :=
  (TopCat.toSSetObjEquiv (StdSimplexTop n)
      (Opposite.op (SimplexCategory.mk (q + 1)))).symm
    { toFun := barycentricConePoint n q σ
      continuous_toFun := barycentricConeSimplex_continuous n q σ }











noncomputable def barycentricConeMap (n q : ℕ) :
    SingChain (StdSimplexTop n) q ⟶ SingChain (StdSimplexTop n) (q + 1) :=
  linearExtendOnSimplices
    (X := StdSimplexTop n) (n := q)
    (M := SingChain (StdSimplexTop n) (q + 1))
    (fun σ : SingularSimplex (StdSimplexTop n) q =>
      simplexChain (X := StdSimplexTop n) (n := q + 1)
        (barycentricConeSimplex n q σ))






theorem barycentricConeMap_simplex
    (n q : ℕ) (σ : SingularSimplex (StdSimplexTop n) q) :
    barycentricConeMap n q (simplexChain σ) =
      simplexChain (barycentricConeSimplex n q σ) := by
  sorry











theorem barycentricCone_identity_zero (n : ℕ) :
    barycentricConeMap n 0 ≫ boundary (StdSimplexTop n) 0 =
      𝟙 (SingChain (StdSimplexTop n) 0) -
        etaEpsilon (StdSimplexTop n) (simplexBarycenter n) 0 := by
  sorry














theorem barycentricCone_identity_succ (n q : ℕ) :
    barycentricConeMap n (q + 1) ≫ boundary (StdSimplexTop n) (q + 1) +
        boundary (StdSimplexTop n) q ≫ barycentricConeMap n q =
      𝟙 (SingChain (StdSimplexTop n) (q + 1)) -
        etaEpsilon (StdSimplexTop n) (simplexBarycenter n) (q + 1) := by
  sorry






























noncomputable def barycentricSubdivisionUniversal :
    (n : ℕ) → SingChain (StdSimplexTop n) n
  | 0 => universalSimplexChain 0
  | n + 1 =>
      barycentricConeMap (n + 1) n
        ((extendByNaturality n
            (barycentricSubdivisionUniversal n)
            (StdSimplexTop (n + 1)))
          ((boundary (StdSimplexTop (n + 1)) n)
            (universalSimplexChain (n + 1))))













noncomputable def barycentricSubdivision :
    ∀ (X : TopCat) (n : ℕ), SingChain X n ⟶ SingChain X n :=
  fun X n => extendByNaturality n (barycentricSubdivisionUniversal n) X










def UniversalSubdivisionRecursion
    (dollar : DegreewiseChainEndFamily) : Prop :=
  dollar (StdSimplexTop 0) 0 (universalSimplexChain 0) =
      universalSimplexChain 0
  ∧
  ∀ n : ℕ,
    dollar (StdSimplexTop (n + 1)) (n + 1)
        (universalSimplexChain (n + 1)) =
      barycentricConeMap (n + 1) n
        (dollar (StdSimplexTop (n + 1)) n
          ((boundary (StdSimplexTop (n + 1)) n)
            (universalSimplexChain (n + 1))))







def IsBarycentricSubdivisionOperator
    (dollar : DegreewiseChainEndFamily) : Prop :=
  ActsByUniversalSimplex dollar ∧
    UniversalSubdivisionRecursion dollar






theorem barycentricSubdivision_isBarycentricSubdivisionOperator :
    IsBarycentricSubdivisionOperator barycentricSubdivision := by
  sorry































noncomputable def barycentricSubdivisionHomotopyUniversal :
    (n : ℕ) → SingChain (StdSimplexTop n) (n + 1)
  | 0 => 0
  | n + 1 =>
      barycentricConeMap (n + 1) (n + 1)
        (barycentricSubdivisionUniversal (n + 1)
          - universalSimplexChain (n + 1)
          - (extendHomotopyByNaturality n
              (barycentricSubdivisionHomotopyUniversal n)
              (StdSimplexTop (n + 1)))
              ((boundary (StdSimplexTop (n + 1)) n)
                (universalSimplexChain (n + 1))))









noncomputable def barycentricSubdivisionHomotopy :
    ChainHomotopyFamily :=
  fun X n =>
    extendHomotopyByNaturality n
      (barycentricSubdivisionHomotopyUniversal n) X












def UniversalHomotopyRecursion
    (dollar : DegreewiseChainEndFamily)
    (T : ChainHomotopyFamily) : Prop :=
  T (StdSimplexTop 0) 0 (universalSimplexChain 0) = 0
  ∧
  ∀ n : ℕ,
    T (StdSimplexTop (n + 1)) (n + 1)
        (universalSimplexChain (n + 1)) =
      barycentricConeMap (n + 1) (n + 1)
        (dollar (StdSimplexTop (n + 1)) (n + 1)
            (universalSimplexChain (n + 1))
          - universalSimplexChain (n + 1)
          - T (StdSimplexTop (n + 1)) n
              ((boundary (StdSimplexTop (n + 1)) n)
                (universalSimplexChain (n + 1))))








def IsBarycentricSubdivisionHomotopy
    (dollar : DegreewiseChainEndFamily)
    (T : ChainHomotopyFamily) : Prop :=
  HomotopyActsByUniversalSimplex T ∧
    UniversalHomotopyRecursion dollar T






theorem barycentricSubdivisionHomotopy_is_recursive :
    IsBarycentricSubdivisionHomotopy
      barycentricSubdivision
      barycentricSubdivisionHomotopy := by
  sorry









theorem barycentricSubdivisionHomotopy_spec :
    ChainHomotopyToIdentity
        barycentricSubdivision
        barycentricSubdivisionHomotopy
    ∧
    ChainHomotopyNatural barycentricSubdivisionHomotopy := by
  sorry










theorem proposition121 :
    DegreewiseNatural barycentricSubdivision ∧
    ChainMapCondition barycentricSubdivision ∧
    ∃ T : ChainHomotopyFamily,
      ChainHomotopyToIdentity barycentricSubdivision T ∧
      ChainHomotopyNatural T := by
  refine ⟨?natural, ?chainMap, ?homotopy⟩
  · sorry
  · sorry
  · exact ⟨barycentricSubdivisionHomotopy,
      barycentricSubdivisionHomotopy_spec⟩

end Autoform_Algebraic_Topology_I_alg_top_proposition121

end