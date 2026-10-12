/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

















noncomputable section

open CategoryTheory Limits
open scoped BigOperators

namespace Autoform_Algebraic_Topology_I_alg_top_proposition121

abbrev ZModCat := ModuleCat ℤ








abbrev SingCC (X : TopCat) : ChainComplex ZModCat ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor ZModCat).obj
    (ModuleCat.of ℤ ℤ)).obj X








abbrev SingCCMap {X Y : TopCat} (f : X ⟶ Y) : SingCC X ⟶ SingCC Y :=
  (((AlgebraicTopology.singularChainComplexFunctor ZModCat).obj
    (ModuleCat.of ℤ ℤ)).map f)







abbrev SingChain (X : TopCat) (n : ℕ) : ZModCat :=
  (SingCC X).X n







abbrev SingChainMap {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    SingChain X n ⟶ SingChain Y n :=
  (SingCCMap f).f n








abbrev boundary (X : TopCat) (n : ℕ) :
    SingChain X (n + 1) ⟶ SingChain X n :=
  (SingCC X).d (n + 1) n







abbrev StdSimplexTop (n : ℕ) : TopCat :=
  TopCat.of (stdSimplex ℝ (Fin (n + 1)))








abbrev SingularSimplex (X : TopCat) (n : ℕ) : Type _ :=
  (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))








noncomputable def zsmulLinearMap {M : ZModCat} (m : M) :
    ℤ →ₗ[ℤ] M :=
  LinearMap.toSpanSingleton ℤ (↑M) m







noncomputable def zsmulHom {M : ZModCat} (m : M) :
    ModuleCat.of ℤ ℤ ⟶ M :=
  ModuleCat.ofHom (zsmulLinearMap m)













noncomputable def linearExtendOnSimplices
    {X : TopCat} {n : ℕ} {M : ZModCat}
    (f : SingularSimplex X n → M) :
    SingChain X n ⟶ M :=
  Sigma.desc (fun σ : SingularSimplex X n => zsmulHom (f σ))








noncomputable def simplexChain {X : TopCat} {n : ℕ}
    (σ : SingularSimplex X n) : SingChain X n :=
  (Sigma.ι (fun _ : SingularSimplex X n => ModuleCat.of ℤ ℤ) σ) (1 : ℤ)










noncomputable def universalSimplex (n : ℕ) :
    SingularSimplex (StdSimplexTop n) n :=
  (TopCat.toSSetObjEquiv (StdSimplexTop n)
      (Opposite.op (SimplexCategory.mk n))).symm
    (ContinuousMap.id (stdSimplex ℝ (Fin (n + 1))))







noncomputable def universalSimplexChain (n : ℕ) :
    SingChain (StdSimplexTop n) n :=
  simplexChain (universalSimplex n)








noncomputable def simplexMapOf {X : TopCat} {n : ℕ}
    (σ : SingularSimplex X n) : StdSimplexTop n ⟶ X :=
  TopCat.ofHom
    ((TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))) σ)








noncomputable def simplexBarycenter (n : ℕ) : ↑(StdSimplexTop n) :=
  (stdSimplex.barycenter (X := Fin (n + 1)) :
    stdSimplex ℝ (Fin (n + 1)))







abbrev ZeroSimplex (X : TopCat) : Type _ :=
  SingularSimplex X 0









noncomputable def zeroSimplexOfPoint {X : TopCat} (x : ↑X) :
    ZeroSimplex X :=
  (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk 0))).symm
    (ContinuousMap.const (stdSimplex ℝ (Fin 1)) x)







noncomputable def constZeroChain {X : TopCat} (x : ↑X) :
    SingChain X 0 :=
  simplexChain (zeroSimplexOfPoint x)










noncomputable def singularAugmentationMap (X : TopCat) :
    SingChain X 0 ⟶ ModuleCat.of ℤ ℤ :=
  linearExtendOnSimplices
    (X := X) (n := 0) (M := ModuleCat.of ℤ ℤ)
    (fun _ : SingularSimplex X 0 => (1 : ModuleCat.of ℤ ℤ))










noncomputable def etaAtPoint {X : TopCat} (b : ↑X) :
    ModuleCat.of ℤ ℤ ⟶ SingChain X 0 :=
  zsmulHom (constZeroChain b)

















noncomputable def etaEpsilon (X : TopCat) (b : ↑X) :
    ∀ n : ℕ, SingChain X n ⟶ SingChain X n
  | 0 => singularAugmentationMap X ≫ etaAtPoint b
  | _ + 1 => 0










noncomputable def coneTailMass (q : ℕ)
    (t : stdSimplex ℝ (Fin ((q + 1) + 1))) : ℝ :=
  ∑ i : Fin (q + 1), t (Fin.succ i)






























noncomputable def extendByNaturality
    (n : ℕ) (u : SingChain (StdSimplexTop n) n) (X : TopCat) :
    SingChain X n ⟶ SingChain X n :=
  linearExtendOnSimplices
    (X := X) (n := n) (M := SingChain X n)
    (fun σ : SingularSimplex X n =>
      SingChainMap (simplexMapOf σ) n u)










abbrev DegreewiseChainEndFamily : Type _ :=
  ∀ (X : TopCat) (n : ℕ), SingChain X n ⟶ SingChain X n








def DegreewiseNatural (dollar : DegreewiseChainEndFamily) : Prop :=
  ∀ {X Y : TopCat} (f : X ⟶ Y) (n : ℕ),
    dollar X n ≫ SingChainMap f n =
      SingChainMap f n ≫ dollar Y n








def ChainMapCondition (dollar : DegreewiseChainEndFamily) : Prop :=
  ∀ (X : TopCat) (n : ℕ),
    dollar X (n + 1) ≫ boundary X n =
      boundary X n ≫ dollar X n










def ActsByUniversalSimplex (dollar : DegreewiseChainEndFamily) : Prop :=
  ∀ {X : TopCat} (n : ℕ) (σ : SingularSimplex X n),
    dollar X n (simplexChain σ) =
      SingChainMap (simplexMapOf σ) n
        (dollar (StdSimplexTop n) n (universalSimplexChain n))













abbrev ChainHomotopyFamily : Type _ :=
  ∀ (X : TopCat) (n : ℕ), SingChain X n ⟶ SingChain X (n + 1)







def ChainHomotopyNatural (T : ChainHomotopyFamily) : Prop :=
  ∀ {X Y : TopCat} (f : X ⟶ Y) (n : ℕ),
    T X n ≫ SingChainMap f (n + 1) =
      SingChainMap f n ≫ T Y n












def ChainHomotopyToIdentity
    (dollar : DegreewiseChainEndFamily)
    (T : ChainHomotopyFamily) : Prop :=
  (∀ X : TopCat,
    T X 0 ≫ boundary X 0 =
      dollar X 0 - 𝟙 (SingChain X 0))
  ∧
  ∀ (X : TopCat) (n : ℕ),
    T X (n + 1) ≫ boundary X (n + 1) +
        boundary X n ≫ T X n =
      dollar X (n + 1) - 𝟙 (SingChain X (n + 1))












noncomputable def extendHomotopyByNaturality
    (n : ℕ) (u : SingChain (StdSimplexTop n) (n + 1)) (X : TopCat) :
    SingChain X n ⟶ SingChain X (n + 1) :=
  linearExtendOnSimplices
    (X := X) (n := n) (M := SingChain X (n + 1))
    (fun σ : SingularSimplex X n =>
      SingChainMap (simplexMapOf σ) (n + 1) u)













def HomotopyActsByUniversalSimplex
    (T : ChainHomotopyFamily) : Prop :=
  ∀ {X : TopCat} (n : ℕ) (σ : SingularSimplex X n),
    T X n (simplexChain σ) =
      SingChainMap (simplexMapOf σ) (n + 1)
        (T (StdSimplexTop n) n (universalSimplexChain n))









end Autoform_Algebraic_Topology_I_alg_top_proposition121

end