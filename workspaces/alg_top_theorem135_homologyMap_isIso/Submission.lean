/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Types.Basic
import Submission.Helpers
import ChallengeDeps
















namespace Submission

open _root_.Autoform_Algebraic_Topology_I_alg_top_theorem135_homologyMap_isIso
noncomputable section

open CategoryTheory Limits

namespace Autoform_Algebraic_Topology_I_alg_top_theorem135_homologyMap_isIso













abbrev SingChain (X : TopCat) (n : ℕ) : ZModCat :=
  (SingCC X).X n


















theorem ASmallSSet_map_mem
    (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X)
    (n m : SimplexCategoryᵒᵖ) (φ : n ⟶ m)
    (σ : ASmallSimplex X 𝒜 n) :
    IsASmallSimplex X 𝒜 (((TopCat.toSSet.obj X).map φ) σ.1) := by
  sorry







def ASmallSSetMap
    (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X)
    (n m : SimplexCategoryᵒᵖ) (φ : n ⟶ m) :
    ASmallSimplex X 𝒜 n ⟶ ASmallSimplex X 𝒜 m :=
  TypeCat.ofHom
    (fun (σ : ASmallSimplex X 𝒜 n) =>
      (⟨((TopCat.toSSet.obj X).map φ) σ.1,
        ASmallSSet_map_mem X 𝒜 n m φ σ⟩ : ASmallSimplex X 𝒜 m))




theorem ASmallSSet_map_id
    (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X)
    (n : SimplexCategoryᵒᵖ) :
    ASmallSSetMap X 𝒜 n n (𝟙 n) = 𝟙 (ASmallSimplex X 𝒜 n) := by
  sorry





theorem ASmallSSet_map_comp
    (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X)
    (n m k : SimplexCategoryᵒᵖ) (f : n ⟶ m) (g : m ⟶ k) :
    ASmallSSetMap X 𝒜 n k (f ≫ g)
      = ASmallSSetMap X 𝒜 n m f ≫ ASmallSSetMap X 𝒜 m k g := by
  sorry















def ASmallSSet
    (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X) : SSet where
  obj n := ASmallSimplex X 𝒜 n
  map {n m} φ := ASmallSSetMap X 𝒜 n m φ
  map_id n := ASmallSSet_map_id X 𝒜 n
  map_comp f g := ASmallSSet_map_comp X 𝒜 _ _ _ f g





def asmallInclApp
    (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X)
    (n : SimplexCategoryᵒᵖ) :
    (ASmallSSet X 𝒜).obj n ⟶ (TopCat.toSSet.obj X).obj n :=
  TypeCat.ofHom
    (fun (σ : (ASmallSSet X 𝒜).obj n) => σ.1)




theorem asmallIncl_naturality
    (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X)
    (n m : SimplexCategoryᵒᵖ) (φ : n ⟶ m) :
    (ASmallSSet X 𝒜).map φ ≫ asmallInclApp X 𝒜 m
      = asmallInclApp X 𝒜 n ≫ (TopCat.toSSet.obj X).map φ := by
  sorry













def asmallIncl
    (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X) :
    ASmallSSet X 𝒜 ⟶ TopCat.toSSet.obj X where
  app n := asmallInclApp X 𝒜 n
  naturality n m φ := asmallIncl_naturality X 𝒜 n m φ












abbrev ASmallChainComplex
    (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X) :
    ChainComplex ZModCat ℕ :=
  SSetChainComplexFunctor.obj (ASmallSSet X 𝒜)












abbrev ASmallChainMap
    (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X) :
    ASmallChainComplex X 𝒜 ⟶ SingCC X :=
  SSetChainComplexFunctor.map (asmallIncl X 𝒜)






abbrev ASmallHomology
    (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X) (n : ℕ) :
    ZModCat :=
  (ASmallChainComplex X 𝒜).homology n








abbrev SingHomology (X : TopCat) (n : ℕ) : ZModCat :=
  (SingCC X).homology n












abbrev ASmallHomologyMap
    (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X) (n : ℕ) :
    ASmallHomology X 𝒜 n ⟶ SingHomology X n :=
  HomologicalComplex.homologyMap (ASmallChainMap X 𝒜) n















theorem theorem135
    (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X)
    (h𝒜 : IsCover X 𝒜) :
    ChainMapQuasiIso (ASmallChainMap X 𝒜) := by
  sorry













theorem theorem135_homologyMap_isIso
    (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X)
    (h𝒜 : IsCover X 𝒜) (n : ℕ) :
    IsIso (ASmallHomologyMap X 𝒜 n) :=
  theorem135 X 𝒜 h𝒜 n

end Autoform_Algebraic_Topology_I_alg_top_theorem135_homologyMap_isIso


end
end Submission