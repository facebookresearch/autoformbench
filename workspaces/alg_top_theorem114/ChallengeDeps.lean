/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open CategoryTheory Limits

namespace Autoform_Algebraic_Topology_I_alg_top_theorem114

abbrev ZModCat := ModuleCat ℤ


abbrev TopSimplex (n : SimplexCategoryᵒᵖ) : TopCat :=
  SimplexCategory.toTop.obj (Opposite.unop n)


abbrev simplexMap {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    TopSimplex m ⟶ TopSimplex n :=
  SimplexCategory.toTop.map φ.unop


def SingSSet' (X : TopCat) : SSet where
  obj n := TopSimplex n ⟶ X
  map {n m} φ := TypeCat.ofHom (fun (σ : TopSimplex n ⟶ X) => simplexMap φ ≫ σ)
  map_id := by
    intro n
    have hId : simplexMap (𝟙 n) = 𝟙 (TopSimplex n) := by
      simpa [simplexMap] using (SimplexCategory.toTop.map_id (Opposite.unop n))
    apply ConcreteCategory.hom_ext; intro σ
    show simplexMap (𝟙 n) ≫ σ = σ
    rw [hId, Category.id_comp]
  map_comp := by
    intro n m k φ ψ
    have hComp : simplexMap (φ ≫ ψ) = simplexMap ψ ≫ simplexMap φ := by
      simpa [simplexMap] using (SimplexCategory.toTop.map_comp ψ.unop φ.unop)
    apply ConcreteCategory.hom_ext; intro σ
    show simplexMap (φ ≫ ψ) ≫ σ = simplexMap ψ ≫ simplexMap φ ≫ σ
    rw [hComp, Category.assoc]





def IsCover (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X) : Prop :=
  ∀ x : ↑X, ∃ i : ι, x ∈ interior (𝒜 i)


abbrev ASmallSimplex (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X) (n : SimplexCategoryᵒᵖ) :=
  {σ : TopSimplex n ⟶ X // ∃ i : ι, Set.range σ.hom ⊆ 𝒜 i}


def ASmallSSet (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X) : SSet where
  obj n := ASmallSimplex X 𝒜 n
  map {n m} φ := TypeCat.ofHom (fun (σ : ASmallSimplex X 𝒜 n) =>
    ⟨simplexMap φ ≫ σ.1,
      by
        rcases σ.2 with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        intro y hy
        rcases hy with ⟨x, rfl⟩
        exact hi ⟨(simplexMap φ).hom x, rfl⟩⟩)
  map_id := by
    intro n
    have hId : simplexMap (𝟙 n) = 𝟙 (TopSimplex n) := by
      simpa [simplexMap] using (SimplexCategory.toTop.map_id (Opposite.unop n))
    apply ConcreteCategory.hom_ext; intro σ
    apply Subtype.ext
    show simplexMap (𝟙 n) ≫ σ.1 = σ.1
    rw [hId, Category.id_comp]
  map_comp := by
    intro n m k φ ψ
    have hComp : simplexMap (φ ≫ ψ) = simplexMap ψ ≫ simplexMap φ := by
      simpa [simplexMap] using (SimplexCategory.toTop.map_comp ψ.unop φ.unop)
    apply ConcreteCategory.hom_ext; intro σ
    apply Subtype.ext
    show simplexMap (φ ≫ ψ) ≫ σ.1 = simplexMap ψ ≫ simplexMap φ ≫ σ.1
    rw [hComp, Category.assoc]


def asmallIncl (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X) :
    ASmallSSet X 𝒜 ⟶ SingSSet' X where
  app n := TypeCat.ofHom (fun (σ : ASmallSimplex X 𝒜 n) => σ.1)
  naturality := by
    intro n m φ
    apply ConcreteCategory.hom_ext; intro σ
    rfl





abbrev ASmallChainComplex (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X) :
    ChainComplex ZModCat ℕ :=
  ((AlgebraicTopology.SSet.singularChainComplexFunctor ZModCat).obj (ModuleCat.of ℤ ℤ)).obj
    (ASmallSSet X 𝒜)


abbrev FullChainComplex (X : TopCat) : ChainComplex ZModCat ℕ :=
  ((AlgebraicTopology.SSet.singularChainComplexFunctor ZModCat).obj (ModuleCat.of ℤ ℤ)).obj
    (SingSSet' X)


abbrev ASmallChainMap (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X) :
    ASmallChainComplex X 𝒜 ⟶ FullChainComplex X :=
  (((AlgebraicTopology.SSet.singularChainComplexFunctor ZModCat).obj (ModuleCat.of ℤ ℤ)).map
    (asmallIncl X 𝒜))


abbrev ASmallHomology (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X) (n : ℕ) : ZModCat :=
  (ASmallChainComplex X 𝒜).homology n


abbrev FullHomology (X : TopCat) (n : ℕ) : ZModCat :=
  (FullChainComplex X).homology n


abbrev ASmallHomologyMap (X : TopCat) {ι : Type _} (𝒜 : ι → Set ↑X) (n : ℕ) :
    ASmallHomology X 𝒜 n ⟶ FullHomology X n :=
  HomologicalComplex.homologyMap (ASmallChainMap X 𝒜) n



end Autoform_Algebraic_Topology_I_alg_top_theorem114
