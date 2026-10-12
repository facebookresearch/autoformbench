/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Autoform_Algebraic_Geometry_I_alg_geom_grothendieck_birkhoff








noncomputable def projectiveLine (k : Type u) [Field k] : Scheme := by
  letI : GradedRing (MvPolynomial.homogeneousSubmodule (Fin 2) k) :=
    MvPolynomial.gradedAlgebra
  exact AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)


abbrev P1CoordinateRing (k : Type u) [Field k] := MvPolynomial (Fin 2) k


abbrev P1Grading (k : Type u) [Field k] :=
  MvPolynomial.homogeneousSubmodule (Fin 2) k

scoped instance p1GradedRing (k : Type u) [Field k] : GradedRing (P1Grading k) :=
  MvPolynomial.gradedAlgebra








noncomputable def finiteFreeModule (X : Scheme) (n : ℕ) : X.Modules := by
  classical
  let f : Fin n → X.Modules :=
    fun _ => SheafOfModules.unit X.ringCatSheaf
  letI : HasBiproduct f :=
    CategoryTheory.Limits.HasBiproduct.of_hasProduct f
  exact biproduct f


















structure HomogeneousFractionOfDegree
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (S : Submonoid A) (d : ℤ) where
  numDeg : ℕ
  denDeg : ℕ
  num : 𝒜 numDeg
  den : 𝒜 denDeg
  den_mem : (den : A) ∈ S
  degree_eq : (numDeg : ℤ) - (denDeg : ℤ) = d

namespace HomogeneousFractionOfDegree


end HomogeneousFractionOfDegree







namespace DegreeDLocalization


end DegreeDLocalization












namespace DegreeZeroLocalization



end DegreeZeroLocalization


abbrev P1Spectrum (k : Type u) [Field k] := ProjectiveSpectrum (P1Grading k)


noncomputable def p1PrimeCompl
    {k : Type u} [Field k] (x : ↑(projectiveLine k)) : Submonoid (P1CoordinateRing k) := by
  
  
  exact (show P1Spectrum k from x).asHomogeneousIdeal.toIdeal.primeCompl













































abbrev restrictToOpen {X : Scheme} (M : X.Modules) (U : X.Opens) :
    (U.toScheme).Modules :=
  (Scheme.Modules.restrictFunctor U.ι).obj M








def IsLocallyFreeOfRank {X : Scheme} (M : X.Modules) (n : ℕ) : Prop :=
  ∀ x : ↑X, ∃ U : X.Opens,
    x ∈ U ∧ Nonempty (restrictToOpen M U ≅ finiteFreeModule (U.toScheme) n)








def SameDegreeMultiset {n : ℕ} (d e : Fin n → ℤ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin n, e i = d (σ i)










abbrev IsCoherentModule {X : Scheme.{u}} (M : X.Modules) : Prop :=
  (show SheafOfModules.{u} X.ringCatSheaf from M).IsFinitePresentation



end Autoform_Algebraic_Geometry_I_alg_geom_grothendieck_birkhoff

end