/-
Copyright (c) Meta Platforms, Inc. and affiliates.

This source code is licensed under the CC BY-NC 4.0 license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import ChallengeDeps

open Autoform_Algebraic_Geometry_I_alg_geom_grothendieck_birkhoff
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Autoform_Algebraic_Geometry_I_alg_geom_grothendieck_birkhoff























namespace HomogeneousFractionOfDegree



end HomogeneousFractionOfDegree




namespace HomogeneousFractionOfDegree

noncomputable def val
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    {𝒜 : ℕ → σ} [GradedRing 𝒜]
    {S : Submonoid A} {d : ℤ}
    (z : HomogeneousFractionOfDegree 𝒜 S d) : Localization S :=
  Localization.mk (z.num : A) ⟨(z.den : A), z.den_mem⟩
end HomogeneousFractionOfDegree







def IsDegreeDLocalizationElement
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (S : Submonoid A) (d : ℤ) (z : Localization S) : Prop :=
  z = 0 ∨ ∃ w : HomogeneousFractionOfDegree 𝒜 S d,
    HomogeneousFractionOfDegree.val w = z




theorem DegreeDLocalization_add_mem
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (S : Submonoid A) (d : ℤ) (x y : Localization S)
    (hx : IsDegreeDLocalizationElement 𝒜 S d x)
    (hy : IsDegreeDLocalizationElement 𝒜 S d y) :
    IsDegreeDLocalizationElement 𝒜 S d (x + y) := by
  
  
  
  sorry





theorem DegreeDLocalization_neg_mem
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (S : Submonoid A) (d : ℤ) (x : Localization S)
    (hx : IsDegreeDLocalizationElement 𝒜 S d x) :
    IsDegreeDLocalizationElement 𝒜 S d (-x) := by
  
  sorry


namespace DegreeDLocalization



end DegreeDLocalization











noncomputable def DegreeDLocalization
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (S : Submonoid A) (d : ℤ) : AddSubgroup (Localization S) where
  carrier := { z | IsDegreeDLocalizationElement 𝒜 S d z }
  zero_mem' := Or.inl rfl
  add_mem' := fun {x y} hx hy => DegreeDLocalization_add_mem 𝒜 S d x y hx hy
  neg_mem' := fun {x} hx => DegreeDLocalization_neg_mem 𝒜 S d x hx

namespace DegreeDLocalization

noncomputable def mk
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    {𝒜 : ℕ → σ} [GradedRing 𝒜]
    {S : Submonoid A} {d : ℤ}
    (z : HomogeneousFractionOfDegree 𝒜 S d) :
    (DegreeDLocalization 𝒜 S d : Type _) :=
  ⟨HomogeneousFractionOfDegree.val z, Or.inr ⟨z, rfl⟩⟩
end DegreeDLocalization

theorem DegreeZeroLocalization_one_mem
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (S : Submonoid A) :
    IsDegreeDLocalizationElement 𝒜 S 0 (1 : Localization S) := by
  
  
  sorry


theorem DegreeZeroLocalization_add_mem
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (S : Submonoid A) (x y : Localization S)
    (hx : IsDegreeDLocalizationElement 𝒜 S 0 x)
    (hy : IsDegreeDLocalizationElement 𝒜 S 0 y) :
    IsDegreeDLocalizationElement 𝒜 S 0 (x + y) := by
  
  sorry


theorem DegreeZeroLocalization_neg_mem
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (S : Submonoid A) (x : Localization S)
    (hx : IsDegreeDLocalizationElement 𝒜 S 0 x) :
    IsDegreeDLocalizationElement 𝒜 S 0 (-x) := by
  
  sorry


theorem DegreeZeroLocalization_mul_mem
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (S : Submonoid A) (x y : Localization S)
    (hx : IsDegreeDLocalizationElement 𝒜 S 0 x)
    (hy : IsDegreeDLocalizationElement 𝒜 S 0 y) :
    IsDegreeDLocalizationElement 𝒜 S 0 (x * y) := by
  
  sorry







noncomputable def DegreeZeroLocalization
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (S : Submonoid A) : Subring (Localization S) where
  carrier := { z | IsDegreeDLocalizationElement 𝒜 S 0 z }
  zero_mem' := Or.inl rfl
  one_mem' := DegreeZeroLocalization_one_mem 𝒜 S
  add_mem' := fun {x y} hx hy => DegreeZeroLocalization_add_mem 𝒜 S x y hx hy
  neg_mem' := fun {x} hx => DegreeZeroLocalization_neg_mem 𝒜 S x hx
  mul_mem' := fun {x y} hx hy => DegreeZeroLocalization_mul_mem 𝒜 S x y hx hy





theorem DegreeZeroLocalization_smul_mem
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (S : Submonoid A) (d : ℤ)
    (r : (DegreeZeroLocalization 𝒜 S : Type _))
    (x : (DegreeDLocalization 𝒜 S d : Type _)) :
    (r : Localization S) * (x : Localization S) ∈ DegreeDLocalization 𝒜 S d := by
  sorry

namespace DegreeZeroLocalization




end DegreeZeroLocalization
















namespace DegreeZeroLocalization


noncomputable def toDegreeD
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    {𝒜 : ℕ → σ} [GradedRing 𝒜]
    {S : Submonoid A}
    (r : (DegreeZeroLocalization 𝒜 S : Type _)) :
    (DegreeDLocalization 𝒜 S 0 : Type _) :=
  ⟨(r : Localization S), r.2⟩
end DegreeZeroLocalization

namespace DegreeZeroLocalization




noncomputable def smul
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    {𝒜 : ℕ → σ} [GradedRing 𝒜]
    {S : Submonoid A} {d : ℤ}
    (r : (DegreeZeroLocalization 𝒜 S : Type _))
    (x : (DegreeDLocalization 𝒜 S d : Type _)) :
    (DegreeDLocalization 𝒜 S d : Type _) :=
  ⟨(r : Localization S) * (x : Localization S),
    DegreeZeroLocalization_smul_mem 𝒜 S d r x⟩
end DegreeZeroLocalization


abbrev P1DegreeDLocalizationAt
    {k : Type u} [Field k] (x : ↑(projectiveLine k)) (d : ℤ) : Type _ :=
  (DegreeDLocalization (P1Grading k) (p1PrimeCompl x) d : Type _)


abbrev P1DegreeZeroLocalizationAt
    {k : Type u} [Field k] (x : ↑(projectiveLine k)) : Type _ :=
  (DegreeZeroLocalization (P1Grading k) (p1PrimeCompl x) : Type _)





def IsHomogeneousFractionOfDegreeOn
    {k : Type u} [Field k] {d : ℤ} {U : (projectiveLine k).Opens}
    (s : ∀ x : U, P1DegreeDLocalizationAt x.1 d) : Prop :=
  ∃ (numDeg denDeg : ℕ)
    (a : P1Grading k numDeg) (b : P1Grading k denDeg)
    (hdeg : (numDeg : ℤ) - (denDeg : ℤ) = d)
    (hb : ∀ x : U, (b : P1CoordinateRing k) ∈ p1PrimeCompl x.1),
      ∀ x : U,
        s x = DegreeDLocalization.mk
          { numDeg := numDeg
            denDeg := denDeg
            num := a
            den := b
            den_mem := hb x
            degree_eq := hdeg }


def restrictDegreeDFunction
    {k : Type u} [Field k] {d : ℤ}
    {U V : (projectiveLine k).Opens} (hVU : V ≤ U)
    (s : ∀ x : U, P1DegreeDLocalizationAt x.1 d) :
    ∀ x : V, P1DegreeDLocalizationAt x.1 d :=
  fun x => s ⟨x.1, hVU x.2⟩







def IsLocallyHomogeneousOfDegree
    {k : Type u} [Field k] {d : ℤ} {U : (projectiveLine k).Opens}
    (s : ∀ x : U, P1DegreeDLocalizationAt x.1 d) : Prop :=
  ∀ x : U, ∃ V : (projectiveLine k).Opens,
    x.1 ∈ V ∧ ∃ hVU : V ≤ U,
      IsHomogeneousFractionOfDegreeOn (d := d)
        (restrictDegreeDFunction (d := d) hVU s)

theorem TwistingSections_zero_mem
    (k : Type u) [Field k] (d : ℤ) (U : (projectiveLine k).Opens) :
    IsLocallyHomogeneousOfDegree (k := k) (d := d) (U := U)
      (0 : ∀ x : U, P1DegreeDLocalizationAt x.1 d) := by
  
  sorry


theorem TwistingSections_add_mem
    (k : Type u) [Field k] (d : ℤ) (U : (projectiveLine k).Opens)
    (s t : ∀ x : U, P1DegreeDLocalizationAt x.1 d)
    (hs : IsLocallyHomogeneousOfDegree (k := k) (d := d) (U := U) s)
    (ht : IsLocallyHomogeneousOfDegree (k := k) (d := d) (U := U) t) :
    IsLocallyHomogeneousOfDegree (k := k) (d := d) (U := U) (s + t) := by
  
  sorry


theorem TwistingSections_neg_mem
    (k : Type u) [Field k] (d : ℤ) (U : (projectiveLine k).Opens)
    (s : ∀ x : U, P1DegreeDLocalizationAt x.1 d)
    (hs : IsLocallyHomogeneousOfDegree (k := k) (d := d) (U := U) s) :
    IsLocallyHomogeneousOfDegree (k := k) (d := d) (U := U) (-s) := by
  
  sorry
















noncomputable def TwistingSections
    (k : Type u) [Field k] (d : ℤ) (U : (projectiveLine k).Opens) :
    AddSubgroup (∀ x : U, P1DegreeDLocalizationAt x.1 d) where
  carrier := { s | IsLocallyHomogeneousOfDegree (k := k) (d := d) s }
  zero_mem' := TwistingSections_zero_mem k d U
  add_mem' := fun {s t} hs ht => TwistingSections_add_mem k d U s t hs ht
  neg_mem' := fun {s} hs => TwistingSections_neg_mem k d U s hs



noncomputable def regularAsDegreeZeroFunction
    {k : Type u} [Field k] {U : (projectiveLine k).Opens}
    (s : ∀ x : U, P1DegreeZeroLocalizationAt x.1) :
    ∀ x : U, P1DegreeDLocalizationAt x.1 0 :=
  fun x => DegreeZeroLocalization.toDegreeD
    (𝒜 := P1Grading k) (S := p1PrimeCompl x.1) (s x)


def IsLocallyRegularDegreeZero
    {k : Type u} [Field k] {U : (projectiveLine k).Opens}
    (s : ∀ x : U, P1DegreeZeroLocalizationAt x.1) : Prop :=
  IsLocallyHomogeneousOfDegree (k := k) (d := 0)
    (regularAsDegreeZeroFunction (k := k) s)

theorem RegularTwistingSections_zero_mem
    (k : Type u) [Field k] (U : (projectiveLine k).Opens) :
    IsLocallyRegularDegreeZero (k := k) (U := U)
      (0 : ∀ x : U, P1DegreeZeroLocalizationAt x.1) := by
  
  sorry


theorem RegularTwistingSections_one_mem
    (k : Type u) [Field k] (U : (projectiveLine k).Opens) :
    IsLocallyRegularDegreeZero (k := k) (U := U)
      (1 : ∀ x : U, P1DegreeZeroLocalizationAt x.1) := by
  
  sorry


theorem RegularTwistingSections_add_mem
    (k : Type u) [Field k] (U : (projectiveLine k).Opens)
    (s t : ∀ x : U, P1DegreeZeroLocalizationAt x.1)
    (hs : IsLocallyRegularDegreeZero (k := k) (U := U) s)
    (ht : IsLocallyRegularDegreeZero (k := k) (U := U) t) :
    IsLocallyRegularDegreeZero (k := k) (U := U) (s + t) := by
  
  sorry


theorem RegularTwistingSections_neg_mem
    (k : Type u) [Field k] (U : (projectiveLine k).Opens)
    (s : ∀ x : U, P1DegreeZeroLocalizationAt x.1)
    (hs : IsLocallyRegularDegreeZero (k := k) (U := U) s) :
    IsLocallyRegularDegreeZero (k := k) (U := U) (-s) := by
  
  sorry


theorem RegularTwistingSections_mul_mem
    (k : Type u) [Field k] (U : (projectiveLine k).Opens)
    (s t : ∀ x : U, P1DegreeZeroLocalizationAt x.1)
    (hs : IsLocallyRegularDegreeZero (k := k) (U := U) s)
    (ht : IsLocallyRegularDegreeZero (k := k) (U := U) t) :
    IsLocallyRegularDegreeZero (k := k) (U := U) (s * t) := by
  
  sorry








noncomputable def RegularTwistingSections
    (k : Type u) [Field k] (U : (projectiveLine k).Opens) :
    Subring (∀ x : U, P1DegreeZeroLocalizationAt x.1) where
  carrier := { s | IsLocallyRegularDegreeZero (k := k) s }
  zero_mem' := RegularTwistingSections_zero_mem k U
  one_mem' := RegularTwistingSections_one_mem k U
  add_mem' := fun {s t} hs ht => RegularTwistingSections_add_mem k U s t hs ht
  neg_mem' := fun {s} hs => RegularTwistingSections_neg_mem k U s hs
  mul_mem' := fun {s t} hs ht => RegularTwistingSections_mul_mem k U s t hs ht





theorem regularSectionSmul_mem
    (k : Type u) [Field k] (d : ℤ) (U : (projectiveLine k).Opens)
    (r : (RegularTwistingSections k U : Type _))
    (s : (TwistingSections k d U : Type _)) :
    ((fun x => DegreeZeroLocalization.smul
      (𝒜 := P1Grading k) (S := p1PrimeCompl x.1) (d := d)
      ((r : ∀ x : U, P1DegreeZeroLocalizationAt x.1) x)
      ((s : ∀ x : U, P1DegreeDLocalizationAt x.1 d) x) :
        ∀ x : U, P1DegreeDLocalizationAt x.1 d)) ∈ TwistingSections k d U := by
  
  
  sorry








noncomputable def regularSectionSmul
    {k : Type u} [Field k] {d : ℤ} {U : (projectiveLine k).Opens}
    (r : (RegularTwistingSections k U : Type _))
    (s : (TwistingSections k d U : Type _)) :
    (TwistingSections k d U : Type _) :=
  ⟨fun x => DegreeZeroLocalization.smul
    (𝒜 := P1Grading k) (S := p1PrimeCompl x.1) (d := d)
    ((r : ∀ x : U, P1DegreeZeroLocalizationAt x.1) x)
    ((s : ∀ x : U, P1DegreeDLocalizationAt x.1 d) x),
   regularSectionSmul_mem k d U r s⟩




theorem twistingSectionsRestrict_mem
    (k : Type u) [Field k] (d : ℤ)
    (U V : (projectiveLine k).Opens) (i : U ⟶ V)
    (s : (TwistingSections k d V : Type _)) :
    restrictDegreeDFunction (d := d) (leOfHom i)
      ((s : ∀ x : V, P1DegreeDLocalizationAt x.1 d)) ∈ TwistingSections k d U := by
  sorry







noncomputable def twistingSectionsRestrict
    {k : Type u} [Field k] {d : ℤ}
    {U V : (projectiveLine k).Opens} (i : U ⟶ V) :
    ↑(TwistingSections k d V : Type _) → (TwistingSections k d U : Type _) :=
  fun s =>
    ⟨restrictDegreeDFunction (d := d) (leOfHom i)
      ((s : ∀ x : V, P1DegreeDLocalizationAt x.1 d)),
     twistingSectionsRestrict_mem k d U V i s⟩











structure SerreTwistConstruction
    (k : Type u) [Field k] (d : ℤ) where
  obj : (projectiveLine k).Modules
  sectionAddEquiv :
    ∀ U : (projectiveLine k).Opens,
      Γ(obj, U) ≃+ (TwistingSections k d U : Type _)
  structureSheafSectionRingEquiv :
    ∀ U : (projectiveLine k).Opens,
      Γ(projectiveLine k, U) ≃+* (RegularTwistingSections k U : Type _)
  restriction_compatible :
    ∀ {U V : (projectiveLine k).Opens} (i : U ⟶ V) (s : Γ(obj, V)),
      sectionAddEquiv U (obj.presheaf.map i.op s) =
        twistingSectionsRestrict (d := d) i (sectionAddEquiv V s)
  scalar_action_compatible :
    ∀ (U : (projectiveLine k).Opens)
      (r : Γ(projectiveLine k, U)) (s : Γ(obj, U)),
      sectionAddEquiv U (r • s) =
        regularSectionSmul (d := d)
          (structureSheafSectionRingEquiv U r)
          (sectionAddEquiv U s)








theorem existsSerreTwistConstruction
    (k : Type u) [Field k] (d : ℤ) :
    Nonempty (SerreTwistConstruction k d) := by
  sorry

















noncomputable def serreTwistConstruction
    (k : Type u) [Field k] (d : ℤ) : SerreTwistConstruction k d :=
  Classical.choice (existsSerreTwistConstruction k d)


noncomputable def twistingSheaf
    (k : Type u) [Field k] (d : ℤ) : (projectiveLine k).Modules :=
  (serreTwistConstruction k d).obj








noncomputable def splitBundle
    {k : Type u} [Field k]
    {n : ℕ} (d : Fin n → ℤ) :
    (projectiveLine k).Modules := by
  classical
  let f : Fin n → (projectiveLine k).Modules :=
    fun i => twistingSheaf k (d i)
  letI : HasBiproduct f :=
    CategoryTheory.Limits.HasBiproduct.of_hasProduct f
  exact biproduct f
















theorem grothendieck_birkhoff
    {k : Type u} [Field k] [IsAlgClosed k]
    (n : ℕ)
    (E : (projectiveLine k).Modules)
    (hE_locallyFree : IsLocallyFreeOfRank E n)
    (hE_coherent : IsCoherentModule E) :
    ∃ d : Fin n → ℤ,
      Nonempty (E ≅ splitBundle (k := k) d) ∧
      ∀ e : Fin n → ℤ,
        Nonempty (E ≅ splitBundle (k := k) e) →
          SameDegreeMultiset d e := by
  sorry

end Autoform_Algebraic_Geometry_I_alg_geom_grothendieck_birkhoff

end