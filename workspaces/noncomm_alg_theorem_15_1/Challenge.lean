import ChallengeDeps




import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RingTheory.TensorProduct.Basic

open Autoform_Noncommutative_Algebra_noncomm_alg_theorem_15_1
































open scoped TensorProduct

universe u

namespace Autoform_Noncommutative_Algebra_noncomm_alg_theorem_15_1

noncomputable section





namespace BrauerClass





end BrauerClass




theorem brauerGroupLaw_exists
    (F : Type u) [Field F] :
    Nonempty (BrauerGroupLaw F) := by
  sorry







noncomputable def brauerGroupLaw
    (F : Type u) [Field F] :
    BrauerGroupLaw F :=
  Classical.choice (brauerGroupLaw_exists F)


noncomputable instance brauerGroupCommGroup
    (F : Type u) [Field F] :
    CommGroup (BrauerGroup.{u, u} F) :=
  (brauerGroupLaw F).commGroup

theorem one_isSplitBy
    (F E : Type u) [Field F] [Field E] [Algebra F E] :
    BrauerClass.IsSplitBy F E (1 : BrauerGroup.{u, u} F) := by
  sorry


theorem mul_isSplitBy
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    {x y : BrauerGroup.{u, u} F}
    (hx : BrauerClass.IsSplitBy F E x)
    (hy : BrauerClass.IsSplitBy F E y) :
    BrauerClass.IsSplitBy F E (x * y) := by
  sorry


theorem inv_isSplitBy
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    {x : BrauerGroup.{u, u} F}
    (hx : BrauerClass.IsSplitBy F E x) :
    BrauerClass.IsSplitBy F E x⁻¹ := by
  sorry


theorem isSplitBy_of_algHom
    {F E K : Type u}
    [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K]
    (ι : E →ₐ[F] K)
    {x : BrauerGroup.{u, u} F}
    (hx : BrauerClass.IsSplitBy F E x) :
    BrauerClass.IsSplitBy F K x := by
  sorry







noncomputable def relativeBrauerSubgroup
    (F E : Type u) [Field F] [Field E] [Algebra F E] :
    Subgroup (BrauerGroup.{u, u} F) where
  carrier := {x | BrauerClass.IsSplitBy F E x}
  one_mem' := one_isSplitBy F E
  mul_mem' := fun hx hy => mul_isSplitBy F E hx hy
  inv_mem' := fun hx => inv_isSplitBy F E hx


abbrev RelativeBrauerGroup
    (F E : Type u) [Field F] [Field E] [Algebra F E] :
    Type (u + 1) :=
  relativeBrauerSubgroup F E





theorem galoisTwoCocycles_one_mem
    (F E : Type u) [Field F] [Field E] [Algebra F E] :
    groupCohomology.IsMulCocycle₂ (1 : Gal(E/F) × Gal(E/F) → Eˣ) := by
  sorry






theorem galoisTwoCocycles_mul_mem
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    (a b : Gal(E/F) × Gal(E/F) → Eˣ)
    (ha : groupCohomology.IsMulCocycle₂ a)
    (hb : groupCohomology.IsMulCocycle₂ b) :
    groupCohomology.IsMulCocycle₂ (a * b) := by
  sorry






theorem galoisTwoCocycles_inv_mem
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    (a : Gal(E/F) × Gal(E/F) → Eˣ)
    (ha : groupCohomology.IsMulCocycle₂ a) :
    groupCohomology.IsMulCocycle₂ a⁻¹ := by
  sorry








def galoisTwoCocycles
    (F E : Type u) [Field F] [Field E] [Algebra F E] :
    Subgroup (Gal(E/F) × Gal(E/F) → Eˣ) where
  carrier := {c | groupCohomology.IsMulCocycle₂ c}
  one_mem' := galoisTwoCocycles_one_mem F E
  mul_mem' := fun {a b} ha hb => galoisTwoCocycles_mul_mem F E a b ha hb
  inv_mem' := fun {a} ha => galoisTwoCocycles_inv_mem F E a ha





theorem galoisTwoCoboundaries_one_mem
    (F E : Type u) [Field F] [Field E] [Algebra F E] :
    groupCohomology.IsMulCoboundary₂
      ((1 : galoisTwoCocycles F E) : Gal(E/F) × Gal(E/F) → Eˣ) := by
  sorry






theorem galoisTwoCoboundaries_mul_mem
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    (a b : galoisTwoCocycles F E)
    (ha : groupCohomology.IsMulCoboundary₂ (a : Gal(E/F) × Gal(E/F) → Eˣ))
    (hb : groupCohomology.IsMulCoboundary₂ (b : Gal(E/F) × Gal(E/F) → Eˣ)) :
    groupCohomology.IsMulCoboundary₂
      ((a * b : galoisTwoCocycles F E) : Gal(E/F) × Gal(E/F) → Eˣ) := by
  sorry






theorem galoisTwoCoboundaries_inv_mem
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    (a : galoisTwoCocycles F E)
    (ha : groupCohomology.IsMulCoboundary₂ (a : Gal(E/F) × Gal(E/F) → Eˣ)) :
    groupCohomology.IsMulCoboundary₂
      ((a⁻¹ : galoisTwoCocycles F E) : Gal(E/F) × Gal(E/F) → Eˣ) := by
  sorry












def galoisTwoCoboundaries
    (F E : Type u) [Field F] [Field E] [Algebra F E] :
    Subgroup (galoisTwoCocycles F E) where
  carrier := {c |
    groupCohomology.IsMulCoboundary₂
      (c : Gal(E/F) × Gal(E/F) → Eˣ)}
  one_mem' := galoisTwoCoboundaries_one_mem F E
  mul_mem' := fun {a b} ha hb => galoisTwoCoboundaries_mul_mem F E a b ha hb
  inv_mem' := fun {a} ha => galoisTwoCoboundaries_inv_mem F E a ha





abbrev GaloisH2
    (F E : Type u) [Field F] [Field E] [Algebra F E] :
    Type u :=
  galoisTwoCocycles F E ⧸ galoisTwoCoboundaries F E






theorem refl_restriction_surjective
    (F E : Type u)
    [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] :
    Function.Surjective (MonoidHom.id Gal(E/F)) := by
  sorry






theorem refl_equivariant
    (F E : Type u)
    [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (σ : Gal(E/F)) (x : E) :
    (AlgHom.id F E) (((MonoidHom.id Gal(E/F)) σ) x) =
      σ ((AlgHom.id F E) x) := by
  sorry







theorem comp_restriction_surjective
    {F E K L : Type u}
    [Field F] [Field E] [Field K] [Field L]
    [Algebra F E] [Algebra F K] [Algebra F L]
    [FiniteDimensional F E] [FiniteDimensional F K]
    [FiniteDimensional F L]
    [IsGalois F E] [IsGalois F K] [IsGalois F L]
    (g : FiniteGaloisExtensionHom F K L)
    (f : FiniteGaloisExtensionHom F E K) :
    Function.Surjective (f.restriction.comp g.restriction) := by
  sorry






theorem comp_equivariant
    {F E K L : Type u}
    [Field F] [Field E] [Field K] [Field L]
    [Algebra F E] [Algebra F K] [Algebra F L]
    [FiniteDimensional F E] [FiniteDimensional F K]
    [FiniteDimensional F L]
    [IsGalois F E] [IsGalois F K] [IsGalois F L]
    (g : FiniteGaloisExtensionHom F K L)
    (f : FiniteGaloisExtensionHom F E K)
    (σ : Gal(L/F)) (x : E) :
    (g.toAlgHom.comp f.toAlgHom) (((f.restriction.comp g.restriction) σ) x) =
      σ ((g.toAlgHom.comp f.toAlgHom) x) := by
  sorry

namespace FiniteGaloisExtensionHom









end FiniteGaloisExtensionHom


namespace FiniteGaloisExtensionHom

def refl
    (F E : Type u)
    [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] :
    FiniteGaloisExtensionHom F E E where
  toAlgHom := AlgHom.id F E
  restriction := MonoidHom.id Gal(E/F)
  restriction_surjective := refl_restriction_surjective F E
  equivariant := refl_equivariant F E
end FiniteGaloisExtensionHom

namespace FiniteGaloisExtensionHom

def comp
    {F E K L : Type u}
    [Field F] [Field E] [Field K] [Field L]
    [Algebra F E] [Algebra F K] [Algebra F L]
    [FiniteDimensional F E] [FiniteDimensional F K]
    [FiniteDimensional F L]
    [IsGalois F E] [IsGalois F K] [IsGalois F L]
    (g : FiniteGaloisExtensionHom F K L)
    (f : FiniteGaloisExtensionHom F E K) :
    FiniteGaloisExtensionHom F E L where
  toAlgHom := g.toAlgHom.comp f.toAlgHom
  restriction := f.restriction.comp g.restriction
  restriction_surjective := comp_restriction_surjective g f
  equivariant := comp_equivariant g f
end FiniteGaloisExtensionHom

theorem mapTwoCochain_isMulCocycle₂
    {F E K : Type u}
    [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K]
    [FiniteDimensional F E] [FiniteDimensional F K]
    [IsGalois F E] [IsGalois F K]
    (f : FiniteGaloisExtensionHom F E K)
    {c : Gal(E/F) × Gal(E/F) → Eˣ}
    (hc : groupCohomology.IsMulCocycle₂ c) :
    groupCohomology.IsMulCocycle₂ (f.mapTwoCochain c) := by
  sorry


theorem mapTwoCochain_isMulCoboundary₂
    {F E K : Type u}
    [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K]
    [FiniteDimensional F E] [FiniteDimensional F K]
    [IsGalois F E] [IsGalois F K]
    (f : FiniteGaloisExtensionHom F E K)
    {c : Gal(E/F) × Gal(E/F) → Eˣ}
    (hc : groupCohomology.IsMulCoboundary₂ c) :
    groupCohomology.IsMulCoboundary₂ (f.mapTwoCochain c) := by
  sorry






theorem galoisTwoCocycleTransition_map_one
    {F E K : Type u}
    [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K]
    [FiniteDimensional F E] [FiniteDimensional F K]
    [IsGalois F E] [IsGalois F K]
    (f : FiniteGaloisExtensionHom F E K) :
    f.mapTwoCochain ((1 : galoisTwoCocycles F E) : Gal(E/F) × Gal(E/F) → Eˣ) =
      1 := by
  sorry






theorem galoisTwoCocycleTransition_map_mul
    {F E K : Type u}
    [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K]
    [FiniteDimensional F E] [FiniteDimensional F K]
    [IsGalois F E] [IsGalois F K]
    (f : FiniteGaloisExtensionHom F E K)
    (a b : galoisTwoCocycles F E) :
    f.mapTwoCochain ((a * b : galoisTwoCocycles F E) :
        Gal(E/F) × Gal(E/F) → Eˣ) =
      f.mapTwoCochain (a : Gal(E/F) × Gal(E/F) → Eˣ) *
        f.mapTwoCochain (b : Gal(E/F) × Gal(E/F) → Eˣ) := by
  sorry










noncomputable def relativeBrauerTransition
    {F E K : Type u}
    [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K]
    [FiniteDimensional F E] [FiniteDimensional F K]
    [IsGalois F E] [IsGalois F K]
    (f : FiniteGaloisExtensionHom F E K) :
    RelativeBrauerGroup F E →* RelativeBrauerGroup F K :=
  Subgroup.inclusion <| by
    intro x hx
    exact isSplitBy_of_algHom f.toAlgHom hx


noncomputable def galoisTwoCocycleTransition
    {F E K : Type u}
    [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K]
    [FiniteDimensional F E] [FiniteDimensional F K]
    [IsGalois F E] [IsGalois F K]
    (f : FiniteGaloisExtensionHom F E K) :
    galoisTwoCocycles F E →* galoisTwoCocycles F K where
  toFun c :=
    ⟨f.mapTwoCochain (c : Gal(E/F) × Gal(E/F) → Eˣ),
      mapTwoCochain_isMulCocycle₂ f c.2⟩
  map_one' := Subtype.ext (galoisTwoCocycleTransition_map_one f)
  map_mul' := fun a b => Subtype.ext (galoisTwoCocycleTransition_map_mul f a b)

theorem galoisTwoCocycleTransition_mem_coboundaries
    {F E K : Type u}
    [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K]
    [FiniteDimensional F E] [FiniteDimensional F K]
    [IsGalois F E] [IsGalois F K]
    (f : FiniteGaloisExtensionHom F E K)
    (c : galoisTwoCocycles F E)
    (hc : c ∈ galoisTwoCoboundaries F E) :
    galoisTwoCocycleTransition f c ∈ galoisTwoCoboundaries F K := by
  sorry





noncomputable def galoisH2Transition
    {F E K : Type u}
    [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K]
    [FiniteDimensional F E] [FiniteDimensional F K]
    [IsGalois F E] [IsGalois F K]
    (f : FiniteGaloisExtensionHom F E K) :
    GaloisH2 F E →* GaloisH2 F K :=
  QuotientGroup.map
    (galoisTwoCoboundaries F E)
    (galoisTwoCoboundaries F K)
    (galoisTwoCocycleTransition f)
    (by
      intro c hc
      exact galoisTwoCocycleTransition_mem_coboundaries f c hc)
@[simp]
theorem relativeBrauerTransition_refl
    (F E : Type u)
    [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] :
    relativeBrauerTransition
        (FiniteGaloisExtensionHom.refl F E) =
      MonoidHom.id (RelativeBrauerGroup F E) := by
  sorry
theorem relativeBrauerTransition_comp
    {F E K L : Type u}
    [Field F] [Field E] [Field K] [Field L]
    [Algebra F E] [Algebra F K] [Algebra F L]
    [FiniteDimensional F E] [FiniteDimensional F K]
    [FiniteDimensional F L]
    [IsGalois F E] [IsGalois F K] [IsGalois F L]
    (g : FiniteGaloisExtensionHom F K L)
    (f : FiniteGaloisExtensionHom F E K) :
    relativeBrauerTransition (g.comp f) =
      (relativeBrauerTransition g).comp (relativeBrauerTransition f) := by
  sorry

@[simp]
theorem galoisH2Transition_refl
    (F E : Type u)
    [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] :
    galoisH2Transition (FiniteGaloisExtensionHom.refl F E) =
      MonoidHom.id (GaloisH2 F E) := by
  sorry
theorem galoisH2Transition_comp
    {F E K L : Type u}
    [Field F] [Field E] [Field K] [Field L]
    [Algebra F E] [Algebra F K] [Algebra F L]
    [FiniteDimensional F E] [FiniteDimensional F K]
    [FiniteDimensional F L]
    [IsGalois F E] [IsGalois F K] [IsGalois F L]
    (g : FiniteGaloisExtensionHom F K L)
    (f : FiniteGaloisExtensionHom F E K) :
    galoisH2Transition (g.comp f) =
      (galoisH2Transition g).comp (galoisH2Transition f) := by
  sorry








structure RelativeBrauerCohomologyNaturalIso
    (F : Type u) [Field F] where
  app :
    ∀ (E : Type u) [Field E] [Algebra F E]
      [FiniteDimensional F E] [IsGalois F E],
      RelativeBrauerGroup F E ≃* GaloisH2 F E
  naturality :
    ∀ {E K : Type u}
      [Field E] [Field K]
      [Algebra F E] [Algebra F K]
      [FiniteDimensional F E] [FiniteDimensional F K]
      [IsGalois F E] [IsGalois F K]
      (f : FiniteGaloisExtensionHom F E K),
      (galoisH2Transition f).comp (app E).toMonoidHom =
        (app K).toMonoidHom.comp (relativeBrauerTransition f)





theorem theorem_15_1_natural
    (F : Type u) [Field F] :
    Nonempty (RelativeBrauerCohomologyNaturalIso F) := by
  sorry


theorem theorem_15_1
    (F E : Type u)
    [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] :
    Nonempty (RelativeBrauerGroup F E ≃* GaloisH2 F E) := by
  sorry

end

end Autoform_Noncommutative_Algebra_noncomm_alg_theorem_15_1
