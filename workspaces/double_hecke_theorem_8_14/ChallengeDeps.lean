import Mathlib

set_option maxSynthPendingDepth 3

















open scoped BigOperators

universe u v

namespace Autoform_Double_Hecke_Algebras_double_hecke_theorem_8_14










structure SymplecticReflectionDatum where
  V : Type u
  [instAddCommGroupV : AddCommGroup V]
  [instModuleV : Module ℂ V]
  [instFiniteDimensionalV : FiniteDimensional ℂ V]
  G : Type v
  [instGroupG : Group G]
  [instFintypeG : Fintype G]
  
  ρ : G →* (V ≃ₗ[ℂ] V)

  


  rho_faithful : Function.Injective ρ

  
  omega : V →ₗ[ℂ] V →ₗ[ℂ] ℂ

  
  omega_skew : ∀ x y : V, omega x y = - omega y x

  
  omega_left_nondegenerate :
    ∀ x : V, (∀ y : V, omega x y = 0) → x = 0

  
  preserves_omega :
    ∀ (g : G) (x y : V), omega (ρ g x) (ρ g y) = omega x y

  



  symplectically_irreducible :
    ∀ η : V →ₗ[ℂ] V →ₗ[ℂ] ℂ,
      (∀ x y : V, η x y = -η y x) →
        (∀ (g : G) (x y : V), η (ρ g x) (ρ g y) = η x y) →
          ∃ a : ℂ, η = a • omega

  



  projMoving : G → V →ₗ[ℂ] V

  projMoving_range :
    ∀ g : G,
      LinearMap.range (projMoving g) =
        LinearMap.range (LinearMap.id - (ρ g : V →ₗ[ℂ] V))

  projMoving_kernel :
    ∀ g : G,
      LinearMap.ker (projMoving g) =
        LinearMap.ker (LinearMap.id - (ρ g : V →ₗ[ℂ] V))

  projMoving_idempotent :
    ∀ g : G, (projMoving g).comp (projMoving g) = projMoving g

attribute [instance]
  SymplecticReflectionDatum.instAddCommGroupV
  SymplecticReflectionDatum.instModuleV
  SymplecticReflectionDatum.instFiniteDimensionalV
  SymplecticReflectionDatum.instGroupG
  SymplecticReflectionDatum.instFintypeG

variable (D : SymplecticReflectionDatum)







def oneSubAction (g : D.G) : D.V →ₗ[ℂ] D.V :=
  LinearMap.id - (D.ρ g : D.V →ₗ[ℂ] D.V)






def IsSymplecticReflection (g : D.G) : Prop :=
  Module.finrank ℂ (LinearMap.range (oneSubAction D g)) = 2





def omegaS (s : D.G) (x y : D.V) : ℂ :=
  D.omega (D.projMoving s x) (D.projMoving s y)








def ConjInvariantOnSymplecticReflections (c : D.G → ℂ) : Prop :=
  ∀ h s : D.G,
    IsSymplecticReflection D s →
      c (h * s * h⁻¹) = c s








inductive Gen where
  | vec : D.V → Gen
  | grp : D.G → Gen


abbrev Free := FreeAlgebra ℂ (Gen D)

namespace Presentation

variable {D}


def X (x : D.V) : Free D :=
  FreeAlgebra.ι ℂ (Gen.vec x)


def U (g : D.G) : Free D :=
  FreeAlgebra.ι ℂ (Gen.grp g)


def C (a : ℂ) : Free D :=
  algebraMap ℂ (Free D) a





noncomputable def reflectionSum
    (c : D.G → ℂ) (x y : D.V) : Free D := by
  classical
  exact
    ∑ s : D.G,
      if IsSymplecticReflection D s then
        C (2 * c s * omegaS D s x y) * U s
      else
        0





noncomputable def bracketRHS
    (t : ℂ) (c : D.G → ℂ) (x y : D.V) : Free D :=
  C (t * D.omega x y) - reflectionSum (D := D) c x y










inductive Rel (t : ℂ) (c : D.G → ℂ) :
    Free D → Free D → Prop
  | vec_zero :
      Rel t c (X (D := D) 0) 0
  | vec_add (x y : D.V) :
      Rel t c
        (X (D := D) (x + y))
        (X (D := D) x + X (D := D) y)
  | vec_smul (a : ℂ) (x : D.V) :
      Rel t c
        (X (D := D) (a • x))
        (C (D := D) a * X (D := D) x)
  | group_one :
      Rel t c
        (U (D := D) 1)
        1
  | group_mul (g h : D.G) :
      Rel t c
        (U (D := D) (g * h))
        (U (D := D) g * U (D := D) h)
  | action (g : D.G) (x : D.V) :
      Rel t c
        (U (D := D) g * X (D := D) x)
        (X (D := D) (D.ρ g x) * U (D := D) g)
  | bracket (x y : D.V) :
      Rel t c
        (X (D := D) x * X (D := D) y - X (D := D) y * X (D := D) x)
        (bracketRHS (D := D) t c x y)

end Presentation

open Presentation







abbrev H (t : ℂ) (c : D.G → ℂ) : Type _ :=
  RingQuot (Presentation.Rel (D := D) t c)


noncomputable def quotientMap (t : ℂ) (c : D.G → ℂ) :
    Free D →ₐ[ℂ] H D t c :=
  RingQuot.mkAlgHom ℂ (Presentation.Rel (D := D) t c)


def zeroParameter : D.G → ℂ :=
  fun _ => 0






abbrev Center (t : ℂ) (c : D.G → ℂ) : Subalgebra ℂ (H D t c) :=
  Subalgebra.center ℂ (H D t c)






def CenterIsTrivial (t : ℂ) (c : D.G → ℂ) : Prop :=
  Center D t c = ⊥






def FiniteOverCenter (c : D.G → ℂ) : Prop :=
  Module.Finite (↥(Center D 0 c)) (H D 0 c)








def genDegree : Gen D → ℕ
  | Gen.vec _ => 1
  | Gen.grp _ => 0


def listDegree : List (Gen D) → ℕ
  | [] => 0
  | g :: gs => genDegree D g + listDegree gs


def word : List (Gen D) → Free D
  | [] => 1
  | g :: gs => FreeAlgebra.ι ℂ g * word gs





def freePBWFiltration (n : ℕ) : Submodule ℂ (Free D) :=
  Submodule.span ℂ
    {a : Free D | ∃ w : List (Gen D), listDegree D w ≤ n ∧ word (D := D) w = a}






noncomputable def pbwFiltration (t : ℂ) (c : D.G → ℂ) (n : ℕ) :
    Submodule ℂ (H D t c) :=
  Submodule.map (quotientMap D t c).toLinearMap (freePBWFiltration D n)




noncomputable def centerPBWFiltration (c : D.G → ℂ) (n : ℕ) :
    Submodule ℂ (↥(Center D 0 c)) :=
{ carrier := {z | (z : H D 0 c) ∈ pbwFiltration D 0 c n}
  zero_mem' := by
    simp
  add_mem' := by
    intro x y hx hy
    exact (pbwFiltration D 0 c n).add_mem hx hy
  smul_mem' := by
    intro a x hx
    exact (pbwFiltration D 0 c n).smul_mem a hx }

namespace AssociatedGraded





def previousPiece
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (F : ℕ → Submodule R M) (n : ℕ) : Submodule R M :=
  match n with
  | 0 => ⊥
  | Nat.succ k => F k





def prevIn
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (F : ℕ → Submodule R M) (n : ℕ) : Submodule R (F n) :=
  Submodule.comap (F n).subtype (previousPiece F n)





abbrev Module
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (F : ℕ → Submodule R M) : Type _ :=
  DirectSum ℕ fun n => (F n ⧸ prevIn F n)

end AssociatedGraded












structure IsAssociatedGradedPBWCenter
    (c : D.G → ℂ) (grZ : Type*) [CommRing grZ] [Algebra ℂ grZ] : Type _ where
  filtration_mono : Monotone (centerPBWFiltration D c)
  filtration_one :
    (1 : ↥(Center D 0 c)) ∈ centerPBWFiltration D c 0
  filtration_mul :
    ∀ {n m : ℕ} (x : centerPBWFiltration D c n)
      (y : centerPBWFiltration D c m),
      (x.1 * y.1 : ↥(Center D 0 c)) ∈ centerPBWFiltration D c (n + m)
  toAssociatedGradedModule :
    grZ ≃ₗ[ℂ] AssociatedGraded.Module (centerPBWFiltration D c)
  map_one :
    toAssociatedGradedModule.symm
        (DirectSum.of _ 0
          (Submodule.Quotient.mk
            ⟨1, filtration_one⟩)) =
      1
  map_mul :
    ∀ {n m : ℕ} (x : centerPBWFiltration D c n)
      (y : centerPBWFiltration D c m),
      toAssociatedGradedModule.symm
          (DirectSum.of _ n (Submodule.Quotient.mk x)) *
        toAssociatedGradedModule.symm
          (DirectSum.of _ m (Submodule.Quotient.mk y)) =
      toAssociatedGradedModule.symm
        (DirectSum.of _ (n + m)
          (Submodule.Quotient.mk
            ⟨x.1 * y.1, filtration_mul x y⟩))




end Autoform_Double_Hecke_Algebras_double_hecke_theorem_8_14
