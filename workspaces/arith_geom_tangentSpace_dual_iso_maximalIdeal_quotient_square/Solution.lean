import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations
import Submission
import ChallengeDeps

open Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_tangentSpace_dual_iso_maximalIdeal_quotient_square






















noncomputable section

open scoped BigOperators

namespace Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_tangentSpace_dual_iso_maximalIdeal_quotient_square


abbrev AffinePolynomialRing (k : Type*) (ι : Type*) [CommSemiring k] :=
  MvPolynomial ι k





theorem pointIdeal_add_mem
    {k ι : Type*} [Field k]
    (P : ι → k) (a b : MvPolynomial ι k)
    (ha : MvPolynomial.eval P a = 0) (hb : MvPolynomial.eval P b = 0) :
    MvPolynomial.eval P (a + b) = 0 := by apply Submission.Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_tangentSpace_dual_iso_maximalIdeal_quotient_square.pointIdeal_add_mem <;> assumption



theorem pointIdeal_smul_mem
    {k ι : Type*} [Field k]
    (P : ι → k) (c x : MvPolynomial ι k)
    (hx : MvPolynomial.eval P x = 0) :
    MvPolynomial.eval P (c • x) = 0 := by apply Submission.Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_tangentSpace_dual_iso_maximalIdeal_quotient_square.pointIdeal_smul_mem <;> assumption







def pointIdeal
    {k ι : Type*} [Field k]
    (P : ι → k) : Ideal (MvPolynomial ι k) where
  carrier := { f : MvPolynomial ι k | MvPolynomial.eval P f = 0 }
  zero_mem' := by
    simp
  add_mem' := by
    intro a b ha hb
    exact pointIdeal_add_mem P a b ha hb
  smul_mem' := by
    intro c x hx
    exact pointIdeal_smul_mem P c x hx


theorem pointIdealSubmodule_add_mem
    {k ι : Type*} [Field k]
    (P : ι → k) (a b : MvPolynomial ι k)
    (ha : MvPolynomial.eval P a = 0) (hb : MvPolynomial.eval P b = 0) :
    MvPolynomial.eval P (a + b) = 0 := by apply Submission.Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_tangentSpace_dual_iso_maximalIdeal_quotient_square.pointIdealSubmodule_add_mem <;> assumption



theorem pointIdealSubmodule_smul_mem
    {k ι : Type*} [Field k]
    (P : ι → k) (c : k) (x : MvPolynomial ι k)
    (hx : MvPolynomial.eval P x = 0) :
    MvPolynomial.eval P (c • x) = 0 := by apply Submission.Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_tangentSpace_dual_iso_maximalIdeal_quotient_square.pointIdealSubmodule_smul_mem <;> assumption












def pointIdealSubmodule
    {k ι : Type*} [Field k]
    (P : ι → k) : Submodule k (MvPolynomial ι k) where
  carrier := { f : MvPolynomial ι k | MvPolynomial.eval P f = 0 }
  zero_mem' := by
    simp
  add_mem' := by
    intro a b ha hb
    exact pointIdealSubmodule_add_mem P a b ha hb
  smul_mem' := by
    intro c x hx
    exact pointIdealSubmodule_smul_mem P c x hx


theorem ZariskiTangentSpace_add_mem
    {k ι : Type*} [Field k] [Fintype ι]
    (I : Ideal (MvPolynomial ι k)) (P : ι → k) (v w : ι → k)
    (hv : ∀ f : MvPolynomial ι k, f ∈ I → directionalDerivativeAt P v f = 0)
    (hw : ∀ f : MvPolynomial ι k, f ∈ I → directionalDerivativeAt P w f = 0)
    (f : MvPolynomial ι k) (hf : f ∈ I) :
    directionalDerivativeAt P (v + w) f = 0 := by apply Submission.Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_tangentSpace_dual_iso_maximalIdeal_quotient_square.ZariskiTangentSpace_add_mem <;> assumption



theorem ZariskiTangentSpace_smul_mem
    {k ι : Type*} [Field k] [Fintype ι]
    (I : Ideal (MvPolynomial ι k)) (P : ι → k) (c : k) (v : ι → k)
    (hv : ∀ f : MvPolynomial ι k, f ∈ I → directionalDerivativeAt P v f = 0)
    (f : MvPolynomial ι k) (hf : f ∈ I) :
    directionalDerivativeAt P (c • v) f = 0 := by apply Submission.Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_tangentSpace_dual_iso_maximalIdeal_quotient_square.ZariskiTangentSpace_smul_mem <;> assumption










def ZariskiTangentSpace
    {k ι : Type*} [Field k] [Fintype ι]
    (I : Ideal (MvPolynomial ι k)) (P : ι → k) :
    Submodule k (ι → k) where
  carrier :=
    { v : ι → k |
      ∀ f : MvPolynomial ι k, f ∈ I → directionalDerivativeAt P v f = 0 }
  zero_mem' := by
    intro f hf
    simp [directionalDerivativeAt]
  add_mem' := by
    intro v w hv hw f hf
    exact ZariskiTangentSpace_add_mem I P v w hv hw f hf
  smul_mem' := by
    intro c v hv f hf
    exact ZariskiTangentSpace_smul_mem I P c v hv f hf

theorem cotangentRelations_zero_mem
    {k ι : Type*} [Field k]
    (I : Ideal (MvPolynomial ι k)) (P : ι → k) :
    ((0 : pointIdealSubmodule P) : MvPolynomial ι k) ∈
      I ⊔ (pointIdeal P) ^ 2 := by apply Submission.Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_tangentSpace_dual_iso_maximalIdeal_quotient_square.cotangentRelations_zero_mem <;> assumption


theorem cotangentRelations_add_mem
    {k ι : Type*} [Field k]
    (I : Ideal (MvPolynomial ι k)) (P : ι → k)
    (f g : pointIdealSubmodule P)
    (hf : (f : MvPolynomial ι k) ∈ I ⊔ (pointIdeal P) ^ 2)
    (hg : (g : MvPolynomial ι k) ∈ I ⊔ (pointIdeal P) ^ 2) :
    ((f + g : pointIdealSubmodule P) : MvPolynomial ι k) ∈
      I ⊔ (pointIdeal P) ^ 2 := by apply Submission.Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_tangentSpace_dual_iso_maximalIdeal_quotient_square.cotangentRelations_add_mem <;> assumption


theorem cotangentRelations_smul_mem
    {k ι : Type*} [Field k]
    (I : Ideal (MvPolynomial ι k)) (P : ι → k)
    (c : k) (f : pointIdealSubmodule P)
    (hf : (f : MvPolynomial ι k) ∈ I ⊔ (pointIdeal P) ^ 2) :
    ((c • f : pointIdealSubmodule P) : MvPolynomial ι k) ∈
      I ⊔ (pointIdeal P) ^ 2 := by apply Submission.Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_tangentSpace_dual_iso_maximalIdeal_quotient_square.cotangentRelations_smul_mem <;> assumption













def cotangentRelations
    {k ι : Type*} [Field k]
    (I : Ideal (MvPolynomial ι k)) (P : ι → k) :
    Submodule k (pointIdealSubmodule P) where
  carrier :=
    { f : pointIdealSubmodule P |
      (f : MvPolynomial ι k) ∈ I ⊔ (pointIdeal P) ^ 2 }
  zero_mem' := cotangentRelations_zero_mem I P
  add_mem' := by
    intro f g hf hg
    exact cotangentRelations_add_mem I P f g hf hg
  smul_mem' := by
    intro c f hf
    exact cotangentRelations_smul_mem I P c f hf







abbrev AlgebraicCotangentSpaceAt
    {k ι : Type*} [Field k]
    (I : Ideal (MvPolynomial ι k)) (P : ι → k) : Type _ :=
  (pointIdealSubmodule P) ⧸ cotangentRelations I P












theorem tangentSpace_dual_iso_maximalIdeal_quotient_square
    {k ι : Type*} [Field k] [Fintype ι]
    (I : Ideal (MvPolynomial ι k)) (P : ι → k)
    (hI : I.IsPrime)
    (hP : PointLiesOnAffineVariety I P) :
    Nonempty
      (Module.Dual k (ZariskiTangentSpace I P) ≃ₗ[k]
        AlgebraicCotangentSpaceAt I P) := by apply Submission.Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_tangentSpace_dual_iso_maximalIdeal_quotient_square.tangentSpace_dual_iso_maximalIdeal_quotient_square <;> assumption

end Autoform_Introduction_to_Arithmetic_Geometry_arith_geom_tangentSpace_dual_iso_maximalIdeal_quotient_square

end