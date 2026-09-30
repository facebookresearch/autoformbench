import Mathlib

noncomputable section

open scoped BigOperators

namespace Autoform_Double_Hecke_Algebras_double_hecke_theorem_2_1_rational_quantum_calogero_moser











abbrev Poly (n : ℕ) : Type :=
  MvPolynomial (Fin n) ℂ





abbrev RatFun (n : ℕ) : Type :=
  FractionRing (Poly n)


abbrev MultiIndex (n : ℕ) : Type :=
  Fin n →₀ ℕ


abbrev DiffEnd (n : ℕ) : Type :=
  Module.End ℂ (RatFun n)







abbrev RatCoeffDifferentialOperator (n : ℕ) : Type :=
  MultiIndex n →₀ RatFun n


noncomputable def ratConst {n : ℕ} (z : ℂ) : RatFun n :=
  algebraMap (Poly n) (RatFun n) (MvPolynomial.C z)


noncomputable def ratVar {n : ℕ} (i : Fin n) : RatFun n :=
  algebraMap (Poly n) (RatFun n) (MvPolynomial.X i)











noncomputable def polyPermAlgEquiv {n : ℕ}
    (σ : Equiv.Perm (Fin n)) : Poly n ≃ₐ[ℂ] Poly n :=
  MvPolynomial.renameEquiv ℂ σ











noncomputable def ratFunPermAlgEquiv {n : ℕ}
    (σ : Equiv.Perm (Fin n)) : RatFun n ≃ₐ[ℂ] RatFun n :=
  IsFractionRing.algEquivOfAlgEquiv
    (R := ℂ) (A := Poly n) (B := Poly n)
    (K := RatFun n) (L := RatFun n)
    (polyPermAlgEquiv σ)



































namespace RatCoeffDifferentialOperator


end RatCoeffDifferentialOperator







noncomputable def permEnd {n : ℕ}
    (σ : Equiv.Perm (Fin n)) : DiffEnd n :=
  (ratFunPermAlgEquiv σ).toLinearMap






def permMultiIndex {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (α : MultiIndex n) : MultiIndex n :=
  Finsupp.mapDomain σ α








noncomputable def permuteOperator {n : ℕ}
    (σ : Equiv.Perm (Fin n))
    (L : RatCoeffDifferentialOperator n) :
    RatCoeffDifferentialOperator n :=
  L.sum fun α f =>
    Finsupp.single (permMultiIndex σ α) (ratFunPermAlgEquiv σ f)




def syntacticSymmetricGroupInvariant {n : ℕ}
    (L : RatCoeffDifferentialOperator n) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), permuteOperator σ L = L






def multiIndexOrder {n : ℕ} (α : MultiIndex n) : ℕ :=
  α.sum fun _ k => k










def orderAtMost {n : ℕ}
    (L : RatCoeffDifferentialOperator n) (m : ℕ) : Prop :=
  ∀ α : MultiIndex n, m < multiIndexOrder α → L α = 0





noncomputable def powerSumDerivativePart
    (n j : ℕ) : RatCoeffDifferentialOperator n :=
  ∑ i : Fin n,
    Finsupp.single (Finsupp.single i j) (1 : RatFun n)








def hasPowerSumLeadingTerm {n : ℕ}
    (j : ℕ) (L : RatCoeffDifferentialOperator n) : Prop :=
  orderAtMost L j ∧
    ∀ α : MultiIndex n,
      multiIndexOrder α = j →
        L α = powerSumDerivativePart n j α











noncomputable def calogeroMoserPotential
    (n : ℕ) (c : ℂ) : RatFun n :=
  -ratConst (n := n) (c * (c + 1)) *
    (∑ i : Fin n, ∑ j : Fin n,
      if i = j then
        0
      else
        (((ratVar i - ratVar j) ^ 2)⁻¹))





noncomputable def rationalQuantumCalogeroMoserHamiltonian
    (n : ℕ) (c : ℂ) : RatCoeffDifferentialOperator n :=
  powerSumDerivativePart n 2 +
    Finsupp.single (0 : MultiIndex n) (calogeroMoserPotential n c)






abbrev DegreeIndex (n : ℕ) : Type :=
  {j : ℕ // 1 ≤ j ∧ j ≤ n}


def degreeTwoIndex {n : ℕ} (hn : 2 ≤ n) : DegreeIndex n :=
  ⟨2, ⟨by decide, hn⟩⟩



end Autoform_Double_Hecke_Algebras_double_hecke_theorem_2_1_rational_quantum_calogero_moser

end