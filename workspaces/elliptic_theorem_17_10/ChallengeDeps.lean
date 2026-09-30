import Mathlib







































noncomputable section

namespace Autoform_Elliptic_Curves_elliptic_theorem_17_10










def IsImaginaryQuadraticField (K : IntermediateField ℚ ℂ) : Prop :=
  Module.rank ℚ K = 2 ∧ ∃ z : K, (z : ℂ).im ≠ 0











structure OrderIn (K : IntermediateField ℚ ℂ) where
  
  carrier : Subalgebra ℤ K
  



  finite_dimensional : Module.Finite ℚ K
  
  free_z : Module.Free ℤ carrier
  



  full_rank : Module.rank ℤ carrier = Module.rank ℚ K

variable {K : IntermediateField ℚ ℂ}

instance instCoeOrderInSubalgebra : Coe (OrderIn K) (Subalgebra ℤ K) :=
  ⟨OrderIn.carrier⟩

instance instCoeSortOrderIn : CoeSort (OrderIn K) (Type _) :=
  ⟨fun 𝓞 => 𝓞.carrier⟩

instance instCommRingOrderIn (𝓞 : OrderIn K) : CommRing 𝓞 :=
  inferInstanceAs (CommRing 𝓞.carrier)

instance instIsDomainOrderIn (𝓞 : OrderIn K) : IsDomain 𝓞 :=
  inferInstanceAs (IsDomain 𝓞.carrier)







instance instAlgebraOrderIn (𝓞 : OrderIn K) : Algebra 𝓞 K :=
  (𝓞.carrier.val : 𝓞 →+* K).toAlgebra











abbrev FracIdeal (𝓞 : OrderIn K) : Type _ :=
  FractionalIdeal (nonZeroDivisors (𝓞 : Type _)) K










noncomputable def idealAbsNorm (𝓞 : OrderIn K) (𝔞 : Ideal 𝓞) : ℕ :=
  Nat.card (𝓞 ⧸ 𝔞)










def IsProperFractionalIdeal (𝓞 : OrderIn K) (I : FracIdeal 𝓞) : Prop :=
  ∀ x : K, (∀ y : K, y ∈ I → x * y ∈ I) ↔ x ∈ (𝓞 : Subalgebra ℤ K)
































end Autoform_Elliptic_Curves_elliptic_theorem_17_10

end
