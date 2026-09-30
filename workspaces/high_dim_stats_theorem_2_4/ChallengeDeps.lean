import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_4

noncomputable section









def momentGeneratingFunction
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (s : ℝ) : ℝ :=
  ∫ ω, Real.exp (s * X ω) ∂μ











def IsSubGaussian
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (sigma : ℝ) : Prop :=
  0 < sigma ∧
    Measurable X ∧
      Integrable X μ ∧
        (∫ ω, X ω ∂μ = 0) ∧
          (∀ s : ℝ,
            Integrable (fun ω => Real.exp (s * X ω)) μ ∧
              momentGeneratingFunction μ X s ≤
                Real.exp ((sigma ^ 2 * s ^ 2) / 2))




def ComponentwiseMeasurableVector
    {Ω ι : Type*} [MeasurableSpace Ω]
    (Z : Ω → ι → ℝ) : Prop :=
  ∀ i : ι, Measurable (fun ω => Z ω i)






def euclideanInner
    {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) : ℝ :=
  ∑ i : ι, x i * y i







def euclideanNormSq
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) : ℝ :=
  ∑ i : ι, x i ^ 2




def euclideanNorm
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) : ℝ :=
  Real.sqrt (euclideanNormSq x)











def IsSubGaussianVector
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ι → ℝ) (sigma : ℝ) : Prop :=
  0 < sigma ∧
    ComponentwiseMeasurableVector Z ∧
      (∀ i : ι,
        Integrable (fun ω => Z ω i) μ ∧
          (∫ ω, Z ω i ∂μ) = 0) ∧
        (∀ u : ι → ℝ, euclideanNorm u = 1 →
          IsSubGaussian μ (fun ω => euclideanInner u (Z ω)) sigma)




abbrev RegressionVector (n : ℕ) :=
  Fin n → ℝ







abbrev DesignMatrix (n d : ℕ) :=
  Fin n → Fin d → ℝ




def vectorSub
    {n : ℕ}
    (x y : RegressionVector n) : RegressionVector n :=
  fun i => x i - y i






def matrixVecMul
    {n d : ℕ}
    (X : DesignMatrix n d) (theta : RegressionVector d) :
    RegressionVector n :=
  fun i => ∑ j : Fin d, X i j * theta j




def designColumn
    {n d : ℕ}
    (X : DesignMatrix n d) (j : Fin d) : RegressionVector n :=
  fun i => X i j








def ColumnsNormalized
    {n d : ℕ}
    (X : DesignMatrix n d) : Prop :=
  ∀ j : Fin d, euclideanNorm (designColumn X j) ≤ Real.sqrt (n : ℝ)







def ellOneNorm
    {d : ℕ}
    (theta : RegressionVector d) : ℝ :=
  ∑ j : Fin d, |theta j|






def ellOneBall (d : ℕ) : Set (RegressionVector d) :=
  {theta : RegressionVector d | ellOneNorm theta ≤ 1}







def FixedDesignLinearModel
    {Ω : Type*} [MeasurableSpace Ω]
    {n d : ℕ}
    (X : DesignMatrix n d)
    (thetaStar : RegressionVector d)
    (epsilon Y : Ω → RegressionVector n) : Prop :=
  ComponentwiseMeasurableVector epsilon ∧
    ComponentwiseMeasurableVector Y ∧
      ∀ ω i, Y ω i = matrixVecMul X thetaStar i + epsilon ω i







def leastSquaresLoss
    {n d : ℕ}
    (X : DesignMatrix n d)
    (y : RegressionVector n)
    (theta : RegressionVector d) : ℝ :=
  euclideanNormSq (vectorSub y (matrixVecMul X theta))







def IsConstrainedLeastSquaresEstimator
    {Ω : Type*} [MeasurableSpace Ω]
    {n d : ℕ}
    (K : Set (RegressionVector d))
    (X : DesignMatrix n d)
    (Y : Ω → RegressionVector n)
    (thetaHat : Ω → RegressionVector d) : Prop :=
  ComponentwiseMeasurableVector thetaHat ∧
    ∀ ω, thetaHat ω ∈ K ∧
      ∀ theta : RegressionVector d, theta ∈ K →
        leastSquaresLoss X (Y ω) (thetaHat ω) ≤
          leastSquaresLoss X (Y ω) theta









def fixedDesignMSE
    {Ω : Type*}
    {n d : ℕ}
    (X : DesignMatrix n d)
    (thetaHat : Ω → RegressionVector d)
    (thetaStar : RegressionVector d) : Ω → ℝ :=
  fun ω =>
    euclideanNormSq
        (vectorSub (matrixVecMul X (thetaHat ω)) (matrixVecMul X thetaStar)) /
      (n : ℝ)



end

end Autoform_High_Dimensional_Statistics_high_dim_stats_theorem_2_4
