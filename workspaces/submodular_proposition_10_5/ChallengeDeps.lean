import Mathlib

open scoped BigOperators

namespace Autoform_Learning_with_Submodular_Functions_submodular_proposition_10_5

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





















def IsSubmodular (F : Finset ι → ℝ) : Prop :=
  ∀ A B : Finset ι, F (A ∪ B) + F (A ∩ B) ≤ F A + F B






def vectorSetSum (s : ι → ℝ) (A : Finset ι) : ℝ :=
  ∑ i ∈ A, s i






def basePolyhedron (F : Finset ι → ℝ) : Set (ι → ℝ) :=
  {s | vectorSetSum s Finset.univ = F Finset.univ ∧
       ∀ A : Finset ι, vectorSetSum s A ≤ F A}








def negativePartSetSum (s : ι → ℝ) (A : Finset ι) : ℝ :=
  ∑ i ∈ A, min (s i) 0







def ListSortedBy (w : ι → ℝ) : List ι → Prop
  | [] => True
  | _ :: [] => True
  | i :: j :: rest => w j ≤ w i ∧ ListSortedBy w (j :: rest)









structure LovaszOrder (w : ι → ℝ) where
  toList : List ι
  nodup : toList.Nodup
  complete : ∀ i : ι, i ∈ toList
  sorted_desc : ListSortedBy w toList











def lovaszSumFromList
    (F : Finset ι → ℝ) (w : ι → ℝ) (pref : Finset ι) :
    List ι → ℝ
  | [] => 0
  | i :: rest =>
      w i * (F (insert i pref) - F pref) +
        lovaszSumFromList F w (insert i pref) rest









def sqEuclideanNorm (x : ι → ℝ) : ℝ :=
  ∑ i : ι, x i ^ 2





def IsSuperlevelSet (w : ι → ℝ) (A : Finset ι) : Prop :=
  ∃ α : ℝ, ∀ i : ι, i ∈ A ↔ α < w i





def IsSmallestValueSuperlevelSet
    (F : Finset ι → ℝ) (w : ι → ℝ) (A : Finset ι) : Prop :=
  IsSuperlevelSet w A ∧
    ∀ B : Finset ι, IsSuperlevelSet w B → F A ≤ F B



end

end Autoform_Learning_with_Submodular_Functions_submodular_proposition_10_5
