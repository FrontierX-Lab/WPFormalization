import WPFormalization.HigherOrder.RecursiveHandle
import WPFormalization.HigherOrder.SeparatingSourceDecomposition
import WPFormalization.HigherOrder.SeparatingCentralRemainder
/-! The genuine normalized intersection recursion is identified with the
three actual sources used in the all-order remainder induction. Original
finite deficit support, every signed merger, and the separating factor 1/2
are preserved. No coordinate compatibility or error assumption is used. -/
noncomputable section
namespace WP.HigherOrder
open Set
lemma normalizedChildren_scaled_recursive_layer (P:PsiTheory) (g k l:ℕ) (d:List ℕ)
    (hg:2 ≤ g) (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    (4:ℝ)^g*normalizedChildren P g (k+l) (d.map Int.ofNat) Y/W P g (d.length+1) Y=
      (W P g d.length Y/W P g (d.length+1) Y)*
        (∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*(if 1 ≤ k+d[j]!+l then profile P g (mergerProfile k d l j) Y else 0))+
      2*(W P (g-1) (d.length+2) Y/W P g (d.length+1) Y)*
        (∑u∈Finset.range (k+l-1),profile P (g-1) (contractionProfile k d l u) Y)+
      (1/2:ℝ)*(∑u∈Finset.range (k+l-1),∑j∈Finset.range (g+1),
        ∑I∈(Finset.range d.length).powerset,secondSeparatingTerm P g (k+l) d u j I Y):=by
  rw[normalizedChildren_scaled_decomposition P g k l d hg Y hY]
  congr 1
  simp only[secondSeparatingTerm,Finset.mul_sum,Finset.sum_div,Nat.cast_add]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro I hI
  ring
lemma profile_adjacent_recursive_source (P:PsiTheory) (g k L:ℕ) (d:List ℕ)
    (hg:2 ≤ g) (hL:2 ≤ L) (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) (S:ℝ)
    (hS:((d.length+1:ℕ):ℝ)+2*L ≤ S) (hsmall:S^2/(complexity g (d.length+1):ℝ)<1)
    (hd:(k::d).sum ≤ dimension g (d.length+1)) :
    profile P g (k::d) Y-profile P g ((k+1)::d) Y=
      recursiveMerger P g k d Y+recursiveHandle P g k d Y+
        (recursiveSeparatingWeightedLow P g k L d Y+recursiveSeparatingWeightedCentral P g k L d Y):=by
  rw[profile_adjacent_degree_difference P g k d (by omega) Y hY (by unfold complexity;omega) hd]
  simp_rw[normalizedChildren_scaled_recursive_layer P g k _ d hg Y hY,mul_add,Finset.sum_add_distrib]
  rw[recursiveMerger_finite_prefix P g k d hg Y,recursiveHandle_finite_prefix P g k d hg Y]
  rw[recursiveSeparating_full_source_prefix P g k L d hL Y hY S (by unfold Stable;omega) hS hsmall]
  simp only[recursiveSeparatingWeightedCentral]
  congr 1
  congr 1
  · apply Finset.sum_congr rfl
    intro l hl
    ring
  · apply Finset.sum_congr rfl
    intro l hl
    ring
end WP.HigherOrder
