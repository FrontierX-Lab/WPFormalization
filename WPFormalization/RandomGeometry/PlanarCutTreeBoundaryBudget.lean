import WPFormalization.RandomGeometry.PlanarCutTreeBudget
import WPFormalization.RandomGeometry.CutBoundaryProduct
noncomputable section
set_option maxHeartbeats 0
namespace WP.RandomGeometry.PlanarCut
open WP.External Finset
variable {n r : ℕ} (D : MulticurveCutData n r)

lemma root_boundaryCount (hcuts : ∀e,∃U,D.IsSide e U) (root : Fin D.components) :
    D.boundaryCount root=n-planarCuspCount D root+rootDegree D root := by
  classical
  have hsum := D.sum_boundaryCount
  have hsplit := Finset.sum_erase_add (s:=Finset.univ) (f:=D.boundaryCount)
    (Finset.mem_univ root)
  have hinc := WP.RandomGeometry.cut_boundary_incidence_sum D (nonrootVertices D root)
  have hcross := crossing_nonroot_eq D hcuts root
  have hpart := internal_nonroot_add_degree D root
  have hcusp : planarCuspCount D root≤n := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  rw [hsum] at hsplit
  change (∑c∈nonrootVertices D root,D.boundaryCount c)+D.boundaryCount root=n+2*r at hsplit
  rw [hinc,hcross] at hsplit
  change (D.cuspSet (nonrootVertices D root)).card+_+_+D.boundaryCount root=n+2*r at hsplit
  change (D.internalEdges (nonrootVertices D root)).card+(rootEdges D root).card=r at hpart
  unfold planarCuspCount rootDegree at *
  omega

lemma nonroot_boundaryCount_le (root c : Fin D.components) (hc : c≠root) :
    D.boundaryCount c≤planarCuspCount D root+2*r := by
  classical
  have hcu : Fintype.card {i : Fin n // D.cuspVertex i=c}≤planarCuspCount D root := by
    simp only [Fintype.card_subtype]
    apply Finset.card_le_card
    intro i hi
    have heq : D.cuspVertex i=c := (Finset.mem_filter.mp hi).2
    simp only [MulticurveCutData.cuspSet,nonrootVertices,
      Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,and_true]
    exact heq ▸ hc
  have hed : Fintype.card {e : Fin r × Fin 2 // D.edgeVertex e=c}≤2*r := by
    calc
      _ ≤ Fintype.card (Fin r × Fin 2) := Fintype.card_subtype_le _
      _ = _ := by simp [Nat.mul_comm]
  simpa only [MulticurveCutData.boundaryCount,MulticurveCutData.Boundary,
    Fintype.card_sum] using Nat.add_le_add hcu hed

lemma nonroot_boundaryCount_le_sum (root c : Fin D.components) (hc : c≠root)
    (k : Fin r → ℕ) (hbudget : planarCuspCount D root≤∑e,k e) :
    D.boundaryCount c≤(∑e,k e)+2*r :=
  (nonroot_boundaryCount_le D root c hc).trans (Nat.add_le_add_right hbudget _)

end WP.RandomGeometry.PlanarCut
