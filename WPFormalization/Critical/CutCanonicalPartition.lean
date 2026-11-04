import WPFormalization.Critical.CutActualEstimate
noncomputable section
set_option maxHeartbeats 0
namespace WP.Critical
open WP.External Finset
open scoped Classical
namespace CutGraphData
variable {n k : ℕ} (D : MulticurveCutData n k)

abbrev OneVertices := {c : Fin D.components // D.genus c=0 ∧ degree D c=1}
abbrev NotOneVertices := {c : Fin D.components // ¬ (D.genus c=0 ∧ degree D c=1)}
abbrev TwoVertices := {c : NotOneVertices D // D.genus c.val=0 ∧ degree D c.val=2}
abbrev BaseStableVertices := {c : NotOneVertices D // ¬ (D.genus c.val=0 ∧ degree D c.val=2)}
abbrev oneCount := Fintype.card (OneVertices D)
abbrev twoCount := Fintype.card (TwoVertices D)
abbrev baseStableCount := Fintype.card (BaseStableVertices D)

def canonicalPartition : CutVertexPartition D.components (oneCount D) (twoCount D) (baseStableCount D) where
  vertices := (Equiv.sumCompl (fun c : Fin D.components => D.genus c=0 ∧ degree D c=1)).symm.trans
    (Equiv.sumCongr (Fintype.equivFin (OneVertices D))
      (((Equiv.sumCompl (fun c : NotOneVertices D => D.genus c.val=0 ∧ degree D c.val=2)).symm).trans
        (Equiv.sumCongr (Fintype.equivFin (TwoVertices D)) (Fintype.equivFin (BaseStableVertices D)))))

lemma canonicalPartition_one (i : Fin (oneCount D)) :
    D.genus ((canonicalPartition D).oneVertex i)=0 ∧
      degree D ((canonicalPartition D).oneVertex i)=1 := by
  change D.genus ((Fintype.equivFin (OneVertices D)).symm i).val=0 ∧
    degree D ((Fintype.equivFin (OneVertices D)).symm i).val=1
  exact ((Fintype.equivFin (OneVertices D)).symm i).property

lemma canonicalPartition_two (i : Fin (twoCount D)) :
    D.genus ((canonicalPartition D).twoVertex i)=0 ∧
      degree D ((canonicalPartition D).twoVertex i)=2 := by
  change D.genus ((Fintype.equivFin (TwoVertices D)).symm i).val.val=0 ∧
    degree D ((Fintype.equivFin (TwoVertices D)).symm i).val.val=2
  exact ((Fintype.equivFin (TwoVertices D)).symm i).property

lemma canonicalPartition_stable (hk : 1≤k) (hconn : D.ConnectedWithin univ)
    (i : Fin (baseStableCount D)) :
    Stable (D.genus ((canonicalPartition D).stableVertex i))
      (degree D ((canonicalPartition D).stableVertex i)) := by
  let a := ((Fintype.equivFin (BaseStableVertices D)).symm i)
  change Stable (D.genus a.val.val) (degree D a.val.val)
  have h1 := a.val.property
  have h2 := a.property
  have hd := degree_pos D hk hconn a.val.val
  unfold Stable
  change ¬ (D.genus a.val.val=0 ∧ degree D a.val.val=1) at h1
  change ¬ (D.genus a.val.val=0 ∧ degree D a.val.val=2) at h2
  omega

lemma canonicalPartition_fits (hk : 1≤k) (hconn : D.ConnectedWithin univ) :
    CutDataFitsPartition D (canonicalPartition D) :=
  ⟨canonicalPartition_one D,canonicalPartition_two D,canonicalPartition_stable D hk hconn⟩

lemma has_canonicalPartition (hk : 1≤k) (hconn : D.ConnectedWithin univ) :
    CutDataHasPartition D (oneCount D) (twoCount D) (baseStableCount D) :=
  ⟨canonicalPartition D,canonicalPartition_fits D hk hconn⟩
end CutGraphData
end WP.Critical
