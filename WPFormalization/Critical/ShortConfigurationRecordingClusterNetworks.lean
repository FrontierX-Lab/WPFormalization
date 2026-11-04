import VersoBlueprint.Attribute
import WPFormalization.Critical.ShortConfigurationRecordingClusters
import WPFormalization.Critical.ShortConfigurationRecordingEmbedded
import WPFormalization.Critical.ShortConfigurationRecordingSupportBudget
noncomputable section
set_option maxHeartbeats 0
universe u v
namespace WP.Critical.ShortConfiguration
open Set Finset WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.FiniteIntersectionClusters
open WP.External.ShortSupportingConstructionGeometry WP.External.ShortFundamentalGroupGeometry
open WP.External.ShortSupportingPieceGeometry
open scoped Classical
variable (B:BorderedGeometry.{u,v}) {r:ℕ} (γ:Fin r→B.curves.Primitive)

def clusterIndexEquiv (c:CurveCluster B γ) :
    Fin (members (traceFamily B γ) c).card ≃ {i:Fin r // i∈members (traceFamily B γ) c} :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe (members (traceFamily B γ) c))).symm

def clusterTuple (c:CurveCluster B γ) :
    Fin (members (traceFamily B γ) c).card→B.curves.Primitive :=
  fun j=>γ (clusterIndexEquiv B γ c j).val

lemma clusterTuple_injective (hinj:Function.Injective γ) (c:CurveCluster B γ) :
    Function.Injective (clusterTuple B γ c) :=
  hinj.comp (Subtype.val_injective.comp (clusterIndexEquiv B γ c).injective)

lemma clusterTuple_carrier (c:CurveCluster B γ) :
    (⋃j,B.curves.trace (clusterTuple B γ c j))=
      WP.FiniteIntersectionClusters.carrier (traceFamily B γ) c := by
  ext p
  simp only [WP.FiniteIntersectionClusters.carrier,Set.mem_iUnion]
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨(clusterIndexEquiv B γ c j).val,(clusterIndexEquiv B γ c j).property,hj⟩
  · rintro ⟨i,hi,hp⟩
    let j:Fin (members (traceFamily B γ) c).card:=(clusterIndexEquiv B γ c).symm ⟨i,hi⟩
    refine ⟨j,?_⟩
    simpa [clusterTuple,j,traceFamily] using hp

variable (SC:SegmentClassics B) (hinj:Function.Injective γ)
  (hsimple:∀i,SimpleTrace B (γ i)) (L:ℝ) (hL:0<L)
  (hlength:∀i,B.curves.length (γ i)≤L)

def clusterNetwork (c:CurveCluster B γ) : EmbeddedNetwork.{u,0} B.surface.Point :=
  tupleEmbeddedNetwork B SC (clusterTuple B γ c) (clusterTuple_injective B γ hinj c)
    (fun j=>hsimple _) L hL (fun j=>hlength _)

lemma clusterNetwork_support (c:CurveCluster B γ) :
    (clusterNetwork B γ SC hinj hsimple L hL hlength c).support=
      WP.FiniteIntersectionClusters.carrier (traceFamily B γ) c := by
  exact (tupleEmbeddedNetwork_support B SC (clusterTuple B γ c)
    (clusterTuple_injective B γ hinj c) (fun j=>hsimple _) L hL (fun j=>hlength _)).trans
      (clusterTuple_carrier B γ c)

lemma clusterNetwork_preconnectedSpace (c:CurveCluster B γ) :
    PreconnectedSpace (clusterNetwork B γ SC hinj hsimple L hL hlength c).support := by
  apply isPreconnected_iff_preconnectedSpace.mp
  rw [clusterNetwork_support]
  exact carrier_isPreconnected (traceFamily B γ) (fun i=>primitive_trace_preconnected B (γ i)) c

lemma clusterNetwork_support_nonempty (c:CurveCluster B γ) :
    (clusterNetwork B γ SC hinj hsimple L hL hlength c).support.Nonempty := by
  rw [clusterNetwork_support]
  exact carrier_nonempty (traceFamily B γ) (fun i=>primitive_trace_nonempty B (γ i)) c

def recordingEdgeCap (r:ℕ) (L:ℝ) : ℕ :=
  r*(r*r*(Nat.floor (L/segmentScale L)+1)^2+1)

lemma clusterNetwork_edges_le (c:CurveCluster B γ) :
    Nat.card (clusterNetwork B γ SC hinj hsimple L hL hlength c).Edge ≤ recordingEdgeCap r L := by
  have hc:(members (traceFamily B γ) c).card ≤ r:=
    (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  apply (tupleEmbeddedNetwork_edges_bound B SC (clusterTuple B γ c)
    (clusterTuple_injective B γ hinj c) (fun j=>hsimple _) L hL (fun j=>hlength _)).trans
  dsimp [recordingEdgeCap]
  gcongr

variable (hcomplete:B.surface.domain=univ) (SP:SupportingPieceClassics B hcomplete)
  (FG:FiniteGraphFundamentalGroupClassics.{u})

def activeSupportNetwork (c:ActiveCurveCluster B γ) : EmbeddedNetwork.{u,0} B.surface.Point :=
  clusterNetwork B γ SC hinj hsimple L hL hlength c.val

include FG in
@[blueprint "ext:short-filling"]
lemma activeSupport_negativeEuler_le (c:ActiveCurveCluster B γ)
    (SF:SurfaceFundamentalGroupClassics (activeClusterSupport B γ hcomplete SP hinj c).piece.model)
    (CR:SupportingCarrierRealization (activeClusterSupport B γ hcomplete SP hinj c).piece
      (activeSupportNetwork B γ SC hinj hsimple L hL hlength c)) :
    (activeClusterSupport B γ hcomplete SP hinj c).piece.model.negativeEuler ≤ recordingEdgeCap r L := by
  letI : PreconnectedSpace (activeSupportNetwork B γ SC hinj hsimple L hL hlength c).support :=
    clusterNetwork_preconnectedSpace B γ SC hinj hsimple L hL hlength c.val
  obtain ⟨p,hp⟩:=clusterNetwork_support_nonempty B γ SC hinj hsimple L hL hlength c.val
  exact (supporting_piece_negativeEuler_le _ _ FG SF CR ⟨p,hp⟩).trans
    (clusterNetwork_edges_le B γ SC hinj hsimple L hL hlength c.val)
end WP.Critical.ShortConfiguration
