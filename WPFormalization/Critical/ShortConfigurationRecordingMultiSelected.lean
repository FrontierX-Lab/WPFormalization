import VersoBlueprint.Attribute
import WPFormalization.Critical.ShortConfigurationRecordingClusterNetworks
import WPFormalization.Critical.ShortConfigurationRecordingSupportingSelected
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical.ShortConfiguration
open Set Finset WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortIntrinsicRegionGeometry WP.External.ShortIntrinsicBoundaryGeometry
open WP.External.ShortSupportingPieceGeometry WP.External.ShortSupportingConstructionGeometry
open WP.External.ShortFundamentalGroupGeometry WP.External.ShortRegularNeighborhoodGeometry
open WP.External.ShortLoopStraighteningGeometry WP.FiniteIntersectionClusters
open scoped Classical
variable {P:WP.PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G}
  {A:AmbientRealization H} {T:MulticurveTopology.{u,v,w,z} G H}
  {g n k r:ℕ} {o:T.Orbit g n k} {X:G.Moduli g n (fun _=>0)}
  {κ:Fin k→H.Primitive g n X} {hκ:T.orbitMem o X κ}

@[blueprint "ext:short-filling"]
lemma actual_cluster_selected_indices
    (Γ:Fin r→(A.model g n X).curves.Primitive) (hinj:Function.Injective Γ)
    (hsimple:∀i,SimpleTrace (A.model g n X) (Γ i)) (SC:SegmentClassics (A.model g n X))
    (L:ℝ) (hL:0<L) (hlength:∀i,(A.model g n X).curves.length (Γ i)≤L)
    (hcomplete:(A.model g n X).surface.domain=univ) (SP:SupportingPieceClassics (A.model g n X) hcomplete)
    (FG:FiniteGraphFundamentalGroupClassics.{u})
    (N:EmbeddedNetwork.{u,0} (A.model g n X).surface.Point) (htrace:∀i,(A.model g n X).curves.trace (Γ i)⊆N.support)
    (D:NeighborhoodData N) (C:WP.External.FiniteCyclicIntervalGeometry.Classics)
    (LS:LoopStraighteningClassics (A.model g n X) hcomplete)
    (SF:∀a:ActiveCurveCluster (A.model g n X) Γ,
      SurfaceFundamentalGroupClassics (activeClusterSupport (A.model g n X) Γ hcomplete SP hinj a).piece.model)
    (CR:∀a:ActiveCurveCluster (A.model g n X) Γ,
      SupportingCarrierRealization (activeClusterSupport (A.model g n X) Γ hcomplete SP hinj a).piece
        (activeSupportNetwork (A.model g n X) Γ SC hinj hsimple L hL hlength a))
    (CB:∀a:ActiveCurveCluster (A.model g n X) Γ,
      SupportingBoundaryRealization (activeClusterSupport (A.model g n X) Γ hcomplete SP hinj a).piece N D C)
    (hcover:∀δ,δ∈augmentedGeodesics (A.model g n X) Γ N D C hcomplete LS ↔
      ∃e,A.primitiveEquiv g n X (κ e)=δ)
    (R:CutComponentRealization A T o X κ hκ)
    (AR:∀c,IntrinsicRegionData (A.model g n X) (R.piece c))
    (BR:∀c,IntrinsicBoundaryData (A.model g n X) (R.piece c)) :
    ∃select:ActiveCurveCluster (A.model g n X) Γ→Fin (T.cut o).components,
      (∀a,(activeClusterSupport (A.model g n X) Γ hcomplete SP hinj a).piece.point ''
        intrinsicInterior (activeClusterSupport (A.model g n X) Γ hcomplete SP hinj a).piece.model=
          (R.piece (select a)).point '' intrinsicInterior (R.piece (select a)).model) ∧
      (supportingSelectedSet select).card ≤ r ∧
      (∀c∈supportingSelectedSet select,((R.piece c).model.negativeEuler:ℝ)≤recordingEdgeCap r L) ∧
      (∀i,(∃e,A.primitiveEquiv g n X (κ e)=Γ i) ∨
        ∃c∈supportingSelectedSet select,(A.model g n X).curves.trace (Γ i)⊆
          (R.piece c).point '' intrinsicInterior (R.piece c).model) ∧
      (∀c∈supportingSelectedSet select,∃i,(A.model g n X).curves.trace (Γ i)⊆
        (R.piece c).point '' intrinsicInterior (R.piece c).model) := by
  let s:=fun a:ActiveCurveCluster (A.model g n X) Γ=>clusterPrimitives (A.model g n X) Γ a.val
  let S:=fun a:ActiveCurveCluster (A.model g n X) Γ=>activeClusterSupport (A.model g n X) Γ hcomplete SP hinj a
  have havoid:∀a,WP.External.ShortSupportingPieceGeometry.carrier (A.model g n X) (s a)⊆cutComplement A κ:=by
    intro a p hp e hpe
    obtain ⟨δ,hδs,hpδ⟩:=Set.mem_iUnion₂.mp hp
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hδs
    have hiiso:=active_cluster_member_not_isolated (A.model g n X) Γ a i hi
    have he: A.primitiveEquiv g n X (κ e)∈augmentedGeodesics (A.model g n X) Γ N D C hcomplete LS:=
      (hcover _).mpr ⟨e,rfl⟩
    exact Set.disjoint_left.mp (nonisolated_disjoint_augmented (A.model g n X) Γ N D C hcomplete LS
      hinj hsimple htrace i hiiso he) hpδ hpe
  have hb:∀a j,∃e,(S a).piece.primitiveProjection ((S a).piece.boundary.curve j)=
      A.primitiveEquiv g n X (κ e):=by
    intro a j
    have hm:=supporting_boundary_mem_global_geodesics hcomplete LS (S a).piece N D C (CB a) j
    obtain ⟨e,he⟩:=(hcover _).mp (Finset.mem_union_left _ hm)
    exact ⟨e,he.symm⟩
  have hK:∀a,((S a).piece.model.negativeEuler:ℝ)≤recordingEdgeCap r L:=by
    intro a
    exact_mod_cast activeSupport_negativeEuler_le (A.model g n X) Γ SC hinj hsimple L hL hlength hcomplete SP FG
      a (SF a) (CR a)
  obtain ⟨select,himages,hcard,hbound,hcoords⟩:=exists_supporting_selected_indices s S
    (fun a=>clusterPrimitives_nonempty (A.model g n X) Γ a.val) R AR BR
    (fun a=>clusterPrimitives_preconnected (A.model g n X) Γ a.val) havoid hb (recordingEdgeCap r L) hK
  refine ⟨select,himages,hcard.trans (ActiveCurveCluster.card_le (A.model g n X) Γ),hbound,?_,?_⟩
  · intro i
    by_cases hi:i∈isolatedIndices (A.model g n X) Γ
    · exact Or.inl ((hcover _).mp (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)))
    · right
      apply hcoords
      exact ⟨activeClusterOfNonisolated (A.model g n X) Γ i hi,supporting_trace_subset_carrier _ _
        (mem_active_cluster_of_nonisolated (A.model g n X) Γ i hi)⟩
  · intro c hc
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hc
    obtain ⟨i,hi⟩:=members_nonempty (traceFamily (A.model g n X) Γ) a.val
    refine ⟨i,?_⟩
    rw [←himages a]
    exact (S a).contains (Γ i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
end WP.Critical.ShortConfiguration
