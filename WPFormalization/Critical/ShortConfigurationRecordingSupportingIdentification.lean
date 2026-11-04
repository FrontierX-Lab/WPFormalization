import WPFormalization.External.ShortSupportingPieceGeometry
import WPFormalization.External.ShortSupportingConstructionGeometry
import WPFormalization.Critical.ShortConfigurationRecordingRegionIdentification
import WPFormalization.Critical.ShortConfigurationRecordingSupportBudget
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical.ShortConfiguration
open Set Finset WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortIntrinsicRegionGeometry WP.External.ShortIntrinsicBoundaryGeometry
open WP.External.ShortSupportingPieceGeometry WP.External.ShortSupportingConstructionGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortRegularNeighborhoodGeometry
open scoped Classical

lemma supporting_boundary_mem_global_geodesics
    {B:BorderedGeometry.{u,v}} (hcomplete:B.surface.domain=univ)
    (H:LoopStraighteningClassics B hcomplete) (Q:IntrinsicPiece B)
    (N:EmbeddedNetwork.{u,0} B.surface.Point) (D:NeighborhoodData N)
    (C:WP.External.FiniteCyclicIntervalGeometry.Classics)
    (R:SupportingBoundaryRealization Q N D C) (j:Fin Q.model.boundaries) :
    Q.primitiveProjection (Q.boundary.curve j)∈essentialGeodesics B N D C hcomplete H := by
  let δ:=Q.primitiveProjection (Q.boundary.curve j)
  have hpos:(frontierCycle B N D C (R.cycle j)).PositiveHomotopyLength:=by
    refine ⟨B.curves.length δ,(B.curves.representative δ).period_pos,?_⟩
    intro f hf
    exact H.length_minimal δ f (ClosedLoop.unoriented_trans (R.homotopic j) hf)
  let c:EssentialCycle B N D C:=⟨R.cycle j,hpos⟩
  have he:straightenedLoop B hcomplete H (essentialFrontier B N D C)
      (essentialFrontier_simple B N D C) (essentialFrontier_positive B N D C) c=δ:=by
    apply (H.class_eq _ _).mp
    exact ClosedLoop.unoriented_trans
      (straightenedLoop_class B hcomplete H (essentialFrontier B N D C)
        (essentialFrontier_simple B N D C) (essentialFrontier_positive B N D C) c)
      (ClosedLoop.unoriented_symm (R.homotopic j))
  exact Finset.mem_image.mpr ⟨c,Finset.mem_univ _,he⟩

variable {P:WP.PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G}

lemma supporting_piece_eq_actual_cut_piece
    {A:AmbientRealization H} {T:MulticurveTopology.{u,v,w,z} G H}
    {g n k:ℕ} {o:T.Orbit g n k} {X:G.Moduli g n (fun _=>0)}
    {κ:Fin k→H.Primitive g n X} {hκ:T.orbitMem o X κ}
    {s:Finset (A.model g n X).curves.Primitive}
    (S:SupportingPieceData (A.model g n X) s) (hs:s.Nonempty)
    (R:CutComponentRealization A T o X κ hκ)
    (AR:∀c,IntrinsicRegionData (A.model g n X) (R.piece c))
    (BR:∀c,IntrinsicBoundaryData (A.model g n X) (R.piece c))
    (c:Fin (T.cut o).components)
    (hcarrier:∀γ∈s,(A.model g n X).curves.trace γ⊆
      (R.piece c).point '' intrinsicInterior (R.piece c).model)
    (hboundary:∀j,∃e,S.piece.primitiveProjection (S.piece.boundary.curve j)=
      A.primitiveEquiv g n X (κ e)) :
    S.piece.point '' intrinsicInterior S.piece.model=
      (R.piece c).point '' intrinsicInterior (R.piece c).model := by
  have hsub:=S.minimal (R.piece c) (AR c) (BR c) hcarrier
  apply Set.Subset.antisymm hsub
  apply preconnected_subset_open_of_frontier_avoid _ _ S.piece.image_open
    (R.piece c).image_connected
  · apply Set.disjoint_left.mpr
    intro p hp hfront
    rw [S.region.frontier_image] at hfront
    obtain ⟨j,hj⟩:=Set.mem_iUnion.mp hfront
    obtain ⟨e,he⟩:=hboundary j
    have hcut:p∈cutComplement A κ:=by
      rw [R.image_eq] at hp
      exact hp.choose
    exact hcut e (he ▸ hj)
  · obtain ⟨γ,hγ⟩:=hs
    obtain ⟨p,hp⟩:=primitive_trace_nonempty (A.model g n X) γ
    exact ⟨p,hcarrier γ hγ hp,S.contains γ hγ hp⟩
end WP.Critical.ShortConfiguration
