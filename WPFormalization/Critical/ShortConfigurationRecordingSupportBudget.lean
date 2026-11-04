import VersoBlueprint.Attribute
import WPFormalization.External.ShortSupportingConstructionGeometry
import WPFormalization.External.ShortFundamentalGroupGeometry
import WPFormalization.Critical.ShortConfigurationNetworkCW
/- Local actual supporting-piece budgets: compose the actual carrier-induced
π1-surjection with actual graph generators and apply the generic surface
lower bound; compare surviving actual boundary sides to actual dart walks.
No budget is an external field, and no G3 expectation is asserted. -/
noncomputable section
set_option maxHeartbeats 0
universe u v
namespace WP.Critical.ShortConfiguration
open Set Topology WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortRegularNeighborhoodGeometry WP.External.ShortLoopStraighteningGeometry
open WP.External.ShortSupportingConstructionGeometry WP.External.ShortFundamentalGroupGeometry
open scoped Classical

lemma supporting_piece_negativeEuler_le {B:BorderedGeometry.{u,v}}
    (Q:IntrinsicPiece B) (N:EmbeddedNetwork.{u,0} B.surface.Point)
    [PreconnectedSpace N.support]
    (FG:FiniteGraphFundamentalGroupClassics.{u})
    (SF:SurfaceFundamentalGroupClassics Q.model)
    (R:SupportingCarrierRealization Q N) (p:N.support) :
    Q.model.negativeEuler ≤ Nat.card N.Edge := by
  obtain ⟨s,hs,hcard⟩:=FG.generators N.support (networkCW N)
    (networkCW_finite N) (fun n hn=>networkCW_high_cells_empty N n hn) inferInstance p
  let f:=FundamentalGroup.map R.point p
  let t:=s.image f
  have ht:Subgroup.closure (t:Set (FundamentalGroup Q.model.surface.Point (R.point p)))=⊤:=by
    dsimp [t]
    rw [Finset.coe_image,←MonoidHom.map_closure,hs,
      Subgroup.map_top_of_surjective f (R.surjective p)]
  calc
    _ ≤ t.card:=SF.generator_lower_bound _ t ht
    _ ≤ s.card:=Finset.card_image_le
    _ ≤ Nat.card N.Edge:=hcard.trans_eq (networkCW_one_cells_card N)

@[blueprint "ext:short-filling"]
lemma supporting_piece_boundaryLength_le {B:BorderedGeometry.{u,v}}
    (hcomplete:B.surface.domain=univ) (H:LoopStraighteningClassics B hcomplete)
    (Q:IntrinsicPiece B) (N:EmbeddedNetwork.{u,0} B.surface.Point)
    (D:NeighborhoodData N) (C:WP.External.FiniteCyclicIntervalGeometry.Classics)
    (R:SupportingBoundaryRealization Q N D C) :
    boundaryLength Q.boundary ≤ 2*∑e,(N.finish e-N.start e) := by
  have hj:∀j,Q.model.curves.length (Q.boundary.curve j) ≤
      cycleWidth B N D (R.cycle j) := by
    intro j
    rw [←Q.length_preserved]
    apply (ENNReal.ofReal_le_ofReal_iff (cycleWidth_nonneg B N D _)).mp
    apply (H.length_minimal _ _ (ClosedLoop.unoriented_trans (R.homotopic j)
      (Or.inl (frontierCycle_homotopic_walk B N D C (R.cycle j))))).trans
    exact cycle_boundary_walk_variation_le_ofReal N D.rotation C (R.cycle j)
  calc
    _ ≤ ∑j,cycleWidth B N D (R.cycle j):=Finset.sum_le_sum (fun j hj'=>hj j)
    _ = ∑c∈Finset.univ.image R.cycle,cycleWidth B N D c:=by
      symm
      exact Finset.sum_image (fun i hi j hj he=>R.cycle.injective he)
    _ ≤ ∑c:D.rotation.BoundaryCycle N,cycleWidth B N D c:=by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun c hc hnot=>cycleWidth_nonneg B N D c)
    _ = 2*∑e,(N.finish e-N.start e):=
      D.rotation.sum_boundary_weights N (fun e=>N.finish e-N.start e)

lemma supporting_piece_boundaries_le {B:BorderedGeometry.{u,v}}
    (Q:IntrinsicPiece B) (N:EmbeddedNetwork.{u,0} B.surface.Point)
    (D:NeighborhoodData N) (C:WP.External.FiniteCyclicIntervalGeometry.Classics)
    (R:SupportingBoundaryRealization Q N D C) :
    Q.model.boundaries ≤ 2*Nat.card N.Edge := by
  calc
    _ = Nat.card (Fin Q.model.boundaries):=by simp
    _ ≤ Nat.card (D.rotation.BoundaryCycle N):=Nat.card_le_card_of_injective R.cycle R.cycle.injective
    _ ≤ 2*Nat.card N.Edge:=D.rotation.boundaryCycle_card_le N

end WP.Critical.ShortConfiguration
