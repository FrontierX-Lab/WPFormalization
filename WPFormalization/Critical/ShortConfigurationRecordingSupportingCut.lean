import WPFormalization.Critical.ShortConfigurationRecordingSupportBudget
import WPFormalization.Critical.ShortConfigurationRecordingPieceCut
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical.ShortConfiguration
open Set WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortIntrinsicRegionGeometry WP.External.ShortIntrinsicBoundaryGeometry
open WP.External.ShortSupportingConstructionGeometry WP.External.ShortFundamentalGroupGeometry
open WP.External.ShortRegularNeighborhoodGeometry WP.External.ShortLoopStraighteningGeometry

variable {P:WP.PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G}

lemma exists_actual_supporting_network_cut
    (A:AmbientRealization H) (T:MulticurveTopology.{u,v,w,z} G H)
    (AC:AmbientCurveCompatibility A T) {g n:ℕ} (X:G.Moduli g n (fun _=>0))
    (Q:IntrinsicPiece (A.model g n X))
    (QD:IntrinsicRegionData (A.model g n X) Q)
    (QB:IntrinsicBoundaryData (A.model g n X) Q)
    (N:EmbeddedNetwork.{u,0} (A.model g n X).surface.Point)
    [PreconnectedSpace N.support] (p:N.support)
    (D:NeighborhoodData N) (C:WP.External.FiniteCyclicIntervalGeometry.Classics)
    (LS:LoopStraighteningClassics (A.model g n X) (AC.complete_domain g n X))
    (FG:FiniteGraphFundamentalGroupClassics.{u})
    (SF:SurfaceFundamentalGroupClassics Q.model)
    (CB:SupportingBoundaryRealization Q N D C)
    (CR:SupportingCarrierRealization Q N) :
    ∃k ≤ 2*Nat.card N.Edge,∃κ:Fin k→H.Primitive g n X,∃o:T.Orbit g n k,
      ∃hκ:T.orbitMem o X κ,
      (∑e,H.length (κ e)) ≤ 2*∑e,(N.finish e-N.start e) ∧
      ∀R:CutComponentRealization A T o X κ hκ,
        ∀AR:∀c,IntrinsicRegionData (A.model g n X) (R.piece c),
        ∃c,(Q.point '' intrinsicInterior Q.model)=
          (R.piece c).point '' intrinsicInterior (R.piece c).model ∧
          N.support⊆(R.piece c).point '' intrinsicInterior (R.piece c).model ∧
          (R.piece c).model.negativeEuler ≤ Nat.card N.Edge := by
  have hN:N.support⊆Q.point '' intrinsicInterior Q.model:=by
    intro x hx
    exact ⟨CR.point ⟨x,hx⟩,CR.interior ⟨x,hx⟩,CR.ambient ⟨x,hx⟩⟩
  have hne:(Q.point '' intrinsicInterior Q.model).Nonempty:=⟨p.val,hN p.property⟩
  have hEuler:=supporting_piece_negativeEuler_le Q N FG SF CR p
  have hbound:=supporting_piece_boundaries_le Q N D C CB
  have hlen:=supporting_piece_boundaryLength_le (AC.complete_domain g n X) LS Q N D C CB
  obtain ⟨k,hk,κ,o,hκ,hκlen,hR⟩:=exists_actual_intrinsic_piece_cut A T AC X Q QD hne QB
  refine ⟨k,hk.trans hbound,κ,o,hκ,hκlen.trans hlen,?_⟩
  intro R AR
  obtain ⟨c,hc,he⟩:=hR R AR
  refine ⟨c,hc,?_,?_⟩
  · rw [←hc]
    exact hN
  · rw [he]
    exact hEuler
end WP.Critical.ShortConfiguration
