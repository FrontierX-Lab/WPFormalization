import WPFormalization.Critical.ShortConfigurationNetworkCW
import WPFormalization.Critical.ShortConfigurationRecordingEuler
import WPFormalization.External.ShortRegularNeighborhoodGeometry
noncomputable section
set_option maxHeartbeats 0
universe u v w
namespace WP.Critical.ShortConfiguration
open Set WP.External.HyperbolicPacking WP.External.ShortRegularNeighborhoodGeometry
open WP.External.ShortSurfaceEulerGeometry

variable {X : Type u} [MetricSpace X] (N : EmbeddedNetwork.{u,0} X)

/- The retraction is a genuine homotopy equivalence, derived from the
reviewed relative deformation rather than added as a new field. -/
def NeighborhoodData.supportEquivalence (D : NeighborhoodData N) :
    ContinuousMap.HomotopyEquiv D.region N.support where
  toFun := D.retract
  invFun := setInclusion (D.support_interior.trans interior_subset)
  left_inv := by
    rcases D.deformation with ⟨h⟩
    exact ⟨h.toHomotopy.symm⟩
  right_inv := by
    have he : D.retract.comp (setInclusion (D.support_interior.trans interior_subset))=
        ContinuousMap.id N.support := by
      ext p
      rcases D.deformation with ⟨h⟩
      have hz := h.eq_snd 0 (show (⟨p.val,D.support_interior.trans interior_subset p.property⟩:D.region) ∈
          {q:D.region | q.val∈N.support} from p.property)
      rw [ContinuousMap.HomotopyWith.apply_zero] at hz
      simpa [setInclusion] using (congrArg Subtype.val hz).symm
    rw [he]

/- A CW model on the ACTUAL network support. The homotopy equivalence to
the actual hyperbolic piece is an explicit argument, not a construction
claim for the still-unfinished G.3 filling. -/
def networkSurfaceCWModel (B : BorderedGeometry.{u,v})
    (e : ContinuousMap.HomotopyEquiv N.support B.surface.Point) : FiniteSurfaceCWModel B where
  Carrier := N.support
  topology := inferInstance
  cw := networkCW N
  finiteType := by
    letI := networkCW N
    letI := networkCW_finite N
    infer_instance
  dimension_two := by
    intro n hn
    exact networkCW_high_cells_empty N n (by omega)
  equivalent := e

/- Local Euler arithmetic after the actual support equivalence is given. -/
lemma negativeEuler_le_network_edges (B : BorderedGeometry.{u,v})
    (E : SurfaceCellularEulerClassics B)
    (e : ContinuousMap.HomotopyEquiv N.support B.surface.Point) :
    B.negativeEuler ≤ Nat.card N.Edge := by
  have h := negativeEuler_le_one_cells B E (networkSurfaceCWModel N B e)
  change B.negativeEuler ≤ Nat.card (ULift.{u} N.Edge) at h
  exact h.trans_eq (Nat.card_congr Equiv.ulift)

end WP.Critical.ShortConfiguration
