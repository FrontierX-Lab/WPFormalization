import WPFormalization.Critical.ShortConfigurationActualTuples
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.External.ShortTupleRecordingGeometry
open WP.Critical.ShortConfiguration
open Set Finset WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortSupportingPieceGeometry WP.External.ShortSupportingConstructionGeometry
open WP.External.ShortFundamentalGroupGeometry WP.External.ShortRegularNeighborhoodGeometry
open scoped Classical
variable {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G}
  (A:AmbientRealization H) {T:MulticurveTopology.{u,v,w,z} G H}
  (AC:AmbientCurveCompatibility A T) {g n r:ℕ} (X:G.Moduli g n (fun _=>0))

/- This data only packages already licensed classical companions of the SAME
actual tuple network and the SAME supports chosen by SP. It contains no
selection, budget, classification, recording, or counting conclusion. -/
structure TupleRecordingCompanions (γ:Fin r→H.Primitive g n X) (hi:Function.Injective γ)
    (hs:∀i,H.simple (γ i)) (SC:SegmentClassics (A.model g n X))
    (L:ℝ) (hL:0<L) (hl:∀i,H.length (γ i)≤L)
    (SP:SupportingPieceClassics (A.model g n X) (AC.complete_domain g n X))
    (C:WP.External.FiniteCyclicIntervalGeometry.Classics) where
  neighborhood : NeighborhoodData (actualTupleNetwork A AC X γ hi hs SC L hL hl)
  surface : ∀a:ActiveCurveCluster (A.model g n X) (actualAmbientTuple A X γ),
    SurfaceFundamentalGroupClassics (activeClusterSupport (A.model g n X) (actualAmbientTuple A X γ)
      (AC.complete_domain g n X) SP (actualAmbientTuple_injective A X γ hi) a).piece.model
  carrier : ∀a:ActiveCurveCluster (A.model g n X) (actualAmbientTuple A X γ),
    SupportingCarrierRealization (activeClusterSupport (A.model g n X) (actualAmbientTuple A X γ)
      (AC.complete_domain g n X) SP (actualAmbientTuple_injective A X γ hi) a).piece
      (activeSupportNetwork (A.model g n X) (actualAmbientTuple A X γ) SC
        (actualAmbientTuple_injective A X γ hi) (actualAmbientTuple_simple A AC X γ hs)
        L hL (actualAmbientTuple_short A X γ L hl) a)
  boundary : ∀a:ActiveCurveCluster (A.model g n X) (actualAmbientTuple A X γ),
    SupportingBoundaryRealization (activeClusterSupport (A.model g n X) (actualAmbientTuple A X γ)
      (AC.complete_domain g n X) SP (actualAmbientTuple_injective A X γ hi) a).piece
      (actualTupleNetwork A AC X γ hi hs SC L hL hl) neighborhood C


end WP.External.ShortTupleRecordingGeometry
