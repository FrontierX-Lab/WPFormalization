import WPFormalization.Critical.ShortConfigurationRecordingTupleRecord
import WPFormalization.Critical.ShortIntersectingFiniteCatalog
import WPFormalization.Critical.ShortConfigurationIntersectingMajorant
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical.ShortConfiguration
open Set Finset Filter WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortSupportingPieceGeometry WP.External.ShortSupportingConstructionGeometry
open WP.External.ShortFundamentalGroupGeometry WP.External.ShortRegularNeighborhoodGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortActualCutRealizationGeometry
open WP.External.ShortBorderedLoopGeometry WP.External.PlanarJordanGeometry
open WP.External.PlanarRegionGeometry WP.External.ShortBorderedPeripheralGeometry
open WP.External.ShortTupleRecordingGeometry
open scoped Classical ENNReal Topology
variable {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G}
  (A:AmbientRealization H) (T:MulticurveTopology.{u,v,w,z} G H)
  (AC:AmbientCurveCompatibility A T) {g n r:ℕ} (X:G.Moduli g n (fun _=>0))

lemma allShortIntersectingSimpleTupleCount_le_actual_cut_majorant
    (SC:SegmentClassics (A.model g n X)) (L:ℝ) (hL:0<L)
    (SP:SupportingPieceClassics (A.model g n X) (AC.complete_domain g n X))
    (FG:FiniteGraphFundamentalGroupClassics.{u})
    (C:WP.External.FiniteCyclicIntervalGeometry.Classics)
    (LS:LoopStraighteningClassics (A.model g n X) (AC.complete_domain g n X))
    (M:∀γ:ShortIntersectingSimpleTuple T X r L,
      TupleRecordingCompanions A AC X γ.val γ.property.1 γ.property.2.1
        SC L hL γ.property.2.2.1 SP C)
    (Cuts:ActualCutRealizationData A T AC.complete_domain)
    (J:PlanarJordanClassics) (PC:PlanarRegionClassics)
    (BC:∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      PrimitiveBoundaryClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (BLS:∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      BorderedLoopStraighteningClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (PP:∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      BorderedPeripheralClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (hg:intersectingRecordingEdgeCap r L+recordingEdgeCap r L+3≤g) :
    allShortIntersectingSimpleTupleCount T X r L≤ intersectingCutMajorant T X r L := by
  let s:=shortIntersectingSimpleTupleCatalog T X r L
  have hex:∀γ:s,∃a:CutMaskedRecordingIndex T (intersectingRecordingEdgeCap r L) (3*(r:ℝ)*L) X,
      MaskedTupleRecordingGeometry T (3*(r:ℝ)*L) X
        (fun {k} o κ hκ=>Cuts.cut o X κ hκ)
        (intersectingRecordingEdgeCap r L) (recordingEdgeCap r L) r γ.val a:=by
    intro γ
    have hp:=(mem_shortIntersectingSimpleTupleCatalog T X r L γ.val).mp γ.property
    exact exists_actual_intersecting_masked_record A T AC X γ.val hp.1 hp.2.1
      SC L hL hp.2.2.1 hp.2.2.2 SP FG C LS (M ⟨γ.val,hp⟩) Cuts J PC BC BLS PP hg
  choose record hgeom using hex
  have hcount:=cut_masked_selected_tuple_count_le T (3*(r:ℝ)*L) X
    (fun {k} o κ hκ=>Cuts.cut o X κ hκ)
    (intersectingRecordingEdgeCap r L) (recordingEdgeCap r L) L r s
    (fun γ hγ=>(mem_shortIntersectingSimpleTupleCatalog T X r L γ).mp hγ |>.2.2.1)
    record hgeom
  rw [allShortIntersectingSimpleTupleCount_eq_card]
  apply hcount.trans
  dsimp only [intersectingCutMajorant,boundedComplexCutFamilyCount,
    intersectingRecordingMultiplicity,intersectingRecordingTupleCap]
  apply mul_le_mul'
  · exact_mod_cast (Nat.le_succ ((intersectingRecordingEdgeCap r L+
      r*WP.Critical.PrimitivePacking.primitiveCountBound (4*Real.pi*recordingEdgeCap r L) L)^r*
      2^(2*intersectingRecordingEdgeCap r L)))
  · exact le_rfl

/- The complete geometric producer is uniform in the cusp-count sequence.
Every companion below is attached to an actual catalog tuple, its actual
network, and supports selected by the same SP creator. -/
lemma actual_intersecting_cut_domination
    (Cuts:ActualCutRealizationData A T AC.complete_domain)
    (SC:∀g n (X:G.Moduli g n (fun _=>0)),SegmentClassics (A.model g n X))
    (SP:∀g n (X:G.Moduli g n (fun _=>0)),
      SupportingPieceClassics (A.model g n X) (AC.complete_domain g n X))
    (FG:FiniteGraphFundamentalGroupClassics.{u})
    (C:WP.External.FiniteCyclicIntervalGeometry.Classics)
    (LS:∀g n (X:G.Moduli g n (fun _=>0)),
      LoopStraighteningClassics (A.model g n X) (AC.complete_domain g n X))
    (M:∀g n r (X:G.Moduli g n (fun _=>0)) L (hL:0<L)
      (γ:ShortIntersectingSimpleTuple T X r L),
      TupleRecordingCompanions A AC X γ.val γ.property.1 γ.property.2.1
        (SC g n X) L hL γ.property.2.2.1 (SP g n X) C)
    (J:PlanarJordanClassics) (PC:PlanarRegionClassics)
    (BC:∀g n {k}(o:T.Orbit g n k)(X:G.Moduli g n (fun _=>0))
      (κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      PrimitiveBoundaryClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (BLS:∀g n {k}(o:T.Orbit g n k)(X:G.Moduli g n (fun _=>0))
      (κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      BorderedLoopStraighteningClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (PP:∀g n {k}(o:T.Orbit g n k)(X:G.Moduli g n (fun _=>0))
      (κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      BorderedPeripheralClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary) :
    ∀r L,0≤L→∀ns:ℕ→ℕ,∀ᶠg in Filter.atTop,∀X:G.Moduli g (ns g) (fun _=>0),
      allShortIntersectingSimpleTupleCount T X r L≤ intersectingCutMajorant T X r L := by
  intro r L hL ns
  by_cases hp:0<L
  · filter_upwards [Filter.eventually_ge_atTop
      (intersectingRecordingEdgeCap r L+recordingEdgeCap r L+3)] with g hg
    intro X
    exact allShortIntersectingSimpleTupleCount_le_actual_cut_majorant A T AC X
      (SC g (ns g) X) L hp (SP g (ns g) X) FG C (LS g (ns g) X)
      (M g (ns g) r X L hp) Cuts J PC
      (fun {k} o κ hκ=>BC g (ns g) o X κ hκ)
      (fun {k} o κ hκ=>BLS g (ns g) o X κ hκ)
      (fun {k} o κ hκ=>PP g (ns g) o X κ hκ) hg
  · apply Filter.Eventually.of_forall
    intro g X
    rw [allShortIntersectingSimpleTupleCount_zero_of_nonpos T X r L (le_of_not_gt hp)]
    exact bot_le
end WP.Critical.ShortConfiguration
