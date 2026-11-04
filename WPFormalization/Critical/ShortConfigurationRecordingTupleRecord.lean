import VersoBlueprint.Attribute
import WPFormalization.Critical.ShortConfigurationRecordingTupleProducer
import WPFormalization.External.ShortTupleRecordingGeometry
import WPFormalization.Critical.ShortConfigurationRecordingMaskedTupleMake
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical.ShortConfiguration
open Set Finset WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortSupportingPieceGeometry WP.External.ShortSupportingConstructionGeometry
open WP.External.ShortFundamentalGroupGeometry WP.External.ShortRegularNeighborhoodGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortActualCutRealizationGeometry
open WP.External.ShortBorderedLoopGeometry WP.External.PlanarJordanGeometry
open WP.External.PlanarRegionGeometry WP.External.ShortBorderedPeripheralGeometry
open WP.External.ShortTupleRecordingGeometry
open scoped Classical
variable {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G}
  (A:AmbientRealization H) (T:MulticurveTopology.{u,v,w,z} G H)
  (AC:AmbientCurveCompatibility A T) {g n r:ℕ} (X:G.Moduli g n (fun _=>0))

@[blueprint "ext:short-filling"]
lemma exists_actual_intersecting_masked_record
    (γ:Fin r→H.Primitive g n X) (hi:Function.Injective γ) (hs:∀i,H.simple (γ i))
    (SC:SegmentClassics (A.model g n X)) (L:ℝ) (hL:0<L) (hl:∀i,H.length (γ i)≤L)
    (hnd:¬∀i j,i≠j→T.disjoint (γ i) (γ j))
    (SP:SupportingPieceClassics (A.model g n X) (AC.complete_domain g n X))
    (FG:FiniteGraphFundamentalGroupClassics.{u})
    (C:WP.External.FiniteCyclicIntervalGeometry.Classics)
    (LS:LoopStraighteningClassics (A.model g n X) (AC.complete_domain g n X))
    (M:TupleRecordingCompanions A AC X γ hi hs SC L hL hl SP C)
    (Cuts:ActualCutRealizationData A T AC.complete_domain)
    (J:PlanarJordanClassics) (PC:PlanarRegionClassics)
    (BC:∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      PrimitiveBoundaryClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (BLS:∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      BorderedLoopStraighteningClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (PP:∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      BorderedPeripheralClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (hg:(2*recordingEdgeCap r L+r)+recordingEdgeCap r L+3≤g) :
    ∃a:CutMaskedRecordingIndex T (2*recordingEdgeCap r L+r) (3*(r:ℝ)*L) X,
      MaskedTupleRecordingGeometry T (3*(r:ℝ)*L) X
        (fun {k} o κ hκ=>Cuts.cut o X κ hκ)
        (2*recordingEdgeCap r L+r) (recordingEdgeCap r L) r γ a := by
  have hnd':=actual_intersecting_tuple_nonisolated A AC X γ hi hnd
  obtain ⟨k,hkpos,hkcap,κ,o,hκ,selected,hlen,hcard,hEuler,hcoords,hclass⟩:=
    exists_actual_intersecting_selected_cut A T AC X (actualAmbientTuple A X γ)
      (actualAmbientTuple_injective A X γ hi) (actualAmbientTuple_simple A AC X γ hs)
      SC L hL (actualAmbientTuple_short A X γ L hl) hnd' SP FG
      M.neighborhood C LS M.surface M.carrier M.boundary
      Cuts J PC BC BLS PP hg
  have hcoordsH:∀i,(∃e,κ e=γ i) ∨ ∃c∈selected,
      (A.model g n X).curves.trace (A.primitiveEquiv g n X (γ i))⊆
        ((Cuts.cut o X κ hκ).piece c).point '' intrinsicInterior ((Cuts.cut o X κ hκ).piece c).model:=by
    intro i
    rcases hcoords i with he|hc
    · obtain ⟨e,he⟩:=he
      exact Or.inl ⟨e,(A.primitiveEquiv g n X).injective he⟩
    · exact Or.inr hc
  have hbox:(fun e=>H.length (κ e))∈cutLengthBox k (3*(r:ℝ)*L):=by
    exact ⟨fun e=>(H.length_pos (κ e)).le,fun e=>
      (Finset.single_le_sum (fun i hi=>(H.length_pos (κ i)).le) (Finset.mem_univ e)).trans hlen⟩
  obtain ⟨a,hao,hak⟩:=exists_actualCutWindow T (3*(r:ℝ)*L) X o κ hκ hkpos hbox hclass
  subst o
  subst κ
  refine ⟨⟨⟨⟨k,by omega⟩,hkpos⟩,makeMaskedWindow T (3*(r:ℝ)*L) X a selected⟩,?_⟩
  exact MaskedTupleRecordingGeometry_makeMaskedWindow T (3*(r:ℝ)*L) X
    (fun {k} o κ hκ=>Cuts.cut o X κ hκ) a selected
    (2*recordingEdgeCap r L+r) hkcap hkpos (recordingEdgeCap r L) r γ
    hcard hEuler hcoordsH
end WP.Critical.ShortConfiguration
