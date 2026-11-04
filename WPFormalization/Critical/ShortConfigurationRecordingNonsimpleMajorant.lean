import WPFormalization.Critical.ShortConfigurationRecordingSingleRecord
import WPFormalization.Critical.ShortConfigurationNonsimpleMajorant
import WPFormalization.External.ShortActualCutRealizationGeometry
import WPFormalization.Critical.ComplexShortConfigurationsStatement
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical.ShortConfiguration
open Set Finset MeasureTheory Filter WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortIntrinsicRegionGeometry WP.External.ShortIntrinsicBoundaryGeometry
open WP.External.ShortIntrinsicCompletionGeometry WP.External.ShortCutPantsGeometry
open WP.External.PantsCluster WP.Critical.PrimitivePacking
open WP.External.ShortActualCutRealizationGeometry
open scoped Classical ENNReal Topology
variable {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G}
  (A:AmbientRealization H) (T:MulticurveTopology.{u,v,w,z} G H)
  (AC:AmbientCurveCompatibility A T) {g n:ℕ} (X:G.Moduli g n (fun _=>0))

lemma nonsimpleNonPantsCount_le_nonsimpleCutMajorant
    (S:SingleCurvePieceClassics A) (hg:Stable g n) (L:ℝ)
    (QD:∀γ (hns:¬H.simple γ),IntrinsicRegionData (A.model g n X) (S.piece g n hg X γ hns).piece)
    (QB:∀γ (hns:¬H.simple γ),IntrinsicBoundaryData (A.model g n X) (S.piece g n hg X γ hns).piece)
    (RF:∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ),
      CutComponentRealization A T o X κ hκ)
    (AR:∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      IntrinsicRegionData (A.model g n X) ((RF o κ hκ).piece c))
    (BR:∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      IntrinsicBoundaryData (A.model g n X) ((RF o κ hκ).piece c))
    (PT:∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ),
      TwoCuspCutRealization (AC.complete_domain g n X) (RF o κ hκ))
    (CC:∀γ(hns:¬H.simple γ){k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ),
      CutCompletionRealization (AC.complete_domain g n X) (S.piece g n hg X γ hns).piece (QD γ hns) (QB γ hns)
        (RF o κ hκ) (AR o κ hκ) (BR o κ hκ))
    (hgenus:singleRecordingEdgeCap L+Nat.ceil (singleRecordingEulerCap L)+3 ≤ g) :
    nonsimpleNonPantsCount A S X L ≤ nonsimpleCutMajorant T X L := by
  let s:=nonsimpleNonPantsFinset A S X L
  have hex:∀γ:s,∃a:CutMaskedRecordingIndex T (singleRecordingEdgeCap L) (2*L) X,
      MaskedRecordingGeometry T (2*L) X RF (singleRecordingEdgeCap L)
        (singleRecordingEulerCap L) γ.val a:=by
    intro γ
    obtain ⟨hbad,hshort⟩:=(mem_nonsimpleNonPantsFinset A S X L γ.val).mp γ.property
    obtain ⟨hns,hpants⟩:=(isNonsimpleNonPants_iff A S hg γ.val).mp hbad
    exact exists_actual_single_nonpants_masked_record A T AC X γ.val L hshort
      (S.piece g n hg X γ.val hns) (QD γ.val hns) (QB γ.val hns) hpants RF AR BR PT (CC γ.val hns) hgenus
  choose record hgeom using hex
  have hcount:=cut_masked_selected_curve_count_le T (2*L) X RF
    (singleRecordingEdgeCap L) (singleRecordingEulerCap L) L s
    (fun γ hγ=>(mem_nonsimpleNonPantsFinset A S X L γ).mp hγ |>.2) record hgeom
  rw [nonsimpleNonPantsCount_eq_card]
  apply hcount.trans
  dsimp only [nonsimpleCutMajorant,boundedComplexCutFamilyCount,singleRecordingMultiplicity]
  apply mul_le_mul'
  · exact_mod_cast (Nat.le_succ (2*singleRecordingEdgeCap L*
      primitiveCountBound (4*Real.pi*singleRecordingEulerCap L) L*2^(2*singleRecordingEdgeCap L)))
  · exact le_rfl

lemma nonsimpleNonPantsCount_le_actual_cut_majorant
    (S:SingleCurvePieceClassics A) (hg:Stable g n) (L:ℝ)
    (Cuts:ActualCutRealizationData A T AC.complete_domain)
    (SC:SingleCurveCutCompanionData Cuts S)
    (hgenus:singleRecordingEdgeCap L+Nat.ceil (singleRecordingEulerCap L)+3 ≤ g) :
    nonsimpleNonPantsCount A S X L ≤ nonsimpleCutMajorant T X L := by
  exact nonsimpleNonPantsCount_le_nonsimpleCutMajorant A T AC X S hg L
    (SC.region g n hg X) (SC.boundary g n hg X)
    (fun {k} o κ hκ=>Cuts.cut o X κ hκ)
    (fun {k} o κ hκ=>Cuts.region o X κ hκ)
    (fun {k} o κ hκ=>Cuts.boundary o X κ hκ)
    (fun {k} o κ hκ=>Cuts.twoCusp o X κ hκ)
    (fun γ hns {k} o κ hκ=>SC.completion g n hg X γ hns o κ hκ) hgenus

lemma nonsimpleNonPants_uniform_measurable_half_majorant
    (S:SingleCurvePieceClassics A)
    (Cuts:ActualCutRealizationData A T AC.complete_domain)
    (SC:SingleCurveCutCompanionData Cuts S)
    (MI:MirzakhaniIntegration G H T) (L:ℝ) (hL:0 ≤ L) (c:ℝ) (hc:0 < c) :
    UniformSequenceMeasurableHalfPowerMajorant
      (fun _ _ X=>nonsimpleNonPantsCount A S X L) c := by
  obtain ⟨C,hC,hRate⟩:=critical_nonsimpleCutMajorant_half_uniform_sequences T MI L hL c hc
  refine ⟨C,hC,fun n hn=>⟨fun g X=>nonsimpleCutMajorant T X L,?_⟩⟩
  filter_upwards [hRate n hn,eventually_ge_atTop
    (singleRecordingEdgeCap L+Nat.ceil (singleRecordingEulerCap L)+3),eventually_ge_atTop (2:ℕ)] with g hr hg hg2
  refine ⟨(nonsimpleCutMajorant_measurable T MI L).aemeasurable,?_,hr⟩
  intro X
  apply nonsimpleNonPantsCount_le_actual_cut_majorant A T AC X S
    (show Stable g (n g) by unfold Stable;omega) L Cuts SC hg
end WP.Critical.ShortConfiguration
