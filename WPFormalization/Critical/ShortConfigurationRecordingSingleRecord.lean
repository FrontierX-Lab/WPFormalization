import VersoBlueprint.Attribute
import WPFormalization.Critical.ShortConfigurationRecordingSingleNonPants
import WPFormalization.Critical.ShortConfigurationRecordingMaskGeometry
import WPFormalization.Critical.NonsimpleNonPantsCounts
import WPFormalization.Critical.ShortConfigurationRecordingPieceCut
import WPFormalization.Critical.ShortConfigurationRecordingCompletion
import WPFormalization.Critical.CutBoundedComponentRealization
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical.ShortConfiguration
open Set Finset WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortIntrinsicRegionGeometry WP.External.ShortIntrinsicBoundaryGeometry
open WP.External.ShortIntrinsicCompletionGeometry WP.External.ShortCutPantsGeometry
open WP.External.PantsCluster
open scoped Classical
variable {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G}
  (A:AmbientRealization H) (T:MulticurveTopology.{u,v,w,z} G H)
  (AC:AmbientCurveCompatibility A T) {g n:ℕ} (X:G.Moduli g n (fun _=>0))

@[blueprint "ext:short-filling"]
lemma exists_actual_single_nonpants_masked_record
    (γ:H.Primitive g n X) (L:ℝ) (hlength:H.length γ ≤ L)
    (Q:SingleCurvePieceData (A.model g n X) (A.primitiveEquiv g n X γ))
    (QD:IntrinsicRegionData (A.model g n X) Q.piece)
    (QB:IntrinsicBoundaryData (A.model g n X) Q.piece)
    (hQ:¬HasPantsTopology Q.piece.model)
    (RF:∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ),
      CutComponentRealization A T o X κ hκ)
    (AR:∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      IntrinsicRegionData (A.model g n X) ((RF o κ hκ).piece c))
    (BR:∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      IntrinsicBoundaryData (A.model g n X) ((RF o κ hκ).piece c))
    (PT:∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ),
      TwoCuspCutRealization (AC.complete_domain g n X) (RF o κ hκ))
    (CC:∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ),
      CutCompletionRealization (AC.complete_domain g n X) Q.piece QD QB
        (RF o κ hκ) (AR o κ hκ) (BR o κ hκ))
    (hg:singleRecordingEdgeCap L+Nat.ceil (singleRecordingEulerCap L)+3 ≤ g) :
    ∃a:CutMaskedRecordingIndex T (singleRecordingEdgeCap L) (2*L) X,
      MaskedRecordingGeometry T (2*L) X RF (singleRecordingEdgeCap L)
        (singleRecordingEulerCap L) γ a := by
  obtain ⟨k,hkpos,hkcap,κ,o,hκ,c,hlen,htrace,hK,hclass⟩:=
    actual_single_nonpants_cut A T AC X γ L hlength Q QD QB hQ RF AR BR PT CC hg
  have hbox:(fun e=>H.length (κ e))∈cutLengthBox k (2*L):=by
    exact ⟨fun e=>(H.length_pos (κ e)).le,fun e=>
      (Finset.single_le_sum (fun i hi=>(H.length_pos (κ i)).le) (Finset.mem_univ e)).trans hlen⟩
  obtain ⟨a,hao,hak⟩:=exists_actualCutWindow T (2*L) X o κ hκ hkpos hbox hclass
  subst o
  subst κ
  refine ⟨⟨⟨⟨k,by omega⟩,hkpos⟩,makeMaskedWindow T (2*L) X a {c}⟩,?_⟩
  apply MaskedWindowGeometry_makeMaskedWindow T (2*L) X RF a {c}
  · simpa only [Finset.mem_singleton,forall_eq] using hK
  · exact ⟨c,Finset.mem_singleton_self _,htrace⟩
end WP.Critical.ShortConfiguration
