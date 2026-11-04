import WPFormalization.Critical.ShortConfigurationRecordingWindows
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

def singleRecordingEdgeCap (L:ℝ) : ℕ := Nat.ceil (2*L/Real.pi+2)
def singleRecordingEulerCap (L:ℝ) : ℝ := 2*L/Real.pi

lemma actual_single_nonpants_cut
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
    ∃k,1 ≤ k ∧ k ≤ singleRecordingEdgeCap L ∧
      ∃κ:Fin k→H.Primitive g n X,∃o:T.Orbit g n k,∃hκ:T.orbitMem o X κ,
      ∃c:Fin (T.cut o).components,
      (∑e,H.length (κ e)) ≤ 2*L ∧
      (A.model g n X).curves.trace (A.primitiveEquiv g n X γ)⊆
        ((RF o κ hκ).piece c).point '' intrinsicInterior ((RF o κ hκ).piece c).model ∧
      (((RF o κ hκ).piece c).model.negativeEuler:ℝ) ≤ singleRecordingEulerCap L ∧
      ((CutGraphData.baseStableCount (T.cut o)≠1 ∨ CutGraphData.twoCount (T.cut o)≠0) ∨
        CutDataHasMarkedPartition (T.cut o) (CutGraphData.oneCount (T.cut o))
          (CutGraphData.twoCount (T.cut o)) (CutGraphData.baseStableCount (T.cut o))) := by
  have hγ:(A.model g n X).curves.length (A.primitiveEquiv g n X γ) ≤ L:=
    (A.length_eq g n X γ).trans_le hlength
  have hEuler:(Q.piece.model.negativeEuler:ℝ) ≤ singleRecordingEulerCap L:=
    (singleCurvePiece_negativeEuler_le _ _ Q).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hγ (by norm_num)) Real.pi_pos.le)
  have hne:(Q.piece.point '' intrinsicInterior Q.piece.model).Nonempty:=by
    obtain ⟨p,hp⟩:=primitive_trace_nonempty (A.model g n X) (A.primitiveEquiv g n X γ)
    exact ⟨p,Q.contains hp⟩
  obtain ⟨k,hk,κ,o,hκ,hlen,hR⟩:=exists_actual_intrinsic_piece_cut A T AC X Q.piece QD hne QB
  have hkcap:k ≤ singleRecordingEdgeCap L:=by
    have hb:=Q.piece.model.euler_eq
    have hh:(k:ℝ) ≤ (Q.piece.model.negativeEuler:ℝ)+2:=by exact_mod_cast (show k ≤ Q.piece.model.negativeEuler+2 by omega)
    dsimp only [singleRecordingEdgeCap]
    exact_mod_cast (show (k:ℝ) ≤ 2*L/Real.pi+2 from by dsimp only [singleRecordingEulerCap] at hEuler;linarith).trans (Nat.le_ceil _)
  obtain ⟨c,hc,he⟩:=hR (RF o κ hκ) (AR o κ hκ)
  have hcK:(((RF o κ hκ).piece c).model.negativeEuler:ℝ) ≤ singleRecordingEulerCap L:=by rwa [he]
  have hcg:k+Nat.ceil (singleRecordingEulerCap L)+3 ≤ g:=by omega
  have hkpos:1 ≤ k:=by
    apply CutGraphData.bounded_component_pos_edges (T.cut o) (T.cut_connected o) (T.cut_euler o) hcg c
    rw [←cutComponent_negativeEuler_eq_complexity (RF o κ hκ) c]
    exact_mod_cast hcK.trans (Nat.le_ceil _)
  have hnotcut:¬((T.cut o).genus c=0 ∧ CutGraphData.cuspCount (T.cut o) c=2 ∧ CutGraphData.degree (T.cut o) c=1):=by
    intro h
    apply actual_nonpants_cut_not_two_cusp_leaf (CC o κ hκ) (PT o κ hκ) hQ c hc
    simpa only [CutGraphData.cuspCount,CutGraphData.degree,Nat.card_eq_fintype_card] using h
  have hnotintrinsic:¬(((RF o κ hκ).piece c).model.genus=0 ∧
      ((RF o κ hκ).piece c).model.cusps=2 ∧ ((RF o κ hκ).piece c).model.boundaries=1):=by
    simpa only [(RF o κ hκ).genus_eq c,cutComponent_cusps_eq_cuspCount (RF o κ hκ) c,
      cutComponent_boundaries_eq_degree (RF o κ hκ) c] using hnotcut
  refine ⟨k,hkpos,hkcap,κ,o,hκ,c,?_,?_,hcK,?_⟩
  · exact hlen.trans (Q.boundary_length_le.trans (mul_le_mul_of_nonneg_left hγ (by norm_num)))
  · rw [←hc];exact Q.contains
  · exact bounded_realization_component_canonical_bad_or_marked (RF o κ hκ)
      (singleRecordingEulerCap L) hcg c hcK hnotintrinsic
end WP.Critical.ShortConfiguration
