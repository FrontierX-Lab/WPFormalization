import WPFormalization.Critical.ShortConfigurationRecordingMultiClassification
import WPFormalization.Critical.ShortConfigurationRecordingAugmentedCut
import WPFormalization.External.ShortActualCutRealizationGeometry
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
open scoped Classical
variable {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G}
  (A:AmbientRealization H) (T:MulticurveTopology.{u,v,w,z} G H)
  (AC:AmbientCurveCompatibility A T) {g n r:ℕ} (X:G.Moduli g n (fun _=>0))

lemma exists_actual_intersecting_selected_cut
    (Γ:Fin r→(A.model g n X).curves.Primitive) (hinj:Function.Injective Γ)
    (hsimple:∀i,SimpleTrace (A.model g n X) (Γ i))
    (SC:SegmentClassics (A.model g n X)) (L:ℝ) (hL:0 < L)
    (hlength:∀i,(A.model g n X).curves.length (Γ i) ≤ L)
    (hintersect:∃i,i∉isolatedIndices (A.model g n X) Γ)
    (SP:SupportingPieceClassics (A.model g n X) (AC.complete_domain g n X))
    (FG:FiniteGraphFundamentalGroupClassics.{u})
    (D:NeighborhoodData (tupleEmbeddedNetwork (A.model g n X) SC Γ hinj hsimple L hL hlength))
    (C:WP.External.FiniteCyclicIntervalGeometry.Classics)
    (LS:LoopStraighteningClassics (A.model g n X) (AC.complete_domain g n X))
    (SF:∀a:ActiveCurveCluster (A.model g n X) Γ,
      SurfaceFundamentalGroupClassics (activeClusterSupport (A.model g n X) Γ
        (AC.complete_domain g n X) SP hinj a).piece.model)
    (CR:∀a:ActiveCurveCluster (A.model g n X) Γ,
      SupportingCarrierRealization (activeClusterSupport (A.model g n X) Γ
        (AC.complete_domain g n X) SP hinj a).piece
        (activeSupportNetwork (A.model g n X) Γ SC hinj hsimple L hL hlength a))
    (CB:∀a:ActiveCurveCluster (A.model g n X) Γ,
      SupportingBoundaryRealization (activeClusterSupport (A.model g n X) Γ
        (AC.complete_domain g n X) SP hinj a).piece
        (tupleEmbeddedNetwork (A.model g n X) SC Γ hinj hsimple L hL hlength) D C)
    (Cuts:ActualCutRealizationData A T AC.complete_domain)
    (J:PlanarJordanClassics) (PC:PlanarRegionClassics)
    (BC:∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      PrimitiveBoundaryClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (BLS:∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      BorderedLoopStraighteningClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (PP:∀{k}(o:T.Orbit g n k)(κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      BorderedPeripheralClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (hg:(2*recordingEdgeCap r L+r)+recordingEdgeCap r L+3 ≤ g) :
    ∃k,1 ≤ k ∧ k ≤ 2*recordingEdgeCap r L+r ∧
      ∃κ:Fin k→H.Primitive g n X,∃o:T.Orbit g n k,∃hκ:T.orbitMem o X κ,
      ∃selected:Finset (Fin (T.cut o).components),
      (∑e,H.length (κ e)) ≤ 3*(r:ℝ)*L ∧ selected.card ≤ r ∧
      (∀c∈selected,(((Cuts.cut o X κ hκ).piece c).model.negativeEuler:ℝ) ≤ recordingEdgeCap r L) ∧
      (∀i,(∃e,A.primitiveEquiv g n X (κ e)=Γ i) ∨
        ∃c∈selected,(A.model g n X).curves.trace (Γ i)⊆
          ((Cuts.cut o X κ hκ).piece c).point '' intrinsicInterior ((Cuts.cut o X κ hκ).piece c).model) ∧
      ((CutGraphData.baseStableCount (T.cut o)≠1 ∨ CutGraphData.twoCount (T.cut o)≠0) ∨
        CutDataHasMarkedPartition (T.cut o) (CutGraphData.oneCount (T.cut o))
          (CutGraphData.twoCount (T.cut o)) (CutGraphData.baseStableCount (T.cut o))) := by
  let N:=tupleEmbeddedNetwork (A.model g n X) SC Γ hinj hsimple L hL hlength
  have htrace:∀i,(A.model g n X).curves.trace (Γ i)⊆N.support:=by
    intro i p hp
    rw [tupleEmbeddedNetwork_support]
    exact Set.mem_iUnion.mpr ⟨i,hp⟩
  let γ:Fin r→H.Primitive g n X:=fun i=>(A.primitiveEquiv g n X).symm (Γ i)
  have hΓ:(fun i=>A.primitiveEquiv g n X (γ i))=Γ:=by funext i;simp [γ]
  have hγinj:Function.Injective γ:=(A.primitiveEquiv g n X).symm.injective.comp hinj
  have hγsimple:∀i,H.simple (γ i):=by
    intro i
    apply (AC.simple_iff g n X (γ i)).mpr
    simpa only [γ,Equiv.apply_symm_apply] using hsimple i
  have hγtrace:∀i,(A.model g n X).curves.trace (A.primitiveEquiv g n X (γ i))⊆N.support:=by
    intro i
    simpa only [γ, Equiv.apply_symm_apply] using htrace i
  obtain ⟨k,hk,κ,o,hκ,hlen,_,_,hcover⟩:=exists_actual_augmented_tuple_cut A T AC X γ hγinj hγsimple N hγtrace D C LS
  rw [hΓ] at hcover
  have hNedge:Nat.card N.Edge ≤ recordingEdgeCap r L:=
    tupleEmbeddedNetwork_edges_bound (A.model g n X) SC Γ hinj hsimple L hL hlength
  have hkcap:k ≤ 2*recordingEdgeCap r L+r:=hk.trans (by omega)
  have hsumγ:(∑i,H.length (γ i))=∑i,(A.model g n X).curves.length (Γ i):=by
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [γ,Equiv.apply_symm_apply] using (A.length_eq g n X (γ i)).symm
  have hsum:(∑i,(A.model g n X).curves.length (Γ i)) ≤ (r:ℝ)*L:=by
    simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using
      (Finset.sum_le_sum (s:=univ) (fun i hi=>hlength i))
  have hNlen:(∑ e : N.Edge, (N.finish e - N.start e))=∑i,(A.model g n X).curves.length (Γ i):=
    tupleEmbeddedNetwork_total_length (A.model g n X) SC Γ hinj hsimple L hL hlength
  have hcutlen:(∑e,H.length (κ e)) ≤ 3*(r:ℝ)*L:=by
    rw [hNlen,hsumγ] at hlen
    nlinarith
  obtain ⟨select,himages,hcard,hEuler,hcoords,hwitness⟩:=actual_cluster_selected_indices Γ hinj hsimple SC L hL hlength
    (AC.complete_domain g n X) SP FG N htrace D C LS SF CR CB hcover
    (Cuts.cut o X κ hκ) (Cuts.region o X κ hκ) (Cuts.boundary o X κ hκ)
  have hcg:k+Nat.ceil (recordingEdgeCap r L:ℝ)+3 ≤ g:=by
    simp only [Nat.ceil_natCast]
    omega
  have hclass:=actual_selected_simple_component_bad_or_marked (Cuts.cut o X κ hκ)
    (Cuts.region o X κ hκ) (AC.complete_domain g n X) (Cuts.twoCusp o X κ hκ) J PC
    (BC o κ hκ) (BLS o κ hκ) (PP o κ hκ) Γ hsimple select hintersect (recordingEdgeCap r L) hcg hEuler hwitness
  obtain ⟨c,hc⟩:=supportingSelectedSet_nonempty_of_nonisolated Γ select hintersect
  have hkpos:1 ≤ k:=by
    apply CutGraphData.bounded_component_pos_edges (T.cut o) (T.cut_connected o) (T.cut_euler o) hcg c
    rw [←cutComponent_negativeEuler_eq_complexity (Cuts.cut o X κ hκ) c]
    exact_mod_cast (hEuler c hc).trans (Nat.le_ceil _)
  exact ⟨k,hkpos,hkcap,κ,o,hκ,supportingSelectedSet select,hcutlen,hcard,hEuler,hcoords,hclass⟩
end WP.Critical.ShortConfiguration
