import WPFormalization.Critical.ShortConfigurationRecordingMultiSelected
import WPFormalization.Critical.ShortConfigurationRecordingPantsExclusion
import WPFormalization.Critical.CutBoundedComponentRealization
import WPFormalization.External.ShortCutPantsGeometry
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical.ShortConfiguration
open Set Finset WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortIntrinsicRegionGeometry WP.External.ShortCutPantsGeometry
open WP.External.ShortBorderedLoopGeometry WP.External.PlanarJordanGeometry
open WP.External.PlanarRegionGeometry WP.External.ShortBorderedPeripheralGeometry
open WP.External.PantsCluster
open WP.FiniteIntersectionClusters
open scoped Classical
variable {P:WP.PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G}
  {A:AmbientRealization H} {T:MulticurveTopology.{u,v,w,z} G H}
  {g n k r:ℕ} {o:T.Orbit g n k} {X:G.Moduli g n (fun _=>0)}
  {κ:Fin k→H.Primitive g n X} {hκ:T.orbitMem o X κ}

lemma actual_cut_piece_containing_simple_not_pants
    (R:CutComponentRealization A T o X κ hκ)
    (AR:∀c,IntrinsicRegionData (A.model g n X) (R.piece c))
    (hcomplete:(A.model g n X).surface.domain=univ)
    (PT:TwoCuspCutRealization hcomplete R)
    (J:PlanarJordanClassics) (PC:PlanarRegionClassics)
    (c:Fin (T.cut o).components)
    (BC:PrimitiveBoundaryClassics (R.piece c).model (R.piece c).boundary)
    (LS:BorderedLoopStraighteningClassics (R.piece c).model (R.piece c).boundary)
    (PP:BorderedPeripheralClassics (R.piece c).model (R.piece c).boundary)
    (γ:(A.model g n X).curves.Primitive) (hsimple:SimpleTrace (A.model g n X) γ)
    (htrace:(A.model g n X).curves.trace γ⊆(R.piece c).point '' intrinsicInterior (R.piece c).model) :
    ¬((R.piece c).model.genus=0 ∧ (R.piece c).model.cusps=2 ∧ (R.piece c).model.boundaries=1) := by
  rintro ⟨hg,hc,hb⟩
  have hgc:(T.cut o).genus c=0:=by rwa [R.genus_eq c] at hg
  have hcc:Nat.card {j:Fin n // (T.cut o).cuspVertex j=c}=2:=by
    have he:=Fintype.card_congr (R.cuspEquiv c)
    simpa only [Fintype.card_fin,←Nat.card_eq_fintype_card,hc,Nat.card_fin] using he.symm
  have hbc:Nat.card {e:Fin k×Fin 2 // (T.cut o).edgeVertex e=c}=1:=by
    have he:=Fintype.card_congr (R.halfSideEquiv c)
    simpa only [Fintype.card_fin,←Nat.card_eq_fintype_card,hb,Nat.card_fin] using he.symm
  exact actual_simple_not_contained_pants_piece (R.piece c) (AR c)
    (PT.topology c hgc hcc hbc) hb BC LS J PC PP γ hsimple htrace

lemma supportingSelectedSet_nonempty_of_nonisolated
    (Γ:Fin r→(A.model g n X).curves.Primitive)
    (select:ActiveCurveCluster (A.model g n X) Γ→Fin (T.cut o).components)
    (hi:∃i,i∉isolatedIndices (A.model g n X) Γ) :
    (supportingSelectedSet select).Nonempty := by
  obtain ⟨i,hi⟩:=hi
  exact ⟨select (activeClusterOfNonisolated (A.model g n X) Γ i hi),
    Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩⟩

lemma actual_selected_simple_component_bad_or_marked
    (R:CutComponentRealization A T o X κ hκ)
    (AR:∀c,IntrinsicRegionData (A.model g n X) (R.piece c))
    (hcomplete:(A.model g n X).surface.domain=univ)
    (PT:TwoCuspCutRealization hcomplete R)
    (J:PlanarJordanClassics) (PC:PlanarRegionClassics)
    (BC:∀c,PrimitiveBoundaryClassics (R.piece c).model (R.piece c).boundary)
    (LS:∀c,BorderedLoopStraighteningClassics (R.piece c).model (R.piece c).boundary)
    (PP:∀c,BorderedPeripheralClassics (R.piece c).model (R.piece c).boundary)
    (Γ:Fin r→(A.model g n X).curves.Primitive) (hsimple:∀i,SimpleTrace (A.model g n X) (Γ i))
    (select:ActiveCurveCluster (A.model g n X) Γ→Fin (T.cut o).components)
    (hintersect:∃i,i∉isolatedIndices (A.model g n X) Γ)
    (K:ℝ) (hg:k+Nat.ceil K+3 ≤ g)
    (hK:∀c∈supportingSelectedSet select,((R.piece c).model.negativeEuler:ℝ) ≤ K)
    (hwitness:∀c∈supportingSelectedSet select,∃i,(A.model g n X).curves.trace (Γ i)⊆
      (R.piece c).point '' intrinsicInterior (R.piece c).model) :
    (CutGraphData.baseStableCount (T.cut o)≠1 ∨ CutGraphData.twoCount (T.cut o)≠0) ∨
      CutDataHasMarkedPartition (T.cut o) (CutGraphData.oneCount (T.cut o))
        (CutGraphData.twoCount (T.cut o)) (CutGraphData.baseStableCount (T.cut o)) := by
  obtain ⟨c,hc⟩:=supportingSelectedSet_nonempty_of_nonisolated Γ select hintersect
  obtain ⟨i,hi⟩:=hwitness c hc
  exact bounded_realization_component_canonical_bad_or_marked R K hg c (hK c hc)
    (actual_cut_piece_containing_simple_not_pants R AR hcomplete PT J PC c (BC c) (LS c) (PP c)
      (Γ i) (hsimple i) hi)
end WP.Critical.ShortConfiguration
