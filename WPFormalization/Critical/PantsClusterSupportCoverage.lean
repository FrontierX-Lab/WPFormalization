import WPFormalization.Critical.PantsClusterSupportRefinement
import WPFormalization.External.ShortActualCutRealizationGeometry

/-! A genuine Hide single-curve pants support is captured by the cut along all
short physical pants waists.  Both the singleton and complete cuts are chosen
by the same classical actual-cut creator.  Coverage is proved locally rather
than included in its data. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.Critical.PantsCluster
open Set Finset WP.External WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry WP.External.PantsCluster
open WP.External.ShortActualCutRealizationGeometry
open WP.External.ShortBorderedLoopGeometry WP.External.PlanarJordanGeometry
open WP.External.PlanarRegionGeometry WP.External.ShortBorderedPeripheralGeometry
open WP.RandomGeometry

variable {P : WP.PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G}

lemma actual_good_single_pants_leaf_coverage
    (A : AmbientRealization H) (T : MulticurveTopology.{u,v,w,z} G H)
    (AC : AmbientCurveCompatibility A T)
    (Cuts : ActualCutRealizationData A T AC.complete_domain)
    (S : SingleCurvePieceClassics A) (SC : SingleCurveCutCompanionData Cuts S)
    {g n : ℕ} (hstable : WP.Stable g n) (hg : 1≤g)
    (X : G.Moduli g n (fun _ => 0)) (γ : H.Primitive g n X)
    (hns : ¬H.simple γ) (L : ℝ) (hlen : H.length γ≤L)
    (hp : HasPantsTopology (S.piece g n hstable X γ hns).piece.model)
    (BC : ∀(o : T.Orbit g n 1)(δ : H.Primitive g n X)
      (hδ : T.orbitMem o X (fun _ : Fin 1=>δ))(c : Fin (T.cut o).components),
      PrimitiveBoundaryClassics ((Cuts.cut o X (fun _ : Fin 1=>δ) hδ).piece c).model
        ((Cuts.cut o X (fun _ : Fin 1=>δ) hδ).piece c).boundary)
    (LS : ∀(o : T.Orbit g n 1)(δ : H.Primitive g n X)
      (hδ : T.orbitMem o X (fun _ : Fin 1=>δ))(c : Fin (T.cut o).components),
      BorderedLoopStraighteningClassics ((Cuts.cut o X (fun _ : Fin 1=>δ) hδ).piece c).model
        ((Cuts.cut o X (fun _ : Fin 1=>δ) hδ).piece c).boundary)
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : ∀(o : T.Orbit g n 1)(δ : H.Primitive g n X)
      (hδ : T.orbitMem o X (fun _ : Fin 1=>δ))(c : Fin (T.cut o).components),
      BorderedPeripheralClassics ((Cuts.cut o X (fun _ : Fin 1=>δ) hδ).piece c).model
        ((Cuts.cut o X (fun _ : Fin 1=>δ) hδ).piece c).boundary)
    {k : ℕ} (o : T.Orbit g n k) (κ : Fin k → H.Primitive g n X)
    (hκ : T.orbitMem o X κ)
    (leaf : Fin k → Fin (T.cut o).components)
    (hleaf : ∀e,PantsLeafData (T.cut o) e (leaf e))
    (hfull : ∀δ : H.Primitive g n X,H.length δ≤2*L →
      (∃U : Finset (Fin n),H.planarSide δ=some U ∧ U.card=2) →
      ∃e,κ e=δ) :
    ∃e,A.primitiveEquiv g n X γ∈
      Set.range ((Cuts.cut o X κ hκ).piece (leaf e)).primitiveProjection := by
  let Q := S.piece g n hstable X γ hns
  let D := SC.region g n hstable X γ hns
  let BD := SC.boundary g n hstable X γ hns
  obtain ⟨δ,hδ,o0,h0,hidentify⟩ := exists_actual_pants_support_boundary_cut
    A T AC hg X γ Q D BD hp L hlen
  let R0 := Cuts.cut o0 X (fun _ : Fin 1=>δ) h0
  obtain ⟨c0,hp0,hQ,hγ,hs⟩ := hidentify R0
    (Cuts.region o0 X (fun _ : Fin 1=>δ) h0)
    (Cuts.boundary o0 X (fun _ : Fin 1=>δ) h0)
    (SC.completion g n hstable X γ hns o0 (fun _ : Fin 1=>δ) h0)
    (Cuts.pantsType o0 X (fun _ : Fin 1=>δ) h0)
  obtain ⟨e0,he0⟩ := hfull δ hδ hs
  exact actual_pants_support_refined_leaf_coverage A T AC R0 c0 hp0
    (BC o0 δ h0 c0) (LS o0 δ h0 c0) J PC (PP o0 δ h0 c0)
    (Cuts.region o0 X (fun _ : Fin 1=>δ) h0 c0)
    γ Q D BD hp hQ (Cuts.cut o X κ hκ)
    (Cuts.region o X κ hκ) (Cuts.boundary o X κ hκ)
    (SC.completion g n hstable X γ hns o κ hκ)
    (Cuts.pantsType o X κ hκ) hg leaf hleaf e0 he0

end WP.Critical.PantsCluster
