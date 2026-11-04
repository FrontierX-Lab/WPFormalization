import WPFormalization.External.ShortIntrinsicCompletionGeometry
import WPFormalization.External.ShortCutPantsGeometry
/- Local transfer of actual pants topology along the actual same-image
completion isometry. The cut-type exclusion is proved here from the actual
homeomorphisms; numeric genus/cusp labels alone are never used as topology.
The classical data does not select a component or assert this exclusion. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical.ShortConfiguration
open Set WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortIntrinsicRegionGeometry WP.External.ShortIntrinsicBoundaryGeometry
open WP.External.ShortIntrinsicCompletionGeometry WP.External.ShortCutPantsGeometry
open WP.External.PantsCluster

lemma sameImageCompletion_hasPantsTopology {B:BorderedGeometry.{u,v}}
    {P Q:IntrinsicPiece B} (e:SameImageCompletionData P Q)
    (hQ:HasPantsTopology Q.model) : HasPantsTopology P.model := by
  obtain ⟨h,hh⟩:=hQ
  refine ⟨e.point.toHomeomorph.trans h,?_⟩
  intro p
  exact (e.boundary p).trans (hh (e.point p))

lemma sameImageCompletion_hasPantsTopology_iff {B:BorderedGeometry.{u,v}}
    {P Q:IntrinsicPiece B} (e:SameImageCompletionData P Q) :
    HasPantsTopology P.model ↔ HasPantsTopology Q.model := by
  constructor
  · intro hP
    obtain ⟨h,hh⟩:=hP
    refine ⟨e.point.symm.toHomeomorph.trans h,?_⟩
    intro p
    have hb:p∈intrinsicBoundary Q.model ↔
        e.point.symm p∈intrinsicBoundary P.model := by
      simpa using (e.boundary (e.point.symm p)).symm
    exact hb.trans (hh (e.point.symm p))
  · exact sameImageCompletion_hasPantsTopology e

variable {P:WP.PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G}

lemma actual_nonpants_cut_not_two_cusp_leaf
    {A:AmbientRealization H} {T:MulticurveTopology.{u,v,w,z} G H}
    {g n k:ℕ} {o:T.Orbit g n k} {X:G.Moduli g n (fun _=>0)}
    {κ:Fin k→H.Primitive g n X} {hκ:T.orbitMem o X κ}
    {hcomplete:(A.model g n X).surface.domain=univ}
    {Q:IntrinsicPiece (A.model g n X)}
    {D:IntrinsicRegionData (A.model g n X) Q}
    {BD:IntrinsicBoundaryData (A.model g n X) Q}
    {R:CutComponentRealization A T o X κ hκ}
    {AR:∀c,IntrinsicRegionData (A.model g n X) (R.piece c)}
    {BR:∀c,IntrinsicBoundaryData (A.model g n X) (R.piece c)}
    (E:CutCompletionRealization hcomplete Q D BD R AR BR)
    (PC:TwoCuspCutRealization hcomplete R)
    (hQ:¬HasPantsTopology Q.model) (c:Fin (T.cut o).components)
    (hc:Q.point '' intrinsicInterior Q.model=
      (R.piece c).point '' intrinsicInterior (R.piece c).model) :
    ¬((T.cut o).genus c=0 ∧
      Nat.card {j:Fin n // (T.cut o).cuspVertex j=c}=2 ∧
      Nat.card {e:Fin k×Fin 2 // (T.cut o).edgeVertex e=c}=1) := by
  rintro ⟨hg,hn,hk⟩
  obtain ⟨e⟩:=E.completion c hc
  exact hQ (sameImageCompletion_hasPantsTopology e (PC.topology c hg hn hk))

end WP.Critical.ShortConfiguration
