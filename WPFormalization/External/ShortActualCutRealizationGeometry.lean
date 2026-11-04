import WPFormalization.External.ShortIntrinsicCompletionGeometry
import WPFormalization.External.ShortCutPantsTypeRecognitionGeometry

/- Data-only Pi/Sigma organization of existing actual creator companions.
No instance is asserted for arbitrary partial A/T/R/S records. The cut factory
selects the SAME actual C in all its existing region, boundary, topology and
completion data. The completion field is scoped to its own genuine cut pieces;
the second structure is scoped to the SAME supplied Hide creator S. No paper
recording, selection, coverage, waist, budget, moment or probability is a field.
All component field types already belong to the reviewed classical interfaces. -/
noncomputable section
universe u v w z
namespace WP.External.ShortActualCutRealizationGeometry
open Set WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortIntrinsicRegionGeometry WP.External.ShortIntrinsicBoundaryGeometry
open WP.External.ShortIntrinsicCompletionGeometry WP.External.ShortCutPantsGeometry
open WP.External.ShortCutPantsTypeRecognitionGeometry

structure ActualCutRealizationData {P : WP.PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} {H : HyperbolicCurveGeometry.{u,v,w} G}
    (A : AmbientRealization H) (T : MulticurveTopology.{u,v,w,z} G H)
    (hcomplete : ∀g n X,(A.model g n X).surface.domain=univ) where
  cut : ∀{g n k : ℕ}(o : T.Orbit g n k)(X : G.Moduli g n (fun _ => 0))
    (κ : Fin k → H.Primitive g n X)(hκ : T.orbitMem o X κ),
      CutComponentRealization A T o X κ hκ
  region : ∀{g n k : ℕ}(o : T.Orbit g n k)(X : G.Moduli g n (fun _ => 0))
    (κ : Fin k → H.Primitive g n X)(hκ : T.orbitMem o X κ)(c : Fin (T.cut o).components),
      IntrinsicRegionData (A.model g n X) ((cut o X κ hκ).piece c)
  boundary : ∀{g n k : ℕ}(o : T.Orbit g n k)(X : G.Moduli g n (fun _ => 0))
    (κ : Fin k → H.Primitive g n X)(hκ : T.orbitMem o X κ)(c : Fin (T.cut o).components),
      IntrinsicBoundaryData (A.model g n X) ((cut o X κ hκ).piece c)
  twoCusp : ∀{g n k : ℕ}(o : T.Orbit g n k)(X : G.Moduli g n (fun _ => 0))
    (κ : Fin k → H.Primitive g n X)(hκ : T.orbitMem o X κ),
      TwoCuspCutRealization (hcomplete g n X) (cut o X κ hκ)
  pantsType : ∀{g n k : ℕ}(o : T.Orbit g n k)(X : G.Moduli g n (fun _ => 0))
    (κ : Fin k → H.Primitive g n X)(hκ : T.orbitMem o X κ),
      CutPantsTypeRecognition (hcomplete g n X) (cut o X κ hκ)
  cut_completion : ∀{g n k : ℕ}(o : T.Orbit g n k)(X : G.Moduli g n (fun _ => 0))
    (κ : Fin k → H.Primitive g n X)(hκ : T.orbitMem o X κ)(c : Fin (T.cut o).components),
    ∀{r : ℕ}(p : T.Orbit g n r)(τ : Fin r → H.Primitive g n X)(hτ : T.orbitMem p X τ),
      CutCompletionRealization (hcomplete g n X)
        ((cut o X κ hκ).piece c) (region o X κ hκ c) (boundary o X κ hκ c)
        (cut p X τ hτ) (region p X τ hτ) (boundary p X τ hτ)

structure SingleCurveCutCompanionData {P : WP.PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} {H : HyperbolicCurveGeometry.{u,v,w} G}
    {A : AmbientRealization H} {T : MulticurveTopology.{u,v,w,z} G H}
    {hcomplete : ∀g n X,(A.model g n X).surface.domain=univ}
    (Cuts : ActualCutRealizationData A T hcomplete) (S : SingleCurvePieceClassics A) where
  region : ∀g n (hg : WP.Stable g n)(X : G.Moduli g n (fun _ => 0))
    (γ : H.Primitive g n X)(hns : ¬H.simple γ),
      IntrinsicRegionData (A.model g n X) (S.piece g n hg X γ hns).piece
  boundary : ∀g n (hg : WP.Stable g n)(X : G.Moduli g n (fun _ => 0))
    (γ : H.Primitive g n X)(hns : ¬H.simple γ),
      IntrinsicBoundaryData (A.model g n X) (S.piece g n hg X γ hns).piece
  completion : ∀g n (hg : WP.Stable g n)(X : G.Moduli g n (fun _ => 0))
    (γ : H.Primitive g n X)(hns : ¬H.simple γ),
    ∀{k : ℕ}(o : T.Orbit g n k)(κ : Fin k → H.Primitive g n X)(hκ : T.orbitMem o X κ),
      CutCompletionRealization (hcomplete g n X) (S.piece g n hg X γ hns).piece
        (region g n hg X γ hns) (boundary g n hg X γ hns)
        (Cuts.cut o X κ hκ) (Cuts.region o X κ hκ) (Cuts.boundary o X κ hκ)

end WP.External.ShortActualCutRealizationGeometry
