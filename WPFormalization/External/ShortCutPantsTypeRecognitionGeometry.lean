import WPFormalization.External.ShortCutPantsGeometry
/- SAME actual cut creator topology semantics. Martelli Ch5 printed83,
Theorem1.1/Definition1.2, with the actual finite-area cusp compactification
on printed80--81; Mirzakhani 2005 printed11--13 for the actual cut types.
This is scoped DATA for the genuine creator R, not an existence theorem for
arbitrary partial R or arbitrary numerical BorderedGeometry labels.
No recording, filling, budget, curve classification or probability field. -/
noncomputable section
universe u v w z
namespace WP.External.ShortCutPantsTypeRecognitionGeometry
open Set WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.PantsCluster

/- Ordinary uniqueness of the finite-type topology labels of this SAME actual
cut creator R. No instance for arbitrary partial R or numerical B is claimed.
Only component topology recognition; no waist/record/budget/probability field. -/
structure CutPantsTypeRecognition {P:WP.PsiTheory}
    {G:WeilPeterssonGeometry.{u,v} P} {H:HyperbolicCurveGeometry.{u,v,w} G}
    {A:AmbientRealization H} {T:MulticurveTopology.{u,v,w,z} G H}
    {g n k:ℕ} {o:T.Orbit g n k} {X:G.Moduli g n (fun _=>0)}
    {κ:Fin k→H.Primitive g n X} {hκ:T.orbitMem o X κ}
    (hcomplete:(A.model g n X).surface.domain=univ)
    (R:CutComponentRealization A T o X κ hκ) : Prop where
  recognize : ∀c:Fin (T.cut o).components,HasPantsTopology (R.piece c).model→
    (T.cut o).genus c=0 ∧
    Nat.card {j:Fin n // (T.cut o).cuspVertex j=c}=2 ∧
    Nat.card {e:Fin k×Fin 2 // (T.cut o).edgeVertex e=c}=1

end WP.External.ShortCutPantsTypeRecognitionGeometry
