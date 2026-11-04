import WPFormalization.External.ShortFillingGeometry
import WPFormalization.External.PantsFamilyUniqueness
/- Same actual-realization DATA under the already reviewed classical license.
Derived ordinary cut/surface or geodesic-boundary semantics, not a verbatim
source record and not an existence theorem for arbitrary partial records.
The actual creator carries this data. No G.3 recording, selection, budget,
count or expectation conclusion is a field.
Exact conditions and primary sources: audit/short-cut-pants-classical-fields.md. -/
noncomputable section
universe u v w z
namespace WP.External.ShortCutPantsGeometry
open Set WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.PantsCluster

/- Actual cut-type realization DATA for this same R, not an existence theorem
for arbitrary numeric labels or arbitrary BorderedGeometry. -/
structure TwoCuspCutRealization {P:WP.PsiTheory}
    {G:WeilPeterssonGeometry.{u,v} P} {H:HyperbolicCurveGeometry.{u,v,w} G}
    {A:AmbientRealization H} {T:MulticurveTopology.{u,v,w,z} G H}
    {g n k:ℕ} {o:T.Orbit g n k} {X:G.Moduli g n (fun _=>0)}
    {κ:Fin k→H.Primitive g n X} {hκ:T.orbitMem o X κ}
    (hcomplete:(A.model g n X).surface.domain=univ)
    (R:CutComponentRealization A T o X κ hκ) : Prop where
  topology : ∀c:Fin (T.cut o).components,(T.cut o).genus c=0→
    Nat.card {j:Fin n // (T.cut o).cuspVertex j=c}=2→
    Nat.card {e:Fin k×Fin 2 // (T.cut o).edgeVertex e=c}=1→
    ∃e:(R.piece c).model.surface.Point ≃ₜ TwicePuncturedDisk,
      ∀p,p∈intrinsicBoundary (R.piece c).model ↔ ‖(e p).val‖=1

end WP.External.ShortCutPantsGeometry
