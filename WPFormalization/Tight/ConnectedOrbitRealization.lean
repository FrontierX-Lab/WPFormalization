import WPFormalization.Tight.ConnectedOrbitCutData
noncomputable section
namespace WP.TightConnected
open Set Filter Finset External MeasureTheory
open scoped Topology BigOperators ENNReal
lemma connected_orbit_exists_unique {P : PsiTheory} {G : WeilPeterssonGeometry P}
    {T : TightRegions G} {H : HyperbolicCurveGeometry G}
    {Q : TightGeodesicGeometry G T H} (A : TightMulticurveTopology G T H Q)
    (g k : ℕ) (hg : 2≤g) (hk : k≤g) :
    ∃!o : A.Orbit g 0 k,(A.cut o).components=1 := by
  obtain ⟨o,⟨f⟩⟩ := A.cut_realizes (by unfold Stable;omega) (connectedCutData g k)
    (connectedCutData_stable g k hg hk) (connectedCutData_connected g k)
    (connectedCutData_euler g k hk)
  have ho : (A.cut o).components=1 := by
    exact (Fin.equiv_iff_eq.mp ⟨f.vertexEquiv⟩).symm
  exact ⟨o,ho,fun q hq=>connected_orbit_unique A q o hq ho⟩

def connectedOrbitFinset {P : PsiTheory} {G : WeilPeterssonGeometry P}
    {T : TightRegions G} {H : HyperbolicCurveGeometry G}
    {Q : TightGeodesicGeometry G T H} (A : TightMulticurveTopology G T H Q)
    (g k : ℕ) : Finset (A.Orbit g 0 k) := by
  classical
  exact univ.filter fun o=>(A.cut o).components=1

lemma connected_orbit_finset_singleton {P : PsiTheory} {G : WeilPeterssonGeometry P}
    {T : TightRegions G} {H : HyperbolicCurveGeometry G}
    {Q : TightGeodesicGeometry G T H} (A : TightMulticurveTopology G T H Q)
    {g k : ℕ} (o : A.Orbit g 0 k) (ho : (A.cut o).components=1) :
    connectedOrbitFinset A g k={o} := by
  classical
  ext q
  simp only [connectedOrbitFinset,mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
  constructor
  · exact fun hq=>connected_orbit_unique A q o hq ho
  · rintro rfl
    exact ho


end WP.TightConnected
