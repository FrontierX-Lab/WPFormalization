import WPFormalization.Critical.PhysicalPantsWaistCatalog
import WPFormalization.RandomGeometry.PantsCutClassification

/- The actual cut of all enumerated physical pants waists has a distinct
numerical pants leaf for each edge. This is cut incidence classification,
not an assertion of actual intrinsic pants topology. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical
open WP.External WP.RandomGeometry
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  (H : HyperbolicCurveGeometry.{u,v,w} G)
  (T : MulticurveTopology.{u,v,w,z} G H) {g n : ℕ}
  (X : G.Moduli g n (fun _ => 0)) (L : ℝ)

lemma physicalPantsWaistTuple_actual_cut_leaves (hg : 1≤g)
    (o : T.Orbit g n (H.shortPlanar X 2 L).card)
    (ho : T.orbitMem o X (physicalPantsWaistTuple H X L)) :
    ∃leaf : Fin (H.shortPlanar X 2 L).card → Fin (T.cut o).components,
      Function.Injective leaf ∧ ∀e,PantsLeafData (T.cut o) e (leaf e) := by
  have hh (e : Fin (H.shortPlanar X 2 L).card) :
      ∃c : Fin (T.cut o).components,PantsLeafData (T.cut o) e c := by
    obtain ⟨_,S,hS,hcard⟩ := (H.mem_shortPlanar X 2 L _).mp
      (physicalPantsWaistTuple_mem H X L e)
    exact planar_two_cusp_leaf (T.cut o) (T.cut_stable o) e S
      ((T.planarSide_iff o X _ ho hg e S).mp hS) hcard
  choose leaf hleaf using hh
  exact ⟨leaf,pantsLeaf_injective (T.cut o) leaf hleaf,hleaf⟩

end WP.Critical
