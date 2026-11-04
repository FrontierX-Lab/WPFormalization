import WPFormalization.Critical.CriticalSpectrumBadEvents
import WPFormalization.RandomGeometry.PantsCounts

/- Enumerate the complete actual physical pants-waist catalog. On the genuine
nonintersection event, this tuple has its actual multicurve orbit under T.
No cut component or short-spectrum classification is supplied as a field. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical
open WP.External WP.RandomGeometry Set
open scoped Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}
  (X : G.Moduli g n (fun _ => 0)) (L : ℝ)

abbrev PhysicalPantsWaistCatalog := {γ : H.Primitive g n X // γ∈H.shortPlanar X 2 L}

def physicalPantsWaistEquiv : Fin (H.shortPlanar X 2 L).card ≃ PhysicalPantsWaistCatalog H X L :=
  (Fintype.equivFinOfCardEq (by simp)).symm

def physicalPantsWaistTuple : Fin (H.shortPlanar X 2 L).card → H.Primitive g n X :=
  fun i => (physicalPantsWaistEquiv H X L i).val

lemma physicalPantsWaistTuple_injective : Function.Injective (physicalPantsWaistTuple H X L) := by
  intro i j hij
  apply (physicalPantsWaistEquiv H X L).injective
  exact Subtype.ext hij

lemma physicalPantsWaistTuple_mem (i : Fin (H.shortPlanar X 2 L).card) :
    physicalPantsWaistTuple H X L i∈H.shortPlanar X 2 L :=
  (physicalPantsWaistEquiv H X L i).property

lemma physicalPantsWaistTuple_complete (γ : H.Primitive g n X) :
    γ∈H.shortPlanar X 2 L ↔ ∃i,physicalPantsWaistTuple H X L i=γ := by
  constructor
  · intro hγ
    exact ⟨(physicalPantsWaistEquiv H X L).symm ⟨γ,hγ⟩,
      congrArg Subtype.val ((physicalPantsWaistEquiv H X L).apply_symm_apply ⟨γ,hγ⟩)⟩
  · rintro ⟨i,rfl⟩
    exact physicalPantsWaistTuple_mem H X L i

lemma physicalPantsWaistTuple_simple (i : Fin (H.shortPlanar X 2 L).card) :
    H.simple (physicalPantsWaistTuple H X L i) := by
  obtain ⟨_,S,hS,_⟩ := (H.mem_shortPlanar X 2 L _).mp
    (physicalPantsWaistTuple_mem H X L i)
  exact H.planar_simple _ S hS

lemma physicalPantsWaistTuple_length (i : Fin (H.shortPlanar X 2 L).card) :
    H.length (physicalPantsWaistTuple H X L i)≤L :=
  ((H.mem_shortPlanar X 2 L _).mp (physicalPantsWaistTuple_mem H X L i)).1

variable (T : MulticurveTopology.{u,v,w,z} G H)

lemma physicalPantsWaistTuple_disjoint_of_no_bad
    (hX : ¬HasIntersectingShortPants T L X)
    (i j : Fin (H.shortPlanar X 2 L).card) (hij : i≠j) :
    T.disjoint (physicalPantsWaistTuple H X L i) (physicalPantsWaistTuple H X L j) := by
  by_contra hd
  exact hX ⟨_,_,(physicalPantsWaistTuple_injective H X L).ne hij,
    physicalPantsWaistTuple_mem H X L i,physicalPantsWaistTuple_mem H X L j,hd⟩

lemma physicalPantsWaistTuple_actual_orbit_of_no_bad
    (hX : ¬HasIntersectingShortPants T L X) :
    ∃!o : T.Orbit g n (H.shortPlanar X 2 L).card,
      T.orbitMem o X (physicalPantsWaistTuple H X L) :=
  T.orbit_partition X _ (physicalPantsWaistTuple_injective H X L)
    (physicalPantsWaistTuple_simple H X L)
    (physicalPantsWaistTuple_disjoint_of_no_bad H X L T hX)

end WP.Critical
