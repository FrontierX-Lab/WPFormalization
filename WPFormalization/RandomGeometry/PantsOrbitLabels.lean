import WPFormalization.RandomGeometry.PantsStarTopology
import WPFormalization.RandomGeometry.PantsStarLabels
import WPFormalization.RandomGeometry.PantsCutIsomorphism
import WPFormalization.External.MirzakhaniIntegration
import WPFormalization.External.MulticurveCutIsomorphism

/-! Local classification and exact count of all ordered pants-star orbits. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External
open scoped ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)

/-- All orbits whose actual cut is an ordered labeled pants star. -/
def PantsStarOrbit (g n r : ℕ) :=
  {o : T.Orbit g n r // ∃f : PantsLabels n r,
    Nonempty (MulticurveCutData.Isomorphism (pantsCutGraph g n r f) (T.cut o))}

instance (g n r : ℕ) : Fintype (PantsStarOrbit T g n r) := by
  classical
  unfold PantsStarOrbit
  infer_instance

lemma pantsOrbit_labels_unique {g n r : ℕ} (hg : 0 < g) (o : T.Orbit g n r)
    (f q : PantsLabels n r)
    (hf : MulticurveCutData.Isomorphism (pantsCutGraph g n r f) (T.cut o))
    (hq : MulticurveCutData.Isomorphism (pantsCutGraph g n r q) (T.cut o)) : f=q :=
  pantsStar_isomorphism_labels g n r f q hg (hf.trans hq.symm)

def pantsOrbitLabel {g n r : ℕ} (o : PantsStarOrbit T g n r) : PantsLabels n r :=
  o.property.choose

def pantsOrbitLabelIso {g n r : ℕ} (o : PantsStarOrbit T g n r) :
    MulticurveCutData.Isomorphism (pantsCutGraph g n r (pantsOrbitLabel T o)) (T.cut o.val) :=
  o.property.choose_spec.some

lemma pantsOrbitLabel_injective {g n r : ℕ} : Function.Injective
    (pantsOrbitLabel T : PantsStarOrbit T g n r → PantsLabels n r) := by
  intro o p h
  apply Subtype.ext
  apply T.cut_classifies
  have I := (pantsOrbitLabelIso T o).symm
  rw [h] at I
  exact ⟨I.trans (pantsOrbitLabelIso T p)⟩

lemma pantsOrbitLabel_surjective {g n r : ℕ} (hg : 2 ≤ g) : Function.Surjective
    (pantsOrbitLabel T : PantsStarOrbit T g n r → PantsLabels n r) := by
  intro f
  obtain ⟨o,⟨I⟩⟩ := T.cut_realizes (pantsCutGraph g n r f)
    (pantsStar_stable g n r f hg) (pantsStar_connected g n r f) (pantsStar_euler g n r f)
  let p : PantsStarOrbit T g n r := ⟨o,f,⟨I⟩⟩
  exact ⟨p,pantsOrbit_labels_unique T (by omega) o _ f (pantsOrbitLabelIso T p) I⟩

def pantsOrbitLabelEquiv {g n r : ℕ} (hg : 2 ≤ g) :
    PantsStarOrbit T g n r ≃ PantsLabels n r :=
  Equiv.ofBijective (pantsOrbitLabel T) ⟨pantsOrbitLabel_injective T,pantsOrbitLabel_surjective T hg⟩

lemma pantsStarOrbit_card (g n r : ℕ) (hg : 2 ≤ g) :
    Fintype.card (PantsStarOrbit T g n r)*2^r=n.descFactorial (2*r) := by
  rw [Fintype.card_congr (pantsOrbitLabelEquiv T hg)]
  exact pantsLabels_card n r

lemma pantsStarOrbit_coefficient {g n r : ℕ} (hg : 2 ≤ g) (o : PantsStarOrbit T g n r) :
    T.coefficient o.val = 1 := by
  have hM := (pantsOrbitLabelIso T o).oneHandleCount_eq
  have hI := (pantsOrbitLabelIso T o).orientationStabilizerIndex_eq
  rw [pantsCutGraph_oneHandleCount _ _ _ _ hg] at hM
  rw [pantsCutGraph_orientation_index _ _ _ _ (by omega)] at hI
  simp [MulticurveTopology.coefficient,←hM,←hI]

lemma orbitMem_unique {g n r : ℕ} (o p : T.Orbit g n r)
    (X : G.Moduli g n (fun _ => 0)) (γ : Fin r → H.Primitive g n X)
    (ho : T.orbitMem o X γ) (hp : T.orbitMem p X γ) : o=p := by
  obtain ⟨q,_,huniq⟩ := T.orbit_partition X γ (T.orbit_injective o X γ ho)
    (T.orbit_simple o X γ ho) (T.orbit_disjoint o X γ ho)
  exact (huniq o ho).trans (huniq p hp).symm

end WP.RandomGeometry
