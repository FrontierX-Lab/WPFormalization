import WPFormalization.RandomGeometry.GeneralPlanarStarCutSides
import WPFormalization.RandomGeometry.PantsOrbitLabels

/-! Genuine ordered-star mapping-class orbits for arbitrary fixed planar cusp
sizes. All orbit labels and symmetry factors are proved from actual cut data. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External
open scoped ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)

def GeneralPlanarStarOrbit (g n r : ℕ) (k : Fin r → ℕ) :=
  {o : T.Orbit g n r // ∃f : PlanarLabelBlocks n r k,
    Nonempty (MulticurveCutData.Isomorphism (generalPlanarStarCut g n r k f) (T.cut o))}

instance (g n r : ℕ) (k : Fin r → ℕ) : Fintype (GeneralPlanarStarOrbit T g n r k) := by
  classical
  unfold GeneralPlanarStarOrbit
  infer_instance

lemma generalPlanarOrbit_labels_unique {g n r : ℕ} {k : Fin r → ℕ}
    (hg : 0<g) (o : T.Orbit g n r) (f q : PlanarLabelBlocks n r k)
    (hf : MulticurveCutData.Isomorphism (generalPlanarStarCut g n r k f) (T.cut o))
    (hq : MulticurveCutData.Isomorphism (generalPlanarStarCut g n r k q) (T.cut o)) : f=q :=
  generalPlanarStarCut_isomorphism_labels g n r k f q hg (hf.trans hq.symm)

def generalPlanarOrbitLabel {g n r : ℕ} {k : Fin r → ℕ}
    (o : GeneralPlanarStarOrbit T g n r k) : PlanarLabelBlocks n r k := o.property.choose

def generalPlanarOrbitLabelIso {g n r : ℕ} {k : Fin r → ℕ}
    (o : GeneralPlanarStarOrbit T g n r k) :
    MulticurveCutData.Isomorphism
      (generalPlanarStarCut g n r k (generalPlanarOrbitLabel T o)) (T.cut o.val) :=
  o.property.choose_spec.some

lemma generalPlanarOrbitLabel_injective {g n r : ℕ} {k : Fin r → ℕ} :
    Function.Injective
      (generalPlanarOrbitLabel T : GeneralPlanarStarOrbit T g n r k → PlanarLabelBlocks n r k) := by
  intro o p h
  apply Subtype.ext
  apply T.cut_classifies
  have I := (generalPlanarOrbitLabelIso T o).symm
  rw [h] at I
  exact ⟨I.trans (generalPlanarOrbitLabelIso T p)⟩

lemma generalPlanarOrbitLabel_surjective {g n r : ℕ} {k : Fin r → ℕ}
    (hg : 2≤g) (hk : ∀i,2≤k i) :
    Function.Surjective
      (generalPlanarOrbitLabel T : GeneralPlanarStarOrbit T g n r k → PlanarLabelBlocks n r k) := by
  intro f
  obtain ⟨o,⟨I⟩⟩ := T.cut_realizes (generalPlanarStarCut g n r k f)
    (generalPlanarStarCut_stable g n r k f hg hk)
    (generalPlanarStarCut_connected g n r k f) (generalPlanarStarCut_euler g n r k f)
  let p : GeneralPlanarStarOrbit T g n r k := ⟨o,f,⟨I⟩⟩
  exact ⟨p,generalPlanarOrbit_labels_unique T (by omega) o _ f
    (generalPlanarOrbitLabelIso T p) I⟩

def generalPlanarOrbitLabelEquiv {g n r : ℕ} {k : Fin r → ℕ}
    (hg : 2≤g) (hk : ∀i,2≤k i) :
    GeneralPlanarStarOrbit T g n r k ≃ PlanarLabelBlocks n r k :=
  Equiv.ofBijective (generalPlanarOrbitLabel T)
    ⟨generalPlanarOrbitLabel_injective T,generalPlanarOrbitLabel_surjective T hg hk⟩

lemma generalPlanarStarOrbit_card (g n r : ℕ) (k : Fin r → ℕ)
    (hg : 2≤g) (hk : ∀i,2≤k i) :
    Fintype.card (GeneralPlanarStarOrbit T g n r k)*(∏i,(k i).factorial)=
      n.descFactorial (∑i,k i) := by
  rw [Fintype.card_congr (generalPlanarOrbitLabelEquiv T hg hk)]
  exact planarLabelBlocks_card n r k

lemma generalPlanarStarOrbit_coefficient {g n r : ℕ} {k : Fin r → ℕ}
    (hg : 2≤g) (hk : ∀i,2≤k i) (o : GeneralPlanarStarOrbit T g n r k) :
    T.coefficient o.val=1 := by
  have hM := (generalPlanarOrbitLabelIso T o).oneHandleCount_eq
  have hI := (generalPlanarOrbitLabelIso T o).orientationStabilizerIndex_eq
  rw [generalPlanarStarCut_oneHandleCount _ _ _ _ _ hg hk] at hM
  rw [generalPlanarStarCut_orientation_index _ _ _ _ _ (by omega)] at hI
  simp [MulticurveTopology.coefficient,←hM,←hI]

end WP.RandomGeometry
