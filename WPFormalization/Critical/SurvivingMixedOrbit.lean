import WPFormalization.Critical.SurvivingMixedStable
import WPFormalization.RandomGeometry.PantsOrbitLabels
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe aa bb cc dd
namespace WP.Critical
open WP.External WP.RandomGeometry
open scoped ENNReal Classical

lemma survivingMixed_isomorphism_labels (g n r k : ℕ) (f q : PantsLabels n r) (hg : k < g)
    (I : MulticurveCutData.Isomorphism (survivingMixedCutGraph g n r k f)
      (survivingMixedCutGraph g n r k q)) : f=q := by
  let v : Equiv.Perm (Fin (r+1)) := I.vertexEquiv
  have hv0 : v 0=0 := survivingMixed_root_fixed g n r k f hg v I.genus_eq
  have hflip (i : Fin r) : I.flip (i.castAdd k)=false := by
    have he := I.edge_eq (i.castAdd k) 0
    cases h : I.flip (i.castAdd k)
    · rfl
    · have hh : v (0 : Fin (r+1))=i.succ := by simpa [v,survivingMixedCutGraph,h] using he
      exact (Fin.succ_ne_zero i (hv0.symm.trans hh).symm).elim
  have hvleaf (i : Fin r) : v i.succ=i.succ := by
    simpa [v,survivingMixedCutGraph,hflip i] using I.edge_eq (i.castAdd k) 1
  apply pantsLabels_eq_of_row_cover f q
  intro i j
  apply pantsStar_leaf_cusp_exists (g-k) n r q i (f.val (i,j))
  have hh := I.cusp_eq (f.val (i,j))
  change v ((pantsCutGraph (g-k) n r f).cuspVertex (f.val (i,j)))=
    (pantsCutGraph (g-k) n r q).cuspVertex (f.val (i,j)) at hh
  rw [pantsCutGraph_cusp_pair] at hh
  exact hh.symm.trans (hvleaf i)

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
  {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)

def SurvivingMixedOrbit (g n r k : ℕ) :=
  {o : T.Orbit g n (r+k) // ∃ f : PantsLabels n r,
    Nonempty (MulticurveCutData.Isomorphism (survivingMixedCutGraph g n r k f) (T.cut o))}
instance (g n r k : ℕ) : Fintype (SurvivingMixedOrbit T g n r k) := by
  unfold SurvivingMixedOrbit
  infer_instance

def survivingMixedOrbitLabel {g n r k : ℕ} (o : SurvivingMixedOrbit T g n r k) : PantsLabels n r :=
  o.property.choose
def survivingMixedOrbitIso {g n r k : ℕ} (o : SurvivingMixedOrbit T g n r k) :
    MulticurveCutData.Isomorphism (survivingMixedCutGraph g n r k (survivingMixedOrbitLabel T o))
      (T.cut o.val) := o.property.choose_spec.some

lemma survivingMixedOrbitLabel_injective {g n r k : ℕ} :
    Function.Injective (survivingMixedOrbitLabel T : SurvivingMixedOrbit T g n r k → PantsLabels n r) := by
  intro o p h
  apply Subtype.ext
  apply T.cut_classifies
  have I := (survivingMixedOrbitIso T o).symm
  rw [h] at I
  exact ⟨I.trans (survivingMixedOrbitIso T p)⟩

lemma survivingMixedOrbitLabel_surjective {g n r k : ℕ} (hg : k+2 ≤ g) :
    Function.Surjective (survivingMixedOrbitLabel T : SurvivingMixedOrbit T g n r k → PantsLabels n r) := by
  intro f
  obtain ⟨o,⟨I⟩⟩ := T.cut_realizes (survivingMixedCutGraph g n r k f)
    (survivingMixed_stable g n r k f hg) (survivingMixed_connected g n r k f)
      (survivingMixed_euler g n r k f (by omega))
  let p : SurvivingMixedOrbit T g n r k := ⟨o,f,⟨I⟩⟩
  refine ⟨p,?_⟩
  exact survivingMixed_isomorphism_labels g n r k _ f (by omega)
    ((survivingMixedOrbitIso T p).trans I.symm)

def survivingMixedOrbitLabelEquiv {g n r k : ℕ} (hg : k+2 ≤ g) :
    SurvivingMixedOrbit T g n r k ≃ PantsLabels n r :=
  Equiv.ofBijective (survivingMixedOrbitLabel T)
    ⟨survivingMixedOrbitLabel_injective T,survivingMixedOrbitLabel_surjective T hg⟩

lemma survivingMixedOrbit_card (g n r k : ℕ) (hg : k+2 ≤ g) :
    Fintype.card (SurvivingMixedOrbit T g n r k)*2^r=n.descFactorial (2*r) := by
  rw [Fintype.card_congr (survivingMixedOrbitLabelEquiv T hg)]
  exact pantsLabels_card n r

lemma survivingMixedOrbit_coefficient {g n r k : ℕ} (hg : k+2 ≤ g)
    (o : SurvivingMixedOrbit T g n r k) :
    T.coefficient o.val=((2:ℝ≥0∞)^k)⁻¹ := by
  have hM := (survivingMixedOrbitIso T o).oneHandleCount_eq
  have hI := (survivingMixedOrbitIso T o).orientationStabilizerIndex_eq
  rw [survivingMixed_oneHandleCount _ _ _ _ _ hg] at hM
  rw [survivingMixed_orientation_index _ _ _ _ _ (by omega)] at hI
  simp [MulticurveTopology.coefficient,←hM,←hI]
end WP.Critical
