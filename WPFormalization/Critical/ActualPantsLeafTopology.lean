import WPFormalization.Critical.PhysicalPantsCutLeaves
import WPFormalization.External.ShortActualCutRealizationGeometry

/- True numerical leaf incidence, transported by the SAME actual cut creator,
yields genuine pants topology and one actual geodesic boundary. -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.Critical.PantsCluster
open WP.External WP.RandomGeometry WP.External.PantsCluster
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortActualCutRealizationGeometry

lemma pantsLeaf_cusp_card {n k : ℕ} (D : MulticurveCutData n k)
    (e : Fin k) (c : Fin D.components) (h : PantsLeafData D e c) :
    Nat.card {i : Fin n // D.cuspVertex i=c}=2 := by
  classical
  simpa [MulticurveCutData.cuspSet, Nat.card_eq_fintype_card,
    Fintype.card_subtype] using h.two_cusps

lemma pantsLeaf_halfSide_card {n k : ℕ} (D : MulticurveCutData n k)
    (e : Fin k) (c : Fin D.components) (h : PantsLeafData D e c) :
    Nat.card {i : Fin k × Fin 2 // D.edgeVertex i=c}=1 := by
  classical
  have hc := pantsLeaf_cusp_card D e c h
  have hb := pantsLeaf_boundaryCount D e c h
  simp only [MulticurveCutData.boundaryCount, MulticurveCutData.Boundary,
    Fintype.card_sum] at hb
  simp only [Nat.card_eq_fintype_card] at hc ⊢
  omega

variable {P : WP.PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G}
  (A : AmbientRealization H) (T : MulticurveTopology.{u,v,w,z} G H)
  (AC : AmbientCurveCompatibility A T)
  (Cuts : ActualCutRealizationData A T AC.complete_domain)
  {g n k : ℕ} (o : T.Orbit g n k) (X : G.Moduli g n (fun _ => 0))
  (κ : Fin k → H.Primitive g n X) (ho : T.orbitMem o X κ)
  (e : Fin k) (c : Fin (T.cut o).components) (h : PantsLeafData (T.cut o) e c)

include e h

lemma actual_pants_leaf_hasPantsTopology :
    HasPantsTopology ((Cuts.cut o X κ ho).piece c).model :=
  (Cuts.twoCusp o X κ ho).topology c h.genus_zero
    (pantsLeaf_cusp_card (T.cut o) e c h) (pantsLeaf_halfSide_card (T.cut o) e c h)

lemma actual_pants_leaf_one_boundary :
    ((Cuts.cut o X κ ho).piece c).model.boundaries=1 := by
  have he := Nat.card_congr ((Cuts.cut o X κ ho).halfSideEquiv c)
  have hh := pantsLeaf_halfSide_card (T.cut o) e c h
  simpa using he.trans hh

end WP.Critical.PantsCluster
