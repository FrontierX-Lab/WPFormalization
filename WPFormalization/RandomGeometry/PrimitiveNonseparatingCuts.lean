import WPFormalization.RandomGeometry.PrimitiveOneEdgeClassification
import WPFormalization.RandomGeometry.GeneralPlanarCutVolumeBound

/-! Uniqueness and actual boundary-volume control of the one nonseparating
one-curve orbit. Its cut has genus g-1 and n+2 physical boundaries. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External Finset
namespace OneEdgeCut
variable {n : ℕ} (D : MulticurveCutData n 1)

lemma vertex_eq (hQ : D.components=1) (a b : Fin D.components) : a=b := by
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  omega

lemma sum_one_component {M : Type*} [AddCommMonoid M] (hQ : D.components=1)
    (c : Fin D.components) (f : Fin D.components→M) : (∑v,f v)=f c := by
  have hu : (univ : Finset (Fin D.components))={c} := by
    ext v
    simp [vertex_eq D hQ v c]
  rw [hu,sum_singleton]

lemma prod_one_component {M : Type*} [CommMonoid M] (hQ : D.components=1)
    (c : Fin D.components) (f : Fin D.components→M) : (∏v,f v)=f c := by
  have hu : (univ : Finset (Fin D.components))={c} := by
    ext v
    simp [vertex_eq D hQ v c]
  rw [hu,prod_singleton]

lemma one_component_genus {g : ℕ} (hQ : D.components=1)
    (he : (∑c,D.genus c)+1+1=g+D.components) (c : Fin D.components) :
    D.genus c=g-1 := by
  rw [sum_one_component D hQ c] at he
  omega

lemma one_component_boundaryCount (hQ : D.components=1) (c : Fin D.components) :
    D.boundaryCount c=n+2 := by
  have hb := D.sum_boundaryCount
  rw [sum_one_component D hQ c] at hb
  omega

lemma one_component_isomorphism {g : ℕ} {E : MulticurveCutData n 1}
    (hD : D.components=1) (hE : E.components=1)
    (heD : (∑c,D.genus c)+1+1=g+D.components)
    (heE : (∑c,E.genus c)+1+1=g+E.components) :
    Nonempty (D.Isomorphism E) := by
  let e : Fin D.components≃Fin E.components := finCongr (hD.trans hE.symm)
  refine ⟨{vertexEquiv:=e,flip:=fun _=>false,genus_eq:=?_,cusp_eq:=?_,edge_eq:=?_}⟩
  · intro c
    rw [one_component_genus E hE heE,one_component_genus D hD heD]
  · intro i
    exact vertex_eq E hE _ _
  · intro a j
    exact vertex_eq E hE _ _

lemma nonseparating_volume_upper {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    {g : ℕ} (hg : 2≤g) (hQ : D.components=1)
    (he : (∑c,D.genus c)+1+1=g+D.components)
    (x : Fin 1→ℝ) (hx : ∀i,0≤x i) :
    D.volumeProduct G x≤Real.exp (x 0)*volumeModel P (g-1) (n+2) := by
  let c : Fin D.components := ⟨0,by omega⟩
  have hgc := one_component_genus D hQ he c
  have hbc := one_component_boundaryCount D hQ c
  have hV := generalPlanar_root_volume_upper P G (g-1) (D.boundaryCount c) (by omega)
    (by omega) (D.boundaryLengths x c) (multicurve_boundaryLengths_nonneg D x hx c)
  have hs : Real.exp ((∑i,D.boundaryLengths x c i)/2)=Real.exp (x 0) := by
    have hh := multicurve_boundary_exp_product D x
    rw [prod_one_component D hQ c] at hh
    simpa [Fin.sum_univ_one] using hh
  unfold MulticurveCutData.volumeProduct
  rw [prod_one_component D hQ c,hgc]
  rw [hs] at hV
  exact hV.trans_eq (by rw [hbc])

end OneEdgeCut
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)

abbrev PrimitiveNonseparatingOrbit (g n : ℕ) :=
  {o : T.Orbit g n 1 // (T.cut o).components=1}
instance (g n : ℕ) : Fintype (PrimitiveNonseparatingOrbit T g n) :=
  inferInstanceAs (Fintype (Subtype _))

lemma primitiveNonseparatingOrbit_subsingleton (g n : ℕ) :
    Subsingleton (PrimitiveNonseparatingOrbit T g n) := by
  constructor
  intro o p
  apply Subtype.ext
  exact T.cut_classifies o.val p.val (OneEdgeCut.one_component_isomorphism (T.cut o.val)
    o.property p.property (T.cut_euler o.val) (T.cut_euler p.val))

lemma primitiveNonseparatingOrbit_card_le_one (g n : ℕ) :
    Fintype.card (PrimitiveNonseparatingOrbit T g n)≤1 := by
  exact Fintype.card_le_one_iff_subsingleton.mpr (primitiveNonseparatingOrbit_subsingleton T g n)

end WP.RandomGeometry
