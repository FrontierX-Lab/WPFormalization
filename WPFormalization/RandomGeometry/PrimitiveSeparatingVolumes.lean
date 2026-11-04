import WPFormalization.RandomGeometry.PrimitiveSeparatingCuts
import WPFormalization.RandomGeometry.GeneralPlanarCutVolumeBound
import WPFormalization.Critical.CutCuspLabels

/-! Physical two-component volume bounds for actual positive-genus separating
cuts. Original cusp labels and both ordered endpoints are retained. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Critical Finset
namespace OneEdgeCut
variable {n : ℕ} (D : MulticurveCutData n 1)

lemma endpoint_degree (hc : D.ConnectedWithin univ) (hQ : D.components=2) (j : Fin 2) :
    CutGraphData.degree D (D.edgeVertex (0,j))=1 := by
  have he : {e : Fin 1×Fin 2 //D.edgeVertex e=D.edgeVertex (0,j)}≃Unit :=
    Equiv.ofBijective (fun _=>()) ⟨by
      intro a b _
      apply Subtype.ext
      exact edgeVertex_injective D hc hQ (a.property.trans b.property.symm),by
      intro _
      exact ⟨⟨(0,j),rfl⟩,rfl⟩⟩
  simpa [CutGraphData.degree] using Fintype.card_congr he

lemma endpoint_cuspCount (hc : D.ConnectedWithin univ) (hQ : D.components=2) (j : Fin 2) :
    CutGraphData.cuspCount D (D.edgeVertex (0,j))=
      cutCuspHistogram (separatingRealization D hc hQ).cusps j := by
  rw [cutCuspHistogram_eq_card]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun i=>by
    change D.cuspVertex i=D.edgeVertex (0,j) ↔(endpointEquiv D hc hQ).symm (D.cuspVertex i)=j
    exact (Equiv.symm_apply_eq (endpointEquiv D hc hQ)).symm)

lemma separating_boundaryCounts (hc : D.ConnectedWithin univ) (hQ : D.components=2) :
    let k:=cutCuspHistogram (separatingRealization D hc hQ).cusps 0
    D.boundaryCount (D.edgeVertex (0,0))=k+1 ∧
      D.boundaryCount (D.edgeVertex (0,1))=n-k+1 := by
  let σ := (separatingRealization D hc hQ).cusps
  have hs := cutCuspHistogram_sum σ
  rw [Fin.sum_univ_two] at hs
  constructor
  · rw [CutGraphData.boundaryCount_eq,endpoint_degree D hc hQ,endpoint_cuspCount D hc hQ]
  · rw [CutGraphData.boundaryCount_eq,endpoint_degree D hc hQ,endpoint_cuspCount D hc hQ]
    change cutCuspHistogram σ 1+1=n-cutCuspHistogram σ 0+1
    omega

lemma separating_volume_upper {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (hc : D.ConnectedWithin univ) (hQ : D.components=2) (hg : ∀c,1≤D.genus c)
    (x : Fin 1→ℝ) (hx : ∀i,0≤x i) :
    let k:=cutCuspHistogram (separatingRealization D hc hQ).cusps 0
    D.volumeProduct G x≤Real.exp (x 0)*
      (volumeModel P (D.genus (D.edgeVertex (0,0))) (k+1)*
       volumeModel P (D.genus (D.edgeVertex (0,1))) (n-k+1)) := by
  have hb (c : Fin D.components) := generalPlanar_root_volume_upper P G
    (D.genus c) (D.boundaryCount c) (hg c)
    (CutGraphData.boundaryCount_pos D (by norm_num) hc c) (D.boundaryLengths x c)
    (multicurve_boundaryLengths_nonneg D x hx c)
  have hp : D.volumeProduct G x≤Real.exp (x 0)*∏c,volumeModel P (D.genus c) (D.boundaryCount c) := by
    calc
      _≤∏c,Real.exp ((∑j,D.boundaryLengths x c j)/2)*volumeModel P (D.genus c) (D.boundaryCount c) :=
        Finset.prod_le_prod₀ (fun _ _=>ENNReal.toReal_nonneg) (fun c _=>hb c)
      _=(∏c,Real.exp ((∑j,D.boundaryLengths x c j)/2))*∏c,volumeModel P (D.genus c) (D.boundaryCount c) := Finset.prod_mul_distrib
      _=_ := by rw [multicurve_boundary_exp_product];simp
  have he := Equiv.prod_comp (endpointEquiv D hc hQ) (fun c=>volumeModel P (D.genus c) (D.boundaryCount c))
  simp only [Fin.prod_univ_two,endpointEquiv_apply] at he
  rw [←he] at hp
  have hbc := separating_boundaryCounts D hc hQ
  rw [hbc.1,hbc.2] at hp
  exact hp

end OneEdgeCut
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    {g n : ℕ}

def primitiveSeparatingOrbitCuspCount (o : PrimitiveSeparatingOrbit T g n) : ℕ :=
  cutCuspHistogram (primitiveSeparatingOrbitCusps T o) 0

lemma primitiveSeparatingOrbit_cusp_le (o : PrimitiveSeparatingOrbit T g n) :
    primitiveSeparatingOrbitCuspCount T o≤n := by
  have hs := cutCuspHistogram_sum (primitiveSeparatingOrbitCusps T o)
  rw [Fin.sum_univ_two] at hs
  change cutCuspHistogram (primitiveSeparatingOrbitCusps T o) 0≤n
  omega

lemma primitiveSeparatingOrbit_volume_upper (o : PrimitiveSeparatingOrbit T g n)
    (x : Fin 1→ℝ) (hx : ∀i,0≤x i) :
    (T.cut o.val).volumeProduct G x≤Real.exp (x 0)*
      (volumeModel P (primitiveSeparatingOrbitGenus T o) (primitiveSeparatingOrbitCuspCount T o+1)*
       volumeModel P (g-primitiveSeparatingOrbitGenus T o) (n-primitiveSeparatingOrbitCuspCount T o+1)) := by
  have hu := OneEdgeCut.separating_volume_upper (T.cut o.val) G (T.cut_connected o.val)
    o.property.1 o.property.2 x hx
  have hg := primitiveSeparatingOrbit_genus_second T o
  change (T.cut o.val).genus ((T.cut o.val).edgeVertex (0,1))=g-primitiveSeparatingOrbitGenus T o at hg
  rw [hg] at hu
  exact hu

end WP.RandomGeometry
