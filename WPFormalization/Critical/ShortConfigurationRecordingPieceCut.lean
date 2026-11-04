import WPFormalization.Critical.ShortConfigurationRecordingActualCut
import WPFormalization.Critical.ShortConfigurationRecordingRegionIdentification
import WPFormalization.External.ShortIntrinsicRegionGeometry
import WPFormalization.External.ShortIntrinsicBoundaryGeometry
/- Local recording of a genuine intrinsic open geodesic piece by its actual
ambient boundary cut. The input region/boundary companions are ordinary
explicit realization DATA, with no arbitrary partial-record instances.
Deduplication, actual orbit construction, connected-component identification,
area/Euler identification and the single-curve quantitative bounds are proved
here. No G.3 marked classification or expectation conclusion is asserted. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical.ShortConfiguration
open Set Finset WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortIntrinsicRegionGeometry WP.External.ShortIntrinsicBoundaryGeometry
open scoped Classical

lemma negativeEuler_eq_of_area_eq (B E:BorderedGeometry.{u,v})
    (he:B.surface.area univ=E.surface.area univ) : B.negativeEuler=E.negativeEuler := by
  have hr:=congrArg ENNReal.toReal he
  rw [B.gauss_bonnet,E.gauss_bonnet,ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)] at hr
  have heq:(B.negativeEuler:ℝ)=(E.negativeEuler:ℝ):=by nlinarith [Real.pi_pos]
  exact_mod_cast heq

variable {P:WP.PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G}

lemma exists_actual_intrinsic_piece_cut
    (A:AmbientRealization H) (T:MulticurveTopology.{u,v,w,z} G H)
    (C:AmbientCurveCompatibility A T) {g n:ℕ} (X:G.Moduli g n (fun _=>0))
    (Q:IntrinsicPiece (A.model g n X)) (D:IntrinsicRegionData (A.model g n X) Q)
    (hne:(Q.point '' intrinsicInterior Q.model).Nonempty)
    (BD:IntrinsicBoundaryData (A.model g n X) Q) :
    ∃k≤Q.model.boundaries,∃κ:Fin k→H.Primitive g n X,∃o:T.Orbit g n k,
      ∃hκ:T.orbitMem o X κ,
      (∑e,H.length (κ e))≤boundaryLength Q.boundary ∧
      ∀R:CutComponentRealization A T o X κ hκ,
        ∀_AR:∀c,IntrinsicRegionData (A.model g n X) (R.piece c),
        ∃c,(Q.point '' intrinsicInterior Q.model)=(R.piece c).point '' intrinsicInterior (R.piece c).model ∧
          (R.piece c).model.negativeEuler=Q.model.negativeEuler := by
  let B:=A.model g n X
  let b:Fin Q.model.boundaries→B.curves.Primitive:=fun j=>Q.primitiveProjection (Q.boundary.curve j)
  let s:Finset B.curves.Primitive:=univ.image b
  have hsimple:∀δ∈s,SimpleTrace B δ := by
    intro δ hδ
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hδ
    exact Q.boundary_simple j
  have hdisjoint:∀δ∈s,∀ε∈s,δ≠ε→Disjoint (B.curves.trace δ) (B.curves.trace ε) := by
    intro δ hδ ε hε hne
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hδ
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hε
    exact BD.disjoint i j hne
  obtain ⟨κ,o,hκ,hlen,hcover⟩:=exists_actual_cut_of_geodesics A T C X s hsimple hdisjoint
  have hbudget:(∑δ∈s,B.curves.length δ)≤boundaryLength Q.boundary := by
    calc
      _ ≤∑δ∈s,∑i∈univ.filter (fun i=>b i=δ),B.curves.length (b i) := by
        apply Finset.sum_le_sum
        intro δ hδ
        obtain ⟨j,hj,he⟩:=Finset.mem_image.mp hδ
        rw [←he]
        exact Finset.single_le_sum (fun i hi=>(B.curves.representative (b i)).period_pos.le)
          (by simp)
      _ =∑i,B.curves.length (b i) := Finset.sum_fiberwise_of_maps_to (s:=univ) (t:=s)
        (g:=b) (fun i hi=>Finset.mem_image.mpr ⟨i,hi,rfl⟩) (fun i=>B.curves.length (b i))
      _ =boundaryLength Q.boundary := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Q.length_preserved (Q.boundary.curve i)
  refine ⟨s.card,(Finset.card_image_le.trans_eq (by simp)),κ,o,hκ,hlen.le.trans hbudget,?_⟩
  intro R AR
  let U:=Q.point '' intrinsicInterior Q.model
  have hf:frontier U=⋃e,B.curves.trace (A.primitiveEquiv g n X (κ e)) := by
    rw [D.frontier_image]
    ext p
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j,hj⟩
      have hbj:b j∈s:=Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
      obtain ⟨e,he⟩:=(hcover (b j)).mp hbj
      exact ⟨e,by simpa only [he] using hj⟩
    · rintro ⟨e,he⟩
      have hmem:(A.primitiveEquiv g n X (κ e))∈s:=(hcover _).mpr ⟨e,rfl⟩
      obtain ⟨j,hj,hje⟩:=Finset.mem_image.mp hmem
      exact ⟨j,by simpa only [←hje] using he⟩
  have hu:U⊆cutComplement A κ := by
    intro p hp e he
    have hfront:p∈frontier U:=hf.symm ▸ Set.mem_iUnion.mpr ⟨e,he⟩
    exact hfront.2 (Q.image_open.interior_eq.symm ▸ hp)
  obtain ⟨c,hc,huq⟩:=open_region_eq_actual_cut_piece R U Q.image_open Q.image_connected hne hu hf.subset
  refine ⟨c,hc,?_⟩
  apply negativeEuler_eq_of_area_eq
  exact (AR c).area_image.symm.trans ((congrArg B.surface.area hc.symm).trans D.area_image)
lemma exists_actual_single_curve_cut
    (A:AmbientRealization H) (T:MulticurveTopology.{u,v,w,z} G H)
    (C:AmbientCurveCompatibility A T) {g n:ℕ} (X:G.Moduli g n (fun _=>0))
    (γ:H.Primitive g n X) (L:ℝ) (hlength:H.length γ≤L)
    (Q:SingleCurvePieceData (A.model g n X) (A.primitiveEquiv g n X γ))
    (D:IntrinsicRegionData (A.model g n X) Q.piece)
    (BD:IntrinsicBoundaryData (A.model g n X) Q.piece) :
    ∃k≤Nat.ceil (2*L/Real.pi+2),∃κ:Fin k→H.Primitive g n X,∃o:T.Orbit g n k,
      ∃hκ:T.orbitMem o X κ,(∑e,H.length (κ e))≤2*L ∧
      ∀R:CutComponentRealization A T o X κ hκ,
        ∀_AR:∀c,IntrinsicRegionData (A.model g n X) (R.piece c),
        ∃c,(A.model g n X).curves.trace (A.primitiveEquiv g n X γ)⊆
            (R.piece c).point '' intrinsicInterior (R.piece c).model ∧
          ((R.piece c).model.negativeEuler:ℝ)≤2*L/Real.pi := by
  let B:=A.model g n X
  have hγ:B.curves.length (A.primitiveEquiv g n X γ)≤L:=
    (A.length_eq g n X γ).trans_le hlength
  have hEuler:(Q.piece.model.negativeEuler:ℝ)≤2*L/Real.pi :=
    (singleCurvePiece_negativeEuler_le B _ Q).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hγ (by norm_num)) Real.pi_pos.le)
  have hne:(Q.piece.point '' intrinsicInterior Q.piece.model).Nonempty := by
    obtain ⟨p,hp⟩:=primitive_trace_nonempty B (A.primitiveEquiv g n X γ)
    exact ⟨p,Q.contains hp⟩
  obtain ⟨k,hk,κ,o,hκ,hlen,hR⟩:=exists_actual_intrinsic_piece_cut A T C X Q.piece D hne BD
  have hboundary:Q.piece.model.boundaries≤Q.piece.model.negativeEuler+2 := by
    have hh:=Q.piece.model.euler_eq
    omega
  have hkre:(k:ℝ)≤2*L/Real.pi+2 := by
    have hh:(k:ℝ)≤(Q.piece.model.negativeEuler:ℝ)+2:=by exact_mod_cast hk.trans hboundary
    linarith
  have hkceil:k≤Nat.ceil (2*L/Real.pi+2) := by
    exact_mod_cast hkre.trans (Nat.le_ceil _)
  refine ⟨k,hkceil,κ,o,hκ,?_,?_⟩
  · exact hlen.trans (Q.boundary_length_le.trans (mul_le_mul_of_nonneg_left hγ (by norm_num)))
  · intro R AR
    obtain ⟨c,hc,he⟩:=hR R AR
    refine ⟨c,?_,?_⟩
    · rw [←hc]
      exact Q.contains
    · rw [he]
      exact hEuler

end WP.Critical.ShortConfiguration
