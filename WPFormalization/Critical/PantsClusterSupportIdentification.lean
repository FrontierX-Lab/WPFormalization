import WPFormalization.Critical.PantsClusterBoundaryCard
import WPFormalization.Critical.ShortConfigurationRecordingCompletion
import WPFormalization.Critical.ShortConfigurationRecordingPieceCut
import WPFormalization.External.ShortCutPantsTypeRecognitionGeometry
import WPFormalization.RandomGeometry.PrimitiveOneEdgeClassification

/-! Actual pants support identification. The same actual intrinsic completion
supplies topology transport; actual cut incidence then recognizes the physical
pants waist. No curve-coverage or filling assertion is a classical field. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.Critical.PantsCluster
open Set Finset WP.External WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry WP.External.PantsCluster
open WP.External.ShortIntrinsicRegionGeometry WP.External.ShortIntrinsicBoundaryGeometry
open WP.External.ShortIntrinsicCompletionGeometry
open WP.External.ShortCutPantsTypeRecognitionGeometry
open WP.Critical.ShortConfiguration WP.RandomGeometry

lemma intrinsic_single_boundary_frontier {B : BorderedGeometry.{u,v}}
    (Q : IntrinsicPiece B) (D : IntrinsicRegionData B Q)
    (hb : Q.model.boundaries = 1) (j : Fin Q.model.boundaries) :
    frontier (Q.point '' intrinsicInterior Q.model) =
      B.curves.trace (Q.primitiveProjection (Q.boundary.curve j)) := by
  rw [D.frontier_image]
  ext p
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i,hi⟩
    have he : i=j := by apply Fin.ext;have hi:=i.isLt;have hj:=j.isLt;omega
    simpa only [he] using hi
  · intro hp
    exact ⟨j,hp⟩

variable {P : WP.PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G}

lemma actual_one_edge_pants_component_planar
    {A : AmbientRealization H} {T : MulticurveTopology.{u,v,w,z} G H}
    {g n : ℕ} (hg : 1 ≤ g) {o : T.Orbit g n 1}
    {X : G.Moduli g n (fun _ => 0)} {κ : Fin 1 → H.Primitive g n X}
    {hκ : T.orbitMem o X κ}
    {hcomplete : (A.model g n X).surface.domain = univ}
    (R : CutComponentRealization A T o X κ hκ)
    (PT : CutPantsTypeRecognition hcomplete R)
    (c : Fin (T.cut o).components) (hp : HasPantsTopology (R.piece c).model) :
    ∃ S : Finset (Fin n), H.planarSide (κ 0) = some S ∧ S.card = 2 := by
  classical
  obtain ⟨hg0,hc2,hh1⟩ := PT.recognize c hp
  have hcomp : (T.cut o).components=2 := by
    rcases OneEdgeCut.components_one_or_two (T.cut o) (T.cut_connected o) with h1|h2
    · have hv : ∀ a : Fin (T.cut o).components,a=c := by
        intro a
        apply Fin.ext
        have ha:=a.isLt
        have hc:=c.isLt
        omega
      have hh2 : Nat.card {e : Fin 1 × Fin 2 // (T.cut o).edgeVertex e=c}=2 := by
        rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
        simp [hv]
      omega
    · exact h2
  let S := (T.cut o).cuspSet {c}
  refine ⟨S,(T.planarSide_iff o X κ hκ hg 0 S).mpr
    (OneEdgeCut.genus_zero_planarSide (T.cut o) (T.cut_connected o) hcomp c hg0),?_⟩
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype] at hc2
  simpa only [S,MulticurveCutData.cuspSet,Finset.mem_singleton] using hc2

lemma exists_actual_pants_support_boundary_cut
    (A : AmbientRealization H) (T : MulticurveTopology.{u,v,w,z} G H)
    (AC : AmbientCurveCompatibility A T) {g n : ℕ} (hg : 1 ≤ g)
    (X : G.Moduli g n (fun _ => 0)) (γ : H.Primitive g n X)
    (Q : SingleCurvePieceData (A.model g n X) (A.primitiveEquiv g n X γ))
    (D : IntrinsicRegionData (A.model g n X) Q.piece)
    (BD : IntrinsicBoundaryData (A.model g n X) Q.piece)
    (hp : HasPantsTopology Q.piece.model) (L : ℝ) (hγ : H.length γ ≤ L) :
    ∃ δ : H.Primitive g n X, H.length δ ≤ 2*L ∧
      ∃ o : T.Orbit g n 1,∃ hκ : T.orbitMem o X (fun _ : Fin 1 => δ),
      ∀ (R : CutComponentRealization A T o X (fun _ : Fin 1 => δ) hκ)
        (AR : ∀ c,IntrinsicRegionData (A.model g n X) (R.piece c))
        (BR : ∀ c,IntrinsicBoundaryData (A.model g n X) (R.piece c)),
        CutCompletionRealization (AC.complete_domain g n X) Q.piece D BD R AR BR →
        CutPantsTypeRecognition (AC.complete_domain g n X) R →
        ∃ c,HasPantsTopology (R.piece c).model ∧
          Q.piece.point '' intrinsicInterior Q.piece.model =
            (R.piece c).point '' intrinsicInterior (R.piece c).model ∧
          A.primitiveEquiv g n X γ ∈ Set.range (R.piece c).primitiveProjection ∧
          ∃ S : Finset (Fin n),H.planarSide δ=some S ∧ S.card=2 := by
  classical
  have hb := actual_pants_boundaries_eq_one Q.piece.model hp Q.piece.boundary
  let j : Fin Q.piece.model.boundaries := ⟨0,by omega⟩
  let δ : H.Primitive g n X := (A.primitiveEquiv g n X).symm
    (Q.piece.primitiveProjection (Q.piece.boundary.curve j))
  have hδ : A.primitiveEquiv g n X δ=
      Q.piece.primitiveProjection (Q.piece.boundary.curve j) :=
    (A.primitiveEquiv g n X).apply_symm_apply _
  have hlen : H.length δ ≤ 2*L := by
    calc
      H.length δ = Q.piece.model.curves.length (Q.piece.boundary.curve j) := by
        rw [←A.length_eq g n X δ,hδ,Q.piece.length_preserved]
      _ ≤ boundaryLength Q.piece.boundary := by
        unfold boundaryLength
        exact Finset.single_le_sum (s:=Finset.univ)
          (f:=fun b=>Q.piece.model.curves.length (Q.piece.boundary.curve b))
          (fun b _=>(Q.piece.model.curves.representative (Q.piece.boundary.curve b)).period_pos.le)
          (Finset.mem_univ j)
      _ ≤ 2*L := Q.boundary_length_le.trans (by rw [A.length_eq];linarith)
  have hs : H.simple δ := (AC.simple_iff g n X δ).mpr (hδ.symm ▸ Q.piece.boundary_simple j)
  obtain ⟨o,ho,hu⟩ := T.orbit_partition X (fun _ : Fin 1=>δ)
    (fun _ _ _=>Subsingleton.elim _ _) (fun _=>hs)
    (fun a b hab=>(hab (Subsingleton.elim _ _)).elim)
  refine ⟨δ,hlen,o,ho,?_⟩
  intro R AR BR E PT
  let U := Q.piece.point '' intrinsicInterior Q.piece.model
  have hf : frontier U = (A.model g n X).curves.trace (A.primitiveEquiv g n X δ) := by
    rw [hδ]
    exact intrinsic_single_boundary_frontier Q.piece D hb j
  have hUne : U.Nonempty := (primitive_trace_nonempty (A.model g n X)
    (A.primitiveEquiv g n X γ)).mono Q.contains
  have hUcut : U ⊆ cutComplement A (fun _ : Fin 1=>δ) := by
    intro p hpU e hpe
    have hpfront : p∈frontier U := hf.symm ▸ hpe
    exact hpfront.2 (Q.piece.image_open.interior_eq.symm ▸ hpU)
  obtain ⟨c,hc,hunique⟩ := open_region_eq_actual_cut_piece R U Q.piece.image_open
    Q.piece.image_connected hUne hUcut (by
      intro p hpfront
      exact Set.mem_iUnion.mpr ⟨0,hf ▸ hpfront⟩)
  obtain ⟨e⟩ := E.completion c hc
  have hpR := (sameImageCompletion_hasPantsTopology_iff e).mp hp
  refine ⟨c,hpR,hc,?_,actual_one_edge_pants_component_planar hg R PT c hpR⟩
  obtain ⟨β,hβ⟩ := (R.piece c).lift_interior (A.primitiveEquiv g n X γ) (by
    rw [←hc]
    exact Q.contains)
  exact ⟨β,hβ⟩

end WP.Critical.PantsCluster
