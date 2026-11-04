import WPFormalization.Critical.PantsClusterSupportIdentification
import WPFormalization.Critical.ShortConfigurationIntrinsicSimpleLift
import WPFormalization.RandomGeometry.PantsCutStar

/-! Refining an actual pants support by a disjoint actual waist multicurve.
Actual simple-curve classification proves that no extra cut enters its open
interior. Exact frontier semantics then identify the same actual component. -/
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
open WP.External.ShortBorderedLoopGeometry WP.External.PlanarJordanGeometry
open WP.External.PlanarRegionGeometry WP.External.ShortBorderedPeripheralGeometry
open WP.Critical.ShortConfiguration WP.RandomGeometry

variable {P : WP.PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G}
  (A : AmbientRealization H) (T : MulticurveTopology.{u,v,w,z} G H)
  (AC : AmbientCurveCompatibility A T)
  {g n : ℕ} {X : G.Moduli g n (fun _ => 0)}
  {δ : H.Primitive g n X} {o0 : T.Orbit g n 1}
  {h0 : T.orbitMem o0 X (fun _ : Fin 1 => δ)}
  (R0 : CutComponentRealization A T o0 X (fun _ : Fin 1 => δ) h0)
  (c0 : Fin (T.cut o0).components) (hp0 : HasPantsTopology (R0.piece c0).model)
  (BC0 : PrimitiveBoundaryClassics (R0.piece c0).model (R0.piece c0).boundary)
  (LS0 : BorderedLoopStraighteningClassics (R0.piece c0).model (R0.piece c0).boundary)
  (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
  (PP0 : BorderedPeripheralClassics (R0.piece c0).model (R0.piece c0).boundary)

include AC hp0 BC0 LS0 J PC PP0 in
lemma actual_one_cut_pants_avoids_disjoint_simple
    (β : H.Primitive g n X) (hs : H.simple β)
    (hside : β=δ ∨ T.disjoint β δ) :
    Disjoint ((R0.piece c0).point '' intrinsicInterior (R0.piece c0).model)
      ((A.model g n X).curves.trace (A.primitiveEquiv g n X β)) := by
  classical
  by_cases hβ : β=δ
  · subst β
    apply Set.disjoint_left.mpr
    intro p hpP hpδ
    exact (cutComponent_interior_subset_cutComplement A R0 c0 hpP) 0 hpδ
  · have hdis := (AC.disjoint_iff g n X β δ hβ).mp (hside.resolve_left hβ)
    obtain ⟨d,hd,hunique⟩ := actual_cut_primitive_unique_piece R0 β (fun _=>hdis)
    by_cases hdc : d=c0
    · subst d
      obtain ⟨ρ,hρ⟩ := (R0.piece c0).lift_interior (A.primitiveEquiv g n X β) hd
      have hsimple : SimpleTrace (R0.piece c0).model ρ :=
        intrinsicPiece_simple_of_projection_eq (R0.piece c0) ρ
          (A.primitiveEquiv g n X β) hρ ((AC.simple_iff g n X β).mp hs)
      have hb := actual_pants_boundaries_eq_one (R0.piece c0).model hp0 (R0.piece c0).boundary
      let j : Fin (R0.piece c0).model.boundaries := ⟨0,by omega⟩
      have hr := (actual_pants_simple_iff_boundary (R0.piece c0).model hp0
        (R0.piece c0).boundary hb BC0 LS0 J PC PP0 ρ j).mp hsimple
      have he : A.primitiveEquiv g n X β=A.primitiveEquiv g n X δ := by
        rw [←hρ,hr,R0.boundary_eq c0 j]
      exact (hβ ((A.primitiveEquiv g n X).injective he)).elim
    · exact (cutComponent_interior_images_disjoint A R0 c0 d (Ne.symm hdc)).mono_right hd

include hp0 in
lemma actual_one_cut_pants_frontier
    (D0 : IntrinsicRegionData (A.model g n X) (R0.piece c0)) :
    frontier ((R0.piece c0).point '' intrinsicInterior (R0.piece c0).model)=
      (A.model g n X).curves.trace (A.primitiveEquiv g n X δ) := by
  have hb := actual_pants_boundaries_eq_one (R0.piece c0).model hp0 (R0.piece c0).boundary
  let j : Fin (R0.piece c0).model.boundaries := ⟨0,by omega⟩
  rw [intrinsic_single_boundary_frontier (R0.piece c0) D0 hb j,R0.boundary_eq c0 j]

include AC hp0 BC0 LS0 J PC PP0 in
lemma actual_pants_support_same_image_after_disjoint_refinement
    (D0 : IntrinsicRegionData (A.model g n X) (R0.piece c0))
    {k : ℕ} {o : T.Orbit g n k} {κ : Fin k → H.Primitive g n X}
    {hκ : T.orbitMem o X κ} (R : CutComponentRealization A T o X κ hκ)
    (e0 : Fin k) (he0 : κ e0=δ)
    (hne : ((R0.piece c0).point '' intrinsicInterior (R0.piece c0).model).Nonempty) :
    ∃! c,(R0.piece c0).point '' intrinsicInterior (R0.piece c0).model=
      (R.piece c).point '' intrinsicInterior (R.piece c).model := by
  let U := (R0.piece c0).point '' intrinsicInterior (R0.piece c0).model
  have hav (i : Fin k) : Disjoint U
      ((A.model g n X).curves.trace (A.primitiveEquiv g n X (κ i))) := by
    apply actual_one_cut_pants_avoids_disjoint_simple A T AC R0 c0 hp0 BC0 LS0 J PC PP0
      (κ i) (T.orbit_simple o X κ hκ i)
    by_cases hie : i=e0
    · exact Or.inl (hie ▸ he0)
    · right
      rw [←he0]
      exact T.orbit_disjoint o X κ hκ i e0 hie
  apply open_region_eq_actual_cut_piece R U (R0.piece c0).image_open
    (R0.piece c0).image_connected hne
  · intro p hp i hpi
    exact Set.disjoint_left.mp (hav i) hp hpi
  · intro p hp
    have hf := actual_one_cut_pants_frontier A T R0 c0 hp0 D0
    rw [hf] at hp
    exact Set.mem_iUnion.mpr ⟨e0,he0.symm ▸ hp⟩

lemma actual_pants_component_is_leaf
    {k : ℕ} {o : T.Orbit g n k} {κ : Fin k → H.Primitive g n X}
    {hκ : T.orbitMem o X κ} (R : CutComponentRealization A T o X κ hκ)
    (PT : CutPantsTypeRecognition (AC.complete_domain g n X) R)
    (hg : 1≤g) (leaf : Fin k → Fin (T.cut o).components)
    (hleaf : ∀e,PantsLeafData (T.cut o) e (leaf e)) (e0 : Fin k)
    (c : Fin (T.cut o).components) (hp : HasPantsTopology (R.piece c).model) :
    ∃e,c=leaf e := by
  have hz := (PT.recognize c hp).1
  obtain ⟨a,ha⟩ := (pantsCutVertexEquiv (T.cut o) leaf hleaf (T.cut_connected o) e0).surjective c
  cases a with
  | none =>
    have hc : c=pantsLeafRoot (T.cut o) leaf e0 := ha.symm
    have hr := pantsCut_genus_root (T.cut o) leaf hleaf g (T.cut_connected o) e0 (T.cut_euler o)
    rw [hc,hr] at hz
    omega
  | some e => exact ⟨e,ha.symm⟩

include AC hp0 BC0 LS0 J PC PP0 in
lemma actual_pants_support_refined_leaf_coverage
    (D0 : IntrinsicRegionData (A.model g n X) (R0.piece c0))
    (γ : H.Primitive g n X)
    (Q : SingleCurvePieceData (A.model g n X) (A.primitiveEquiv g n X γ))
    (D : IntrinsicRegionData (A.model g n X) Q.piece)
    (BD : IntrinsicBoundaryData (A.model g n X) Q.piece)
    (hpQ : HasPantsTopology Q.piece.model)
    (hQ : Q.piece.point '' intrinsicInterior Q.piece.model=
      (R0.piece c0).point '' intrinsicInterior (R0.piece c0).model)
    {k : ℕ} {o : T.Orbit g n k} {κ : Fin k → H.Primitive g n X}
    {hκ : T.orbitMem o X κ} (R : CutComponentRealization A T o X κ hκ)
    (AR : ∀c,IntrinsicRegionData (A.model g n X) (R.piece c))
    (BR : ∀c,IntrinsicBoundaryData (A.model g n X) (R.piece c))
    (E : CutCompletionRealization (AC.complete_domain g n X) Q.piece D BD R AR BR)
    (PT : CutPantsTypeRecognition (AC.complete_domain g n X) R)
    (hg : 1≤g) (leaf : Fin k → Fin (T.cut o).components)
    (hleaf : ∀e,PantsLeafData (T.cut o) e (leaf e))
    (e0 : Fin k) (he0 : κ e0=δ) :
    ∃e,A.primitiveEquiv g n X γ∈Set.range (R.piece (leaf e)).primitiveProjection := by
  have hne : ((R0.piece c0).point '' intrinsicInterior (R0.piece c0).model).Nonempty := by
    rw [←hQ]
    exact (primitive_trace_nonempty (A.model g n X) (A.primitiveEquiv g n X γ)).mono Q.contains
  obtain ⟨c,hc,hunique⟩ := actual_pants_support_same_image_after_disjoint_refinement
    A T AC R0 c0 hp0 BC0 LS0 J PC PP0 D0 R e0 he0 hne
  have hQc := hQ.trans hc
  obtain ⟨e⟩ := E.completion c hQc
  have hpc := (sameImageCompletion_hasPantsTopology_iff e).mp hpQ
  obtain ⟨i,hi⟩ := actual_pants_component_is_leaf A T AC R PT hg leaf hleaf e0 c hpc
  subst c
  refine ⟨i,?_⟩
  obtain ⟨β,hβ⟩ := (R.piece (leaf i)).lift_interior (A.primitiveEquiv g n X γ) (by
    rw [←hQc]
    exact Q.contains)
  exact ⟨β,hβ⟩

end WP.Critical.PantsCluster
