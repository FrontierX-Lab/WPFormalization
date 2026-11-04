import WPFormalization.Critical.PantsClusterConnected
import WPFormalization.Critical.PantsClusterSupportBudget
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-! Actual interior connectedness and local support-image uniqueness on pants.
The statement concerns the genuine open image and its genuine frontier; it
asserts no arbitrary filling predicate or ambient short-curve classification. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open Set WP.External.PantsCluster WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.PlanarJordanGeometry WP.External.PlanarRegionGeometry
open WP.External.ShortBorderedPeripheralGeometry

lemma openPantsDisk_pathConnectedSpace : PathConnectedSpace GenericPants.openPantsDisk := by
  let e : ℂ ≃ₜ Metric.ball (0 : ℂ) 1 := Homeomorph.unitBall
  let S : Set ℂ := (fun z => (e z).val) ⁻¹' {(1/2:ℂ),-(1/2:ℂ)}
  have hinj : Function.Injective (fun z => (e z).val) :=
    Subtype.val_injective.comp e.injective
  have hcount : S.Countable :=
    (((Set.finite_singleton (-(1/2:ℂ))).insert (1/2:ℂ)).countable).preimage hinj
  have hconn : IsPathConnected Sᶜ := hcount.isPathConnected_compl_of_one_lt_rank (by
    rw [Complex.rank_real_complex]
    norm_num)
  letI : PathConnectedSpace ↥(Sᶜ) := isPathConnected_iff_pathConnectedSpace.mp hconn
  let ff : ↥(Sᶜ) → ℂ := fun z => (e z.val).val
  have hff : ∀z,ff z ∈ GenericPants.openPantsDisk := by
    intro z
    have hz : (e z.val).val ≠ (1/2:ℂ) ∧ (e z.val).val ≠ -(1/2:ℂ) := by
      simpa only [S,Set.mem_compl_iff,Set.mem_preimage,Set.mem_insert_iff,
        Set.mem_singleton_iff,not_or] using z.property
    exact ⟨by simpa only [Metric.mem_ball,dist_zero_right] using (e z.val).property,hz⟩
  have hcont : Continuous ff :=
    (continuous_subtype_val.comp e.continuous).comp continuous_subtype_val
  let f : C(↥(Sᶜ),GenericPants.openPantsDisk) :=
    ⟨fun z => ⟨ff z,hff z⟩,hcont.subtype_mk hff⟩
  have hsurj : Function.Surjective f := by
    intro z
    let w : Metric.ball (0:ℂ) 1 := ⟨z.val,by
      simpa only [Metric.mem_ball,dist_zero_right] using z.property.1⟩
    have he : (e (e.symm w)).val = z.val := congrArg Subtype.val (e.apply_symm_apply w)
    let a : ↥(Sᶜ) := ⟨e.symm w,by
      simp only [S,Set.mem_compl_iff,Set.mem_preimage,Set.mem_insert_iff,
        Set.mem_singleton_iff,not_or,he]
      exact z.property.2⟩
    refine ⟨a,?_⟩
    apply Subtype.ext
    exact he
  apply pathConnectedSpace_iff_univ.mpr
  rw [←hsurj.range_eq]
  exact isPathConnected_range f.continuous

lemma actual_pants_intrinsicInterior_preconnected (B : BorderedGeometry.{u,v})
    (hp : HasPantsTopology B) (R : BoundaryRealization B) (hb : B.boundaries = 1)
    (j : Fin B.boundaries) : IsPreconnected (intrinsicInterior B) := by
  letI := openPantsDisk_pathConnectedSpace
  obtain ⟨e,he⟩ := hp
  let C : GenericPants.Chart := ⟨B,e,he,R,hb,j⟩
  rw [←GenericPants.openPantsDiskToSurface_range C]
  exact (isPathConnected_range (GenericPants.openPantsDiskToSurface C).continuous).isConnected.isPreconnected

lemma actual_pants_intrinsicInterior_isOpen (B : BorderedGeometry.{u,v})
    (hp : HasPantsTopology B) (R : BoundaryRealization B) (hb : B.boundaries = 1)
    (j : Fin B.boundaries) : IsOpen (intrinsicInterior B) := by
  obtain ⟨e,he⟩ := hp
  let C : GenericPants.Chart := ⟨B,e,he,R,hb,j⟩
  rw [←GenericPants.openPantsDiskToSurface_range C]
  exact (GenericPants.openPantsDiskToSurface_isOpenEmbedding C).isOpen_range

lemma actual_pants_piece_image_eq_intrinsicInterior (B : BorderedGeometry.{u,v})
    (hp : HasPantsTopology B) (R : BoundaryRealization B) (hb : B.boundaries = 1)
    (BC : PrimitiveBoundaryClassics B R) (LS : BorderedLoopStraighteningClassics B R)
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics B R) (j : Fin B.boundaries)
    (E : IntrinsicPiece B)
    (hne : (E.point '' intrinsicInterior E.model).Nonempty)
    (hinside : E.point '' intrinsicInterior E.model ⊆ intrinsicInterior B)
    (hfront : frontier (E.point '' intrinsicInterior E.model) =
      ⋃i,B.curves.trace (E.primitiveProjection (E.boundary.curve i))) :
    E.point '' intrinsicInterior E.model = intrinsicInterior B := by
  let U := E.point '' intrinsicInterior E.model
  let I := intrinsicInterior B
  have hfb : frontier U ⊆ intrinsicBoundary B := by
    intro p hpfront
    rw [hfront] at hpfront
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hpfront
    rw [actual_pants_piece_boundary_projection B hp R hb BC LS J PC PP E i j] at hi
    rw [←R.cover]
    exact Set.mem_iUnion.mpr ⟨j,hi⟩
  have hIopen : IsOpen I := actual_pants_intrinsicInterior_isOpen B hp R hb j
  letI : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp
    (actual_pants_intrinsicInterior_preconnected B hp R hb j)
  have hf : frontier ((Subtype.val : I → B.surface.Point) ⁻¹' U) = ∅ := by
    rw [←hIopen.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
      continuous_subtype_val]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hpfront
    exact Set.disjoint_left.mp (intrinsic_interior_disjoint_boundary B)
      p.property (hfb hpfront)
  have hUne : ((Subtype.val : I → B.surface.Point) ⁻¹' U).Nonempty := by
    obtain ⟨p,hpU⟩ := hne
    exact ⟨⟨p,hinside hpU⟩,hpU⟩
  have hu : ((Subtype.val : I → B.surface.Point) ⁻¹' U) = univ :=
    (isClopen_iff_frontier_eq_empty.mpr hf).eq_univ hUne
  apply Set.Subset.antisymm hinside
  intro p hpI
  have h : (⟨p,hpI⟩ : I) ∈ ((Subtype.val : I → B.surface.Point) ⁻¹' U) :=
    hu.symm ▸ Set.mem_univ _
  exact h

end WP.Critical.PantsCluster
