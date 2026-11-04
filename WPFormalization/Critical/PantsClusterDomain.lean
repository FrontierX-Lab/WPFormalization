import WPFormalization.Critical.PantsClusterTransport

/-! Intrinsic interiors and boundaries refer to the actual convex lift
domain. Their partition is proved from quotient fibers and deck invariance,
and agrees with the canonical pants topological chart. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry Set

lemma deck_image_domain (S : QuotientSurface.{u}) (δ : S.Γ) :
    δ.val '' S.domain = S.domain := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z,hz,rfl⟩
    exact S.invariant δ z hz
  · intro z hz
    refine ⟨δ.val.symm z,S.invariant δ⁻¹ z hz,?_⟩
    exact δ.val.apply_symm_apply z

lemma deck_image_interior_domain (S : QuotientSurface.{u}) (δ : S.Γ) :
    δ.val '' interior S.domain = interior S.domain := by
  calc
    δ.val '' interior S.domain = δ.val.toHomeomorph '' interior S.domain := rfl
    _ = interior (δ.val.toHomeomorph '' S.domain) :=
      δ.val.toHomeomorph.image_interior S.domain
    _ = interior S.domain := congrArg interior (deck_image_domain S δ)

lemma intrinsic_interior_disjoint_boundary (B : BorderedGeometry.{u,v}) :
    Disjoint (intrinsicInterior B) (intrinsicBoundary B) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨z,hz,hzp⟩ ⟨q,hq,hqp⟩
  obtain ⟨δ,hδ⟩ := (B.surface.fibers z (interior_subset hz) q
    (B.surface.domain_closed.closure_subset (frontier_subset_closure hq))).mp
      (hzp.trans hqp.symm)
  have hqi : q ∈ interior B.surface.domain := by
    rw [←deck_image_interior_domain B.surface δ]
    exact ⟨z,hz,hδ⟩
  exact Set.disjoint_left.mp disjoint_interior_frontier hqi hq

lemma intrinsic_interior_union_boundary (B : BorderedGeometry.{u,v}) :
    intrinsicInterior B ∪ intrinsicBoundary B = univ := by
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨z,hz,rfl⟩ := B.surface.surjective_on_domain p
  have hh : z ∈ interior B.surface.domain ∪ frontier B.surface.domain := by
    rw [←closure_eq_interior_union_frontier,B.surface.domain_closed.closure_eq]
    exact hz
  rcases hh with hi|hb
  · exact Or.inl ⟨z,hi,rfl⟩
  · exact Or.inr ⟨z,hb,rfl⟩

lemma intrinsic_interior_eq_compl_boundary (B : BorderedGeometry.{u,v}) :
    intrinsicInterior B = (intrinsicBoundary B)ᶜ := by
  ext p
  constructor
  · intro hp hb
    exact Set.disjoint_left.mp (intrinsic_interior_disjoint_boundary B) hp hb
  · intro hp
    have hh : p ∈ intrinsicInterior B ∪ intrinsicBoundary B := by
      rw [intrinsic_interior_union_boundary]
      trivial
    exact hh.resolve_right hp

lemma canonical_pants_interior_iff (F : Family.{u,v}) (s : Waist)
    (p : (F.model s).surface.Point) :
    p ∈ intrinsicInterior (F.model s) ↔ ‖((F.topology s) p).val‖ < 1 := by
  rw [intrinsic_interior_eq_compl_boundary,Set.mem_compl_iff,F.topological_boundary]
  have hle := ((F.topology s p).property).1
  constructor
  · intro h
    exact lt_of_le_of_ne hle h
  · exact ne_of_lt

end WP.Critical.PantsCluster
