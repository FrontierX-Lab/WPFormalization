import WPFormalization.Critical.PantsClusterWholeInterior

/-! An actual two-punctured disk has exactly one actual geodesic boundary
component. The conclusion is proved from the genuine topology and genuine
finite disjoint boundary realization, never from an unchecked numeric tag. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open Set WP.External.PantsCluster WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry WP.External.ShortLoopStraighteningGeometry

lemma primitive_trace_isCompact (B : BorderedGeometry.{u,v}) (γ : B.curves.Primitive) :
    IsCompact (B.curves.trace γ) := by
  rw [←WP.Critical.ShortConfiguration.primitiveLoop_trace]
  exact isCompact_range (primitiveLoop B γ).map.continuous

lemma actual_pants_boundary_isConnected (B : BorderedGeometry.{u,v})
    (hp : HasPantsTopology B) : IsConnected (intrinsicBoundary B) := by
  obtain ⟨e,he⟩ := hp
  let q : Metric.sphere (0:ℂ) 1 → TwicePuncturedDisk := fun z => ⟨z.val,by
    have hn : ‖z.val‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using z.property
    refine ⟨hn.le,?_,?_⟩
    · intro hz
      rw [hz] at hn
      norm_num at hn
    · intro hz
      rw [hz] at hn
      norm_num at hn⟩
  have hq : Continuous q := by fun_prop
  let f : C(Metric.sphere (0:ℂ) 1,B.surface.Point) :=
    ⟨fun z => e.symm (q z),e.symm.continuous.comp hq⟩
  have hrange : Set.range f = intrinsicBoundary B := by
    ext p
    constructor
    · rintro ⟨z,rfl⟩
      apply (he _).mpr
      change ‖(e (e.symm (q z))).val‖ = 1
      rw [e.apply_symm_apply]
      simpa only [q,Metric.mem_sphere,dist_zero_right] using z.property
    · intro hp
      have hn := (he p).mp hp
      let z : Metric.sphere (0:ℂ) 1 := ⟨(e p).val,by
        simpa only [Metric.mem_sphere,dist_zero_right] using hn⟩
      refine ⟨z,?_⟩
      change e.symm (q z) = p
      apply e.injective
      rw [e.apply_symm_apply]
  have hc : IsPathConnected (Metric.sphere (0:ℂ) 1) :=
    isPathConnected_sphere (by rw [Complex.rank_real_complex];norm_num) _ (by norm_num)
  letI := isPathConnected_iff_pathConnectedSpace.mp hc
  rw [←hrange]
  exact (isPathConnected_range f.continuous).isConnected

lemma actual_pants_boundary_index_unique (B : BorderedGeometry.{u,v})
    (hp : HasPantsTopology B) (R : BoundaryRealization B)
    (i j : Fin B.boundaries) : i = j := by
  classical
  let I := intrinsicBoundary B
  letI : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp
    (actual_pants_boundary_isConnected B hp).isPreconnected
  let U : Set I := (Subtype.val : I → B.surface.Point) ⁻¹' B.curves.trace (R.curve i)
  have hclosed : IsClosed U := (primitive_trace_isCompact B (R.curve i)).isClosed.preimage
    continuous_subtype_val
  have hcomp : Uᶜ = ⋃ a : {a : Fin B.boundaries // a ≠ i},
      (Subtype.val : I → B.surface.Point) ⁻¹' B.curves.trace (R.curve a.val) := by
    ext p
    constructor
    · intro hnot
      have hpB : p.val ∈ intrinsicBoundary B := p.property
      rw [←R.cover] at hpB
      obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hpB
      have hai : a ≠ i := by
        intro he
        subst a
        exact hnot ha
      exact Set.mem_iUnion.mpr ⟨⟨a,hai⟩,ha⟩
    · intro h
      obtain ⟨a,ha⟩ := Set.mem_iUnion.mp h
      exact Set.disjoint_left.mp (R.disjoint a.val i a.property) ha
  have hclosedcomp : IsClosed Uᶜ := by
    rw [hcomp]
    exact isClosed_iUnion_of_finite (fun a =>
      (primitive_trace_isCompact B (R.curve a.val)).isClosed.preimage continuous_subtype_val)
  have hopen : IsOpen U := by simpa only [compl_compl] using hclosedcomp.isOpen_compl
  have hne : U.Nonempty := by
    obtain ⟨p,hp⟩ := primitive_trace_nonempty B (R.curve i)
    refine ⟨⟨p,?_⟩,hp⟩
    change p ∈ intrinsicBoundary B
    rw [←R.cover]
    exact Set.mem_iUnion.mpr ⟨i,hp⟩
  have hu : U = univ := (show IsClopen U from ⟨hclosed,hopen⟩).eq_univ hne
  by_contra hij
  obtain ⟨p,hpj⟩ := primitive_trace_nonempty B (R.curve j)
  have hpB : p ∈ I := by
    change p ∈ intrinsicBoundary B
    rw [←R.cover]
    exact Set.mem_iUnion.mpr ⟨j,hpj⟩
  have hpi : p ∈ B.curves.trace (R.curve i) := by
    have h : (⟨p,hpB⟩ : I) ∈ U := hu.symm ▸ Set.mem_univ _
    exact h
  exact Set.disjoint_left.mp (R.disjoint i j hij) hpi hpj

lemma actual_pants_boundaries_eq_one (B : BorderedGeometry.{u,v})
    (hp : HasPantsTopology B) (R : BoundaryRealization B) : B.boundaries = 1 := by
  have hne := (actual_pants_boundary_isConnected B hp).nonempty
  obtain ⟨p,hpB⟩ := hne
  rw [←R.cover] at hpB
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hpB
  have hbpos : 0 < B.boundaries := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  by_contra hnot
  have hb2 : 2 ≤ B.boundaries := by omega
  have he := actual_pants_boundary_index_unique B hp R (⟨0,by omega⟩ : Fin B.boundaries)
    (⟨1,by omega⟩ : Fin B.boundaries)
  have hv := congrArg Fin.val he
  norm_num at hv

end WP.Critical.PantsCluster
