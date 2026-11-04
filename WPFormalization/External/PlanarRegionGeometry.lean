import WPFormalization.External.ShortComplementaryRegionGeometry

/- Generic classical interfaces, explicitly supplied; no instance and no sorry.
Generic planar annulus theorem (Viro--Ivanov--Netsvetaev--Kharlamov,
Elementary Topology, Part III, 54.Cx printed 363), plus the elementary
punctured-disk polar-coordinate consequence of Jordan--Schoenflies.
The exact parameterizations are derived interfaces, not verbatim field text.
None mentions pants, hyperbolic length, primitive curves, filling or support.
Field derivations: audit/pants-planar-regions-classical-fields.md. -/
noncomputable section
universe u v
namespace WP.External.PlanarRegionGeometry
open Set WP.External.ShortLoopStraighteningGeometry
open WP.External.ShortComplementaryRegionGeometry

structure PuncturedDiskCoordinates {f : ClosedLoop ℂ} (D : DiskBoundedBy f)
    (p : ℂ) where
  coordinates : (LoopCircle × Ici (0:ℝ)) ≃ₜ
    {z : ℂ // z ∈ Set.range D.map ∧ z ≠ p}
  boundary : ∀ z, (coordinates (z,⟨0,by simp⟩)).val = f.circleMap z
  inner_range : coordinates '' {z : LoopCircle × Ici (0:ℝ) | 0 < z.2.val} =
    {z | z.val ∈ interior (Set.range D.map)}

structure PlanarRegionClassics where
  punctured_disk : ∀ {f : ClosedLoop ℂ} (D : DiskBoundedBy f) (p : ℂ),
    p ∈ interior (Set.range D.map) → Nonempty (PuncturedDiskCoordinates D p)
  nested_annulus : ∀ {f g : ClosedLoop ℂ} (D : DiskBoundedBy f)
      (E : DiskBoundedBy g), Set.range D.map ⊆ interior (Set.range E.map) →
    ∃ A : AnnulusBetween f g,
      Set.range A.map = Set.range E.map \ interior (Set.range D.map)
end WP.External.PlanarRegionGeometry
