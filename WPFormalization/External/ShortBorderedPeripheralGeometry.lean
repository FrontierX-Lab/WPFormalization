import WPFormalization.External.ShortBorderedLoopGeometry
import WPFormalization.External.ShortComplementaryRegionGeometry

noncomputable section
universe u v
/- Generic derived extension of the ALREADY APPROVED complete-surface
PeripheralAxialClassics.cusp_no_axial to a closed convex bordered quotient.
Actual geodesic BoundaryRealization is mandatory. Sources and derivation are recorded in audit/pants-planar-regions-classical-fields.md.
The cyclic parabolic
subgroup/no-hyperbolic-axis proof lifts into the actual convex covering domain;
no domain=univ conclusion and no filling statement are assumed. -/
namespace WP.External.ShortBorderedPeripheralGeometry
open WP.External.HyperbolicPacking WP.External.ShortLoopStraighteningGeometry
open WP.External.ShortFillingGeometry
open WP.External.ShortComplementaryRegionGeometry
structure BorderedPeripheralClassics (B : BorderedGeometry.{u,v})
    (R : BoundaryRealization B) where
  cusp_no_axial : ∀ (f : ClosedLoop B.surface.Point) (E : CuspEndBoundedBy f)
    (γ : B.curves.Primitive), ¬ B.curves.trace γ ⊆ Set.range E.map
  annulus_axial_class : ∀ (f g : ClosedLoop B.surface.Point) (E : AnnulusBetween f g)
    (γ : B.curves.Primitive), f.Simple → f.PositiveHomotopyLength →
    B.curves.trace γ ⊆ Set.range E.map →
      (primitiveLoop B γ).UnorientedFreelyHomotopic f
end WP.External.ShortBorderedPeripheralGeometry
