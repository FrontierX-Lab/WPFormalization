import WPFormalization.External.ShortComplementaryRegionGeometry
/- Generic axial/parabolic consequences for actual complete finite-area surfaces.
These two fields are derived combinations, not verbatim single-source theorems:
Martelli, Ch4 pp80--81 (actual cusp ends); Farb--Margalit, printed p22 and
Props1.3--1.4 pp25--28 (peripheral/axial and primitive simple classes);
Hatcher, Prop1.5 p28 and Thm1.7 p29 (basepoint and circle fundamental group).
The complete domain and actual proper/embedded region hypotheses are retained.
No instance, network, filling, recording, budget or expectation is asserted.
Field-by-field derivation: audit/short-peripheral-axial-classical-fields.md. -/
noncomputable section
set_option maxHeartbeats 0
universe u v
namespace WP.External.ShortPeripheralAxialGeometry
open Set WP.External.HyperbolicPacking WP.External.ShortLoopStraighteningGeometry
open WP.External.ShortComplementaryRegionGeometry

/- Only elementary axial/parabolic homotopy facts in ACTUAL standard regions.
The disk analogue is proved locally from Mathlib convex contraction, so it is
not a field here. Neither field mentions a network, an RN, a tuple, a filled
piece, cusp allocation, a graph budget, a record or an expectation. -/
structure PeripheralAxialClassics (B:BorderedGeometry.{u,v})
    (hcomplete:B.surface.domain=univ) where
  cusp_no_axial : ∀(f:ClosedLoop B.surface.Point) (E:CuspEndBoundedBy f)
    (γ:B.curves.Primitive),¬B.curves.trace γ⊆range E.map
  annulus_axial_class : ∀(f g:ClosedLoop B.surface.Point) (E:AnnulusBetween f g)
    (γ:B.curves.Primitive),f.Simple→f.PositiveHomotopyLength→
      B.curves.trace γ⊆range E.map→(primitiveLoop B γ).UnorientedFreelyHomotopic f

end WP.External.ShortPeripheralAxialGeometry
