import WPFormalization.External.ShortSurfaceEulerGeometry
noncomputable section
namespace WP.Critical.ShortConfiguration
open WP.External.HyperbolicPacking WP.External.ShortSurfaceEulerGeometry
universe u v

/- A local arithmetic consequence of the generic cellular Euler identity.
G.3 must still construct the actual filled-piece CW model with its true arcs
as one-cells; no existence or network budget is assumed here. -/
lemma negativeEuler_le_one_cells (B : BorderedGeometry.{u,v})
    (E : SurfaceCellularEulerClassics B) (F : FiniteSurfaceCWModel B) :
    B.negativeEuler≤Nat.card (F.cells 1) := by
  have h := E.euler F
  omega

end WP.Critical.ShortConfiguration
