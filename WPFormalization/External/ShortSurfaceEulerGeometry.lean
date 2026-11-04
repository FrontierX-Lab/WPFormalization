import WPFormalization.External.ShortFillingGeometry
import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Topology.Homotopy.Equiv
/- Hatcher Theorem2.44 printed pp146--147 and the already reviewed Martelli
finite-area cusp-core/Gauss--Bonnet theory. The Euler field is their generic
combination, not a G.3 cell-model existence or complexity bound. No instance
is asserted. Source conditions: audit/short-surface-euler-classical-fields.md. -/
noncomputable section
set_option maxHeartbeats 0
universe u v
namespace WP.External.ShortSurfaceEulerGeometry
open Set WP.External.HyperbolicPacking

/- A genuine finite 2-dimensional CW model, explicitly homotopy equivalent to
THE actual hyperbolic quotient. This definition asserts no model exists for a
particular G.3 construction. -/
structure FiniteSurfaceCWModel (B : BorderedGeometry.{u,v}) where
  Carrier : Type u
  [topology : TopologicalSpace Carrier]
  [cw : Topology.CWComplex (univ : Set Carrier)]
  [finiteType : Topology.CWComplex.FiniteType (univ : Set Carrier)]
  dimension_two : ∀n:ℕ,3≤n→IsEmpty (Topology.RelCWComplex.cell (univ : Set Carrier) n)
  equivalent : ContinuousMap.HomotopyEquiv Carrier B.surface.Point

attribute [instance] FiniteSurfaceCWModel.topology FiniteSurfaceCWModel.cw
  FiniteSurfaceCWModel.finiteType

def FiniteSurfaceCWModel.cells {B : BorderedGeometry.{u,v}}
    (F : FiniteSurfaceCWModel B) (n : ℕ) : Type u :=
  Topology.RelCWComplex.cell (univ : Set F.Carrier) n

instance {B : BorderedGeometry.{u,v}} (F : FiniteSurfaceCWModel B) (n : ℕ) :
    Finite (F.cells n) := Topology.CWComplex.FiniteType.finite_cell n

/- Hatcher Theorem2.44 (finite CW Euler characteristic and homotopy
invariance) plus surface Gauss--Bonnet/compact cusp-core topology from the
already-reviewed G.2 classical source. No G.3 particular cell structure or
network complexity bound is supplied. -/
structure SurfaceCellularEulerClassics (B : BorderedGeometry.{u,v}) : Prop where
  euler : ∀F:FiniteSurfaceCWModel B,
    (Nat.card (F.cells 0) : ℤ)-Nat.card (F.cells 1)+Nat.card (F.cells 2)=
      -(B.negativeEuler:ℤ)

end WP.External.ShortSurfaceEulerGeometry
