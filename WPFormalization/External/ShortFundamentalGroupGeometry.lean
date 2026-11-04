import WPFormalization.External.HyperbolicSurfacePacking
import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.Rank
/- Generic classical actual fundamental-group inputs. Hatcher Prop1A.2
printed84–85, Cor1.27 proof printed51, Ex1B.2 printed87; Martelli printed21–22,
80–83 finite-type and cusp compactification. Derived consequences, not literal
single theorem quotations. No network/surface recording bound is returned.
Explicit interfaces without constructed arbitrary partial-record instances.
Full conditions and source: audit/short-supporting-construction-classical-fields.md. -/
noncomputable section
universe u v
namespace WP.External.ShortFundamentalGroupGeometry
open Set Topology WP.External.HyperbolicPacking
/- Generic finite connected one-dimensional CW theorem, not a network theorem:
Hatcher Proposition1A.2. The generators are in the actual fundamental group.
No surface, carrier, cutoff, recording or probability occurs. -/
structure FiniteGraphFundamentalGroupClassics : Prop where
  generators : ∀(X:Type u) [TopologicalSpace X] [T2Space X]
      (K:CWComplex (univ:Set X)),
    (letI:=K;CWComplex.Finite (univ:Set X))→
    (letI:=K;∀n:ℕ,2 ≤ n→IsEmpty (RelCWComplex.cell (univ:Set X) n))→
    PreconnectedSpace X→∀x:X,
    ∃s:Finset (FundamentalGroup X x),
      Subgroup.closure (s:Set (FundamentalGroup X x))=⊤ ∧
      (letI:=K;s.card ≤ Nat.card (RelCWComplex.cell (univ:Set X) 1))

/- Ordinary surface-group generator lower bound, for this same genuine actual
finite-area orientable hyperbolic surface. Derived from the standard surface
presentation/abelianization and cusp compactification, not a network bound.
No instance is claimed for arbitrary partial metadata. -/
structure SurfaceFundamentalGroupClassics (B:BorderedGeometry.{u,v}) : Prop where
  generator_lower_bound : ∀x:B.surface.Point,
    ∀s:Finset (FundamentalGroup B.surface.Point x),
      Subgroup.closure (s:Set (FundamentalGroup B.surface.Point x))=⊤→
      B.negativeEuler ≤ s.card

end WP.External.ShortFundamentalGroupGeometry
