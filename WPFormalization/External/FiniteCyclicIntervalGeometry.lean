import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Homeomorph.Quotient

noncomputable section
open scoped Classical

namespace WP.External.FiniteCyclicIntervalGeometry

/-- Arithmetic successor for a polygon with `m` directed edges. -/
def next (m : ℕ) (hm : 0 < m) (j : Fin m) : Fin m :=
  ⟨(j.val+1)%m,Nat.mod_lt _ hm⟩

/-- Identify the right endpoint of each segment with the left endpoint of the next.
The quotient closes the last segment onto the first, including the one-segment case. -/
def endpointRelation (m : ℕ) (hm : 0 < m)
    (p q : Fin m × unitInterval) : Prop :=
  p.2=1 ∧ q=(next m hm p.1,0)

abbrev Polygon (m : ℕ) (hm : 0 < m) := Quot (endpointRelation m hm)

/-- Classical finite cyclic subdivision of the circle.

This exact segment formula is an elementary derived corollary of finite
adjunction-space gluing, as described in Hatcher, *Algebraic Topology*,
Chapter 0, printed pp. 5 and 13. It is not asserted to be a named theorem
with this precise formula in that source. The verification sends `[j,s]`
to `[(j+s)/m]` in `ℝ/ℤ`; it is a continuous bijection by endpoint arithmetic,
from a compact finite quotient to a Hausdorff circle. Its inverse is the
homeomorphism specified here. In particular, the one-segment case is included.
The complete proof derivation and source are maintained in the accompanying
audit notes.

This has no graph, surface, network, regular-neighborhood, length, filling,
recording, or paper-specific field.  The explicit segment formula is needed
by downstream proofs of variation, which are deliberately not fields here. -/
structure Classics where
  circle : ∀ (m : ℕ) (hm : 0 < m),
    ∃ h : AddCircle (1:ℝ) ≃ₜ Polygon m hm,
      ∀ (j : Fin m) (s : unitInterval),
        h (((j.val:ℝ)+(s:ℝ))/(m:ℝ) : ℝ) = Quot.mk _ (j,s)

end WP.External.FiniteCyclicIntervalGeometry
