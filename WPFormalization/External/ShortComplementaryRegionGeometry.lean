import WPFormalization.External.ShortLoopStraighteningGeometry
import Mathlib.Analysis.Complex.Basic
/- Generic derived combination of Farb--Margalit p22/Prop1.3 and
Marden--Richards--Rodin (1966) pp337--339, together with the already reviewed
finite-area hyperbolic cusp geometry. These exact data fields are not a
verbatim separately numbered theorem. No concrete classical instance is
asserted. See audit/short-complementary-region-classical-fields.md. -/
noncomputable section
set_option maxHeartbeats 0
universe u v
namespace WP.External.ShortComplementaryRegionGeometry
open Set WP.External.HyperbolicPacking WP.External.ShortLoopStraighteningGeometry

/- Actual standard disk; no genus/cusp metadata is used to name its shape. -/
def ClosedDisk := Metric.closedBall (0:ℂ) 1

structure DiskBoundedBy {X : Type u} [MetricSpace X] (f : ClosedLoop X) where
  map : C(ClosedDisk,X)
  embedding : Topology.IsEmbedding map
  circle : LoopCircle ≃ₜ Metric.sphere (0:ℂ) 1
  boundary : ∀z, map ⟨(circle z).val,le_of_eq (circle z).property⟩=f.circleMap z
  inner_open : IsOpen (map '' {z:ClosedDisk | dist z.val 0<1})
  frontier_eq : frontier (Set.range map)=f.trace

/- A proper actual cusp-end region, not a chosen cusp label/function. The
closed embedding prevents any missing interior cusp or other surface point. -/
structure CuspEndBoundedBy {X : Type u} [MetricSpace X] (f : ClosedLoop X) where
  map : C(LoopCircle × Ici (0:ℝ),X)
  closedEmbedding : Topology.IsClosedEmbedding map
  boundary : ∀z,map (z,⟨0,by simp⟩)=f.circleMap z
  inner_open : IsOpen (map '' {p:LoopCircle × Ici (0:ℝ) | 0<p.2.val})
  frontier_eq : frontier (Set.range map)=f.trace

/- Derived generic trichotomy for SIMPLE loops in an actual complete oriented
finite-area hyperbolic quotient. It returns only actual disk/end geometry;
no network, tuple, filling, retained annulus, cut, record or count occurs. -/
structure SimpleComplementClassics (B : BorderedGeometry.{u,v})
    (hcomplete : B.surface.domain=univ) where
  trichotomy : ∀f:ClosedLoop B.surface.Point,f.Simple →
    f.PositiveHomotopyLength ∨ Nonempty (DiskBoundedBy f) ∨ Nonempty (CuspEndBoundedBy f)

end WP.External.ShortComplementaryRegionGeometry
