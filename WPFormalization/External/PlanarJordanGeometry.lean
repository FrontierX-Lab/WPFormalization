import WPFormalization.External.ShortComplementaryRegionGeometry

/-! Stage-one generic classical data approved by the root source audit on
2026-11-01. Generic planar Jordan--Schoenflies extension, before any
puncture, geodesic, surface, primitive, filling or count specialization.
Primary source: C.Thomassen, The Jordan--Schoenflies theorem and the
classification of surfaces, Amer.Math.Monthly99(1992),116--130,
Theorem3.1 printed123 (proof123--125).
https://doi.org/10.1080/00029890.1992.11995820
Actual article: https://people.math.wisc.edu/~dymarz/751/thomass.pdf
The source says every homeomorphism between two planar Jordan curves
extends to a homeomorphism of the plane. The sphere has compact domain, so
a continuous injection onto its image is such an actual homeomorphism.
No pants classification, whole filling, support cutoff or cluster is a field.
-/
noncomputable section
namespace WP.External.PlanarJordanGeometry

structure PlanarJordanClassics : Prop where
  extend_circle : ∀ f : C(Metric.sphere (0 : ℂ) 1, ℂ), Function.Injective f →
    ∃ e : ℂ ≃ₜ ℂ, ∀ z : Metric.sphere (0 : ℂ) 1, e z.val = f z

end WP.External.PlanarJordanGeometry
