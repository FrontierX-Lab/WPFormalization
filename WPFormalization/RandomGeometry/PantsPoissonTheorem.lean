import WPFormalization.RandomGeometry.PantsPoissonConclusion
import WPFormalization.RandomGeometry.PrimitiveSystoleJointLimit

/-! The complete conditional formalization of Theorem14.1. All new geometry,
combinatorics, moment, tail and limiting estimates are proved locally. The
explicit classical first-point interfaces have generic probability scope;
no paper-specific moment, convergence, minimum or tie conclusion is assumed. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)
    (D : MarkedPoissonFirstPointData) (FC : MarkedFirstPointConvergence.{v})

include C MI in
lemma pants_poisson_part_one (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop) : PantsPoissonPartOne H n := by
  refine ⟨pantsLengthPointProcess_actual_eventually H n hn,pants_poisson_process G H T C MI n hn,?_,?_⟩
  · intro d lo hi ho hd
    exact pants_closed_interval_counts_poisson G H T C MI d n hn lo hi ho hd
  · intro t ht
    exact pants_minimum_length_limit G H T C MI n hn t ht

include C MI D FC in
lemma planar_primitive_poisson_density_conclusion (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (l : ℝ≥0∞) (hl : Tendsto (fun g : ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) :
    PlanarPrimitivePoissonDensityConclusion H n l := by
  refine ⟨generalPlanarMarkedLengthPointProcess_actual_eventually H n hn,
    generalPlanar_marked_poisson_process H T C MI n hn l hl,
    generalPlanar_length_poisson_process H T C MI n hn l hl,
    primitiveLengthPointProcess_actual_eventually H n hn,
    primitive_poisson_process H T C MI n hn l hl,?_,
    primitive_all_systolic_planar_probability_tendsto_one H T C MI n hn,
    generalPlanarSystolicJointMeasure_rectangle P l,generalPlanarSystolicJointMeasure_top P l,
    generalPlanarSystolicJointMeasure_probability H T C MI D n hn l hl,?_⟩
  · intro t ht
    exact primitive_minimum_length_limit H T C MI n hn l hl t ht
  · intro k hm hs
    exact (primitive_systole_joint_type_limit H T C MI D FC n hn l hl k hm hs).2

include C MI D FC in
/- The whole original Theorem14.1, including every clause of (i), (ii), (iii)
and the complete joint distribution and mark marginal (14.5). The systole is
the infimum over actual unoriented primitive classes, including nonsimple ones;
empty catalogs have value infinity. We retain the classical semantic use that
a shortest closed geodesic is primitive, without inventing a missing separate
nonprimitive-cover representation or asserting that such a bridge was proved.
Concrete geometry instances and the generic classical interfaces are explicit
phase-one dependencies. -/
@[blueprint "thm:pants-poisson"]
theorem pants_poisson_theorem (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop) : PantsPoissonConclusion H n := by
  exact ⟨pants_poisson_part_one H T C MI n hn,
    fun l hl=>planar_primitive_poisson_density_conclusion H T C MI D FC n hn l hl⟩

end WP.RandomGeometry
