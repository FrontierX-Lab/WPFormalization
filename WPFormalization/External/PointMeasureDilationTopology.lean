import WPFormalization.Probability.PointMeasureDilation
import Mathlib.Topology.Metrizable.Basic

/-! Explicit stage-one classical topology inputs, parent source/type approved.
Kallenberg (2002), Theorem A2.3(i), printed p.564 gives the ambient locally
finite Radon measure vague space a Polish topology. Metrizability and second
countability restrict to the integer-valued subspace. The second declaration
is a generic derived continuity fact, proved mathematically by common compact
support, a cutoff mass bound and uniform convergence of dilated tests; it is
not claimed to be the literal statement of A2.3. No probability convergence,
WP geometry or random-scale conclusion is assumed here. -/
noncomputable section
namespace WP.External
open WP.Probability TopologicalSpace
open scoped NNReal

/-- Restriction of the lcscH Radon vague topology in Kallenberg A2.3(i), p.564.
Only hereditary properties are requested; no subspace completeness is asserted. -/
theorem pointMeasure_nnreal_vague_metrizable_secondCountable :
    MetrizableSpace (PointMeasure ℝ≥0) ∧ SecondCountableTopology (PointMeasure ℝ≥0) := by
  sorry

/-- Classical compact-test corollary: the actual positive measure-map action is
jointly continuous. The uniform common-support/cutoff proof is recorded in the
separate source/type audit; this statement contains no probability data. -/
theorem pointMeasure_nnreal_dilation_joint_continuous :
    Continuous (fun p : PositiveScale × PointMeasure ℝ≥0 => pointMeasureDilation p.1 p.2) := by
  sorry

end WP.External
