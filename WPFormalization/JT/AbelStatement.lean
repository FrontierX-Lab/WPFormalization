import WPFormalization.JT.BesselEnergy
import WPFormalization.Analysis.CriticalParameterCoordinates

/-! Literal statement of the Abel density and the critical edge in §15.1.
The physical identification of this integral is the cited JT model convention;
all identities and asymptotic conclusions below concern this actual integral. -/
noncomputable section
namespace WP.JT
open MeasureTheory Filter Asymptotics
open scoped Topology

/-- The Abel integral with the topological prefactor removed.  The numerator
is its entire energy-variable Bessel series, also at negative energies. -/
def abelDensity (Y E : ℝ) : ℝ :=
  (1 / (4 * Real.pi)) *
    ∫ u in (edgeEnergy Y)..E, besselI0Energy u / Real.sqrt (E-u)

/-- The complete displayed Abel-kernel identity, undeformed density, and
critical cubic edge.  No finite-genus moment or all-genus summation is asserted. -/
structure AbelDensityConclusion : Prop where
  integrable : ∀ Y E : ℝ, edgeEnergy Y ≤ E →
    IntervalIntegrable (fun u => besselI0Energy u / Real.sqrt (E-u)) volume (edgeEnergy Y) E
  kernel : ∀ Y E : ℝ, edgeEnergy Y ≤ E →
    abelDensity Y E = Real.sqrt (E-edgeEnergy Y) / (2 * Real.pi) *
      (K (Y : ℂ) ((-2 * Real.pi^2 * (E-edgeEnergy Y) : ℝ) : ℂ)).re
  undeformed : ∀ E : ℝ, 0 ≤ E →
    abelDensity 0 E = Real.sinh (2 * Real.pi * Real.sqrt E) / (4 * Real.pi^2)
  critical_b_positive : 0 < Analysis.criticalB
  critical :
    (fun q : ℝ => abelDensity y₀ (edgeEnergy y₀ + q) -
      (Real.pi * Analysis.criticalB / 3) * q ^ (3/2 : ℝ))
      =O[𝓝[>] (0 : ℝ)] (fun q : ℝ => q ^ (5/2 : ℝ))

end WP.JT
