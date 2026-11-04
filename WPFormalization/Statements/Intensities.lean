import WPFormalization.Statements.Parameter

/-! Deterministic length scales and genuine Borel intensity measures.
No random hyperbolic surface or Poisson point process is replaced by a free function. -/
noncomputable section
namespace WP
open MeasureTheory

/- Eq.14.1. Natural n(n-1) counts ordered distinct cusp pairs. -/
/- Blueprint label(s): eq:PS1
Paper v3: 14.1 [PDF 57]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:PS1"]
def pantsScale (g n : ℕ) : ℝ := (n : ℝ)*(n-1)/(8*g*profileC ((n : ℝ)/g))
/- Eq.14.17. -/
/- Blueprint label(s): eq:tight-scale
Paper v3: 14.17 [PDF 63]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:tight-scale"]
def tightScale (l : ℝ) : ℝ := Real.sqrt (2*r (densityY l))/Real.pi

/- Blueprint label(s): eq:tight-scale
Paper v3: 14.17 [PDF 63]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:tight-scale"]
def tightIntensityDensity (t : ℝ) : ℝ := (Real.cosh t-1)/t
/- Measure on [0,∞) represented by restricting the ambient real Borel measure. -/
/- Blueprint label(s): eq:tight-scale, eq:cluster-intensities
Paper v3: 14.17 [PDF 63]; 14.19 [PDF 64]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:tight-scale", blueprint "eq:cluster-intensities"]
def tightIntensity : Measure ℝ :=
  (volume.restrict (Set.Ici 0)).withDensity (fun t => ENNReal.ofReal (tightIntensityDensity t))
/- Blueprint label(s): eq:cluster-intensities
Paper v3: 14.19 [PDF 64]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:cluster-intensities"]
def criticalIntensityDensity (c s : ℝ) : ℝ := c^2/(8*Real.pi^2)*Real.sinh (s/2)
/- Blueprint label(s): eq:cluster-intensities
Paper v3: 14.19 [PDF 64]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:cluster-intensities"]
def criticalIntensity (c : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ici 0)).withDensity (fun s => ENNReal.ofReal (criticalIntensityDensity c s))
end WP
