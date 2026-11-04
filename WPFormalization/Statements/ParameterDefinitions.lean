import WPFormalization.Statements.Kernels

/-! The original stationary-parameter definitions, separated from their proofs. -/
noncomputable section
namespace WP
open Filter Asymptotics
open scoped Topology

/- Blueprint label(s): eq:SP1
Paper v3: 1.2 [PDF 4]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:SP1"]
def stationaryIntegral (Y T : ℝ) : ℝ := ∫ v in Y..T, a v / Real.sqrt (T-v)
/- Eq.1.2. First root above y₀; its upper bound is proved separately.
This also defines the analytic extension at Y=0 from negative Y. -/
/- Blueprint label(s): eq:SP1
Paper v3: 1.2 [PDF 4]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:SP1"]
def T (Y : ℝ) : ℝ := if Y = y₀ then y₀ else sInf {t : ℝ | y₀ < t ∧ stationaryIntegral Y t = 0}
/- Blueprint label(s): eq:SP2
Paper v3: 1.3 [PDF 4]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:SP2"]
def Delta (Y : ℝ) : ℝ := T Y - Y
/- Eq.1.3, action and density. -/
/- Blueprint label(s): eq:SP2
Paper v3: 1.3 [PDF 4]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:SP2"]
def action (Y : ℝ) : ℝ := ∫ v in Y..T Y, a v * Real.sqrt (T Y-v)
/- Blueprint label(s): eq:SP2
Paper v3: 1.3 [PDF 4]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:SP2"]
def density (Y : ℝ) : ℝ := 2*XR Y*Real.sqrt (Delta Y)/action Y
def densityY (l : ℝ) : ℝ := sInf {Y : ℝ | Y ∈ Set.Ico 0 y₀ ∧ density Y = l}
def Psi (x : ℝ) : ℝ := density (inverseY x) / 2
def euler (f : ℝ → ℝ) (x : ℝ) : ℝ := x * deriv f x
def J (Y : ℝ) : ℝ := ∫ s : ℝ in (0)..1, XR (T Y - Delta Y*s^2)
def beta (Y : ℝ) : ℝ := XR Y / J Y

/- Blueprint label(s): eq:SP3
Paper v3: 1.7 [PDF 7]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:SP3"]
def profileB (l : ℝ) : ℝ := Real.pi^2 / (4*Delta (densityY l))
/- Blueprint label(s): eq:SP3
Paper v3: 1.7 [PDF 7]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:SP3"]
def profileC (l : ℝ) : ℝ := if l = 0 then 4*Real.pi^2 else l*Real.pi^2 / XR (densityY l)


end WP
