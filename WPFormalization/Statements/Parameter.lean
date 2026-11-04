import WPFormalization.Analysis.ParameterIdentities
import WPFormalization.Analysis.StationaryAnalytic
import WPFormalization.Analysis.ParameterRegular
import WPFormalization.Analysis.CriticalParameterAsymptotics
import WPFormalization.Analysis.CuspWeight
import WPFormalization.Analysis.BoundaryEndpoints
import WPFormalization.Analysis.TrigSaddle

/-! Stationary-parameter statements with the original full specifications. -/
noncomputable section
namespace WP
open Filter Asymptotics
open scoped Topology

/- Eq.1.2's defining property and identification with the first kernel root. -/
/- Blueprint label(s): eq:SP1
Paper v3: 1.2 [PDF 4]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:SP1"]
theorem stationary_root (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    T Y ∈ Set.Ioc y₀ (Real.pi^2/4) ∧ stationaryIntegral Y (T Y) = 0 ∧
    (∀ t ∈ Set.Ioc y₀ (Real.pi^2/4), stationaryIntegral Y t = 0 → t = T Y) ∧
    r Y = 2*Delta Y := by
  exact stationary_root_proof Y hY

/- Lemma 3.1(i)--(ii); the endpoint and asymptotic clauses continue below. -/
/- Blueprint label(s): lem:parameter
Paper v3: 3.1 [PDF 18]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:parameter"]
theorem parameter_regular :
    (∀ Y ∈ Set.Ico 0 y₀,
      AnalyticAt ℝ T Y ∧ -1 ≤ deriv T Y ∧ deriv T Y < 0 ∧
      0 < iteratedDeriv 2 T Y ∧ 0 < action Y ∧
      J Y = XR Y + action Y / Real.sqrt (Delta Y) ∧
      beta Y = density Y / (2+density Y) ∧ 0 < deriv beta Y ∧ AnalyticAt ℝ density Y) ∧
    StrictMonoOn density (Set.Ico 0 y₀) ∧
    Set.BijOn density (Set.Ico 0 y₀) (Set.Ici 0) ∧
    T 0 = Real.pi^2/4 ∧ action 0 = Real.pi/4 ∧ J 0 = 1/2 ∧
    Tendsto T (𝓝[<] y₀) (𝓝 y₀) ∧
    (fun Y => density Y - 4*Y) =O[𝓝[>] (0 : ℝ)] (fun Y => Y^2) := by
  exact Analysis.parameter_regular_proof

/- Lemma 3.1(iii): all stated leading constants and the two-sided scale comparison. -/
/- Blueprint label(s): lem:parameter
Paper v3: 3.1 [PDF 18]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:parameter"]
theorem parameter_critical :
    let b := -(iteratedDeriv 2 X y₀).re
    0 < b ∧ b = xCritical/y₀ ∧
    (fun Y => Delta Y - 3/2*(y₀-Y)) =O[𝓝[<] y₀] (fun Y => (y₀-Y)^2) ∧
    (fun Y => action Y / (8*b/45 * Real.rpow (Delta Y) (5/2 : ℝ)) - 1)
      =O[𝓝[<] y₀] Delta ∧
    Tendsto (fun Y => density Y / (45*xCritical/(4*b) * (Delta Y)⁻¹^2))
      (𝓝[<] y₀) (𝓝 1) ∧
    Tendsto (fun l => profileB l /
      (Real.pi^2/(3*Real.sqrt 5*(2*Real.sqrt y₀))*Real.sqrt l)) atTop (𝓝 1) ∧
    Tendsto (fun l => profileC l / (Real.pi^2/xCritical*l)) atTop (𝓝 1) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ Y in 𝓝[<] y₀,
      c*Real.sqrt (1-beta Y) ≤ Delta Y ∧ Delta Y ≤ C*Real.sqrt (1-beta Y)) := by
  exact Analysis.parameter_critical_proof

/- Lemma 3.1(iv), including all Euler derivatives and both bounded ratio limits. -/
/- Blueprint label(s): lem:parameter
Paper v3: 3.1 [PDF 18]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:parameter"]
theorem parameter_cusp_weight :
    (∀ x ∈ Set.Ioo 0 xCritical, AnalyticAt ℝ Psi x) ∧
    StrictMonoOn Psi (Set.Ioo 0 xCritical) ∧
    (∀ j ∈ Finset.range 3,
      (fun x => (euler^[j]) Psi x - 2*x) =O[𝓝[>] (0 : ℝ)] (fun x => x^2)) ∧
    (fun x => Psi x / (5/(4*(1-x/xCritical))) - 1)
      =O[𝓝[<] xCritical] (fun x => Real.sqrt (1-x/xCritical)) ∧
    (fun x => euler Psi x / (5/(4*(1-x/xCritical)^2)) - 1)
      =O[𝓝[<] xCritical] (fun x => Real.sqrt (1-x/xCritical)) ∧
    (euler (euler Psi)) =O[𝓝[<] xCritical] (fun x => (1-x/xCritical)⁻¹^3) ∧
    Tendsto (fun x => Psi x^2 / euler Psi x) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun x => Psi x^2 / euler Psi x) (𝓝[<] xCritical) (𝓝 (5/4)) ∧
    (∃ C : ℝ, ∀ x ∈ Set.Ioo 0 xCritical, |Psi x^2 / euler Psi x| ≤ C) := by
  exact Analysis.parameter_cusp_weight_proof

/- The removable entire function X(v)/v, with value 1 at zero. -/
/- Blueprint label(s): eq:intro-varpi
Paper v3: 1.6 [PDF 5]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:intro-varpi"]
def Xdiv (v : ℝ) : ℝ := if v = 0 then 1 else XR v / v
/- Eq.1.6, positive square-root choice. -/
/- Blueprint label(s): eq:intro-varpi
Paper v3: 1.6 [PDF 5]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:intro-varpi"]
def varpi (Y : ℝ) : ℝ := Real.sqrt
  (action Y / Real.rpow (Delta Y) (3/2 : ℝ) /
    (∫ s : ℝ in (0)..1, (1-s^2)*Xdiv (T Y - Delta Y*s^2)))

/- Eq.9.23 including the removable boundary-length values. -/
/- Blueprint label(s): eq:boundary-profile
Paper v3: 9.23 [PDF 7]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:boundary-profile"]
def boundaryFactor (Y L : ℝ) : ℝ :=
  ∫ s : ℝ in (0)..1, (I₀ (L/Real.pi*Real.sqrt (T Y-Delta Y*s^2))).re

/- Blueprint label(s): eq:boundary-profile
Paper v3: 9.23 [PDF 7]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:boundary-profile"]
theorem boundary_factor_endpoints (L : ℝ) :
    boundaryFactor 0 L = (if L = 0 then 1 else Real.sinh (L/2)/(L/2)) ∧
    boundaryFactor y₀ L = (I₀ (Real.sqrt y₀*L/Real.pi)).re := by
  simpa only [boundaryFactor] using Analysis.boundary_endpoints_integral L

/- Exact-density trigonometric saddle, Eq.13.1. -/
/- Blueprint label(s): eq:C1
Paper v3: 13.1 [PDF 52]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:C1"]
def trigDensity (t : ℝ) : ℝ := t^2*Real.sin t / (Real.sin t-t*Real.cos t)
/- Blueprint label(s): eq:C1
Paper v3: 13.1 [PDF 52]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:C1"]
def trigSaddle (g k : ℕ) : ℝ := sInf {t : ℝ | t ∈ Set.Ioo 0 Real.pi ∧
  trigDensity t = (2*(k : ℝ)+1)/(2*(g : ℝ)-1)}
/- Blueprint label(s): eq:C1
Paper v3: 13.1 [PDF 52]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:C1"]
theorem trig_saddle_spec (g k : ℕ) (hg : 1 ≤ g) (hk : k < 3*g-2) :
    trigSaddle g k ∈ Set.Ioo 0 Real.pi ∧
    trigDensity (trigSaddle g k) = (2*(k : ℝ)+1)/(2*(g : ℝ)-1) ∧
    (∀ t ∈ Set.Ioo 0 Real.pi, trigDensity t = (2*(k : ℝ)+1)/(2*(g : ℝ)-1) →
      t = trigSaddle g k) := by
  simpa only [trigSaddle,trigDensity,Analysis.densityTrig,Analysis.trigDen] using
    Analysis.trig_saddle_spec_proof g k hg hk
/- Convergent coordinate expansions specified at the end of Lemma 3.1(iv). -/
/- Blueprint label(s): lem:parameter
Paper v3: 3.1 [PDF 18]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:parameter"]
theorem parameter_analytic_expansions :
    AnalyticAt ℝ Psi 0 ∧ AnalyticAt ℝ (euler Psi) 0 ∧ AnalyticAt ℝ (euler (euler Psi)) 0 ∧
    ∃ δ : ℝ, 0 < δ ∧ ∃ f₀ f₁ f₂ : ℝ → ℝ,
      AnalyticAt ℝ f₀ 0 ∧ AnalyticAt ℝ f₁ 0 ∧ AnalyticAt ℝ f₂ 0 ∧
      f₀ 0 = 5/4 ∧ f₁ 0 = 5/4 ∧ ∀ t ∈ Set.Ioo 0 δ,
        Psi (xCritical*(1-t^2))*t^2 = f₀ t ∧
        euler Psi (xCritical*(1-t^2))*t^4 = f₁ t ∧
        euler (euler Psi) (xCritical*(1-t^2))*t^6 = f₂ t := by
  exact Analysis.parameter_analytic_expansions_proof

end WP
