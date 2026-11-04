import WPFormalization.Analysis.GevreyOneLog
import WPFormalization.HigherOrder.Endpoint
noncomputable section
namespace WP.Analysis
open PowerSeries Filter
open scoped Topology
lemma finiteExp_finiteLog_unit (f : WP.HigherOrder.Series) (hf : PowerSeries.constantCoeff f=1) :
    WP.HigherOrder.finiteExp (WP.HigherOrder.finiteLog f)=f := by
  ext n
  let P : ℂ → ℂ := truncatedSeriesPolynomial f n
  have hPa : AnalyticAt ℂ P 0 := truncatedSeriesPolynomial_analytic f n 0
  have hP0 : P 0=1 := by
    have ht := truncatedSeriesPolynomial_coeff f n 0
    simpa only [WP.coeff,iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,div_one,
      ite_eq_left (Nat.zero_le n),PowerSeries.coeff_zero_eq_constantCoeff,hf,Complex.ofReal_one] using ht
  have hplane : P 0 ∈ Complex.slitPlane := by rw [hP0];simp
  have hLa : AnalyticAt ℂ (fun z => Complex.log (P z)) 0 := (analyticAt_clog hplane).comp hPa
  have hL0 : Complex.log (P 0)=0 := by rw [hP0,Complex.log_one]
  have he := taylor_exp_coeff_of_real_jets (WP.HigherOrder.finiteLog f) (fun z => Complex.log (P z))
    hLa hL0 n (fun i hi => truncatedSeriesPolynomial_log_coeff f hf n i hi) n le_rfl
  have heq : (fun z => Complex.exp (Complex.log (P z))) =ᶠ[𝓝 0] P := by
    have hpne : P 0 ≠ 0 := by rw [hP0];norm_num
    filter_upwards [hPa.continuousAt.eventually_ne hpne] with z hz
    exact Complex.exp_log hz
  have hc := coeff_congr_of_eventuallyEq _ _ heq n
  rw [he,truncatedSeriesPolynomial_coeff f n n,ite_eq_left le_rfl] at hc
  exact Complex.ofReal_injective hc
end WP.Analysis
namespace WP.HigherOrder
open PowerSeries
lemma markedLogSeries_endpoint_all (P : PsiTheory) (p : ℕ) :
    markedLogSeries P p y₀=finiteLog (endpointSeries p) := by
  ext n
  by_cases hn : n=0
  · subst n
    simp [markedLogSeries,logarithmicMarkedCoefficient]
  · simp only [markedLogSeries,PowerSeries.coeff_mk,logarithmicMarkedCoefficient_endpoint P p n hn,endpointLogCoefficient]
lemma markedCoefficient_endpoint_all (P : PsiTheory) (p n : ℕ) :
    markedCoefficient P p n y₀=PowerSeries.coeff n (endpointSeries p) := by
  rw [markedCoefficient,markedLogSeries_endpoint_all,Analysis.finiteExp_finiteLog_unit _ (endpointSeries_constant p)]
end WP.HigherOrder
