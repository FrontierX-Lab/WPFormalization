import WPFormalization.Analysis.CriticalStationaryBranch
import WPFormalization.Analysis.ParameterAnalytic

/-! The exact critical stationary derivative and compact-moment jets.
These derivatives are taken on the proved local analytic germ. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology ContDiff
lemma stationaryWeighted_diagonal (q : ℝ → ℝ) (hq : Continuous q)
    (g : ℂ → ℂ) (hg : Continuous g) (Y : ℝ) :
    stationaryWeighted q g Y Y = (∫ s : ℝ in (0)..1,q s)*(g (Y:ℂ)).re := by
  rw [stationaryWeighted_real_integral q hq g hg]
  simp only [sub_self,zero_mul,sub_zero,intervalIntegral.integral_mul_const]
lemma integral_one_sub_sq : (∫ s : ℝ in (0)..1,1-s^2) = (2/3:ℝ) := by
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 1)
    ((by fun_prop : Continuous (fun s : ℝ => s^2)).intervalIntegrable 0 1)]
  norm_num
lemma criticalStationaryBranch_deriv_value : deriv criticalStationaryBranch y₀ = -1/2 := by
  have hb : HasDerivAt criticalStationaryBranch (deriv criticalStationaryBranch y₀) y₀ :=
    criticalStationaryBranch_analyticAt.differentiableAt.hasDerivAt
  have hd := stationaryWeighted_hasDerivAt_comp (fun _ => 1) continuous_const
    (deriv X) X_differentiable.deriv criticalStationaryBranch y₀ (deriv criticalStationaryBranch y₀) hb
  have heq : (fun Y => stationaryWeighted (fun _ => 1) (deriv X) Y (criticalStationaryBranch Y)) =ᶠ[𝓝 y₀] fun _ => 0 := by
    filter_upwards [criticalStationaryBranch_root] with Y hY
    rw [stationaryWeighted_one_derivX]
    exact hY
  have hz := (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const y₀ (0:ℝ))
  simp only [one_mul,criticalStationaryBranch_value] at hz
  have hg : Continuous (deriv (deriv X)) := X_differentiable.deriv.deriv.continuous
  have ha := stationaryWeighted_add (fun s : ℝ => s^2)
    (fun s => deriv criticalStationaryBranch y₀*(1-s^2)) (by fun_prop) (by fun_prop)
    (deriv (deriv X)) hg y₀ y₀
  have hb' := stationaryWeighted_smul (deriv criticalStationaryBranch y₀) (fun s : ℝ => 1-s^2)
    (by fun_prop) (deriv (deriv X)) hg y₀ y₀
  rw [ha,hb',stationaryWeighted_diagonal _ (by fun_prop) _ hg,
    stationaryWeighted_diagonal _ (by fun_prop) _ hg,integral_one_sub_sq] at hz
  norm_num at hz
  have hn : (deriv (deriv X) (y₀:ℂ)).re < 0 := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      second_X_neg_before y₀ (by linarith [y₀_lt_three_halves])
  nlinarith
lemma stationaryWeighted_analytic_implicit (q : ℝ → ℝ) (hq : Continuous q)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) (b : ℝ → ℝ) (Y : ℝ)
    (hInv : (fderiv ℂ stationaryQProd ((Y:ℂ),(b Y:ℂ)) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible)
    (hb : ContinuousAt b Y)
    (hEq : ∀ᶠ x : ℝ in 𝓝 Y,stationaryQProd ((x:ℂ),(b x:ℂ)) = stationaryQProd ((Y:ℂ),(b Y:ℂ))) :
    AnalyticAt ℝ (fun x => stationaryWeighted q g x (b x)) Y := by
  let H (p : ComplexPair) : ℂ := ∫ s : ℝ in (0)..1,(q s:ℂ)*g (stationaryQLinear s p)
  have hc : ContDiff ℂ 1 H := by
    simpa only [H,zero_add] using
      affineIntegral_prod_contDiff_one (fun s => (q s:ℂ)) (fun _ => 0) stationaryQLinear
        (Complex.continuous_ofReal.comp hq) continuous_const stationaryQLinear_continuous g hg
  exact analyticAt_real_implicit_comp stationaryQProd H b Y stationaryQ_contDiff_one.contDiffAt
    hc.contDiffAt hInv hb hEq
lemma criticalMoment_analyticAt :
    AnalyticAt ℝ (fun Y => stationaryWeighted (fun s => s^2) (deriv X) Y (criticalStationaryBranch Y)) y₀ := by
  have hV := criticalStationaryBranch_value
  apply stationaryWeighted_analytic_implicit (fun s => s^2) (by fun_prop) (deriv X) X_differentiable.deriv
    criticalStationaryBranch y₀ (by simpa only [hV] using stationaryQ_critical_partial_isInvertible)
    criticalStationaryBranch_contDiffAt.continuousAt
  have hbase := stationaryQ_zero_of_real_zero y₀ y₀ stationaryQRealProd_critical_zero
  filter_upwards [criticalStationaryBranch_root] with Y hY
  rw [hV,hbase,stationaryQ_zero_of_real_zero Y _ hY]
lemma criticalMoment_value :
    stationaryWeighted (fun s => s^2) (deriv X) y₀ (criticalStationaryBranch y₀) = 0 := by
  rw [criticalStationaryBranch_value,stationaryWeighted_diagonal _ (by fun_prop) _ X_differentiable.deriv.continuous,
    derivX_y₀_zero,Complex.zero_re,mul_zero]
lemma criticalMoment_hasDerivAt :
    HasDerivAt (fun Y => stationaryWeighted (fun s => s^2) (deriv X) Y (criticalStationaryBranch Y))
      ((2/15:ℝ)*(deriv (deriv X) (y₀:ℂ)).re) y₀ := by
  have hd := stationaryWeighted_hasDerivAt_comp (fun s => s^2) (by fun_prop)
    (deriv X) X_differentiable.deriv criticalStationaryBranch y₀ (-1/2)
    (by rw [← criticalStationaryBranch_deriv_value];exact criticalStationaryBranch_analyticAt.differentiableAt.hasDerivAt)
  have hg : Continuous (deriv (deriv X)) := X_differentiable.deriv.deriv.continuous
  rw [criticalStationaryBranch_value,stationaryWeighted_diagonal _ (by fun_prop) _ hg] at hd
  have he : (∫ s : ℝ in (0)..1,s^2*(s^2+(-1/2:ℝ)*(1-s^2))) = (2/15:ℝ) := by
    have heq : (fun s : ℝ => s^2*(s^2+(-1/2:ℝ)*(1-s^2))) =
        (fun s => (3/2:ℝ)*s^4-(1/2:ℝ)*s^2) := by funext s;ring
    rw [heq,intervalIntegral.integral_sub ((by fun_prop : Continuous (fun s : ℝ => (3/2:ℝ)*s^4)).intervalIntegrable 0 1)
      ((by fun_prop : Continuous (fun s : ℝ => (1/2:ℝ)*s^2)).intervalIntegrable 0 1),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
    norm_num
  rwa [he] at hd

end WP.Analysis
