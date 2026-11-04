import WPFormalization.Analysis.GevreyOneMatching
import Mathlib
/-! A genuinely analytic germ with real Taylor coefficients has a simultaneous
Gevrey-one inverse-power expansion of its actual real restriction. A fixed
Cauchy circle proves all orders, with no assumed coefficient identities or
asymptotic remainder. -/
noncomputable section
namespace WP.Analysis
open PowerSeries Filter Set
open scoped Topology

lemma GevreyOneAsymptotic.of_analytic_at_zero (F:ℝ→ℝ) (f:HigherOrder.Series)
    (fc:ℂ→ℂ) (hf:AnalyticAt ℂ fc 0)
    (ht:taylor fc=PowerSeries.map Complex.ofRealHom f)
    (he:∀h:ℝ,0<h → fc ((1/h:ℝ):ℂ)=(F h:ℂ)) :
    GevreyOneAsymptotic F f := by
  obtain ⟨r,hr,ha⟩ := Metric.eventually_nhds_iff.mp hf.eventually_analyticAt
  have hD : DifferentiableOn ℂ fc (Metric.closedBall 0 (r/2)) := by
    intro z hz
    have hzn : ‖z‖≤r/2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    exact (ha (by simpa only [dist_zero_right] using (show ‖z‖<r by linarith))).differentiableAt.differentiableWithinAt
  obtain ⟨M₀,hM₀⟩ := (isCompact_closedBall (0:ℂ) (r/2)).exists_bound_of_continuousOn hD.continuousOn
  let M:ℝ:=max 1 M₀
  have hM:0<M:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hR:0<r/2:=by positivity
  have hcircle:∀z∈Metric.sphere (0:ℂ) (r/2),‖fc z‖≤M := by
    intro z hz
    exact (hM₀ z (Metric.sphere_subset_closedBall hz)).trans (le_max_right _ _)
  refine ⟨2*M,1/(r/2),1,max 1 (4/r),by positivity,by positivity,by norm_num,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro K h hh hK
  have hh1:1≤h:=(le_max_left _ _).trans hh
  have hh0:0<h:=lt_of_lt_of_le zero_lt_one hh1
  have hhr:4/r≤h:=(le_max_right _ _).trans hh
  have hzr:‖((1/h:ℝ):ℂ)‖≤(r/2)/2 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh0)]
    have hmul:4≤h*r:=(div_le_iff₀ hr).mp hhr
    apply (div_le_iff₀ hh0).mpr
    nlinarith
  have hcoeff (n:ℕ):WP.coeff fc n=((PowerSeries.coeff n f:ℝ):ℂ) := by
    have hc:=congrArg (PowerSeries.coeff n) ht
    simpa only [taylor_coeff,PowerSeries.coeff_map,Complex.ofRealHom_eq_coe] using hc
  have hpoly:(∑i∈Finset.range (K+1),WP.coeff fc i*((1/h:ℝ):ℂ)^i)=
      (inversePowerTruncation f K h:ℂ) := by
    simp_rw [hcoeff]
    unfold inversePowerTruncation
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    rw [div_pow,one_pow,mul_one_div]
  have hb:=complex_taylor_remainder_bound fc (r/2) M hR hM.le hD hcircle (K+1) ((1/h:ℝ):ℂ) hzr
  rw [he h hh0,hpoly,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hb
  have hn:‖((1/h:ℝ):ℂ)‖=1/h := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh0)]
  rw [hn] at hb
  have heq:(1/h/(r/2))^(K+1)=(1/(r/2))^(K+1)/h^(K+1) := by
    rw [←div_pow]
    congr 1
    field_simp
  rw [heq] at hb
  apply hb.trans
  have hfac:(1:ℝ)≤(K+1).factorial := by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (K+1))
  have hpos:0≤2*M*(1/(r/2))^(K+1)/h^(K+1):=by positivity
  convert mul_le_mul_of_nonneg_left hfac hpos using 1 <;> ring

end WP.Analysis
