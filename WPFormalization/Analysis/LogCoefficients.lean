import WPFormalization.Analysis.Taylor

/-! Exact finite convolution identities for coefficients of a normalized local logarithm. -/
noncomputable section
namespace WP.Analysis
open Filter
open scoped Topology
lemma logarithmic_taylor_identity (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (ha : f 0 ≠ 0) :
    PowerSeries.derivative (taylor (fun z => Complex.log (f 0/f z)))*taylor f =
      -PowerSeries.derivative (taylor f) := by
  let T (z : ℂ) := Complex.log (f 0/f z)
  have hr : AnalyticAt ℂ (fun z => f 0/f z) 0 := analyticAt_const.div hf ha
  have hT : AnalyticAt ℂ T 0 := hr.clog (by simp [ha])
  have hslit : ∀ᶠ z in 𝓝 (0 : ℂ), f 0/f z ∈ Complex.slitPlane :=
    hr.continuousAt.eventually (Complex.isOpen_slitPlane.mem_nhds (by simp [ha]))
  have he : (fun z => deriv T z*f z) =ᶠ[𝓝 0] (fun z => -deriv f z) := by
    filter_upwards [hf.eventually_analyticAt,hf.continuousAt.eventually_ne ha,hslit] with z hzf hzne hz
    have hd := ((hasDerivAt_const z (f 0)).div hzf.differentiableAt.hasDerivAt hzne).clog hz
    change deriv (fun w => Complex.log (((fun _ : ℂ => f 0)/f) w)) z*f z = _
    rw [hd.deriv]
    simp only [Pi.div_apply]
    field_simp [ha,hzne]
    <;> ring
  have ht := taylor_congr he
  rw [taylor_mul hT.deriv hf,taylor_deriv] at ht
  have hneg : (fun z => -deriv f z) = fun z => (-1 : ℂ)*deriv f z := by funext z; ring
  rw [hneg,taylor_const_mul,taylor_deriv] at ht
  simpa only [map_neg,map_one,neg_one_mul,T] using ht
lemma logarithmic_coeff_identity (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (ha : f 0 ≠ 0)
    (m : ℕ) :
    (∑ i ∈ Finset.range (m+1), (i+1 : ℂ)*
      WP.coeff (fun z => Complex.log (f 0/f z)) (i+1)*WP.coeff f (m-i)) =
        -(m+1 : ℂ)*WP.coeff f (m+1) := by
  have h := congrArg (PowerSeries.coeff m) (logarithmic_taylor_identity f hf ha)
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [PowerSeries.coeff_derivative,taylor_coeff,map_neg] at h
  calc
    _ = ∑ i ∈ Finset.range (m+1),
        (WP.coeff (fun z => Complex.log (f 0/f z)) (i+1)*(i+1 : ℂ))*WP.coeff f (m-i) := by
      apply Finset.sum_congr rfl
      intro i hi
      push_cast
      ring
    _ = -WP.coeff f (m+1)*(m+1 : ℂ) := by simpa only [neg_mul] using h
    _ = _ := by ring


end WP.Analysis
