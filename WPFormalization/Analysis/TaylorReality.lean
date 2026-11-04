import WPFormalization.Analysis.Taylor

/-! Reality and real Taylor jets under local analytic operations. -/
noncomputable section
namespace WP.Analysis
open PowerSeries

lemma realCoefficients_of_taylor_map {f : ℂ → ℂ} {p : PowerSeries ℝ}
    (he : taylor f = PowerSeries.map Complex.ofRealHom p) : RealCoefficients f := by
  intro n
  have hn := congrArg (fun q : PowerSeries ℂ => (PowerSeries.coeff n q).im) he
  simpa only [taylor_coeff,PowerSeries.coeff_map,Complex.ofRealHom_eq_coe,
    Complex.ofReal_im] using hn

lemma realCoefficients_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hrf : RealCoefficients f) (hrg : RealCoefficients g) :
    RealCoefficients (fun z => f z+g z) := by
  apply realCoefficients_of_taylor_map (p := realTaylor f+realTaylor g)
  rw [taylor_add hf hg,taylor_real_lift hrf,taylor_real_lift hrg,map_add]

lemma realCoefficients_sub {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hrf : RealCoefficients f) (hrg : RealCoefficients g) :
    RealCoefficients (fun z => f z-g z) := by
  apply realCoefficients_of_taylor_map (p := realTaylor f-realTaylor g)
  rw [taylor_sub hf hg,taylor_real_lift hrf,taylor_real_lift hrg,map_sub]

lemma realCoefficients_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hrf : RealCoefficients f) (hrg : RealCoefficients g) :
    RealCoefficients (fun z => f z*g z) := by
  apply realCoefficients_of_taylor_map (p := realTaylor f*realTaylor g)
  rw [taylor_mul hf hg,taylor_real_lift hrf,taylor_real_lift hrg,map_mul]

lemma realCoefficients_const_mul {f : ℂ → ℂ} (c : ℝ) (hrf : RealCoefficients f) :
    RealCoefficients (fun z => (c : ℂ)*f z) := by
  apply realCoefficients_of_taylor_map (p := C c*realTaylor f)
  rw [taylor_const_mul,taylor_real_lift hrf,map_mul]
  congr 1
  ext n
  simp [PowerSeries.coeff_C]

lemma realCoefficients_div {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hg0 : g 0 ≠ 0) (hrf : RealCoefficients f) (hrg : RealCoefficients g) :
    RealCoefficients (fun z => f z/g z) := by
  simpa only [div_eq_mul_inv] using realCoefficients_mul (f := f) (g := fun z => (g z)⁻¹)
    hf (hg.inv hg0) hrf (realCoefficients_inv hg hg0 hrg)

lemma realCoefficients_deriv {f : ℂ → ℂ} (hr : RealCoefficients f) :
    RealCoefficients (deriv f) := by
  intro n
  have hn := congrArg (fun q : PowerSeries ℂ => (PowerSeries.coeff n q).im)
    (taylor_deriv (f := f))
  simpa [PowerSeries.coeff_derivative, taylor_coeff, Complex.mul_im, hr (n+1)] using hn

lemma realTaylor_deriv (f : ℂ → ℂ) :
    realTaylor (deriv f) = PowerSeries.derivative (realTaylor f) := by
  ext n
  have hn := congrArg (fun q : PowerSeries ℂ => (PowerSeries.coeff n q).re)
    (taylor_deriv (f := f))
  simpa [PowerSeries.coeff_derivative, taylor_coeff, realTaylor_coeff, WP.realCoeff] using hn

end WP.Analysis
