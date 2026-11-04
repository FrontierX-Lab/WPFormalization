import WPFormalization.Analysis.HKernelUniform
import WPFormalization.Analysis.ParameterTaylor
import WPFormalization.Analysis.KernelJets
import WPFormalization.Analysis.HarmonicPositivity
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology
lemma barH_one_im_zero (Y:ℝ) : (barH Y 1).im=0 := by
  simpa only [Complex.ofReal_one] using entire_ofReal_im_zero_of_realCoefficients
    (barH Y) (barH_differentiable Y) (barH_realCoefficients Y) 1
lemma barH_one_re_pos (Y:ℝ)(hY:Y∈Icc 0 y₀) : 0<(barH Y 1).re := by
  by_cases he : Y=y₀
  · simp [barH,he]
    norm_num
  · have hYi : Y∈Ico 0 y₀ := ⟨hY.1,lt_of_le_of_ne hY.2 he⟩
    have hh := H_re_pos_to_r Y hYi (r Y) ⟨(r_pos Y hYi).le,le_rfl⟩
    simp only [barH,if_neg he,mul_one,div_eq_mul_inv,←Complex.ofReal_inv,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_pos hh (inv_pos.mpr (a_pos Y hYi))
lemma harmonicPGF_eq_real_mul_inv (Y:ℝ) : harmonicPGF Y = fun w=>((barH Y 1).re:ℂ)*(barH Y w)⁻¹ := by
  funext w
  unfold harmonicPGF
  have he : barH Y 1 = ((barH Y 1).re:ℂ) := by apply Complex.ext; rfl; simpa using barH_one_im_zero Y
  simp only [div_eq_mul_inv]
  exact congrArg (fun c=>c*(barH Y w)⁻¹) he
lemma harmonicMass_pos (Y:ℝ)(hY:Y∈Icc 0 y₀)(m:ℕ) : 0<harmonicMass Y m := by
  unfold harmonicMass
  rw [harmonicPGF_eq_real_mul_inv,realCoeff_const_mul]
  apply mul_pos (barH_one_re_pos Y hY)
  simpa only [harmonicCoeff,pow_one] using harmonicCoeff_pos Y 1 m zero_lt_one hY
lemma harmonicPGF_realCoefficients (Y:ℝ)(hY:Y∈Icc 0 y₀) : RealCoefficients (harmonicPGF Y) := by
  rw [harmonicPGF_eq_real_mul_inv]
  exact realCoefficients_const_mul _ (realCoefficients_inv ((barH_differentiable Y).analyticAt 0)
    (by rw [barH_zero Y hY]; exact one_ne_zero) (barH_realCoefficients Y))
lemma harmonicPGF_diffOn {η:ℝ}(hη:0<η)
    (hzero:∀Y∈Icc (0:ℝ) y₀,∀w:ℂ,‖w‖≤1+η→barH Y w≠0)
    (Y:ℝ)(hY:Y∈Icc 0 y₀) : DifferentiableOn ℂ (harmonicPGF Y) (Metric.closedBall 0 (1+η)) := by
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  exact (differentiableAt_const (c := barH Y 1)).div ((barH_differentiable Y) w) (hzero Y hY w (by simpa only [Metric.mem_closedBall,dist_zero_right] using hw))
lemma harmonicPGF_joint_closed {η:ℝ}(hη:0<η)
    (hzero:∀Y∈Icc (0:ℝ) y₀,∀w:ℂ,‖w‖≤1+η→barH Y w≠0) :
    Continuous (fun p:Icc (0:ℝ) y₀ × Metric.closedBall (0:ℂ) (1+η) => harmonicPGF (p.1:ℝ) p.2) := by
  have hn : Continuous (fun p:Icc (0:ℝ) y₀ × Metric.closedBall (0:ℂ) (1+η) => barH (p.1:ℝ) 1) :=
    barH_joint_continuous.comp (continuous_fst.prodMk continuous_const)
  have hd : Continuous (fun p:Icc (0:ℝ) y₀ × Metric.closedBall (0:ℂ) (1+η) => barH (p.1:ℝ) p.2) :=
    barH_joint_continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  apply hn.div hd
  intro p
  exact hzero p.1 p.1.property p.2 (by simpa only [Metric.mem_closedBall,dist_zero_right] using p.2.property)
lemma harmonicMass_continuous (m:ℕ) : Continuous (fun Y:Icc (0:ℝ) y₀=>harmonicMass (Y:ℝ) m) := by
  obtain ⟨η,hη,hzero⟩ := barH_uniform_zero_free
  have hc := parameter_coeff_continuous (fun Y:Icc (0:ℝ) y₀ => harmonicPGF (Y:ℝ)) (1+η) (by linarith)
    (fun Y=>harmonicPGF_diffOn hη hzero Y Y.property) (harmonicPGF_joint_closed hη hzero) m
  exact Complex.continuous_re.comp hc
lemma hasSum_coeff_on_ball (f:ℂ→ℂ)(R:ℝ)(hf:DifferentiableOn ℂ f (Metric.ball 0 R))
    (z:ℂ)(hz:‖z‖<R) : HasSum (fun n=>WP.coeff f n*z^n) (f z) := by
  convert Complex.hasSum_taylorSeries_on_ball hf (by simpa only [Metric.mem_ball,dist_zero_right] using hz) using 1
  ext n
  simp only [WP.coeff,sub_zero,smul_eq_mul]
  ring
lemma harmonicMass_hasSum_weighted {η:ℝ}(hη:0<η)
    (hzero:∀Y∈Icc (0:ℝ) y₀,∀w:ℂ,‖w‖≤1+η→barH Y w≠0)
    (Y:ℝ)(hY:Y∈Icc 0 y₀)(x:ℝ)(hx:|x|<1+η) :
    HasSum (fun m=>harmonicMass Y m*x^m) (harmonicPGF Y x).re := by
  have hs := hasSum_coeff_on_ball (harmonicPGF Y) (1+η)
    ((harmonicPGF_diffOn hη hzero Y hY).mono Metric.ball_subset_closedBall)
    (x:ℂ) (by simpa only [Complex.norm_real,Real.norm_eq_abs] using hx)
  convert Complex.hasSum_re hs using 1
  ext m
  simp only [harmonicMass,realCoeff,Complex.mul_re,←Complex.ofReal_pow,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero]
lemma harmonicMass_hasSum (Y:ℝ)(hY:Y∈Icc 0 y₀) : HasSum (harmonicMass Y) 1 := by
  obtain ⟨η,hη,hzero⟩ := barH_uniform_zero_free
  have hs := harmonicMass_hasSum_weighted hη hzero Y hY 1 (by simpa using hη)
  simpa only [one_pow,mul_one,Complex.ofReal_one,harmonicPGF,div_self (barH_zero_free_unit Y hY 1 (by norm_num)),Complex.one_re] using hs
end WP.Analysis
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology
lemma barK_one_zero (Y:ℝ)(hY:Y∈Icc 0 y₀) : barK Y 1=0 := by
  by_cases he:Y=y₀
  · simp [barK,he]
  · simp only [barK,if_neg he,mul_one,K_r_zero Y ⟨hY.1,lt_of_le_of_ne hY.2 he⟩,zero_div]
lemma harmonicPGF_deriv_one (Y:ℝ)(hY:Y∈Icc 0 y₀) : deriv (harmonicPGF Y) 1 = 3/2 := by
  have hH : barH Y 1 ≠0 := barH_zero_free_unit Y hY 1 (by norm_num)
  have hd := normalized_kernel_identity Y hY 1
  rw [barK_one_zero Y hY] at hd
  have hdH : deriv (barH Y) 1 = -(3/2:ℂ)*barH Y 1 := by linear_combination -(3/2:ℂ)*hd
  have he : HasDerivAt (harmonicPGF Y) ((0*barH Y 1-barH Y 1*deriv (barH Y) 1)/(barH Y 1)^2) 1 :=
    (hasDerivAt_const 1 (barH Y 1)).div ((barH_differentiable Y) 1).hasDerivAt hH
  rw [he.deriv,hdH]
  field_simp
  <;> ring
lemma harmonic_coeff_euler (f:ℂ→ℂ)(hf:AnalyticAt ℂ f 0)(n:ℕ) :
    WP.coeff (fun z=>z*deriv f z) n = (n:ℂ)*WP.coeff f n := by
  have he := congrArg (fun p:PowerSeries ℂ=>PowerSeries.coeff n p) (taylor_euler hf)
  cases n with
  | zero => simpa [taylor_coeff] using he
  | succ n => simpa [taylor_coeff,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_derivative,mul_comm] using he
lemma harmonicMass_mean (Y:ℝ)(hY:Y∈Icc 0 y₀) : HasSum (fun m:ℕ=>(m:ℝ)*harmonicMass Y m) (3/2) := by
  obtain ⟨η,hη,hzero⟩ := barH_uniform_zero_free
  have hf := (harmonicPGF_diffOn hη hzero Y hY).mono Metric.ball_subset_closedBall
  have hA (z:ℂ)(hz:z∈Metric.ball 0 (1+η)) : AnalyticAt ℂ (harmonicPGF Y) z :=
    hf.analyticAt (Metric.isOpen_ball.mem_nhds hz)
  have hz0 : (0:ℂ)∈Metric.ball 0 (1+η) := by simp only [Metric.mem_ball,dist_self]; linarith
  have hD : DifferentiableOn ℂ (fun z=>z*deriv (harmonicPGF Y) z) (Metric.ball 0 (1+η)) := by
    intro z hz
    exact (differentiableAt_id.mul (hA z hz).deriv.differentiableAt).differentiableWithinAt
  have hs := hasSum_coeff_on_ball _ (1+η) hD 1 (by norm_num; linarith)
  rw [one_mul,harmonicPGF_deriv_one Y hY] at hs
  convert Complex.hasSum_re hs using 1
  · ext n
    rw [one_pow,mul_one,harmonic_coeff_euler _ (hA 0 hz0) n]
    simp only [harmonicMass,realCoeff,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
  · norm_num
end WP.Analysis
