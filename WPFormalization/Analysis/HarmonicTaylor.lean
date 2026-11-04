import WPFormalization.Analysis.HarmonicLaw
import WPFormalization.Analysis.HarmonicFourier
import WPFormalization.Analysis.QuadraticRemainder
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
noncomputable def centeredHarmonic (Y:ℝ)(u:ℂ) : ℂ :=
  Complex.exp (-(3/2:ℂ)*u*Complex.I)*harmonicPGF Y (Complex.exp (u*Complex.I))
lemma centeredHarmonic_uniform_analytic : ∃R M:ℝ,0<R ∧ 0<M ∧ ∀Y∈Icc (0:ℝ) y₀,
    DifferentiableOn ℂ (centeredHarmonic Y) (Metric.closedBall 0 R) ∧
    ∀u:ℂ,‖u‖≤R → ‖centeredHarmonic Y u‖≤M := by
  obtain ⟨η,hη,hzero⟩ := barH_uniform_zero_free
  let R : ℝ := Real.log (1+η)/2
  have hR : 0<R := half_pos (Real.log_pos (by linarith))
  have hR1 : 0<1+η := by linarith
  have hlog : 0<Real.log (1+η) := Real.log_pos (by linarith)
  have heMem (u:ℂ)(hu:‖u‖≤R) : Complex.exp (u*Complex.I)∈Metric.closedBall 0 (1+η) := by
    rw [Metric.mem_closedBall,dist_zero_right,Complex.norm_exp]
    have hb : (u*Complex.I).re≤Real.log (1+η) := by
      simp only [Complex.mul_re,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_sub]
      have hh := (neg_le_abs u.im).trans (Complex.abs_im_le_norm u)
      dsimp [R] at hu
      linarith
    exact (Real.exp_le_exp.mpr hb).trans_eq (Real.exp_log hR1)
  have hc : Continuous (fun p:Icc (0:ℝ) y₀ × Metric.closedBall (0:ℂ) (1+η) => ‖harmonicPGF (p.1:ℝ) p.2‖) :=
    (harmonicPGF_joint_closed hη hzero).norm
  obtain ⟨B,hB⟩ := isCompact_univ.bddAbove_image hc.continuousOn
  let M := Real.exp ((3/2)*R)*max B 1
  have hM : 0<M := mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  refine ⟨R,M,hR,hM,?_⟩
  intro Y hY
  constructor
  · intro u hu
    have he := heMem u (by simpa only [Metric.mem_closedBall,dist_zero_right] using hu)
    have hP : DifferentiableAt ℂ (harmonicPGF Y) (Complex.exp (u*Complex.I)) :=
      (differentiableAt_const (c:=barH Y 1)).div ((barH_differentiable Y) _) (hzero Y hY _ (by simpa only [Metric.mem_closedBall,dist_zero_right] using he))
    have hcE : Differentiable ℂ (fun v:ℂ=>Complex.exp (-(3/2:ℂ)*v*Complex.I)) := by fun_prop
    have hcP : Differentiable ℂ (fun v:ℂ=>Complex.exp (v*Complex.I)) := by fun_prop
    exact ((hcE u).mul (hP.comp u (hcP u))).differentiableWithinAt
  · intro u hu
    have he := heMem u hu
    have hvalue : ‖harmonicPGF Y (Complex.exp (u*Complex.I))‖ ≤ max B 1 :=
      (hB (mem_image_of_mem _ (show (⟨Y,hY⟩,(⟨Complex.exp (u*Complex.I),he⟩:Metric.closedBall (0:ℂ) (1+η)))∈univ from mem_univ _))).trans (le_max_left _ _)
    have hePhase : ‖Complex.exp (-(3/2:ℂ)*u*Complex.I)‖≤Real.exp ((3/2)*R) := by
      apply (Complex.norm_exp_le_exp_norm _).trans
      apply Real.exp_le_exp.mpr
      simpa only [norm_mul,norm_neg,norm_I,mul_one,norm_div,norm_ofNat] using (mul_le_mul_of_nonneg_left hu (by norm_num : (0:ℝ)≤3/2))
    unfold centeredHarmonic
    rw [norm_mul]
    exact mul_le_mul hePhase hvalue (norm_nonneg _) (Real.exp_pos _).le
lemma harmonicMass_second_moment_complex (Y:ℝ)(hY:Y∈Icc 0 y₀) :
    HasSum (fun m:ℕ=>(m:ℂ)^2*(harmonicMass Y m:ℂ))
      (deriv (harmonicPGF Y) 1+deriv (deriv (harmonicPGF Y)) 1) := by
  obtain ⟨η,hη,hzero⟩ := barH_uniform_zero_free
  let f := harmonicPGF Y
  let g : ℂ→ℂ := fun z=>z*deriv f z
  have hf := (harmonicPGF_diffOn hη hzero Y hY).mono Metric.ball_subset_closedBall
  have hA (z:ℂ)(hz:z∈Metric.ball 0 (1+η)) : AnalyticAt ℂ f z := hf.analyticAt (Metric.isOpen_ball.mem_nhds hz)
  have hG (z:ℂ)(hz:z∈Metric.ball 0 (1+η)) : AnalyticAt ℂ g z := analyticAt_id.mul (hA z hz).deriv
  have hz0 : (0:ℂ)∈Metric.ball 0 (1+η) := by simp only [Metric.mem_ball,dist_self]; linarith
  have hz1 : (1:ℂ)∈Metric.ball 0 (1+η) := by norm_num; linarith
  have hD : DifferentiableOn ℂ (fun z=>z*deriv g z) (Metric.ball 0 (1+η)) := by
    intro z hz
    exact (differentiableAt_id.mul (hG z hz).deriv.differentiableAt).differentiableWithinAt
  have hderiv : deriv g 1 = deriv f 1+deriv (deriv f) 1 := by
    exact ((hasDerivAt_id (1:ℂ)).mul (hA 1 hz1).deriv.differentiableAt.hasDerivAt).deriv.trans (by simp only [id_eq,one_mul])
  have hs := hasSum_coeff_on_ball _ (1+η) hD 1 (by norm_num; linarith)
  rw [one_mul,hderiv] at hs
  have hcoeff (n:ℕ) : WP.coeff f n=(harmonicMass Y n:ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using harmonicPGF_realCoefficients Y hY n
  convert hs using 1
  ext n
  rw [one_pow,mul_one,harmonic_coeff_euler _ (hG 0 hz0) n,harmonic_coeff_euler _ (hA 0 hz0) n,hcoeff]
  ring
end WP.Analysis
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma harmonicVariance_complex_formula (Y:ℝ)(hY:Y∈Icc 0 y₀) :
    (harmonicVariance Y:ℂ)=deriv (harmonicPGF Y) 1+deriv (deriv (harmonicPGF Y)) 1-9/4 := by
  have h0 := Complex.hasSum_ofReal.mpr (harmonicMass_hasSum Y hY)
  have h1 := Complex.hasSum_ofReal.mpr (harmonicMass_mean Y hY)
  have h2 := harmonicMass_second_moment_complex Y hY
  have hs := (h2.sub (h1.mul_left (3:ℂ))).add (h0.mul_left (9/4:ℂ))
  have hVar := Complex.hasSum_ofReal.mpr (harmonicVariance_summable Y hY).hasSum
  change HasSum (fun m:ℕ=>Complex.ofReal (((m:ℝ)-3/2)^2*harmonicMass Y m)) (harmonicVariance Y:ℂ) at hVar
  have he : (fun m:ℕ=>Complex.ofReal (((m:ℝ)-3/2)^2*harmonicMass Y m)) =
      (fun m:ℕ=>(m:ℂ)^2*(harmonicMass Y m:ℂ)-3*((((m:ℝ)*harmonicMass Y m:ℝ):ℂ))+(9/4:ℂ)*(harmonicMass Y m:ℂ)) := by
    ext m
    push_cast
    ring
  rw [he] at hVar
  exact hVar.unique hs |>.trans (by norm_num; ring)
end WP.Analysis
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma harmonicPGF_one (Y:ℝ)(hY:Y∈Icc 0 y₀) : harmonicPGF Y 1=1 := div_self (barH_zero_free_unit Y hY 1 (by norm_num))
lemma harmonicPGF_analyticAt_one (Y:ℝ)(hY:Y∈Icc 0 y₀) : AnalyticAt ℂ (harmonicPGF Y) 1 :=
  analyticAt_const.div ((barH_differentiable Y).analyticAt 1) (barH_zero_free_unit Y hY 1 (by norm_num))
lemma centeredHarmonic_hasDerivAt (Y:ℝ)(u:ℂ)
    (hP:DifferentiableAt ℂ (harmonicPGF Y) (Complex.exp (u*Complex.I))) :
    HasDerivAt (centeredHarmonic Y)
      (Complex.exp (-(3/2:ℂ)*u*Complex.I)*
        ((-(3/2:ℂ)*Complex.I)*harmonicPGF Y (Complex.exp (u*Complex.I))+
          deriv (harmonicPGF Y) (Complex.exp (u*Complex.I))*Complex.exp (u*Complex.I)*Complex.I)) u := by
  have hA := (((hasDerivAt_id u).const_mul (-(3/2:ℂ))).mul_const Complex.I).cexp
  have hE := ((hasDerivAt_id u).mul_const Complex.I).cexp
  have hPe := hP.hasDerivAt.comp u hE
  convert hA.mul hPe using 1
  · rfl
  · simp only [id_eq,Function.comp_apply,mul_one,one_mul]
    ring
lemma centeredHarmonic_coeff_zero (Y:ℝ)(hY:Y∈Icc 0 y₀) : WP.coeff (centeredHarmonic Y) 0=1 := by
  simp [WP.coeff,centeredHarmonic,harmonicPGF_one Y hY]
lemma centeredHarmonic_coeff_one (Y:ℝ)(hY:Y∈Icc 0 y₀) : WP.coeff (centeredHarmonic Y) 1=0 := by
  have hP : DifferentiableAt ℂ (harmonicPGF Y) (Complex.exp ((0:ℂ)*Complex.I)) := by simpa using (harmonicPGF_analyticAt_one Y hY).differentiableAt
  have hd := (centeredHarmonic_hasDerivAt Y 0 hP).deriv
  unfold WP.coeff
  rw [iteratedDeriv_one,hd]
  norm_num [harmonicPGF_one Y hY,harmonicPGF_deriv_one Y hY]
end WP.Analysis
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma centeredHarmonic_coeff_two (Y:ℝ)(hY:Y∈Icc 0 y₀) :
    WP.coeff (centeredHarmonic Y) 2 = -(harmonicVariance Y:ℂ)/2 := by
  let P := harmonicPGF Y
  let E (u:ℂ) := Complex.exp (u*Complex.I)
  let A (u:ℂ) := Complex.exp (-(3/2:ℂ)*u*Complex.I)
  let B (u:ℂ) := (-(3/2:ℂ)*Complex.I)*P (E u)+deriv P (E u)*E u*Complex.I
  have hPA : AnalyticAt ℂ P 1 := harmonicPGF_analyticAt_one Y hY
  have hEn : Tendsto E (𝓝 0) (𝓝 1) := by
    have hc : Continuous E := by dsimp [E]; fun_prop
    have ht : Tendsto E (𝓝 (0:ℂ)) (𝓝 (E 0)) := hc.continuousAt.tendsto
    simpa only [E,zero_mul,Complex.exp_zero] using ht
  have hNP : ∀ᶠu:ℂ in 𝓝 0,DifferentiableAt ℂ P (E u) :=
    hEn.eventually (hPA.eventually_analyticAt.mono (fun _ h=>h.differentiableAt))
  have hDfun : deriv (centeredHarmonic Y) =ᶠ[𝓝 0] (fun u=>A u*B u) := by
    filter_upwards [hNP] with u hu
    exact (centeredHarmonic_hasDerivAt Y u hu).deriv
  have hE : HasDerivAt E Complex.I 0 := by
    simpa [E] using ((hasDerivAt_id (0:ℂ)).mul_const Complex.I).cexp
  have hA : HasDerivAt A (-(3/2:ℂ)*Complex.I) 0 := by
    simpa [A] using (((hasDerivAt_id (0:ℂ)).const_mul (-(3/2:ℂ))).mul_const Complex.I).cexp
  have hP1 : HasDerivAt P (3/2:ℂ) (E 0) := by
    simpa [P,E,harmonicPGF_deriv_one Y hY] using hPA.differentiableAt.hasDerivAt
  have hPP1 : HasDerivAt (deriv P) (deriv (deriv P) 1) (E 0) := by
    simpa [E] using hPA.deriv.differentiableAt.hasDerivAt
  have hPe := hP1.comp 0 hE
  have hPPe := hPP1.comp 0 hE
  have hdB := (hPe.const_mul (-(3/2:ℂ)*Complex.I)).add ((hPPe.mul hE).mul_const Complex.I)
  have hd : HasDerivAt (fun u=>A u*B u) ((9/4:ℂ)-deriv (deriv P) 1-3/2) 0 := by
    convert hA.mul hdB using 1
    · rfl
    · simp only [A,B,E,P,Function.comp_apply,Pi.add_apply,Pi.mul_apply,Complex.I_sq,zero_mul,mul_zero,Complex.exp_zero,harmonicPGF_one Y hY,harmonicPGF_deriv_one Y hY,one_mul,mul_one]
      ring_nf <;> norm_num <;> ring
  have hsecond : deriv (deriv (centeredHarmonic Y)) 0 = -(harmonicVariance Y:ℂ) := by
    rw [hDfun.deriv_eq,hd.deriv,harmonicVariance_complex_formula Y hY,harmonicPGF_deriv_one Y hY]
    dsimp [P]
    ring
  unfold WP.coeff
  rw [show iteratedDeriv 2 (centeredHarmonic Y) = deriv (deriv (centeredHarmonic Y)) by simp only [iteratedDeriv_succ,iteratedDeriv_zero],hsecond]
  norm_num
end WP.Analysis
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma centeredHarmonic_uniform_cubic : ∃δ C:ℝ,0<δ ∧ 0<C ∧ ∀Y∈Icc (0:ℝ) y₀,∀u:ℂ,‖u‖≤δ →
    ‖centeredHarmonic Y u-(1-(harmonicVariance Y:ℂ)/2*u^2)‖≤C*‖u‖^3 := by
  obtain ⟨R,M,hR,hM,hfamily⟩ := centeredHarmonic_uniform_analytic
  refine ⟨R/2,2*M/R^3,by positivity,by positivity,?_⟩
  intro Y hY u hu
  have hc : ∀z∈Metric.sphere (0:ℂ) R,‖centeredHarmonic Y z‖≤M := by
    intro z hz
    exact (hfamily Y hY).2 z (by simpa only [Metric.mem_sphere,dist_zero_right] using hz.le)
  have hb := complex_quadratic_remainder_bound (centeredHarmonic Y) R M hR hM.le (hfamily Y hY).1 hc u hu
  rw [centeredHarmonic_coeff_zero Y hY,centeredHarmonic_coeff_one Y hY,centeredHarmonic_coeff_two Y hY] at hb
  simpa only [zero_mul,add_zero,neg_div,neg_mul,←sub_eq_add_neg] using hb
lemma centeredHarmonic_norm_real (Y t:ℝ) : ‖centeredHarmonic Y t‖=‖harmonicCharacteristic Y t‖ := by
  unfold centeredHarmonic harmonicCharacteristic
  rw [norm_mul]
  have hn : ‖Complex.exp (-(3/2:ℂ)*(t:ℂ)*Complex.I)‖=1 := by
    rw [Complex.norm_exp]
    norm_num [Complex.mul_re,Complex.mul_im]
  rw [hn,one_mul]
lemma centeredHarmonic_norm_real_le_one (Y:ℝ)(hY:Y∈Icc 0 y₀)(t:ℝ) : ‖centeredHarmonic Y t‖≤1 := by
  rw [centeredHarmonic_norm_real]
  exact harmonicCharacteristic_norm_le_one Y hY t
end WP.Analysis

namespace WP.Analysis
lemma unit_power_difference_bound (x y:ℂ)(hx:‖x‖≤1)(hy:‖y‖≤1)(n:ℕ) :
    ‖x^n-y^n‖≤(n:ℝ)*‖x-y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : x^(n+1)-y^(n+1) = (x^n-y^n)*x+y^n*(x-y) := by rw [pow_succ,pow_succ]; ring
    rw [he]
    have hyn : ‖y^n‖≤1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg y) hy
    calc ‖(x^n-y^n)*x+y^n*(x-y)‖ ≤ ‖(x^n-y^n)*x‖+‖y^n*(x-y)‖ := norm_add_le _ _
         _ = ‖x^n-y^n‖*‖x‖+‖y^n‖*‖x-y‖ := by rw [norm_mul,norm_mul]
         _ ≤ (n:ℝ)*‖x-y‖+‖x-y‖ := add_le_add
           ((mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans (by simpa using ih))
           (by simpa using mul_le_mul_of_nonneg_right hyn (norm_nonneg (x-y)))
         _ = ((n+1:ℕ):ℝ)*‖x-y‖ := by push_cast; ring
end WP.Analysis
