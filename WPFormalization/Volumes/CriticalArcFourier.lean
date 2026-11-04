import WPFormalization.Volumes.CriticalPuiseux
import WPFormalization.Analysis.UniformTaylorRemainder
/-! The actual critical small-arc Fourier bound (9.11).
The true Puiseux factor has a real logarithmic germ and a uniform local
linear bound. A Cauchy disk of radius epsilon/8 controls the quadratic
correction; a separate coarse estimate controls the remaining arc. Fixed
choices absorb both errors into the exact exponent -1/8. The public bound
has only the original PsiTheory parameter and no assumed Fourier estimate. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma CriticalFoldData.Xi_real_positive_germ (d : CriticalFoldData) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∃ q : ℝ, 0 < q ∧ d.Ξ (t:ℂ)=(q:ℂ) := by
  have hsq : Tendsto (fun t : ℝ => t^2) (𝓝[>] 0) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun t : ℝ => t^2) 0 := by fun_prop
      simpa only [zero_pow (by norm_num : 2 ≠ 0)] using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sq_pos_of_pos (show 0 < t from ht)
  have htc : Tendsto (fun t : ℝ => (t:ℂ)) (𝓝[>] 0) (𝓝 (0:ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlt : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hlt,hsq.eventually d.inverseY_coordinate,htc.eventually d.residue_identity]
    with t ht hlt hD hres
  have htpos : 0 < t := ht
  rw [Real.sqrt_sq htpos.le] at hD
  let x : ℝ := xCritical*(1-t^2)
  have hx : x ∈ Ico (0:ℝ) xCritical := by
    dsimp [x]
    constructor
    · have hp : 0 < 1-t^2 := by nlinarith
      exact (mul_pos critical_x_pos hp).le
    · have hp : 0 < xCritical*t^2 := mul_pos critical_x_pos (sq_pos_of_pos htpos)
      nlinarith
  have hY := (inverseY_branch x hx).1
  have ha := a_pos (inverseY x) hY
  have hDY : (y₀:ℂ)-d.D (t:ℂ)=(inverseY x:ℂ) := by
    rw [hD]
    push_cast
    ring
  have htn : (t:ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
  have hcn : (d.c:ℂ) ≠ 0 := by exact_mod_cast d.c_pos.ne'
  have han : (a (inverseY x):ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hr := hres htn
  rw [hDY,derivX_ofReal] at hr
  let q : ℝ := d.c*t/a (inverseY x)
  have hq : 0 < q := div_pos (mul_pos d.c_pos htpos) ha
  refine ⟨q,hq,?_⟩
  change d.Ξ (t:ℂ)=((d.c*t/a (inverseY x):ℝ):ℂ)
  rw [Complex.ofReal_div,Complex.ofReal_mul]
  apply (eq_div_iff han).2
  field_simp [hcn,htn] at hr
  convert hr using 1 <;> ring

lemma complex_deriv_im_zero_of_real_germ (f : ℂ → ℂ) (x : ℝ)
    (hf : DifferentiableAt ℂ f (x:ℂ)) (he : ∀ᶠ t : ℝ in 𝓝 x, (f (t:ℂ)).im=0) :
    (deriv f (x:ℂ)).im=0 := by
  have hd : HasDerivAt (fun t : ℝ => (f (t:ℂ)).im) (deriv f (x:ℂ)).im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hf.hasDerivAt.comp_ofReal
  have heq : (fun t : ℝ => (f (t:ℂ)).im) =ᶠ[𝓝 x] (fun _ : ℝ => 0) := he
  have hder := (hd.congr_of_eventuallyEq heq.symm).deriv
  simpa only [deriv_const] using hder.symm
end WP.Analysis
namespace WP.Analysis
lemma complex_analytic_zero_linear_bound (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (h0 : f 0=0) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ z : ℂ, ‖z‖ ≤ r → AnalyticAt ℂ f z ∧ ‖f z‖ ≤ C*‖z‖ := by
  obtain ⟨G,hG,hG0,hfactor⟩ := complex_analytic_linear_factor f hf h0
  let C : ℝ := ‖G 0‖+1
  have hC : 0 < C := by dsimp [C];positivity
  have hb : ∀ᶠ z : ℂ in 𝓝 0, ‖G z‖ < C :=
    hG.continuousAt.norm.tendsto.eventually (eventually_lt_nhds (by dsimp [C];linarith))
  have hall : ∀ᶠ z : ℂ in 𝓝 0, AnalyticAt ℂ f z ∧ f z=z*G z ∧ ‖G z‖ < C := by
    filter_upwards [hf.eventually_analyticAt,hfactor,hb] with z hfa he hgb
    exact ⟨hfa,he,hgb⟩
  obtain ⟨R,hR,hall⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨R/2,C,by positivity,hC,?_⟩
  intro z hz
  have ht := hall (by rw [dist_zero_right];linarith : dist z 0 < R)
  refine ⟨ht.1,?_⟩
  rw [ht.2.1,norm_mul]
  nlinarith [norm_nonneg z]

def CriticalFoldData.logXi (d : CriticalFoldData) (t : ℂ) : ℂ := Complex.log (d.Ξ t)
lemma CriticalFoldData.logXi_analytic (d : CriticalFoldData) : AnalyticAt ℂ d.logXi 0 := by
  have hplane : d.Ξ 0 ∈ Complex.slitPlane := by rw [d.Xi_zero];simp
  exact (analyticAt_clog hplane).comp d.Xi_analytic
lemma CriticalFoldData.logXi_zero (d : CriticalFoldData) : d.logXi 0=0 := by simp only [logXi,d.Xi_zero,Complex.log_one]
lemma CriticalFoldData.logXi_real_positive_axis (d : CriticalFoldData) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (d.logXi (t:ℂ)).im=0 := by
  filter_upwards [d.Xi_real_positive_germ] with t ht
  obtain ⟨q,hq,hreal⟩ := ht
  dsimp only [logXi]
  rw [hreal,←Complex.ofReal_log hq.le,Complex.ofReal_im]
lemma CriticalFoldData.logXi_uniform_linear_bound (d : CriticalFoldData) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ t : ℂ, ‖t‖ ≤ r →
      AnalyticAt ℂ d.logXi t ∧ ‖d.logXi t‖ ≤ C*‖t‖ :=
  complex_analytic_zero_linear_bound d.logXi d.logXi_analytic d.logXi_zero
end WP.Analysis
namespace WP.Analysis
lemma complex_sqrt_deriv_im_zero (x : ℝ) (hx : 0 < x) : (deriv Complex.sqrt (x:ℂ)).im=0 := by
  apply complex_deriv_im_zero_of_real_germ Complex.sqrt x (Complex.differentiableAt_sqrt (Or.inl hx))
  filter_upwards [eventually_gt_nhds hx] with t ht
  have hs := Complex.sqrt_of_nonneg (a := (t:ℂ)) (by exact_mod_cast ht.le)
  simpa only [Complex.ofReal_re,Complex.ofReal_im] using congrArg Complex.im hs
lemma CriticalFoldData.logXi_derivative_real_near (d : CriticalFoldData) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Ioo (0:ℝ) r,
      DifferentiableAt ℂ d.logXi (t:ℂ) → (deriv d.logXi (t:ℂ)).im=0 := by
  have he : ∀ᶠ t : ℝ in 𝓝 0, 0 < t → (d.logXi (t:ℂ)).im=0 :=
    eventually_nhdsWithin_iff.mp d.logXi_real_positive_axis
  obtain ⟨r,hr,hreal⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r,hr,?_⟩
  intro t ht hf
  apply complex_deriv_im_zero_of_real_germ d.logXi t hf
  filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
  exact hreal (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hu.1] using hu.2) hu.1

def criticalArcGap (ε : ℝ) (ζ : ℂ) : ℂ := 1-(1-ε:ℂ)*Complex.exp (ζ*Complex.I)
def criticalArcRoot (ε : ℝ) (ζ : ℂ) : ℂ := Complex.sqrt (criticalArcGap ε ζ)
lemma criticalArcGap_zero (ε : ℝ) : criticalArcGap ε 0=(ε:ℂ) := by simp [criticalArcGap]
lemma criticalArcRoot_zero (ε : ℝ) (hε : 0 ≤ ε) : criticalArcRoot ε 0=((Real.sqrt ε:ℝ):ℂ) := by
  rw [criticalArcRoot,criticalArcGap_zero]
  simpa only [Complex.ofReal_re] using (Complex.sqrt_of_nonneg (a := (ε:ℂ)) (by exact_mod_cast hε))
lemma criticalArcGap_hasDerivAt (ε : ℝ) :
    HasDerivAt (criticalArcGap ε) (-((1-ε:ℝ):ℂ)*Complex.I) 0 := by
  have he : HasDerivAt (fun ζ : ℂ => Complex.exp (ζ*Complex.I)) Complex.I 0 := by
    convert! (Complex.hasDerivAt_exp (0*Complex.I)).comp 0 ((hasDerivAt_id (0:ℂ)).mul_const Complex.I) using 1 <;> simp
  convert! (hasDerivAt_const (0:ℂ) (1:ℂ)).sub (he.const_mul ((1-ε:ℝ):ℂ)) using 1 <;>
    (first | funext ζ | skip) <;>
    simp only [criticalArcGap,Complex.ofReal_sub,Complex.ofReal_one,Pi.sub_apply,zero_sub,mul_neg] <;> ring
lemma criticalArc_composition_deriv_re_zero (f : ℂ → ℂ) (ε : ℝ) (hε : 0 < ε)
    (hf : DifferentiableAt ℂ f (((Real.sqrt ε):ℝ):ℂ))
    (hfIm : (deriv f (((Real.sqrt ε):ℝ):ℂ)).im=0) :
    (deriv (fun ζ : ℂ => f (criticalArcRoot ε ζ)) 0).re=0 := by
  have hroot : Complex.sqrt (criticalArcGap ε 0)=(((Real.sqrt ε):ℝ):ℂ) := criticalArcRoot_zero ε hε.le
  have hS : HasDerivAt Complex.sqrt (deriv Complex.sqrt (ε:ℂ)) (criticalArcGap ε 0) := by
    rw [criticalArcGap_zero]
    exact (Complex.differentiableAt_sqrt (Or.inl hε)).hasDerivAt
  have hF : HasDerivAt f (deriv f (((Real.sqrt ε):ℝ):ℂ)) (Complex.sqrt (criticalArcGap ε 0)) := by
    rw [hroot]
    exact hf.hasDerivAt
  have hd := hF.comp 0 (hS.comp 0 (criticalArcGap_hasDerivAt ε))
  have hde : deriv (fun ζ : ℂ => f (criticalArcRoot ε ζ)) 0=
      deriv f (((Real.sqrt ε):ℝ):ℂ)*(deriv Complex.sqrt (ε:ℂ)*(-((1-ε:ℝ):ℂ)*Complex.I)) := by
    convert! hd.deriv using 1
  rw [hde]
  simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im,hfIm,complex_sqrt_deriv_im_zero ε hε]
  ring
end WP.Analysis
namespace WP.Analysis
lemma criticalArcGap_sub_norm (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ζ : ℂ) (hζ : ‖ζ‖ ≤ 1) : ‖criticalArcGap ε ζ-(ε:ℂ)‖ ≤ 2*‖ζ‖ := by
  have he : ‖ζ*Complex.I‖ ≤ 1 := by simpa only [norm_mul,Complex.norm_I,mul_one] using hζ
  have he' := Complex.norm_exp_sub_one_le he
  have hid : criticalArcGap ε ζ-(ε:ℂ)=-((1-ε:ℝ):ℂ)*(Complex.exp (ζ*Complex.I)-1) := by
    dsimp only [criticalArcGap]
    push_cast
    ring
  rw [hid,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hε1)]
  calc _ ≤ (1-ε)*(2*‖ζ*Complex.I‖) := mul_le_mul_of_nonneg_left he' (sub_nonneg.mpr hε1)
       _ ≤ 2*‖ζ‖ := by simp only [norm_mul,Complex.norm_I,mul_one];nlinarith [norm_nonneg ζ]
lemma criticalArcGap_norm (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ζ : ℂ) (hζ : ‖ζ‖ ≤ 1) : ‖criticalArcGap ε ζ‖ ≤ ε+2*‖ζ‖ := by
  calc _ ≤ ‖criticalArcGap ε ζ-(ε:ℂ)‖+‖(ε:ℂ)‖ := by simpa only [sub_add_cancel] using norm_add_le (criticalArcGap ε ζ-(ε:ℂ)) (ε:ℂ)
       _ ≤ 2*‖ζ‖+ε := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hε];exact add_le_add (criticalArcGap_sub_norm ε hε hε1 ζ hζ) le_rfl
       _ = _ := by ring
lemma criticalArcGap_re_pos (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ζ : ℂ) (hζ : ‖ζ‖ ≤ ε/8) : 0 < (criticalArcGap ε ζ).re := by
  have hz1 : ‖ζ‖ ≤ 1 := by linarith
  have hn := criticalArcGap_sub_norm ε hε.le hε1 ζ hz1
  have hr := (abs_le.mp ((Complex.abs_re_le_norm (criticalArcGap ε ζ-(ε:ℂ))).trans hn)).1
  simp only [Complex.sub_re,Complex.ofReal_re] at hr
  linarith
lemma criticalArcRoot_norm_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ζ : ℂ) (hζ : ‖ζ‖ ≤ ε/8) : ‖criticalArcRoot ε ζ‖ ≤ 2*Real.sqrt ε := by
  have hz1 : ‖ζ‖ ≤ 1 := by linarith
  have hn := criticalArcGap_norm ε hε.le hε1 ζ hz1
  have hs : ‖criticalArcRoot ε ζ‖^2=‖criticalArcGap ε ζ‖ := by
    rw [←norm_pow,criticalArcRoot,complex_sqrt_sq]
  nlinarith [Real.sq_sqrt hε.le,Real.sqrt_nonneg ε,norm_nonneg (criticalArcRoot ε ζ)]
lemma criticalArcRoot_analytic (ε : ℝ) (ζ : ℂ) (h : 0 < (criticalArcGap ε ζ).re) :
    AnalyticAt ℂ (criticalArcRoot ε) ζ := by
  have hf : AnalyticAt ℂ (criticalArcGap ε) ζ := by unfold criticalArcGap;fun_prop
  have hs : AnalyticAt ℂ Complex.sqrt (criticalArcGap ε ζ) := complex_sqrt_analyticAt (Or.inl h)
  exact AnalyticAt.comp (f := criticalArcGap ε) (x := ζ) hs hf

lemma criticalArcLog_small_taylor_bound (f : ℂ → ℂ) (r C : ℝ)
    (hr : 0 < r) (hC : 0 ≤ C)
    (hfa : ∀ t : ℂ, ‖t‖ ≤ r → AnalyticAt ℂ f t)
    (hfb : ∀ t : ℂ, ‖t‖ ≤ r → ‖f t‖ ≤ C*‖t‖)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεr : 2*Real.sqrt ε ≤ r)
    (hfIm : (deriv f (((Real.sqrt ε):ℝ):ℂ)).im=0)
    (θ : ℝ) (hθ : |θ| ≤ ε/16) :
    |(f (criticalArcRoot ε (θ:ℂ))).re-(f (criticalArcRoot ε 0)).re| ≤
      256*C*Real.sqrt ε*θ^2/ε^2 := by
  let F : ℂ → ℂ := fun ζ => f (criticalArcRoot ε ζ)
  let R : ℝ := ε/8
  have hR : 0 < R := by dsimp [R];positivity
  have hlocal (ζ : ℂ) (hζ : ‖ζ‖ ≤ R) : AnalyticAt ℂ F ζ ∧ ‖F ζ‖ ≤ 2*C*Real.sqrt ε := by
    have hrn := criticalArcRoot_norm_bound ε hε hε1 ζ hζ
    have hrs := hrn.trans hεr
    refine ⟨(hfa _ hrs).comp (criticalArcRoot_analytic ε ζ (criticalArcGap_re_pos ε hε hε1 ζ hζ)),?_⟩
    exact (hfb _ hrs).trans (by nlinarith)
  have hdiff : DifferentiableOn ℂ F (Metric.closedBall 0 R) := by
    intro ζ hζ
    exact (hlocal ζ (by simpa only [Metric.mem_closedBall,dist_zero_right] using hζ)).1.differentiableAt.differentiableWithinAt
  have hcircle : ∀ ζ ∈ Metric.sphere (0:ℂ) R, ‖F ζ‖ ≤ 2*C*Real.sqrt ε := by
    intro ζ hζ
    exact (hlocal ζ (by simpa only [Metric.mem_closedBall,dist_zero_right] using Metric.sphere_subset_closedBall hζ)).2
  have hθR : ‖(θ:ℂ)‖ ≤ R/2 := by rw [Complex.norm_real,Real.norm_eq_abs];dsimp [R];linarith
  have ht := complex_taylor_remainder_bound F R (2*C*Real.sqrt ε) hR (by positivity) hdiff hcircle 2 (θ:ℂ) hθR
  have hsum : (∑ i ∈ Finset.range 2,WP.coeff F i*(θ:ℂ)^i)=F 0+deriv F 0*(θ:ℂ) := by
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,WP.coeff,iteratedDeriv_zero,iteratedDeriv_one,
      Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one,pow_zero,pow_one,mul_one]
  rw [hsum] at ht
  have hFn : ‖(((Real.sqrt ε):ℝ):ℂ)‖ ≤ r := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg ε)]
    nlinarith [Real.sqrt_nonneg ε]
  have hderRe : (deriv F 0).re=0 := criticalArc_composition_deriv_re_zero f ε hε (hfa _ hFn).differentiableAt hfIm
  have hre : (F (θ:ℂ)-(F 0+deriv F 0*(θ:ℂ))).re=(F (θ:ℂ)).re-(F 0).re := by
    simp only [Complex.sub_re,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,hderRe,zero_mul,mul_zero,sub_zero,add_zero]
  have hb := ((Complex.abs_re_le_norm _).trans ht)
  rw [hre] at hb
  apply hb.trans_eq
  rw [Complex.norm_real,Real.norm_eq_abs]
  dsimp [R]
  rw [div_pow,sq_abs]
  field_simp [hε.ne']
  <;> ring
end WP.Analysis
namespace WP.Analysis
lemma criticalArcLog_coarse_bound (f : ℂ → ℂ) (r C : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ t : ℂ, ‖t‖ ≤ r → ‖f t‖ ≤ C*‖t‖)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδr : 2*Real.sqrt δ ≤ r)
    (ε : ℝ) (hε : 0 < ε) (hεδ : ε ≤ δ) (θ : ℝ) (hθ : |θ| ≤ δ) :
    |(f (criticalArcRoot ε (θ:ℂ))).re-(f (criticalArcRoot ε 0)).re| ≤ 3*C*Real.sqrt δ := by
  have hζ : ‖(θ:ℂ)‖ ≤ 1 := by rw [Complex.norm_real,Real.norm_eq_abs];exact hθ.trans hδ1
  have hn := criticalArcGap_norm ε hε.le (hεδ.trans hδ1) (θ:ℂ) hζ
  rw [Complex.norm_real,Real.norm_eq_abs] at hn
  have hs : ‖criticalArcRoot ε (θ:ℂ)‖^2=‖criticalArcGap ε (θ:ℂ)‖ := by
    rw [←norm_pow,criticalArcRoot,complex_sqrt_sq]
  have hrθ : ‖criticalArcRoot ε (θ:ℂ)‖ ≤ 2*Real.sqrt δ := by
    nlinarith [Real.sq_sqrt hδ.le,Real.sqrt_nonneg δ,norm_nonneg (criticalArcRoot ε (θ:ℂ))]
  have hr0 : ‖criticalArcRoot ε 0‖ ≤ Real.sqrt δ := by
    rw [criticalArcRoot_zero ε hε.le,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg ε)]
    exact Real.sqrt_le_sqrt hεδ
  have hfθ := hfb _ (hrθ.trans hδr)
  have hf0 := hfb _ (hr0.trans (by nlinarith [Real.sqrt_nonneg δ] : Real.sqrt δ ≤ r))
  have hRe : |(f (criticalArcRoot ε (θ:ℂ))).re-(f (criticalArcRoot ε 0)).re| ≤
      ‖f (criticalArcRoot ε (θ:ℂ))-f (criticalArcRoot ε 0)‖ := by simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (f (criticalArcRoot ε (θ:ℂ))-f (criticalArcRoot ε 0)))
  apply (hRe.trans (norm_sub_le _ _)).trans
  have h1 := mul_le_mul_of_nonneg_left hrθ hC
  have h2 := mul_le_mul_of_nonneg_left hr0 hC
  nlinarith
lemma log_one_add_half_lower (v : ℝ) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    v/2 ≤ Real.log (1+v) := by
  apply le_trans _ (Real.le_log_one_add_of_nonneg hv)
  apply (le_div_iff₀ (by linarith : 0 < v+2)).2
  nlinarith [mul_nonneg hv (sub_nonneg.mpr hv1)]

lemma CriticalFoldData.logXi_uniform_arc_correction (d : CriticalFoldData) :
    ∃ δ ε₀ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < ε₀ ∧ ε₀ ≤ min δ (1/2) ∧
      ∀ ε ∈ Ioo (0:ℝ) ε₀, ∀ θ : ℝ, |θ| ≤ δ →
      |(d.logXi (criticalArcRoot ε (θ:ℂ))).re-(d.logXi (criticalArcRoot ε 0)).re| ≤
        (1/8:ℝ)*Real.log (1+θ^2/(4*ε^2)) := by
  obtain ⟨r,C,hr,hC,hdata⟩ := d.logXi_uniform_linear_bound
  obtain ⟨ρ,hρ,hder⟩ := d.logXi_derivative_real_near
  let R : ℝ := min r ρ
  have hR : 0 < R := lt_min hr hρ
  have hRr : R ≤ r := min_le_left _ _
  have hRρ : R ≤ ρ := min_le_right _ _
  let α : ℝ := Real.log (1+1/(1024:ℝ))
  have hα : 0 < α := Real.log_pos (by norm_num)
  let δ : ℝ := min 1 (min (R^2/16) ((α/(24*C))^2))
  let ε₀ : ℝ := min δ (min (1/2) ((1/(16384*C))^2))
  have hδ : 0 < δ := lt_min zero_lt_one (lt_min (by positivity) (sq_pos_of_pos (by positivity)))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδR : δ ≤ R^2/16 := (min_le_right _ _).trans (min_le_left _ _)
  have hδα : δ ≤ (α/(24*C))^2 := (min_le_right _ _).trans (min_le_right _ _)
  have hε₀ : 0 < ε₀ := lt_min hδ (lt_min (by norm_num) (sq_pos_of_pos (by positivity)))
  have hε₀δ : ε₀ ≤ δ := min_le_left _ _
  have hε₀half : ε₀ ≤ 1/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε₀small : ε₀ ≤ (1/(16384*C))^2 := (min_le_right _ _).trans (min_le_right _ _)
  have hrootδ : 2*Real.sqrt δ ≤ R := by nlinarith [Real.sq_sqrt hδ.le,Real.sqrt_nonneg δ]
  have hrootα : Real.sqrt δ ≤ α/(24*C) := by
    have hq : 0 < α/(24*C) := by positivity
    nlinarith [Real.sq_sqrt hδ.le,Real.sqrt_nonneg δ]
  have hcoarse : 3*C*Real.sqrt δ ≤ α/8 := by
    have ht := mul_le_mul_of_nonneg_left hrootα (by positivity : 0 ≤ 3*C)
    have he : 3*C*(α/(24*C))=α/8 := by field_simp [hC.ne'] <;> ring
    exact ht.trans_eq he
  refine ⟨δ,ε₀,hδ,hδ1,hε₀,le_min hε₀δ hε₀half,?_⟩
  intro ε hε θ hθ
  have hεp : 0 < ε := hε.1
  have hεδ : ε ≤ δ := hε.2.le.trans hε₀δ
  have hε1 : ε ≤ 1 := hεδ.trans hδ1
  have hrootεδ := Real.sqrt_le_sqrt hεδ
  have hεr : 2*Real.sqrt ε ≤ r := by linarith
  have hrootρ : Real.sqrt ε < ρ := by linarith [Real.sqrt_nonneg δ]
  have hfIm : (deriv d.logXi (((Real.sqrt ε):ℝ):ℂ)).im=0 := hder _ ⟨Real.sqrt_pos.mpr hε.1,hrootρ⟩
    (hdata _ (by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg ε)];linarith)).1.differentiableAt
  let v : ℝ := θ^2/(4*ε^2)
  have hv : 0 ≤ v := by dsimp [v];positivity
  by_cases hθsmall : |θ| ≤ ε/16
  · have he := criticalArcLog_small_taylor_bound d.logXi r C hr hC.le
      (fun t ht => (hdata t ht).1) (fun t ht => (hdata t ht).2)
      ε hε.1 hε1 hεr hfIm θ hθsmall
    have hrootsmall : Real.sqrt ε ≤ 1/(16384*C) := by
      have hs := hε.2.le.trans hε₀small
      have hq : 0 < 1/(16384*C) := by positivity
      nlinarith [Real.sq_sqrt hε.1.le,Real.sqrt_nonneg ε]
    have hcoeff : 256*C*Real.sqrt ε ≤ 1/64 := by
      have ht := mul_le_mul_of_nonneg_left hrootsmall (by positivity : 0 ≤ 256*C)
      have heq : 256*C*(1/(16384*C))=1/64 := by field_simp [hC.ne'] <;> ring
      exact ht.trans_eq heq
    have hvs : v ≤ 1 := by
      have ht := pow_le_pow_left₀ (abs_nonneg θ) hθsmall 2
      rw [sq_abs,div_pow] at ht
      dsimp [v]
      apply (div_le_one (by positivity : 0 < 4*ε^2)).2
      nlinarith
    have hlog := log_one_add_half_lower v hv hvs
    have hfactor : 0 ≤ θ^2/ε^2 := by positivity
    have hscaled := mul_le_mul_of_nonneg_right hcoeff hfactor
    apply he.trans
    have heq : 256*C*Real.sqrt ε*θ^2/ε^2=(256*C*Real.sqrt ε)*(θ^2/ε^2) := by ring
    rw [heq]
    apply hscaled.trans
    dsimp [v] at hlog
    have hscaledLog := mul_le_mul_of_nonneg_left hlog (by norm_num : (0:ℝ) ≤ 1/8)
    convert hscaledLog using 1 <;> field_simp [hεp.ne'] <;> ring
  · have hlarge : ε/16 < |θ| := lt_of_not_ge hθsmall
    have ht := pow_le_pow_left₀ (by positivity : 0 ≤ ε/16) hlarge.le 2
    rw [sq_abs,div_pow] at ht
    have hvlow : 1/(1024:ℝ) ≤ v := by
      dsimp [v]
      apply (le_div_iff₀ (by positivity : 0 < 4*ε^2)).2
      nlinarith
    have hlog : α ≤ Real.log (1+v) := Real.log_le_log (by norm_num) (by dsimp [α] at *;linarith)
    have he := criticalArcLog_coarse_bound d.logXi r C hC.le (fun t ht => (hdata t ht).2)
      δ hδ hδ1 (hrootδ.trans hRr) ε hε.1 hεδ θ hθ
    apply he.trans (hcoarse.trans _)
    dsimp [v] at hlog
    linarith
end WP.Analysis
namespace WP.Analysis
lemma one_sub_cos_quarter (θ : ℝ) (hθ : |θ| ≤ 1) : θ^2/4 ≤ 1-Real.cos θ := by
  have hc := (abs_le.mp (Real.cos_bound hθ)).2
  have hs := pow_le_pow_left₀ (abs_nonneg θ) hθ 2
  norm_num only [one_pow] at hs
  have hfour : |θ|^4 ≤ |θ|^2 := by nlinarith [mul_nonneg (sq_nonneg |θ|) (sub_nonneg.mpr hs)]
  nlinarith [sq_abs θ]
lemma criticalArcGap_norm_sq_real (ε θ : ℝ) :
    ‖criticalArcGap ε (θ:ℂ)‖^2=ε^2+2*(1-ε)*(1-Real.cos θ) := by
  have hr : (criticalArcGap ε (θ:ℂ)).re=1-(1-ε)*Real.cos θ := by
    simp [criticalArcGap,Complex.exp_mul_I,Complex.mul_re,Complex.cos_ofReal_re,Complex.sin_ofReal_re]
  have hi : (criticalArcGap ε (θ:ℂ)).im=-(1-ε)*Real.sin θ := by
    simp [criticalArcGap,Complex.exp_mul_I,Complex.mul_im,Complex.cos_ofReal_re,Complex.sin_ofReal_re]
    ring
  rw [Complex.sq_norm,Complex.normSq_apply,hr,hi]
  have ht := congrArg (fun x : ℝ => (1-ε)^2*x) (Real.sin_sq_add_cos_sq θ)
  nlinarith
lemma criticalArcRoot_log_norm_ratio (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1/2)
    (θ : ℝ) (hθ : |θ| ≤ 1) :
    Real.log (Real.sqrt ε)-Real.log ‖criticalArcRoot ε (θ:ℂ)‖ ≤
      -(1/4:ℝ)*Real.log (1+θ^2/(4*ε^2)) := by
  have hc := one_sub_cos_quarter θ hθ
  have hc0 : 0 ≤ 1-Real.cos θ := sub_nonneg.mpr (Real.cos_le_one θ)
  have hm := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ 2*(1-ε) by linarith) hc0
  have hw : ε^2+θ^2/4 ≤ ‖criticalArcGap ε (θ:ℂ)‖^2 := by
    rw [criticalArcGap_norm_sq_real]
    nlinarith
  have hwpos : 0 < ‖criticalArcGap ε (θ:ℂ)‖ := by
    nlinarith [norm_nonneg (criticalArcGap ε (θ:ℂ)),sq_pos_of_pos hε,sq_nonneg θ]
  have hrootSq : ‖criticalArcRoot ε (θ:ℂ)‖^2=‖criticalArcGap ε (θ:ℂ)‖ := by
    rw [←norm_pow,criticalArcRoot,complex_sqrt_sq]
  have hrootPos : 0 < ‖criticalArcRoot ε (θ:ℂ)‖ := by nlinarith [norm_nonneg (criticalArcRoot ε (θ:ℂ))]
  have hv : 0 ≤ θ^2/(4*ε^2) := by positivity
  have hquot : 1+θ^2/(4*ε^2) ≤ ‖criticalArcGap ε (θ:ℂ)‖^2/ε^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hε)).2
    have heq : (1+θ^2/(4*ε^2))*ε^2=ε^2+θ^2/4 := by field_simp [hε.ne'] <;> ring
    rwa [heq]
  have hl := Real.log_le_log (by positivity : 0 < 1+θ^2/(4*ε^2)) hquot
  rw [Real.log_div (pow_ne_zero 2 hwpos.ne') (pow_ne_zero 2 hε.ne'),Real.log_pow,Real.log_pow] at hl
  have hs := congrArg Real.log hrootSq
  rw [Real.log_pow] at hs
  rw [Real.log_sqrt hε.le]
  norm_num only [Nat.cast_ofNat] at hl hs
  linarith
end WP.Analysis
namespace WP.Analysis
lemma log_norm_normalized_pole_ratio (c q q₀ t t₀ : ℂ)
    (hc : c ≠ 0) (hq : q ≠ 0) (hq₀ : q₀ ≠ 0) (ht : t ≠ 0) (ht₀ : t₀ ≠ 0) :
    Real.log ‖(c⁻¹*q/t)/(c⁻¹*q₀/t₀)‖=
      (Complex.log q).re-(Complex.log q₀).re+Real.log ‖t₀‖-Real.log ‖t‖ := by
  have he : (c⁻¹*q/t)/(c⁻¹*q₀/t₀)=(q/q₀)*(t₀/t) := by field_simp [hc,hq₀,ht,ht₀] <;> ring
  rw [he,norm_mul,norm_div,norm_div,
    Real.log_mul (div_ne_zero (norm_ne_zero_iff.mpr hq) (norm_ne_zero_iff.mpr hq₀))
      (div_ne_zero (norm_ne_zero_iff.mpr ht₀) (norm_ne_zero_iff.mpr ht)),
    Real.log_div (norm_ne_zero_iff.mpr hq) (norm_ne_zero_iff.mpr hq₀),
    Real.log_div (norm_ne_zero_iff.mpr ht₀) (norm_ne_zero_iff.mpr ht),Complex.log_re,Complex.log_re]
  ring

def criticalRayPoint (ε θ : ℝ) : ℂ := ((xCritical*(1-ε):ℝ):ℂ)*Complex.exp ((θ:ℂ)*Complex.I)
lemma criticalRayPoint_norm (ε θ : ℝ) (hε : ε ≤ 1) :
    ‖criticalRayPoint ε θ‖=xCritical*(1-ε) := by
  rw [criticalRayPoint,norm_mul,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,Real.exp_zero,mul_one]
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg critical_x_pos.le (sub_nonneg.mpr hε))]
lemma criticalRayPoint_root (ε θ : ℝ) :
    criticalRootParameter (criticalRayPoint ε θ)=criticalArcRoot ε (θ:ℂ) := by
  unfold criticalRootParameter criticalArcRoot criticalArcGap criticalRayPoint
  congr 1
  push_cast
  field_simp [show (xCritical:ℂ) ≠ 0 by exact_mod_cast critical_x_pos.ne']
  <;> ring
lemma criticalRayPoint_gap_norm (ε θ : ℝ) :
    ‖criticalRayPoint ε θ-(xCritical:ℂ)‖=xCritical*‖criticalArcGap ε (θ:ℂ)‖ := by
  have he : criticalRayPoint ε θ-(xCritical:ℂ)=-(xCritical:ℂ)*criticalArcGap ε (θ:ℂ) := by
    dsimp only [criticalRayPoint,criticalArcGap]
    push_cast
    ring
  rw [he,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos critical_x_pos]

lemma universalV_critical_small_arc_bound (P : PsiTheory) :
    ∃ δ ε₀ : ℝ, 0 < δ ∧ 0 < ε₀ ∧ ∀ ε ∈ Ioo (0:ℝ) ε₀,
      ∀ θ : ℝ, |θ| ≤ δ →
      ‖universalV P (criticalRayPoint ε θ)/universalV P (((xCritical*(1-ε):ℝ):ℂ))‖ ≤
        Real.rpow (1+θ^2/(4*ε^2)) (-1/8:ℝ) := by
  obtain ⟨d⟩ := exists_criticalFoldData
  obtain ⟨δa,εa,hδa,hδa1,hεa,hεac,hcorr⟩ := d.logXi_uniform_arc_correction
  obtain ⟨η,hη,hmodel⟩ := d.universalV_complex_puiseux P
  let δ : ℝ := min δa (η/(4*xCritical))
  let ε₀ : ℝ := min εa (min δ (1/2))
  have hxc := critical_x_pos
  have hδ : 0 < δ := lt_min hδa (by positivity)
  have hε₀ : 0 < ε₀ := lt_min hεa (lt_min hδ (by norm_num))
  have hδa' : δ ≤ δa := min_le_left _ _
  have hδ1 : δ ≤ 1 := hδa'.trans hδa1
  have hδη : δ ≤ η/(4*xCritical) := min_le_right _ _
  have hεa' : ε₀ ≤ εa := min_le_left _ _
  have hεhalf : ε₀ ≤ 1/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hεδ' : ε₀ ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨δ,ε₀,hδ,hε₀,?_⟩
  intro ε hε θ hθ
  have hεp : 0 < ε := hε.1
  have hεh : ε ≤ 1/2 := hε.2.le.trans hεhalf
  have hε1 : ε ≤ 1 := by linarith
  have hεδ : ε ≤ δ := hε.2.le.trans hεδ'
  have hpoint (φ : ℝ) (hφ : |φ| ≤ δ) :
      ‖criticalRayPoint ε φ‖ < xCritical ∧
      universalV P (criticalRayPoint ε φ)=(d.c:ℂ)⁻¹*d.Ξ (criticalArcRoot ε (φ:ℂ))/criticalArcRoot ε (φ:ℂ) := by
    have hn : ‖criticalRayPoint ε φ‖ < xCritical := by
      rw [criticalRayPoint_norm ε φ hε1]
      nlinarith
    have hnear : ‖criticalRayPoint ε φ-(xCritical:ℂ)‖ < η := by
      rw [criticalRayPoint_gap_norm]
      have hφ1 : ‖(φ:ℂ)‖ ≤ 1 := by rw [Complex.norm_real,Real.norm_eq_abs];exact hφ.trans hδ1
      have ht := criticalArcGap_norm ε hεp.le hε1 (φ:ℂ) hφ1
      rw [Complex.norm_real,Real.norm_eq_abs] at ht
      have hmul := (le_div_iff₀ (by positivity : 0 < 4*xCritical)).mp hδη
      have hgap : ‖criticalArcGap ε (φ:ℂ)‖ ≤ 3*δ := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hgap hxc.le]
    refine ⟨hn,?_⟩
    rw [hmodel _ hn hnear,criticalRayPoint_root]
  have hθpoint := hpoint θ hθ
  have h0point := hpoint 0 (by simpa using hδ.le)
  simp only [Complex.ofReal_zero] at h0point
  have h0z : criticalRayPoint ε 0=(((xCritical*(1-ε)):ℝ):ℂ) := by simp [criticalRayPoint]
  have hvθ : universalV P (criticalRayPoint ε θ) ≠ 0 :=
    PositiveConvolution.planar_third_ne_zero P _ hθpoint.1
  have hv0 : universalV P (criticalRayPoint ε 0) ≠ 0 :=
    PositiveConvolution.planar_third_ne_zero P _ h0point.1
  have htθ : criticalArcRoot ε (θ:ℂ) ≠ 0 := by
    rw [←criticalRayPoint_root]
    exact criticalRootParameter_ne_zero _ hθpoint.1
  have ht0 : criticalArcRoot ε 0 ≠ 0 := by
    rw [criticalArcRoot_zero ε hεp.le]
    exact_mod_cast (Real.sqrt_pos.mpr hεp).ne'
  have hqθ : d.Ξ (criticalArcRoot ε (θ:ℂ)) ≠ 0 := by
    intro hz
    have he := hθpoint.2
    rw [hz,mul_zero,zero_div] at he
    exact hvθ he
  have hq0 : d.Ξ (criticalArcRoot ε 0) ≠ 0 := by
    intro hz
    have he := h0point.2
    rw [hz,mul_zero,zero_div] at he
    exact hv0 he
  have hcn : (d.c:ℂ) ≠ 0 := by exact_mod_cast d.c_pos.ne'
  have hlog : Real.log ‖universalV P (criticalRayPoint ε θ)/universalV P (criticalRayPoint ε 0)‖=
      (d.logXi (criticalArcRoot ε (θ:ℂ))).re-(d.logXi (criticalArcRoot ε 0)).re+
        Real.log (Real.sqrt ε)-Real.log ‖criticalArcRoot ε (θ:ℂ)‖ := by
    rw [hθpoint.2,h0point.2,log_norm_normalized_pole_ratio _ _ _ _ _ hcn hqθ hq0 htθ ht0]
    rw [criticalArcRoot_zero ε hεp.le,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg ε)]
    rfl
  have hcor := hcorr ε ⟨hεp,hε.2.trans_le hεa'⟩ θ (hθ.trans hδa')
  have hlead := criticalArcRoot_log_norm_ratio ε hεp hεh θ (hθ.trans hδ1)
  have hlogBound : Real.log ‖universalV P (criticalRayPoint ε θ)/universalV P (criticalRayPoint ε 0)‖ ≤
      (-1/8:ℝ)*Real.log (1+θ^2/(4*ε^2)) := by
    rw [hlog]
    linarith [le_abs_self ((d.logXi (criticalArcRoot ε (θ:ℂ))).re-(d.logXi (criticalArcRoot ε 0)).re)]
  rw [←h0z]
  have hnormp : 0 < ‖universalV P (criticalRayPoint ε θ)/universalV P (criticalRayPoint ε 0)‖ :=
    norm_pos_iff.mpr (div_ne_zero hvθ hv0)
  rw [←Real.exp_log hnormp,Real.rpow_eq_pow,Real.rpow_def_of_pos (by positivity : 0 < 1+θ^2/(4*ε^2))]
  exact Real.exp_le_exp.mpr (by nlinarith)
end WP.Analysis
