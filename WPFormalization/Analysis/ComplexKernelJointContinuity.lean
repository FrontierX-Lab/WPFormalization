import WPFormalization.Analysis.KernelJetComplexification
import WPFormalization.Analysis.ParameterDerivative
/-! The genuine removable normalized kernels are jointly continuous in the
complex parameter and kernel variable. A real-segment fundamental theorem
formula removes the critical parameter singularity uniformly in the kernel
variable. Compact integral calculus then yields joint continuity and entire
w-dependence of the first-root deflation. No uniform complex coefficient
bound is assumed in this construction. -/
set_option maxHeartbeats 800000
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace WP.Analysis

def kernelDividedDifference (B : ℂ → ℂ → ℂ) (z u : ℂ) : ℂ :=
  ∫ t : ℝ in (0)..1,deriv (B z) ((t:ℂ)*u)

lemma entire_increment_integral (f : ℂ → ℂ) (hf : Differentiable ℂ f) (u : ℂ) :
    f u=f 0+u*(∫ t : ℝ in (0)..1,deriv f ((t:ℂ)*u)) := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => f ((s:ℂ)*u))
      (u*deriv f ((t:ℂ)*u)) t := by
    have hc : HasDerivAt (fun s : ℂ => f (s*u)) (u*deriv f ((t:ℂ)*u)) (t:ℂ) := by
      convert (hf ((t:ℂ)*u)).hasDerivAt.comp (t:ℂ) ((hasDerivAt_id (t:ℂ)).mul_const u) using 1 <;> first | rfl | (funext s; simp only [Function.comp_apply,id_eq]; congr 1; ring) | ring
    exact hc.comp_ofReal
  have hc : Continuous (fun t : ℝ => u*deriv f ((t:ℂ)*u)) := by
    have hc' : Continuous (deriv f) := hf.deriv.continuous
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=(0:ℝ)) (b:=1)
    (fun t _ => hd t) (hc.intervalIntegrable 0 1)
  simp only [Complex.ofReal_one,Complex.ofReal_zero,one_mul,zero_mul] at h
  rw [intervalIntegral.integral_const_mul] at h
  linear_combination -h

lemma K_jet_prod_contDiff_one (j : ℕ) :
    ContDiff ℂ 1 (fun p : ℂ × ℂ => iteratedDeriv j (K p.1) p.2) := by
  have he : (fun p : ℂ × ℂ => iteratedDeriv j (K p.1) p.2)=
      (fun p => ∫ s : ℝ in (0)..1,((1-(s:ℂ)^2)/2)^j*
        iteratedDeriv (j+1) X (p.1+p.2/2*(1-(s:ℂ)^2))) :=
    funext (fun p => iteratedDeriv_K_integral j p.1 p.2)
  rw [he]
  exact kernel_moment_prod_contDiff_one _ (by fun_prop) _ (iteratedDeriv_X_differentiable (j+1))

lemma H_jet_prod_contDiff_one (j : ℕ) :
    ContDiff ℂ 1 (fun p : ℂ × ℂ => iteratedDeriv j (H p.1) p.2) := by
  have he : (fun p : ℂ × ℂ => iteratedDeriv j (H p.1) p.2)=
      (fun p => 3*(∫ s : ℝ in (0)..1,(s:ℂ)^2*((1-(s:ℂ)^2)/2)^j*
        iteratedDeriv (j+1) X (p.1+p.2/2*(1-(s:ℂ)^2)))) :=
    funext (fun p => iteratedDeriv_H_integral j p.1 p.2)
  rw [he]
  exact contDiff_const.mul (kernel_moment_prod_contDiff_one _ (by fun_prop) _ (iteratedDeriv_X_differentiable (j+1)))

lemma kernelDividedDifference_joint_continuous (B : ℂ → ℂ → ℂ)
    (hB : Continuous (fun p : ℂ × ℂ => deriv (B p.1) p.2)) :
    Continuous (fun p : ℂ × ℂ => kernelDividedDifference B p.1 p.2) := by
  have hF : Continuous (fun p : (ℂ × ℂ) × ℝ => deriv (B p.1.1) ((p.2:ℂ)*p.1.2)) :=
    hB.comp (continuous_fst.fst.prodMk ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_fst.snd))
  have hi := continuous_parametric_integral_of_continuous
    (X:=ℂ × ℂ) (Y:=ℝ) (E:=ℂ) (f:=fun p t => deriv (B p.1) ((t:ℂ)*p.2))
    (μ:=volume) hF (s:=Icc (0:ℝ) 1) isCompact_Icc
  convert hi using 1
  funext p
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one]
  rfl

def alternativeNormalizedKernel (B : ℂ → ℂ → ℂ) (R : ℂ → ℂ) (z w : ℂ) : ℂ :=
  1+rootPowerFactor R 1 z*w*kernelDividedDifference B z (R z*w)

lemma alternativeNormalizedKernel_continuousAt (Ω : Set ℂ) (hΩ : IsOpen Ω) (hc : (y₀:ℂ)∈Ω)
    (B : ℂ → ℂ → ℂ) (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R Ω)
    (hunit : ∀ z∈Ω,complexAUnit z≠0)
    (hB : Continuous (fun p : ℂ × ℂ => deriv (B p.1) p.2)) (w z : ℂ) (hz : z∈Ω) :
    ContinuousAt (fun ζ => alternativeNormalizedKernel B R ζ w) z := by
  have hP := (rootPowerFactor_analyticOnNhd Ω hΩ hc R hR hunit 1 z hz).continuousAt
  have hRc := (hR z hz).continuousAt
  exact continuousAt_const.add ((hP.mul continuousAt_const).mul
    ((kernelDividedDifference_joint_continuous B hB).continuousAt.comp
      (continuousAt_id.prodMk (hRc.mul continuousAt_const))))

lemma alternativeNormalizedKernel_joint_continuous (Ω : Set ℂ) (hΩ : IsOpen Ω) (hc : (y₀:ℂ)∈Ω)
    (B : ℂ → ℂ → ℂ) (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R Ω)
    (hunit : ∀ z∈Ω,complexAUnit z≠0)
    (hB : Continuous (fun p : ℂ × ℂ => deriv (B p.1) p.2)) :
    Continuous (fun p : Ω × ℂ => alternativeNormalizedKernel B R (p.1:ℂ) p.2) := by
  have hP : Continuous (fun z : Ω => rootPowerFactor R 1 (z:ℂ)) :=
    continuousOn_iff_continuous_restrict.mp (rootPowerFactor_analyticOnNhd Ω hΩ hc R hR hunit 1).continuousOn
  have hRc : Continuous (fun z : Ω => R (z:ℂ)) := continuousOn_iff_continuous_restrict.mp hR.continuousOn
  exact continuous_const.add (((hP.comp continuous_fst).mul continuous_snd).mul
    ((kernelDividedDifference_joint_continuous B hB).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk ((hRc.comp continuous_fst).mul continuous_snd))))

lemma regularizedKernel_eq_raw_off_critical (B : ℂ → ℂ → ℂ) (R : ℂ → ℂ)
    (hB0 : ∀ z : ℂ,B z 0=deriv X z) (hR0 : R (y₀:ℂ)=0)
    (z w : ℂ) (hz : z≠(y₀:ℂ)) (hunit : complexAUnit z≠0) :
    regularizedKernel B R z w=B z (R z*w)/deriv X z := by
  have hN0 : B (y₀:ℂ) (R (y₀:ℂ)*w)=0 := by rw [hR0,zero_mul,hB0,derivX_y₀_zero]
  have hδ : z-(y₀:ℂ)≠0 := sub_ne_zero.mpr hz
  unfold regularizedKernel
  rw [dslope_of_ne _ hz]
  simp only [slope,vsub_eq_sub,smul_eq_mul,hN0,sub_zero]
  rw [←complexAUnit_factor z]
  field_simp [hδ,hunit]

lemma alternativeNormalizedKernel_eq_raw_off_critical (B : ℂ → ℂ → ℂ) (R : ℂ → ℂ)
    (hB0 : ∀ z : ℂ,B z 0=deriv X z) (hR0 : R (y₀:ℂ)=0)
    (hBD : ∀ z : ℂ,Differentiable ℂ (B z))
    (z w : ℂ) (hz : z≠(y₀:ℂ)) (hunit : complexAUnit z≠0) :
    alternativeNormalizedKernel B R z w=B z (R z*w)/deriv X z := by
  have hδ : z-(y₀:ℂ)≠0 := sub_ne_zero.mpr hz
  have ha : deriv X z≠0 := by rw [←complexAUnit_factor z];exact mul_ne_zero hδ hunit
  have h : B z (R z*w)=deriv X z+R z*w*kernelDividedDifference B z (R z*w) := by
    simpa only [kernelDividedDifference,hB0] using entire_increment_integral (B z) (hBD z) (R z*w)
  unfold alternativeNormalizedKernel
  rw [rootPowerFactor_scale R 1 le_rfl hR0 z hz hunit,pow_one,h]
  field_simp [ha] <;> ring
lemma regularizedKernel_eq_alternative (Ω : Set ℂ) (hΩ : IsOpen Ω) (hc : (y₀:ℂ)∈Ω)
    (B : ℂ → ℂ → ℂ) (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R Ω) (hR0 : R (y₀:ℂ)=0)
    (hunit : ∀ z∈Ω,complexAUnit z≠0) (hB0 : ∀ z : ℂ,B z 0=deriv X z)
    (hBD : ∀ z : ℂ,Differentiable ℂ (B z))
    (hBJ : Continuous (fun p : ℂ × ℂ => deriv (B p.1) p.2))
    (hcurve : ∀ w : ℂ,AnalyticOnNhd ℂ (fun z => B z (R z*w)) Ω)
    (z : ℂ) (hz : z∈Ω) (w : ℂ) :
    regularizedKernel B R z w=alternativeNormalizedKernel B R z w := by
  by_cases he : z=(y₀:ℂ)
  · subst z
    have hA := alternativeNormalizedKernel_continuousAt Ω hΩ hc B R hR hunit hBJ w y₀ hc
    have hG := regularizedKernel_analyticOnNhd Ω hΩ hc B R hcurve hunit w (y₀:ℂ) hc
    have hmap : Tendsto (fun Y : ℝ => (Y:ℂ)) (𝓝[<] y₀) (𝓝 (y₀:ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have heq : (fun Y : ℝ => alternativeNormalizedKernel B R (Y:ℂ) w)=ᶠ[𝓝[<] y₀]
        (fun Y => regularizedKernel B R (Y:ℂ) w) := by
      filter_upwards [hmap.eventually (hΩ.mem_nhds hc), self_mem_nhdsWithin] with Y hYU hY
      have hYne : (Y:ℂ)≠(y₀:ℂ) := by exact_mod_cast ne_of_lt hY
      exact (alternativeNormalizedKernel_eq_raw_off_critical B R hB0 hR0 hBD _ w hYne (hunit _ hYU)).trans
        (regularizedKernel_eq_raw_off_critical B R hB0 hR0 _ w hYne (hunit _ hYU)).symm
    exact (tendsto_nhds_unique (hA.tendsto.comp hmap) ((hG.continuousAt.tendsto.comp hmap).congr' heq.symm)).symm
  · exact (regularizedKernel_eq_raw_off_critical B R hB0 hR0 z w he (hunit z hz)).trans
      (alternativeNormalizedKernel_eq_raw_off_critical B R hB0 hR0 hBD z w he (hunit z hz)).symm

lemma normalized_complex_kernels_joint_continuous (Ω : Set ℂ) (hΩ : IsOpen Ω) (hc : (y₀:ℂ)∈Ω)
    (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R Ω) (hR0 : R (y₀:ℂ)=0)
    (hunit : ∀ z∈Ω,complexAUnit z≠0) :
    Continuous (fun p : Ω × ℂ => regularizedKernel K R (p.1:ℂ) p.2) ∧
      Continuous (fun p : Ω × ℂ => regularizedKernel H R (p.1:ℂ) p.2) := by
  have hKJ : Continuous (fun p : ℂ × ℂ => deriv (K p.1) p.2) := by
    simpa only [iteratedDeriv_one] using (K_jet_prod_contDiff_one 1).continuous
  have hHJ : Continuous (fun p : ℂ × ℂ => deriv (H p.1) p.2) := by
    simpa only [iteratedDeriv_one] using (H_jet_prod_contDiff_one 1).continuous
  constructor
  · apply (alternativeNormalizedKernel_joint_continuous Ω hΩ hc K R hR hunit hKJ).congr
    intro p
    exact (regularizedKernel_eq_alternative Ω hΩ hc K R hR hR0 hunit K_zero K_differentiable hKJ
      (K_root_curve_analyticOnNhd Ω R hR) _ p.1.property p.2).symm
  · apply (alternativeNormalizedKernel_joint_continuous Ω hΩ hc H R hR hunit hHJ).congr
    intro p
    exact (regularizedKernel_eq_alternative Ω hΩ hc H R hR hR0 hunit H_zero H_differentiable hHJ
      (H_root_curve_analyticOnNhd Ω R hR) _ p.1.property p.2).symm

lemma normalized_complex_kernels_entire (Ω : Set ℂ) (hΩ : IsOpen Ω) (hc : (y₀:ℂ)∈Ω)
    (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R Ω) (hR0 : R (y₀:ℂ)=0)
    (hraw : ∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) (hunit : ∀ z∈Ω,complexAUnit z≠0) :
    ∀ z∈Ω,Differentiable ℂ (fun w => regularizedKernel K R z w) ∧
      Differentiable ℂ (fun w => regularizedKernel H R z w) := by
  intro z hz
  by_cases he : z=(y₀:ℂ)
  · subst z
    have hK (w : ℂ) := regularizedK_critical R hR0 hraw w
      (regularizedKernel_analyticOnNhd Ω hΩ hc K R (K_root_curve_analyticOnNhd Ω R hR) hunit w _ hc)
    have hH (w : ℂ) := regularizedH_critical R hR0 hraw w
      (regularizedKernel_analyticOnNhd Ω hΩ hc H R (H_root_curve_analyticOnNhd Ω R hR) hunit w _ hc)
    rw [show (fun w => regularizedKernel K R (y₀:ℂ) w)=(fun w => 1-w) from funext hK,
      show (fun w => regularizedKernel H R (y₀:ℂ) w)=(fun w => 1-(3/5:ℂ)*w) from funext hH]
    constructor <;> fun_prop
  · have hK : (fun w => regularizedKernel K R z w)=(fun w => K z (R z*w)/deriv X z) :=
      funext (fun w => regularizedKernel_eq_raw_off_critical K R K_zero hR0 z w he (hunit z hz))
    have hH : (fun w => regularizedKernel H R z w)=(fun w => H z (R z*w)/deriv X z) :=
      funext (fun w => regularizedKernel_eq_raw_off_critical H R H_zero hR0 z w he (hunit z hz))
    rw [hK,hH]
    exact ⟨((K_differentiable z).comp ((differentiable_const (R z)).mul differentiable_id)).div_const _,
      ((H_differentiable z).comp ((differentiable_const (R z)).mul differentiable_id)).div_const _⟩
lemma firstRootDeflation_eq_neg_dslope (f : ℂ → ℂ) (hf : Differentiable ℂ f) (w : ℂ) :
    -(∫ t : ℝ in (0)..1,deriv f (1+(t:ℂ)*(w-1))) = -dslope f 1 w := by
  by_cases hw : w=1
  · subst w
    simp
  · have hd (t : ℝ) : HasDerivAt (fun u : ℝ => f (1+(u:ℂ)*(w-1)))
        ((w-1)*deriv f (1+(t:ℂ)*(w-1))) t := by
      have hh : HasDerivAt (fun u : ℂ => f (1+u*(w-1)))
          ((w-1)*deriv f (1+(t:ℂ)*(w-1))) (t:ℂ) := by
        convert (hf _).hasDerivAt.comp (t:ℂ) (((hasDerivAt_id (t:ℂ)).mul_const (w-1)).const_add 1) using 1
        · rfl
        · dsimp;ring
      exact hh.comp_ofReal
    have hc : Continuous (fun t : ℝ => (w-1)*deriv f (1+(t:ℂ)*(w-1))) := by
      have hc' := hf.deriv.continuous
      fun_prop
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=(0:ℝ)) (b:=1)
      (fun t _ => hd t) (hc.intervalIntegrable 0 1)
    simp only [Complex.ofReal_zero,Complex.ofReal_one,zero_mul,one_mul,add_zero,add_sub_cancel] at hi
    rw [intervalIntegral.integral_const_mul] at hi
    rw [dslope_of_ne f hw]
    simp only [slope,vsub_eq_sub,smul_eq_mul]
    rw [←hi]
    simp only [inv_mul_cancel_left₀ (sub_ne_zero.mpr hw)]

def complexDeflatedKernel (R : ℂ → ℂ) (z w : ℂ) : ℂ :=
  -(∫ t : ℝ in (0)..1,deriv (fun v => regularizedKernel K R z v) (1+(t:ℂ)*(w-1)))

lemma complexDeflatedKernel_joint_continuous (Ω : Set ℂ) (hΩ : IsOpen Ω) (hc : (y₀:ℂ)∈Ω)
    (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R Ω) (hR0 : R (y₀:ℂ)=0)
    (hraw : ∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) (hunit : ∀ z∈Ω,complexAUnit z≠0) :
    Continuous (fun p : Ω × ℂ => complexDeflatedKernel R (p.1:ℂ) p.2) := by
  letI : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  have hK := (normalized_complex_kernels_joint_continuous Ω hΩ hc R hR hR0 hunit).1
  have hd := parameter_derivative_joint_continuous (fun z : Ω => fun w => regularizedKernel K R (z:ℂ) w)
    (fun z => (normalized_complex_kernels_entire Ω hΩ hc R hR hR0 hraw hunit z z.property).1) hK
  have hF : Continuous (fun p : (Ω × ℂ) × ℝ =>
      deriv (fun v => regularizedKernel K R (p.1.1:ℂ) v) (1+(p.2:ℂ)*(p.1.2-1))) := by
    exact hd.comp (continuous_fst.fst.prodMk
      (continuous_const.add ((Complex.continuous_ofReal.comp continuous_snd).mul (continuous_fst.snd.sub continuous_const))))
  have hi := continuous_parametric_integral_of_continuous
    (X:=Ω × ℂ) (Y:=ℝ) (E:=ℂ)
    (f:=fun p t => deriv (fun v => regularizedKernel K R (p.1:ℂ) v) (1+(t:ℂ)*(p.2-1)))
    (μ:=volume) hF (s:=Icc (0:ℝ) 1) isCompact_Icc
  have hi' : Continuous (fun p : Ω × ℂ =>
      ∫ t : ℝ in (0)..1,deriv (fun v => regularizedKernel K R (p.1:ℂ) v) (1+(t:ℂ)*(p.2-1))) := by
    convert hi using 1
    funext p
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one]
  exact hi'.neg

lemma complexDeflatedKernel_entire (Ω : Set ℂ) (hΩ : IsOpen Ω) (hc : (y₀:ℂ)∈Ω)
    (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R Ω) (hR0 : R (y₀:ℂ)=0)
    (hraw : ∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) (hunit : ∀ z∈Ω,complexAUnit z≠0)
    (z : ℂ) (hz : z∈Ω) : Differentiable ℂ (complexDeflatedKernel R z) := by
  have he : complexDeflatedKernel R z=(fun w => -dslope (fun v => regularizedKernel K R z v) 1 w) := by
    funext w
    exact firstRootDeflation_eq_neg_dslope _
      (normalized_complex_kernels_entire Ω hΩ hc R hR hR0 hraw hunit z hz).1 w
  rw [he]
  intro w
  exact (dslope_analyticOnNhd_complex univ isOpen_univ _
    (fun w _ => ((normalized_complex_kernels_entire Ω hΩ hc R hR hR0 hraw hunit z hz).1).analyticAt w)
      1 (mem_univ _) w (mem_univ _)).differentiableAt.neg

lemma complexDeflatedKernel_restrict_closed (R : ℂ → ℂ)
    (hclosed : ∀ Y∈Icc (0:ℝ) y₀,∀ w : ℂ,regularizedKernel K R (Y:ℂ) w=barK Y w)
    (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) (w : ℂ) :
    complexDeflatedKernel R (Y:ℂ) w=deflatedBarK Y w := by
  have he : (fun v => regularizedKernel K R (Y:ℂ) v)=barK Y := funext (hclosed Y hY)
  simp only [complexDeflatedKernel,deflatedBarK,he]

lemma continuousAt_of_open_parameter_product (Ω : Set ℂ) (hΩ : IsOpen Ω) (F : ℂ → ℂ → ℂ)
    (hF : Continuous (fun p : Ω × ℂ => F (p.1:ℂ) p.2)) (z : ℂ) (hz : z∈Ω) (w : ℂ) :
    ContinuousAt (fun p : ℂ × ℂ => F p.1 p.2) (z,w) := by
  have hm : Continuous (fun p : Ω ×ˢ (univ : Set ℂ) =>
      ((⟨(p:ℂ × ℂ).1,p.property.1⟩ : Ω),(p:ℂ × ℂ).2)) := by fun_prop
  have hC : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2) (Ω ×ˢ (univ : Set ℂ)) :=
    continuousOn_iff_continuous_restrict.mpr (hF.comp hm)
  exact hC.continuousAt ((hΩ.prod isOpen_univ).mem_nhds ⟨hz,mem_univ w⟩)
end WP.Analysis
