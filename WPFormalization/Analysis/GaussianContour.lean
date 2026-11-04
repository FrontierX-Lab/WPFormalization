import WPFormalization.Analysis.GaussianModelRemainder
import Mathlib.Analysis.Complex.HasPrimitives
/-! Finite analytic substitutions reduce exactly to two straight endpoint connectors. The proof uses Mathlib holomorphic primitives on a disk and real FTC. Uniform connector estimates retain the genuine quadratic phase and segment lengths; no contour-deformation assumption is added. -/
noncomputable section
open Set MeasureTheory
namespace WP.Analysis
lemma complex_square_re_lower_near_real (z:ℂ) (b:ℝ)
    (hz:‖z-(b:ℂ)‖ ≤ |b|/4) : b^2/2 ≤ (z^2).re := by
  have hRe:|z.re-b| ≤ ‖z-(b:ℂ)‖ := by simpa only [Complex.sub_re,Complex.ofReal_re] using Complex.abs_re_le_norm (z-(b:ℂ))
  have hIm:|z.im| ≤ ‖z-(b:ℂ)‖ := by simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using Complex.abs_im_le_norm (z-(b:ℂ))
  have htri:|b| ≤ |z.re|+|z.re-b| := by
    calc _ = |z.re-(z.re-b)| := by congr 1;ring
         _ ≤ _ := abs_sub _ _
  have hr:(3/4:ℝ)*|b| ≤ |z.re| := by linarith
  have hrs:((3/4:ℝ)*|b|)^2 ≤ z.re^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (by positivity) hr 2
  have hims:z.im^2 ≤ (|b|/4)^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hIm.trans hz) 2
  simp only [pow_two,Complex.mul_re]
  nlinarith [sq_abs b]

def complexSegmentIntegral (f:ℂ → ℂ) (a b:ℂ):ℂ :=
  ∫t:ℝ in (0)..1,f (a+(t:ℂ)*(b-a))*(b-a)

lemma complexSegmentIntegral_norm_le (f:ℂ → ℂ) (a b:ℂ) (M:ℝ) (_hM:0 ≤ M)
    (hbound:∀t ∈ Icc (0:ℝ) 1,‖f (a+(t:ℂ)*(b-a))‖ ≤ M) :
    ‖complexSegmentIntegral f a b‖ ≤ M*‖b-a‖ := by
  unfold complexSegmentIntegral
  have hb:∀t ∈ Icc (0:ℝ) 1,‖f (a+(t:ℂ)*(b-a))*(b-a)‖ ≤ M*‖b-a‖ := by
    intro t ht
    rw[norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _)
  have h:=intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0:ℝ)) (b:=1) (C:=M*‖b-a‖) (by
    intro t ht
    have ht':t ∈ Ioc (0:ℝ) 1 := by simpa only [uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using ht
    exact hb t ⟨ht'.1.le,ht'.2⟩)
  simpa using h

lemma gaussian_connector_norm_bound (f:ℂ → ℂ) (h M:ℝ) (hh:0<h) (hM:0 ≤ M)
    (b:ℝ) (e:ℂ) (he:‖e‖ ≤ |b|/4)
    (hbound:∀t ∈ Icc (0:ℝ) 1,‖f ((b:ℂ)+(t:ℂ)*e)‖ ≤ M) :
    ‖complexSegmentIntegral (fun z:ℂ=>Complex.exp (-(h:ℂ)/2*z^2)*f z) (b:ℂ) ((b:ℂ)+e)‖ ≤
      M*Real.exp (-(h/4)*b^2)*‖e‖ := by
  have hp(t:ℝ)(ht:t ∈ Icc (0:ℝ) 1):
      b^2/2 ≤ (((b:ℂ)+(t:ℂ)*e)^2).re := by
    apply complex_square_re_lower_near_real
    simp only [add_sub_cancel_left,norm_mul,Complex.norm_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg e)).trans (by simpa using he)
  have hb:∀t ∈ Icc (0:ℝ) 1,
      ‖Complex.exp (-(h:ℂ)/2*((b:ℂ)+(t:ℂ)*e)^2)*f ((b:ℂ)+(t:ℂ)*e)‖ ≤ M*Real.exp (-(h/4)*b^2) := by
    intro t ht
    rw[norm_mul,Complex.norm_exp]
    have hexp:(-(h:ℂ)/2*((b:ℂ)+(t:ℂ)*e)^2).re ≤ -(h/4)*b^2 := by
      simp only [Complex.mul_re,Complex.div_ofNat_re,Complex.neg_re,Complex.ofReal_re,
        Complex.div_ofNat_im,Complex.neg_im,Complex.ofReal_im]
      nlinarith [hp t ht]
    calc _ ≤ Real.exp (-(h/4)*b^2)*M := mul_le_mul (Real.exp_le_exp.mpr hexp)
          (hbound t ht) (norm_nonneg _) (Real.exp_pos _).le
         _ = _ := by ring
  have hseg:=complexSegmentIntegral_norm_le
    (fun z:ℂ=>Complex.exp (-(h:ℂ)/2*z^2)*f z) (b:ℂ) ((b:ℂ)+e)
    (M*Real.exp (-(h/4)*b^2)) (by positivity)
    (by simpa only [add_sub_cancel_left] using hb)
  simpa only [add_sub_cancel_left] using hseg
lemma complex_curve_integral_primitive (F f:ℂ → ℂ) (γ γ':ℝ → ℂ) (a b:ℝ)
    (hγ:∀t ∈ uIcc a b,HasDerivAt γ (γ' t) t)
    (hF:∀t ∈ uIcc a b,HasDerivAt F (f (γ t)) (γ t))
    (hi:IntervalIntegrable (fun t=>f (γ t)*γ' t) volume a b) :
    (∫t:ℝ in a..b,f (γ t)*γ' t)=F (γ b)-F (γ a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
  intro t ht
  convert! (hF t ht).scomp t (hγ t ht) using 1
  change f (γ t)*γ' t=γ' t*f (γ t)
  ring

lemma complexSegmentIntegral_primitive (F f:ℂ → ℂ) (a b:ℂ)
    (hF:∀t ∈ Icc (0:ℝ) 1,HasDerivAt F (f (a+(t:ℂ)*(b-a))) (a+(t:ℂ)*(b-a)))
    (hc:ContinuousOn (fun t:ℝ=>f (a+(t:ℂ)*(b-a))) (Icc (0:ℝ) 1)) :
    complexSegmentIntegral f a b=F b-F a := by
  have hp(t:ℝ):HasDerivAt (fun t:ℝ=>a+(t:ℂ)*(b-a)) (b-a) t := by
    convert! (Complex.ofRealCLM.hasDerivAt.mul_const (b-a)).const_add a using 1
    simp
  have hi:IntervalIntegrable (fun t:ℝ=>f (a+(t:ℂ)*(b-a))*(b-a)) volume 0 1 :=
    (hc.mul_const (b-a)).intervalIntegrable_of_Icc (by norm_num)
  have he:=complex_curve_integral_primitive F f (fun t:ℝ=>a+(t:ℂ)*(b-a)) (fun _=>b-a) 0 1
    (fun t ht=>hp t) (fun t ht=>hF t (by simpa only [uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using ht)) hi
  simpa only [complexSegmentIntegral,Complex.ofReal_zero,Complex.ofReal_one,zero_mul,add_zero,one_mul,add_sub_cancel] using he
lemma finite_analytic_substitution_contour (f U:ℂ → ℂ) (r R S:ℝ) (a b:ℂ)
    (hr:0<r) (hrR:r<R) (hrS:r<S)
    (hf:DifferentiableOn ℂ f (Metric.ball 0 S))
    (hU:DifferentiableOn ℂ U (Metric.ball 0 R))
    (hmap:MapsTo U (Metric.ball 0 R) (Metric.ball 0 S))
    (ha:‖a‖<R) (hb:‖b‖<R) (hUa:U a=(-(r:ℂ))) (hUb:U b=(r:ℂ)) :
    (∫u:ℝ in (-r)..r,f (u:ℂ))-
      (∫w:ℝ in (-r)..r,f (U (w:ℂ))*deriv U (w:ℂ))=
      complexSegmentIntegral (fun w:ℂ=>f (U w)*deriv U w) (r:ℂ) b-
        complexSegmentIntegral (fun w:ℂ=>f (U w)*deriv U w) (-(r:ℂ)) a := by
  obtain ⟨F,hF⟩:=hf.isExactOn_ball
  let g:ℂ → ℂ:=fun w=>f (U w)*deriv U w
  have hUat(w:ℂ)(hw:w ∈ Metric.ball (0:ℂ) R):AnalyticAt ℂ U w :=
    hU.analyticAt (Metric.isOpen_ball.mem_nhds hw)
  have hprim(w:ℂ)(hw:w ∈ Metric.ball (0:ℂ) R):
      HasDerivAt (fun w:ℂ=>F (U w)) (g w) w := by
    exact (hF (U w) (hmap hw)).comp w (hUat w hw).differentiableAt.hasDerivAt
  have hgc:ContinuousOn g (Metric.ball (0:ℂ) R) := by
    intro w hw
    have hfw:=hf.differentiableAt (Metric.isOpen_ball.mem_nhds (hmap hw))
    exact ((hfw.continuousAt.comp (hUat w hw).continuousAt).mul
      (hUat w hw).deriv.continuousAt).continuousWithinAt
  have hreal (T:ℝ)(hT:r<T)(u:ℝ)(hu:u ∈ Icc (-r) r):(u:ℂ) ∈ Metric.ball (0:ℂ) T := by
    rw [Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs]
    exact (abs_le.mpr ⟨by linarith [hu.1],hu.2⟩).trans_lt hT
  have hfr:ContinuousOn (fun u:ℝ=>f (u:ℂ)) (Icc (-r) r) :=
    hf.continuousOn.comp Complex.continuous_ofReal.continuousOn (hreal S hrS)
  have hgr:ContinuousOn (fun u:ℝ=>g (u:ℂ)) (Icc (-r) r) :=
    hgc.comp Complex.continuous_ofReal.continuousOn (hreal R hrR)
  have ho:(∫u:ℝ in (-r)..r,f (u:ℂ))=F (r:ℂ)-F (-(r:ℂ)) := by
    have he:=complex_curve_integral_primitive F f (fun u:ℝ=>(u:ℂ)) (fun _=>1) (-r) r
      (fun u hu=>Complex.ofRealCLM.hasDerivAt)
      (fun u hu=>hF (u:ℂ) (hreal S hrS u (by simpa only [uIcc_of_le (by linarith: -r ≤ r)] using hu)))
      (by simpa only [mul_one] using hfr.intervalIntegrable_of_Icc (by linarith))
    simpa only [mul_one,Complex.ofReal_neg] using he
  have hn:(∫u:ℝ in (-r)..r,g (u:ℂ))=F (U (r:ℂ))-F (U (-(r:ℂ))) := by
    have he:=complex_curve_integral_primitive (fun w:ℂ=>F (U w)) g (fun u:ℝ=>(u:ℂ)) (fun _=>1) (-r) r
      (fun u hu=>Complex.ofRealCLM.hasDerivAt)
      (fun u hu=>hprim (u:ℂ) (hreal R hrR u (by simpa only [uIcc_of_le (by linarith: -r ≤ r)] using hu)))
      (by simpa only [mul_one] using hgr.intervalIntegrable_of_Icc (by linarith))
    simpa only [mul_one,Complex.ofReal_neg] using he
  have hseg (c e:ℂ)(hc:‖c‖<R)(he:‖e‖<R):
      complexSegmentIntegral g c e=F (U e)-F (U c) := by
    have hcv:Convex ℝ (Metric.ball (0:ℂ) R):=convex_ball _ _
    have hpoint(t:ℝ)(ht:t ∈ Icc (0:ℝ) 1):c+(t:ℂ)*(e-c) ∈ Metric.ball (0:ℂ) R := by
      have hp:=hcv.add_smul_sub_mem (Metric.mem_ball.mpr (by simpa only[dist_zero_right] using hc))
        (Metric.mem_ball.mpr (by simpa only[dist_zero_right] using he)) ht
      simpa only [Complex.real_smul] using hp
    apply complexSegmentIntegral_primitive (fun w:ℂ=>F (U w)) g c e
    · intro t ht
      exact hprim _ (hpoint t ht)
    · have hm:Continuous (fun t:ℝ=>c+(t:ℂ)*(e-c)) := by fun_prop
      exact hgc.comp hm.continuousOn hpoint
  have hpos:‖(r:ℂ)‖<R := by rw [Complex.norm_of_nonneg hr.le];exact hrR
  have hneg:‖-(r:ℂ)‖<R := by rw[norm_neg];exact hpos
  change (∫u:ℝ in (-r)..r,f (u:ℂ))-(∫w:ℝ in (-r)..r,g (w:ℂ))=
    complexSegmentIntegral g (r:ℂ) b-complexSegmentIntegral g (-(r:ℂ)) a
  rw [ho,hn,hseg _ _ hpos hb,hseg _ _ hneg ha,hUa,hUb]
  ring
end WP.Analysis
