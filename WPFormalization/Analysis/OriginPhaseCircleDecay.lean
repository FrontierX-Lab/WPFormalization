import WPFormalization.Volumes.CriticalMorseNormalization
/-! A genuine analytic phase with real derivative 2 at the origin has a
uniform full-circle decay bound on positive small radii. A joint quadratic
Taylor remainder and the actual right real trace prove this directly;
no coefficient positivity or new classical input is assumed. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma complex_analytic_uniform_linear_remainder (S:ℂ→ℂ)(hS:AnalyticAt ℂ S 0):
    ∃R C:ℝ,0<R ∧ 0<C ∧ ∀x z:ℂ,‖x‖<R→‖z‖<R→
      ‖S z-S x-deriv S x*(z-x)‖≤C*‖z-x‖^2:=by
  let F:ℂ × ℂ→ℂ:=fun p=>S (p.1+p.2)-S p.1-deriv S p.1*p.2
  have hF:AnalyticAt ℂ F (0,0):=by
    have ha:AnalyticAt ℂ (fun p:ℂ × ℂ=>S (p.1+p.2)) (0,0):=
      AnalyticAt.comp (f:=fun p:ℂ × ℂ=>p.1+p.2) (x:=(0,0)) (by simpa using hS)
        (analyticAt_fst.add analyticAt_snd)
    have hb:AnalyticAt ℂ (fun p:ℂ × ℂ=>S p.1) (0,0):=AnalyticAt.comp (f:=fun p:ℂ × ℂ=>p.1) (x:=(0,0)) hS analyticAt_fst
    have hc:AnalyticAt ℂ (fun p:ℂ × ℂ=>deriv S p.1) (0,0):=AnalyticAt.comp (f:=fun p:ℂ × ℂ=>p.1) (x:=(0,0)) hS.deriv analyticAt_fst
    exact (ha.sub hb).sub (hc.mul analyticAt_snd)
  have haxis:∀ᶠx:ℂ in 𝓝 0,F (x,0)=0:=by
    exact Filter.Eventually.of_forall (fun x=>by simp[F])
  have hderiv:∀ᶠx:ℂ in 𝓝 0,deriv (fun w:ℂ=>F (x,w)) 0=0:=by
    filter_upwards[hS.eventually_analyticAt] with x hx
    have hshift:HasDerivAt (fun w:ℂ=>S (x+w)) (deriv S x) 0:=by
      have ht:HasDerivAt (fun w:ℂ=>x+w) 1 0:=by simpa using (hasDerivAt_id 0).const_add x
      have hs:HasDerivAt S (deriv S x) (x+0):=by simpa using hx.differentiableAt.hasDerivAt
      convert! hs.comp 0 ht using 1 <;>first | rfl | simp only[mul_one]
    have hlin:HasDerivAt (fun w:ℂ=>deriv S x*w) (deriv S x) 0:=by
      convert (hasDerivAt_id 0).const_mul (deriv S x) using 1 <;>simp
    have hd:=((hshift.sub_const (S x)).sub hlin).deriv
    convert! hd using 1 <;>simp only[F,Pi.sub_apply,sub_self]
  obtain ⟨R,C,hR,hC,hbound⟩:=analytic_parameter_quadratic_bound F hF haxis hderiv
  refine ⟨R/3,C,by positivity,hC,?_⟩
  intro x z hx hz
  have hd:‖z-x‖<R:=(norm_sub_le _ _).trans_lt (by linarith)
  have ht:=hbound x (z-x) (by linarith) hd
  simpa only[F,add_sub_cancel] using ht

lemma derivative_im_zero_of_real_interval (S:ℂ→ℂ)(R x:ℝ)(hR:0<R)
    (hSa:AnalyticAt ℂ S (x:ℂ))(hx:x∈Ioo (0:ℝ) R)
    (hreal:∀t∈Ioo (0:ℝ) R,(S (t:ℂ)).im=0):
    (deriv S (x:ℂ)).im=0:=by
  have hd:HasDerivAt (fun t:ℝ=>(S (t:ℂ)).im) (deriv S (x:ℂ)).im x:=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hSa.differentiableAt.hasDerivAt.comp_ofReal
  have he:(fun t:ℝ=>(S (t:ℂ)).im)=ᶠ[𝓝 x] (fun _=>0):=by
    filter_upwards[isOpen_Ioo.mem_nhds hx] with t ht
    exact hreal t ht
  have hh:HasDerivAt (fun _:ℝ=>0) (deriv S (x:ℂ)).im x:=
    hd.congr_of_eventuallyEq he.symm
  exact hh.unique (hasDerivAt_const x 0)

lemma complex_circle_difference_sq (x:ℝ)(θ:ℝ):
    ‖(x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)-(x:ℂ)‖^2=2*x^2*(1-Real.cos θ):=by
  rw[Complex.sq_norm,Complex.normSq_apply]
  simp only[Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero,Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  nlinarith[Real.sin_sq_add_cos_sq θ]

lemma origin_phase_circle_decay_of_real_germ (S:ℂ→ℂ)(hS:AnalyticAt ℂ S 0)
    (hd:deriv S 0=(2:ℂ))
    (hreal:∀ᶠx:ℝ in 𝓝 0,0≤x→(S (x:ℂ)).im=0):
    ∃r:ℝ,0<r ∧ ∀x∈Ioo (0:ℝ) r,∀θ:ℝ,
      (S ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))-S (x:ℂ)).re≤
        -(x/2)*(1-Real.cos θ):=by
  obtain ⟨R,C,hR,hC,hrem⟩:=complex_analytic_uniform_linear_remainder S hS
  have hnear:∀ᶠz:ℂ in 𝓝 0,AnalyticAt ℂ S z ∧ 1<(deriv S z).re:=by
    have hc:ContinuousAt (fun z:ℂ=>(deriv S z).re) 0:=Complex.continuous_re.continuousAt.comp hS.deriv.continuousAt
    have hv:1<(deriv S 0).re:=by rw[hd];norm_num
    exact hS.eventually_analyticAt.and (hc.tendsto.eventually (eventually_gt_nhds hv))
  obtain ⟨Ra,hRa,hball⟩:=Metric.eventually_nhds_iff.mp hnear
  obtain ⟨Rr,hRr,hrball⟩:=Metric.eventually_nhds_iff.mp hreal
  let r:ℝ:=min R (min Ra (min Rr (1/(4*C))))
  have hr:0<r:=lt_min hR (lt_min hRa (lt_min hRr (by positivity)))
  have hrR:r≤R:=min_le_left _ _
  have hrRa:r≤Ra:=(min_le_right _ _).trans (min_le_left _ _)
  have hrRr:r≤Rr:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrC:r≤1/(4*C):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hreal':∀t∈Ioo (0:ℝ) r,(S (t:ℂ)).im=0:=by
    intro t ht
    exact hrball (by rw[Real.dist_eq,sub_zero,abs_of_pos ht.1];exact ht.2.trans_le hrRr) ht.1.le
  refine ⟨r,hr,?_⟩
  intro x hx θ
  let z:ℂ:=(x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)
  have hxn:‖(x:ℂ)‖=x:=Complex.norm_of_nonneg hx.1.le
  have hzn:‖z‖=x:=by simp only[z,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,hxn]
  have hnx:dist (x:ℂ) 0<Ra:=by rw[dist_zero_right,hxn];exact hx.2.trans_le hrRa
  have ha:=hball hnx
  have him:=derivative_im_zero_of_real_interval S r x hr ha.1 hx hreal'
  have hb:=hrem (x:ℂ) z (by rw[hxn];exact hx.2.trans_le hrR) (by rw[hzn];exact hx.2.trans_le hrR)
  have hre:((S z-S (x:ℂ))-deriv S (x:ℂ)*(z-(x:ℂ))).re≤C*‖z-(x:ℂ)‖^2:=
    (Complex.re_le_norm _).trans hb
  have hsquare:=complex_circle_difference_sq x θ
  have hmul:(deriv S (x:ℂ)*(z-(x:ℂ))).re=
      -(deriv S (x:ℂ)).re*x*(1-Real.cos θ):=by
    dsimp[z]
    simp only[Complex.mul_re,Complex.sub_re,Complex.ofReal_re,Complex.ofReal_im,him,zero_mul,sub_zero]
    rw[Complex.exp_ofReal_mul_I_re]
    ring
  rw[Complex.sub_re,hmul,hsquare] at hre
  have hd0:0≤1-Real.cos θ:=sub_nonneg.mpr (Real.cos_le_one θ)
  have hCx:4*C*x≤1:=by
    have ht:=(le_div_iff₀ (by positivity:0<4*C)).mp (hx.2.le.trans hrC)
    nlinarith
  have hfirst:-(deriv S (x:ℂ)).re*x*(1-Real.cos θ)≤-x*(1-Real.cos θ):=by
    nlinarith[mul_nonneg hx.1.le hd0,mul_le_mul_of_nonneg_right ha.2.le (mul_nonneg hx.1.le hd0)]
  have hlast:2*C*x^2*(1-Real.cos θ)≤(x/2)*(1-Real.cos θ):=by
    nlinarith[mul_le_mul_of_nonneg_right hCx (mul_nonneg hx.1.le hd0)]
  change (S z).re-(S (x:ℂ)).re- _≤_ at hre
  change (S z).re-(S (x:ℂ)).re≤_
  nlinarith
end WP.Analysis
