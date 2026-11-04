import Mathlib
/-! A two-constants estimate from the proved Hadamard three-lines theorem.
The cosh strip map and its algebraic inverse give a square-root bound on
the inner disk from a real slit and a larger disk. The centered normalization
lemma is generic and supplies no generating-function or asymptotic premise. -/

noncomputable section
namespace WP.Analysis
open Set Complex
open Complex.HadamardThreeLines

lemma cosh_strip_disk_bound (z:ℂ) (hz:z.re∈Icc (0:ℝ) 1):
    ‖Complex.cosh ((Real.log 16:ℝ)*z)‖<16:=by
  have hα:0<Real.log 16:=Real.log_pos (by norm_num)
  have hre:((Real.log 16:ℂ)*z).re=Real.log 16*z.re:=by
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hup:Real.log 16*z.re≤Real.log 16:=by nlinarith[hz.2]
  have hlo:0≤Real.log 16*z.re:=mul_nonneg hα.le hz.1
  have he1:‖Complex.exp ((Real.log 16:ℂ)*z)‖≤16:=by
    rw[Complex.norm_exp,hre]
    exact (Real.exp_le_exp.mpr hup).trans_eq (Real.exp_log (by norm_num))
  have he2:‖Complex.exp (-((Real.log 16:ℂ)*z))‖≤1:=by
    rw[Complex.norm_exp,Complex.neg_re,hre]
    exact (Real.exp_le_exp.mpr (neg_nonpos.mpr hlo)).trans_eq Real.exp_zero
  rw[Complex.cosh,norm_div]
  norm_num only [Complex.norm_ofNat]
  have ht:=norm_add_le (Complex.exp ((Real.log 16:ℂ)*z)) (Complex.exp (-((Real.log 16:ℂ)*z)))
  linarith

lemma cosh_strip_left (z:ℂ) (hz:z.re=0):
    ∃t:ℝ,t∈Icc (-1:ℝ) 1 ∧ Complex.cosh ((Real.log 16:ℝ)*z)=(t:ℂ):=by
  have hze:z=(z.im:ℂ)*Complex.I:=by apply Complex.ext <;>simp[hz]
  rw[hze,←mul_assoc,←Complex.ofReal_mul,Complex.cosh_mul_I,←Complex.ofReal_cos]
  exact ⟨Real.cos (Real.log 16*z.im),⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩,rfl⟩

lemma cosh_strip_inner_preimage (w:ℂ) (hw:‖w‖≤3/2):
    ∃z:ℂ,z.re∈Icc (0:ℝ) (1/2) ∧ Complex.cosh ((Real.log 16:ℝ)*z)=w:=by
  obtain ⟨v,hv⟩:=IsAlgClosed.exists_pow_nat_eq (w^2-1) (n:=2) (by norm_num)
  have hvnorm:‖v‖≤2:=by
    have he:‖v‖^2=‖w^2-1‖:=by rw[←norm_pow,hv]
    have ht:‖w^2-1‖≤13/4:=by
      calc
        _≤‖w^2‖+‖(1:ℂ)‖:=norm_sub_le _ _
        _≤13/4:=by rw[norm_pow,norm_one];nlinarith[norm_nonneg w]
    nlinarith[norm_nonneg v]
  have hprod:(w+v)*(w-v)=1:=by
    calc
      _ = w^2-v^2:=by ring
      _ = 1:=by rw[hv];ring
  have hnormprod:‖w+v‖*‖w-v‖=1:=by rw[←norm_mul,hprod,norm_one]
  have hchoice:∃u:ℂ,1≤‖u‖ ∧ ‖u‖≤7/2 ∧ u+u⁻¹=2*w:=by
    have hsumplus:‖w+v‖≤7/2:=(norm_add_le _ _).trans (by linarith)
    have hsumminus:‖w-v‖≤7/2:=(norm_sub_le _ _).trans (by linarith)
    by_cases hbig:1≤‖w+v‖
    · refine ⟨w+v,hbig,hsumplus,?_⟩
      have hn:w+v≠0:=norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hbig)
      have hi:(w+v)⁻¹=w-v:=by
        apply mul_left_cancel₀ hn
        rw[mul_inv_cancel₀ hn,hprod]
      rw[hi];ring
    · have hb:1≤‖w-v‖:=by
        by_contra hh
        have hn1:‖w+v‖<1:=lt_of_not_ge hbig
        have hn2:‖w-v‖<1:=lt_of_not_ge hh
        nlinarith[norm_nonneg (w+v),norm_nonneg (w-v)]
      refine ⟨w-v,hb,hsumminus,?_⟩
      have hn:w-v≠0:=norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hb)
      have hi:(w-v)⁻¹=w+v:=by
        apply mul_left_cancel₀ hn
        rw[mul_inv_cancel₀ hn,mul_comm (w-v),hprod]
      rw[hi];ring
  obtain ⟨u,hu1,hu3,hue⟩:=hchoice
  have hun:u≠0:=norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hu1)
  have hα:0<Real.log 16:=Real.log_pos (by norm_num)
  let z:ℂ:=Complex.log u/(Real.log 16:ℝ)
  have hz:((Real.log 16:ℝ):ℂ)*z=Complex.log u:=by
    have hαc:((Real.log 16:ℝ):ℂ)≠0:=by exact_mod_cast hα.ne'
    dsimp[z];field_simp
  have hzr:z.re=Real.log ‖u‖/Real.log 16:=by
    simp only[z,Complex.div_ofReal_re,Complex.log_re]
  refine ⟨z,⟨?_,?_⟩,?_⟩
  · rw[hzr];exact div_nonneg (Real.log_nonneg hu1) hα.le
  · rw[hzr]
    apply (div_le_iff₀ hα).mpr
    have hlog:Real.log ‖u‖≤Real.log 4:=Real.log_le_log (lt_of_lt_of_le zero_lt_one hu1) (by linarith)
    have h16:Real.log (16:ℝ)=2*Real.log 4:=by rw[show (16:ℝ)=4^2 by norm_num,Real.log_pow];norm_num
    linarith
  · rw[hz,Complex.cosh,Complex.exp_log hun,Complex.exp_neg,Complex.exp_log hun,hue]
    ring
end WP.Analysis

namespace WP.Analysis
open Set Complex
open Complex.HadamardThreeLines
lemma slit_disk_two_constants (f:ℂ→ℂ) (b B:ℝ) (hb:0<b) (hbB:b≤B)
    (hf:AnalyticOnNhd ℂ f (Metric.ball 0 16))
    (hbound:∀z:ℂ,‖z‖<16→‖f z‖≤B)
    (hslit:∀x:ℝ,x∈Icc (-1:ℝ) 1→‖f x‖≤b)
    (w:ℂ) (hw:‖w‖≤3/2):‖f w‖≤Real.sqrt (b*B):=by
  let φ:ℂ→ℂ:=fun z=>Complex.cosh ((Real.log 16:ℝ)*z)
  let g:ℂ→ℂ:=fun z=>f (φ z)
  have hφ:∀z:ℂ,AnalyticAt ℂ φ z:=by intro z;dsimp[φ];fun_prop
  have hg:∀z:ℂ,z∈verticalClosedStrip (0:ℝ) 1→AnalyticAt ℂ g z:=by
    intro z hz
    apply (hf (φ z) ?_).comp (hφ z)
    simpa only[φ,Metric.mem_ball,dist_zero_right] using cosh_strip_disk_bound z hz
  have hd:DiffContOnCl ℂ g (verticalStrip (0:ℝ) 1):=by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    have hclosed:IsClosed (verticalClosedStrip (0:ℝ) 1):=isClosed_Icc.preimage Complex.continuous_re
    have hsub:closure (verticalStrip (0:ℝ) 1)⊆verticalClosedStrip (0:ℝ) 1:=
      closure_minimal (fun z hz=>⟨hz.1.le,hz.2.le⟩) hclosed
    exact (hg z (hsub hz)).differentiableAt.differentiableWithinAt
  have hgb:BddAbove ((norm∘g) '' verticalClosedStrip (0:ℝ) 1):=by
    refine ⟨B,?_⟩
    rintro y ⟨z,hz,rfl⟩
    exact hbound (φ z) (cosh_strip_disk_bound z hz)
  have hleft:∀z∈Complex.re ⁻¹' {(0:ℝ)},‖g z‖≤b:=by
    intro z hz
    obtain ⟨t,ht,he⟩:=cosh_strip_left z hz
    dsimp only[g,φ]
    rw[he]
    exact hslit t ht
  have hright:∀z∈Complex.re ⁻¹' {(1:ℝ)},‖g z‖≤B:=by
    intro z hz
    exact hbound (φ z) (cosh_strip_disk_bound z ⟨by rw[show z.re=1 from hz];norm_num,by exact (show z.re=1 from hz).le⟩)
  obtain ⟨z,hz,he⟩:=cosh_strip_inner_preimage w hw
  have hn:=Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f:=g) (a:=b) (b:=B) (by norm_num:(0:ℝ)<1) (show z∈verticalClosedStrip (0:ℝ) 1 from ⟨hz.1,by linarith[hz.2]⟩)
    hd hgb hleft hright
  change ‖f (φ z)‖≤_ at hn
  rw[show φ z=w from he] at hn
  simp only[sub_zero,div_one] at hn
  have hB:0<B:=hb.trans_le hbB
  have hlog:Real.log b≤Real.log B:=Real.log_le_log hb hbB
  have hexp:b^(1-z.re)*B^z.re≤Real.sqrt (b*B):=by
    rw[Real.rpow_def_of_pos hb,Real.rpow_def_of_pos hB,←Real.exp_add,
      Real.sqrt_eq_rpow,Real.rpow_def_of_pos (mul_pos hb hB),Real.log_mul hb.ne' hB.ne']
    apply Real.exp_le_exp.mpr
    nlinarith[hz.2]
  exact hn.trans hexp
end WP.Analysis

namespace WP.Analysis
open Set Complex
lemma slit_disk_two_constants_scaled (f:ℂ→ℂ) (r b B:ℝ) (hr:0<r)
    (hb:0<b) (hbB:b≤B)
    (hf:AnalyticOnNhd ℂ f (Metric.ball 0 (16*r)))
    (hbound:∀z:ℂ,‖z‖<16*r→‖f z‖≤B)
    (hslit:∀x:ℝ,x∈Icc (-r) r→‖f x‖≤b)
    (w:ℂ) (hw:‖w‖≤3*r/2):‖f w‖≤Real.sqrt (b*B):=by
  let g:ℂ→ℂ:=fun z=>f ((r:ℂ)*z)
  have hga:AnalyticOnNhd ℂ g (Metric.ball 0 16):=by
    intro z hz
    have hz':‖z‖<16:=by simpa only[Metric.mem_ball,dist_zero_right] using hz
    have hn:‖(r:ℂ)*z‖<16*r:=by rw[norm_mul,Complex.norm_of_nonneg hr.le];nlinarith
    exact (hf _ (by simpa only[Metric.mem_ball,dist_zero_right] using hn)).comp (by fun_prop)
  have hgb:∀z:ℂ,‖z‖<16→‖g z‖≤B:=by
    intro z hz
    apply hbound
    rw[norm_mul,Complex.norm_of_nonneg hr.le];nlinarith
  have hgs:∀x:ℝ,x∈Icc (-1:ℝ) 1→‖g x‖≤b:=by
    intro x hx
    dsimp[g]
    rw[←Complex.ofReal_mul]
    apply hslit
    constructor <;>nlinarith[hr,hx.1,hx.2]
  have hw':‖w/(r:ℂ)‖≤3/2:=by
    rw[norm_div,Complex.norm_of_nonneg hr.le]
    exact (div_le_iff₀ hr).mpr (by linarith)
  have ht:=slit_disk_two_constants g b B hb hbB hga hgb hgs (w/(r:ℂ)) hw'
  simpa only[g,mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')] using ht

lemma slit_disk_exponential_transfer (f:ℂ→ℂ) (r C a H Q:ℝ)
    (hr:0<r) (hC:0<C) (ha:0≤a) (hH:0≤H)
    (hf:AnalyticOnNhd ℂ f (Metric.ball 0 (16*r)))
    (hbound:∀z:ℂ,‖z‖<16*r→‖f z‖≤C*Real.exp Q)
    (hslit:∀x:ℝ,x∈Icc (-r) r→‖f x‖≤C*Real.exp (-a*Real.sqrt H+Q))
    (w:ℂ) (hw:‖w‖≤3*r/2):
    ‖f w‖≤C*Real.exp (-a*Real.sqrt H/2+Q):=by
  let b:=C*Real.exp (-a*Real.sqrt H+Q)
  let B:=C*Real.exp Q
  have hb:0<b:=by dsimp[b];positivity
  have hbB:b≤B:=by
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact Real.exp_le_exp.mpr (by nlinarith[Real.sqrt_nonneg H])
  have ht:=slit_disk_two_constants_scaled f r b B hr hb hbB hf hbound hslit w hw
  have hs:Real.sqrt (b*B)=C*Real.exp (-a*Real.sqrt H/2+Q):=by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    dsimp[b,B]
    rw[pow_two]
    have he:Real.exp (-a*Real.sqrt H+Q)*Real.exp Q=
        Real.exp (-a*Real.sqrt H/2+Q)*Real.exp (-a*Real.sqrt H/2+Q):=by
      rw[←Real.exp_add,←Real.exp_add]
      congr 1
      ring
    calc
      _=C*C*(Real.exp (-a*Real.sqrt H+Q)*Real.exp Q):=by ring
      _=C*C*(Real.exp (-a*Real.sqrt H/2+Q)*Real.exp (-a*Real.sqrt H/2+Q)):=by rw[he]
      _=_:=by ring
  exact ht.trans_eq hs
end WP.Analysis

namespace WP.Analysis
open Set Complex
lemma normalized_relative_perturbation (e e₀:ℂ) (ε:ℝ)
    (hε:0≤ε) (hεhalf:ε≤1/2) (he:‖e‖≤ε) (he₀:‖e₀‖≤ε):
    ‖(1+e)/(1+e₀)‖≤3 ∧ ‖(1+e)/(1+e₀)-1‖≤4*ε:=by
  have hden:1/2≤‖1+e₀‖:=by
    have ht:=norm_sub_norm_le (1:ℂ) (-e₀)
    simp only[norm_one,norm_neg,sub_neg_eq_add] at ht
    linarith
  have hdp:0<‖1+e₀‖:=by linarith
  have hdn:1+e₀≠0:=norm_pos_iff.mp hdp
  constructor
  · rw[norm_div]
    apply (div_le_iff₀ hdp).mpr
    have hnum:=norm_add_le (1:ℂ) e
    simp only[norm_one] at hnum
    linarith
  · rw[div_sub_one hdn]
    have hsub:(1+e)-(1+e₀)=e-e₀:=by ring
    rw[hsub,norm_div]
    apply (div_le_iff₀ hdp).mpr
    have hnum:‖e-e₀‖≤2*ε:=(norm_sub_le _ _).trans (by linarith)
    nlinarith

lemma centered_slit_comparison (F M:ℂ→ℂ) (r G ε:ℝ)
    (hr:0<r) (hG:0<G) (hε:0<ε) (hεhalf:ε≤1/2)
    (hF:AnalyticOnNhd ℂ F (Metric.ball 0 (16*r)))
    (hM:AnalyticOnNhd ℂ M (Metric.ball 0 (16*r)))
    (hMb:∀z:ℂ,‖z‖<16*r→‖M z‖≤G)
    (hpos:∀z:ℂ,‖z‖<16*r→‖F z‖≤‖F (z.re:ℂ)‖)
    (e₀:ℂ) (he₀:‖e₀‖≤ε)
    (hreal:∀u:ℝ,|u|<16*r→∃e:ℂ,‖e‖≤ε ∧ F (u:ℂ)=M (u:ℂ)*((1+e)/(1+e₀)))
    (w:ℂ) (hw:‖w‖≤3*r/2):
    ‖F w-M w‖≤4*Real.sqrt ε*G:=by
  have hFreal:∀u:ℝ,|u|<16*r→‖F (u:ℂ)‖≤3*G:=by
    intro u hu
    obtain ⟨e,he,heq⟩:=hreal u hu
    have hp:=(normalized_relative_perturbation e e₀ ε hε.le hεhalf he he₀).1
    rw[heq,norm_mul]
    have hmu:‖M (u:ℂ)‖≤G:=hMb _ (by simpa only[Complex.norm_real,Real.norm_eq_abs] using hu)
    nlinarith[norm_nonneg (M (u:ℂ)),norm_nonneg ((1+e)/(1+e₀))]
  have hdiff:∀z:ℂ,‖z‖<16*r→‖F z-M z‖≤4*G:=by
    intro z hz
    have hRe:|z.re|<16*r:=(Complex.abs_re_le_norm z).trans_lt hz
    have hf:‖F z‖≤3*G:=(hpos z hz).trans (hFreal z.re hRe)
    exact (norm_sub_le _ _).trans (by linarith[hMb z hz])
  have hsmall:∀u:ℝ,u∈Icc (-r) r→‖F (u:ℂ)-M (u:ℂ)‖≤4*ε*G:=by
    intro u hu
    have hu':|u|<16*r:=by rw[abs_lt];constructor <;>linarith[hu.1,hu.2]
    obtain ⟨e,he,heq⟩:=hreal u hu'
    have hp:=(normalized_relative_perturbation e e₀ ε hε.le hεhalf he he₀).2
    rw[heq,←mul_sub_one,norm_mul]
    have hmu:‖M (u:ℂ)‖≤G:=hMb _ (by simpa only[Complex.norm_real,Real.norm_eq_abs] using hu')
    calc
      _≤G*(4*ε):=mul_le_mul hmu hp (norm_nonneg _) hG.le
      _=_:=by ring
  have ht:=slit_disk_two_constants_scaled (fun z=>F z-M z) r (4*ε*G) (4*G) hr
    (by positivity) (by nlinarith) (hF.sub hM) hdiff hsmall w hw
  have hs:Real.sqrt ((4*ε*G)*(4*G))=4*Real.sqrt ε*G:=by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    nlinarith[Real.sq_sqrt hε.le]
  exact ht.trans_eq hs
end WP.Analysis
