import WPFormalization.Analysis.SlitDiskComparison
/-! A small-disk exponential comparison from a genuine real relative error.
The shifted real segment is handled by the proved slit estimate. The radius
is d/sqrt(h); positivity controls the true function on the larger disk. No
paper generating function or model is assumed by this generic numerical lemma. -/
set_option maxHeartbeats 1000000
noncomputable section
namespace WP.Analysis
open Set Complex
lemma segment_slit_exponential_transfer (f:ℂ→ℂ) (r C a h Q:ℝ)
    (hr:0<r) (hC:0<C) (ha:0≤a) (hh:0≤h)
    (hf:AnalyticOnNhd ℂ f (Metric.ball 0 (9*r)))
    (hbound:∀z:ℂ,‖z‖<9*r→‖f z‖≤C*Real.exp Q)
    (hslit:∀x:ℝ,x∈Icc (0:ℝ) r→‖f x‖≤C*Real.exp (-a*Real.sqrt h+Q))
    (w:ℂ) (hw:‖w‖≤r/4):
    ‖f w‖≤C*Real.exp (-a*Real.sqrt h/2+Q):=by
  let g:ℂ→ℂ:=fun z=>f ((r/2:ℝ)+z)
  have hnorm(z:ℂ)(hz:‖z‖<16*(r/2)):‖((r/2:ℝ):ℂ)+z‖<9*r:=by
    have ht:=norm_add_le (((r/2:ℝ):ℂ)) z
    rw[Complex.norm_of_nonneg (by positivity:0≤r/2)] at ht
    linarith
  have hga:AnalyticOnNhd ℂ g (Metric.ball 0 (16*(r/2))):=by
    intro z hz
    have hz':‖z‖<16*(r/2):=by simpa only[Metric.mem_ball,dist_zero_right] using hz
    have hmem:((r/2:ℝ):ℂ)+z∈Metric.ball 0 (9*r):=by
      simpa only[Metric.mem_ball,dist_zero_right] using hnorm z hz'
    exact (hf _ hmem).comp (by fun_prop)
  have hgb:∀z:ℂ,‖z‖<16*(r/2)→‖g z‖≤C*Real.exp Q:=by
    intro z hz
    exact hbound _ (hnorm z hz)
  have hgs:∀x:ℝ,x∈Icc (-(r/2)) (r/2)→‖g x‖≤C*Real.exp (-a*Real.sqrt h+Q):=by
    intro x hx
    dsimp only[g]
    rw[←Complex.ofReal_add]
    exact hslit _ ⟨by linarith[hx.1],by linarith[hx.2]⟩
  have hw':‖w-((r/2:ℝ):ℂ)‖≤3*(r/2)/2:=by
    have ht:=norm_sub_le w (((r/2:ℝ):ℂ))
    rw[Complex.norm_of_nonneg (by positivity:0≤r/2)] at ht
    linarith
  have ht:=slit_disk_exponential_transfer g (r/2) C a h Q (by positivity) hC ha hh hga hgb hgs
    (w-((r/2:ℝ):ℂ)) hw'
  have hp:g (w-((r/2:ℝ):ℂ))=f w:=by dsimp[g];congr 1;ring
  rw[hp] at ht
  exact ht
end WP.Analysis

namespace WP.Analysis
open Set Complex
lemma small_disk_comparison_of_real_relative_error (F M:ℂ→ℂ)
    (ρ D E a d h:ℝ) (hρ:0<ρ) (hD:0<D) (hE:0<E) (ha:0<a) (hd:0<d)
    (hdr:d≤ρ/18) (hda:36*D*d≤a) (hh:1≤h)
    (hF:AnalyticOnNhd ℂ F (Metric.ball 0 ρ))
    (hM:AnalyticOnNhd ℂ M (Metric.ball 0 ρ))
    (hMb:∀z:ℂ,‖z‖≤ρ→‖M z‖≤D*Real.exp (D*h*‖z‖))
    (hpos:∀z:ℂ,‖z‖≤ρ→‖F z‖≤‖F (‖z‖:ℂ)‖)
    (herr:∀x∈Icc (0:ℝ) ρ,M (x:ℂ)≠0 ∧ ‖F (x:ℂ)/M (x:ℂ)-1‖≤E*Real.exp (-a*Real.sqrt h))
    (w:ℂ) (hw:‖w‖≤d/(4*Real.sqrt h)):
    ‖F w-M w‖≤((E+2)*D)*Real.exp (-(a/4)*Real.sqrt h):=by
  have hhp:0<h:=by linarith
  have hs:0<Real.sqrt h:=Real.sqrt_pos.mpr hhp
  have hss:(Real.sqrt h)^2=h:=Real.sq_sqrt hhp.le
  have hs1:1≤Real.sqrt h:=by nlinarith[Real.sqrt_nonneg h]
  let r:ℝ:=d/Real.sqrt h
  have hr:0<r:=div_pos hd hs
  have hrle:r≤d:=(div_le_iff₀ hs).mpr (by nlinarith)
  have h9r:9*r≤ρ:=by nlinarith
  let Q:ℝ:=D*h*(9*r)
  let C:ℝ:=(E+2)*D
  have hC:0<C:=by dsimp[C];positivity
  have hexp0:Real.exp (-a*Real.sqrt h)≤1:=by
    exact (Real.exp_le_exp.mpr (by nlinarith[hs.le])).trans_eq Real.exp_zero
  have heq(x:ℝ)(hx:x∈Icc (0:ℝ) ρ):
      ‖F (x:ℂ)-M (x:ℂ)‖≤E*Real.exp (-a*Real.sqrt h)*‖M (x:ℂ)‖:=by
    have he:F (x:ℂ)-M (x:ℂ)=M (x:ℂ)*(F (x:ℂ)/M (x:ℂ)-1):=by field_simp[(herr x hx).1] <;>ring
    rw[he,norm_mul]
    have ht:=mul_le_mul_of_nonneg_left (herr x hx).2 (norm_nonneg (M (x:ℂ)))
    nlinarith
  have hFreal(x:ℝ)(hx:x∈Icc (0:ℝ) ρ):‖F (x:ℂ)‖≤(E+1)*‖M (x:ℂ)‖:=by
    have he:=heq x hx
    have ht:=norm_sub_norm_le (F (x:ℂ)) (M (x:ℂ))
    have hε:=mul_le_mul_of_nonneg_left hexp0 hE.le
    have hmul:=mul_le_mul_of_nonneg_right hε (norm_nonneg (M (x:ℂ)))
    nlinarith
  have hdisk:∀z:ℂ,‖z‖<9*r→‖F z-M z‖≤C*Real.exp Q:=by
    intro z hz
    have hzρ:‖z‖≤ρ:=hz.le.trans h9r
    have ht:‖M z‖≤D*Real.exp Q:=by
      apply (hMb z hzρ).trans
      apply mul_le_mul_of_nonneg_left _ hD.le
      apply Real.exp_le_exp.mpr
      dsimp only[Q]
      nlinarith[mul_pos hD hhp]
    have htr:‖M (‖z‖:ℂ)‖≤D*Real.exp Q:=by
      have ht':=hMb (‖z‖:ℂ) (by simpa only[Complex.norm_of_nonneg (norm_nonneg z)] using hzρ)
      rw[Complex.norm_of_nonneg (norm_nonneg z)] at ht'
      apply ht'.trans
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact Real.exp_le_exp.mpr (by dsimp only[Q];nlinarith[mul_pos hD hhp])
    have hf:‖F z‖≤(E+1)*(D*Real.exp Q):=
      (hpos z hzρ).trans ((hFreal ‖z‖ ⟨norm_nonneg z,hzρ⟩).trans
        (mul_le_mul_of_nonneg_left htr (by linarith:0≤E+1)))
    have he:=norm_sub_le (F z) (M z)
    dsimp only[C]
    nlinarith
  have hslit:∀x:ℝ,x∈Icc (0:ℝ) r→‖F (x:ℂ)-M (x:ℂ)‖≤C*Real.exp (-a*Real.sqrt h+Q):=by
    intro x hx
    have hxρ:x∈Icc (0:ℝ) ρ:=⟨hx.1,by nlinarith[hr.le,hx.2]⟩
    have hm:‖M (x:ℂ)‖≤D*Real.exp Q:=by
      have ht:=hMb (x:ℂ) (by rw[Complex.norm_of_nonneg hx.1];exact hxρ.2)
      rw[Complex.norm_of_nonneg hx.1] at ht
      apply ht.trans
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact Real.exp_le_exp.mpr (by
        dsimp only[Q]
        exact mul_le_mul_of_nonneg_left (show x≤9*r by nlinarith[hx.2,hr.le]) (mul_pos hD hhp).le)
    calc
      _≤E*Real.exp (-a*Real.sqrt h)*‖M (x:ℂ)‖:=heq x hxρ
      _≤E*Real.exp (-a*Real.sqrt h)*(D*Real.exp Q):=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _=(E*D)*Real.exp (-a*Real.sqrt h+Q):=by rw[Real.exp_add];ring
      _≤C*Real.exp (-a*Real.sqrt h+Q):=by
        dsimp only[C]
        have ht:=Real.exp_pos (-a*Real.sqrt h+Q)
        nlinarith
  have hsmall:‖w‖≤r/4:=by dsimp[r];convert hw using 1 <;>field_simp
  have hfa:AnalyticOnNhd ℂ (fun z=>F z-M z) (Metric.ball 0 (9*r)):=
    (hF.sub hM).mono (Metric.ball_subset_ball h9r)
  have ht:=segment_slit_exponential_transfer (fun z=>F z-M z) r C a h Q hr hC ha.le hhp.le hfa hdisk hslit w hsmall
  have hratio:h*r=d*Real.sqrt h:=by
    dsimp[r]
    rw[←mul_div_assoc]
    apply (div_eq_iff hs.ne').mpr
    nlinarith[hss]
  have hQ:Q≤a/4*Real.sqrt h:=by
    have ht:=mul_le_mul_of_nonneg_right hda hs.le
    dsimp only[Q]
    rw[show D*h*(9*r)=9*D*(h*r) by ring,hratio]
    nlinarith
  exact ht.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC.le)
end WP.Analysis
