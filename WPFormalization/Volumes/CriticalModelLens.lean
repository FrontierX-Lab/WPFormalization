import WPFormalization.Volumes.CriticalGaussianCoordinates
import WPFormalization.Volumes.CriticalExtractionPhysical
import WPFormalization.Volumes.MarkedGeneratingPositivity
/-! The actual critical tilt remains inside the genuine cusp disk on one
parameter-angle neighborhood. Its holomorphic fold branch agrees there with
the original planar inverse. The disk inclusion follows from the true
quadratic X gap and an exponential estimate; equality follows from ordinary
local inverse uniqueness and the analytic identity principle. The physical
delta parameter is positive, so no totalized root value at y₀ is used. -/
noncomputable section
namespace WP.PositiveConvolution
open Set Filter
open scoped Topology
lemma X_planarInverse_eq (P:PsiTheory) (z:ℂ) (hz:‖z‖<xCritical):
    X (planarInverse P z)=z:=by
  have hf:AnalyticOnNhd ℂ (fun z:ℂ=>X (planarInverse P z)) (Metric.ball 0 xCritical):=by
    intro w hw
    exact (X_differentiable.analyticAt _).comp (planarInverse_analyticAt P w
      (by simpa only[Metric.mem_ball,dist_zero_right] using hw))
  have hc:xCritical/2∈Ioo (0:ℝ) xCritical:=⟨half_pos Analysis.xCritical_pos_parameter,
    half_lt_self Analysis.xCritical_pos_parameter⟩
  have hmem:((xCritical/2:ℝ):ℂ)∈Metric.ball 0 xCritical:=by
    simpa only[Metric.mem_ball,dist_zero_right,Complex.norm_of_nonneg hc.1.le] using hc.2
  have he:EqOn (fun z:ℂ=>X (planarInverse P z)) id (Metric.ball 0 xCritical):=by
    apply Analysis.complex_identity_of_real_germ _ id _ (xCritical/2) hf analyticOnNhd_id
      (convex_ball (0:ℂ) xCritical).isPreconnected hmem
    filter_upwards[isOpen_Ioo.mem_nhds hc] with x hx
    rw[planarInverse_ofReal P x ⟨hx.1.le,hx.2⟩]
    have hb:=(inverseY_branch x ⟨hx.1.le,hx.2⟩).2
    apply Complex.ext
    · exact hb
    · simpa using X_im_ofReal (inverseY x)
  exact he (by simpa only[Metric.mem_ball,dist_zero_right] using hz)
end WP.PositiveConvolution

namespace WP.Analysis
open Set Filter
open scoped Topology
lemma analytic_root_curves_eq_on_ball (F g h:ℂ→ℂ) (R:ℝ) (hR:0<R)
    (hg:AnalyticOnNhd ℂ g (Metric.ball 0 R)) (hh:AnalyticOnNhd ℂ h (Metric.ball 0 R))
    (hF:AnalyticAt ℂ F (g 0)) (hne:deriv F (g 0)≠0) (hzero:g 0=h 0)
    (hroot:∀u∈Metric.ball (0:ℂ) R,F (g u)=F (h u)):
    ∀u∈Metric.ball (0:ℂ) R,g u=h u:=by
  have h0:(0:ℂ)∈Metric.ball 0 R:=Metric.mem_ball_self hR
  have hli:=hF.hasStrictDerivAt.eventually_left_inverse hne
  have hgt:Tendsto g (𝓝 0) (𝓝 (g 0)):=(hg 0 h0).continuousAt.tendsto
  have hht:Tendsto h (𝓝 0) (𝓝 (g 0)):=by rw[hzero];exact (hh 0 h0).continuousAt.tendsto
  have heq:g=ᶠ[𝓝 (0:ℂ)] h:=by
    filter_upwards[hgt.eventually hli,hht.eventually hli,Metric.ball_mem_nhds (0:ℂ) hR] with u hgu hhu hu
    rw[←hgu,←hhu,hroot u hu]
  exact hg.eqOn_of_preconnected_of_eventuallyEq hh (convex_ball (0:ℂ) R).isPreconnected h0 heq
end WP.Analysis

namespace WP.Analysis
open Set Complex

def CriticalGaussianCoordinateData.tiltPoint (d:CriticalGaussianCoordinateData) (δ u:ℂ):ℂ:=
  X ((y₀:ℂ)-δ)*Complex.exp (Complex.I*u*δ^2*d.L δ)

lemma CriticalGaussianCoordinateData.q_eq_planarInverse_of_lens
    (d:CriticalGaussianCoordinateData) (P:PsiTheory) (R δ:ℝ)
    (hR:0<R) (hδ:δ∈Ioo (0:ℝ) (min R y₀))
    (hq:AnalyticOnNhd ℂ d.q (Metric.ball 0 R ×ˢ Metric.ball 0 R))
    (hq0:d.q ((δ:ℂ),0)=1)
    (hfold:∀u:ℂ,‖u‖<R→X ((y₀:ℂ)-(δ:ℂ)*d.q ((δ:ℂ),u))=d.tiltPoint (δ:ℂ) u)
    (hlens:∀u:ℂ,‖u‖<R→‖d.tiltPoint (δ:ℂ) u‖<xCritical):
    ∀u:ℂ,‖u‖<R→PositiveConvolution.planarInverse P (d.tiltPoint (δ:ℂ) u)=
      (y₀:ℂ)-(δ:ℂ)*d.q ((δ:ℂ),u):=by
  let g:ℂ→ℂ:=fun u=>(y₀:ℂ)-(δ:ℂ)*d.q ((δ:ℂ),u)
  let h:ℂ→ℂ:=fun u=>PositiveConvolution.planarInverse P (d.tiltPoint (δ:ℂ) u)
  have hdR:δ<R:=hδ.2.trans_le (min_le_left _ _)
  have hdy:δ<y₀:=hδ.2.trans_le (min_le_right _ _)
  have hY:y₀-δ∈Ico (0:ℝ) y₀:=⟨by linarith,by linarith[hδ.1]⟩
  have hqδ:(δ:ℂ)∈Metric.ball 0 R:=by
    simpa only[Metric.mem_ball,dist_zero_right,Complex.norm_of_nonneg hδ.1.le] using hdR
  have hg:AnalyticOnNhd ℂ g (Metric.ball 0 R):=by
    intro u hu
    exact analyticAt_const.sub (analyticAt_const.mul ((hq ((δ:ℂ),u) ⟨hqδ,hu⟩).comp
      (analyticAt_const.prod analyticAt_id)))
  have ht:∀u:ℂ,AnalyticAt ℂ (d.tiltPoint (δ:ℂ)) u:=by
    intro u
    unfold CriticalGaussianCoordinateData.tiltPoint
    fun_prop
  have hh:AnalyticOnNhd ℂ h (Metric.ball 0 R):=by
    intro u hu
    exact (PositiveConvolution.planarInverse_analyticAt P _ (hlens u
      (by simpa only[Metric.mem_ball,dist_zero_right] using hu))).comp (ht u)
  have hg0:g 0=((y₀-δ:ℝ):ℂ):=by dsimp[g];rw[hq0,mul_one,Complex.ofReal_sub]
  have hx:XR (y₀-δ)∈Ico (0:ℝ) xCritical:=by
    exact ⟨XR_nonneg_interior _ hY,XR_strictMonoOn (show y₀-δ∈Iic y₀ from hY.2.le) (by simp) hY.2⟩
  have hh0:h 0=((y₀-δ:ℝ):ℂ):=by
    dsimp[h,CriticalGaussianCoordinateData.tiltPoint]
    simp only[mul_zero,zero_mul,Complex.exp_zero,mul_one]
    rw[←Complex.ofReal_sub,X_eq_ofReal_XR,PositiveConvolution.planarInverse_ofReal P _ hx,
      inverseY_eq_of_root _ _ hY.2.le rfl]
  have hne:deriv X (g 0)≠0:=by
    rw[hg0,derivX_ofReal]
    exact_mod_cast (a_pos _ hY).ne'
  have heq:=analytic_root_curves_eq_on_ball X g h R hR hg hh (X_differentiable.analyticAt _) hne
    (hg0.trans hh0.symm) (fun u hu=>by
      have hu':‖u‖<R:=by simpa only[Metric.mem_ball,dist_zero_right] using hu
      exact (hfold u hu').trans (PositiveConvolution.X_planarInverse_eq P _ (hlens u hu')).symm)
  intro u hu
  exact (heq u (by simpa only[Metric.mem_ball,dist_zero_right] using hu)).symm
end WP.Analysis

namespace WP.Analysis
lemma fold_tilt_norm_lt (x xc δ b M U:ℝ) (z:ℂ)
    (hxc:0<xc) (hx:0≤x) (hxx:x≤xc) (hδ:0<δ) (hb:0<b)
    (hgap:xc*b*δ^2≤xc-x) (hz:‖z‖≤M*U*δ^2) (hz1:‖z‖≤1)
    (hcap:4*M*U≤b):‖(x:ℂ)*Complex.exp z‖<xc:=by
  have hrem:=Complex.norm_exp_sub_one_sub_id_le hz1
  have htriangle:‖Complex.exp z‖≤‖Complex.exp z-1-z‖+‖z‖+1:=by
    have ht:=norm_add_le (Complex.exp z-1-z) z
    have ht':=norm_add_le ((Complex.exp z-1-z)+z) (1:ℂ)
    rw[norm_one] at ht'
    have he:(Complex.exp z-1-z)+z+1=Complex.exp z:=by ring
    rw[he] at ht'
    linarith
  have he:‖Complex.exp z‖≤1+2*‖z‖:=by nlinarith[norm_nonneg z]
  have hnorm:‖(x:ℂ)*Complex.exp z‖≤x+2*xc*‖z‖:=by
    rw[norm_mul,Complex.norm_of_nonneg hx]
    have ht:=mul_le_mul_of_nonneg_left he hx
    have ht':=mul_le_mul_of_nonneg_right hxx (norm_nonneg z)
    nlinarith
  have hp:=mul_le_mul_of_nonneg_right hcap (mul_nonneg hxc.le (sq_nonneg δ))
  have hzp:=mul_le_mul_of_nonneg_left hz (show 0≤2*xc by positivity)
  have hstrict:0<xc*b*δ^2:=by positivity
  nlinarith
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology
lemma CriticalGaussianCoordinateData.uniform_tilt_lens (d:CriticalGaussianCoordinateData):
    ∃R:ℝ,0<R ∧ R<y₀ ∧ ∀δ∈Ioo (0:ℝ) R,∀u:ℂ,‖u‖<R→
      ‖d.tiltPoint (δ:ℂ) u‖<xCritical:=by
  obtain ⟨f⟩:=exists_criticalFoldData
  let b:ℝ:=f.b/2
  let M:ℝ:=‖d.L 0‖+1
  have hb:0<b:=half_pos f.b_pos
  have hM:0<M:=by dsimp[M];positivity
  have hc:Tendsto (fun δ:ℝ=>(δ:ℂ)) (𝓝 0) (𝓝 (0:ℂ)):=
    Complex.continuous_ofReal.continuousAt.tendsto
  have hb0:b<(f.B 0).re:=by rw[f.B_zero,Complex.ofReal_re];dsimp[b];linarith[f.b_pos]
  have hbn:∀ᶠδ:ℝ in 𝓝 0,b<(f.B (δ:ℂ)).re:=
    (Complex.continuous_re.continuousAt.tendsto.comp (f.B_analytic.continuousAt.tendsto.comp hc)).eventually
      (eventually_gt_nhds hb0)
  have hl0:‖d.L 0‖<M:=by dsimp[M];linarith
  have hln:∀ᶠδ:ℝ in 𝓝 0,‖d.L (δ:ℂ)‖<M:=
    ((d.L_analytic.continuousAt.tendsto.comp hc).norm).eventually (eventually_lt_nhds hl0)
  have he:∀ᶠδ:ℝ in 𝓝 0,complexCriticalGap (δ:ℂ)=(δ:ℂ)^2*f.B (δ:ℂ) ∧
      b≤(f.B (δ:ℂ)).re ∧ ‖d.L (δ:ℂ)‖≤M:=by
    filter_upwards[hc.eventually f.gap_factor,hbn,hln] with δ hg hb hl
    exact ⟨hg,hb.le,hl.le⟩
  obtain ⟨R₀,hR₀,heball⟩:=Metric.eventually_nhds_iff.mp he
  let R₁:ℝ:=min R₀ 1
  let R₂:ℝ:=min R₁ (y₀/2)
  let R:ℝ:=min R₂ (min (b/(4*M)) (1/(M+1)))
  have hy0:=y₀_pos
  have hR:0<R:=by dsimp[R,R₂,R₁];positivity
  have hRR₂:R≤R₂:=min_le_left _ _
  have hRR₁:R≤R₁:=hRR₂.trans (min_le_left _ _)
  have hRR₀:R≤R₀:=hRR₁.trans (min_le_left _ _)
  have hRone:R≤1:=hRR₁.trans (min_le_right _ _)
  have hRy:R≤y₀/2:=hRR₂.trans (min_le_right _ _)
  have hRb:R≤b/(4*M):=(min_le_right _ _).trans (min_le_left _ _)
  have hRu:R≤1/(M+1):=(min_le_right _ _).trans (min_le_right _ _)
  have hcap:4*M*R≤b:=by
    have ht:=(le_div_iff₀ (by positivity:0<4*M)).mp hRb
    nlinarith
  have hMR:M*R≤1:=by
    have ht:=(le_div_iff₀ (by positivity:0<M+1)).mp hRu
    nlinarith
  refine ⟨R,hR,by linarith,?_⟩
  intro δ hδ u hu
  have hδR:δ<R₀:=hδ.2.trans_le hRR₀
  have hδ1:δ≤1:=hδ.2.le.trans hRone
  have hδy:δ<y₀:=by linarith[hδ.2]
  have hY:y₀-δ∈Ico (0:ℝ) y₀:=⟨by linarith,by linarith[hδ.1]⟩
  have ht:=heball (show dist δ 0<R₀ by rw[Real.dist_eq,sub_zero,abs_of_pos hδ.1];exact hδR)
  have hgapre:1-XR (y₀-δ)/xCritical=δ^2*(f.B (δ:ℂ)).re:=by
    have he':=congrArg Complex.re ht.1
    rw[complexCriticalGap,←Complex.ofReal_sub,X_eq_ofReal_XR,←Complex.ofReal_div,
      Complex.sub_re,Complex.one_re,Complex.ofReal_re,←Complex.ofReal_pow,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at he'
    exact he'
  have hgapEq:xCritical-XR (y₀-δ)=xCritical*δ^2*(f.B (δ:ℂ)).re:=by
    have hm:=congrArg (fun t:ℝ=>t*xCritical) hgapre
    field_simp[critical_x_pos.ne'] at hm
    nlinarith only[hm]
  have hgap:xCritical*b*δ^2≤xCritical-XR (y₀-δ):=by
    rw[hgapEq]
    have hp:=mul_le_mul_of_nonneg_left ht.2.1 (mul_nonneg critical_x_pos.le (sq_nonneg δ))
    nlinarith
  let v:ℂ:=Complex.I*u*(δ:ℂ)^2*d.L (δ:ℂ)
  have hv:‖v‖≤M*R*δ^2:=by
    dsimp only[v]
    rw[norm_mul,norm_mul,norm_mul,Complex.norm_I,one_mul,norm_pow,Complex.norm_of_nonneg hδ.1.le]
    calc
      _≤(R*δ^2)*M:=mul_le_mul
        (mul_le_mul_of_nonneg_right hu.le (sq_nonneg δ)) ht.2.2 (norm_nonneg _) (by positivity)
      _=_:=by ring
  have hδsq:δ^2≤1:=by nlinarith[hδ.1]
  have hv1:‖v‖≤1:=hv.trans (by
    have hp:=mul_le_mul hMR hδsq (sq_nonneg δ) (by norm_num:(0:ℝ)≤1)
    simpa only[one_mul] using hp)
  have hx:0≤XR (y₀-δ):=XR_nonneg_interior _ hY
  have hxx:XR (y₀-δ)≤xCritical:=
    (XR_strictMonoOn (show y₀-δ∈Iic y₀ from hY.2.le) (by simp) hY.2).le
  rw[CriticalGaussianCoordinateData.tiltPoint,←Complex.ofReal_sub,X_eq_ofReal_XR]
  exact fold_tilt_norm_lt _ _ δ b M R v critical_x_pos hx hxx hδ.1 hb hgap hv hv1 hcap
end WP.Analysis

namespace WP.Analysis
open Set Complex
lemma CriticalGaussianCoordinateData.q_planar_inverse_common_lens
    (d:CriticalGaussianCoordinateData) (P:PsiTheory):
    ∃R:ℝ,0<R ∧ R<y₀ ∧ ∀δ∈Ioo (0:ℝ) R,∀u:ℂ,‖u‖<R→
      ‖d.tiltPoint (δ:ℂ) u‖<xCritical ∧
      PositiveConvolution.planarInverse P (d.tiltPoint (δ:ℂ) u)=
        (y₀:ℂ)-(δ:ℂ)*d.q ((δ:ℂ),u):=by
  obtain ⟨Rc,hRc,hL,hq,hU,haxis,hfold,hphysical⟩:=d.common_neighborhood
  obtain ⟨Rl,hRl,hRly,hlens⟩:=d.uniform_tilt_lens
  let R:ℝ:=min Rc Rl
  have hR:0<R:=lt_min hRc hRl
  have hRyc:R<y₀:=(min_le_right _ _).trans_lt hRly
  have hqR:AnalyticOnNhd ℂ d.q (Metric.ball 0 R ×ˢ Metric.ball 0 R):=by
    apply hq.mono
    intro z hz
    exact ⟨Metric.ball_subset_ball (min_le_left _ _) hz.1,Metric.ball_subset_ball (min_le_left _ _) hz.2⟩
  refine ⟨R,hR,hRyc,?_⟩
  intro δ hδ u hu
  have hdRc:‖(δ:ℂ)‖<Rc:=by
    rw[Complex.norm_of_nonneg hδ.1.le]
    exact hδ.2.trans_le (min_le_left _ _)
  have hdRl:δ∈Ioo (0:ℝ) Rl:=⟨hδ.1,hδ.2.trans_le (min_le_right _ _)⟩
  have hdR:δ∈Ioo (0:ℝ) (min R y₀):=⟨hδ.1,lt_min hδ.2 (hδ.2.trans hRyc)⟩
  have h0:d.q ((δ:ℂ),0)=1:=(haxis _ hdRc).1
  have hf:∀v:ℂ,‖v‖<R→X ((y₀:ℂ)-(δ:ℂ)*d.q ((δ:ℂ),v))=d.tiltPoint (δ:ℂ) v:=by
    intro v hv
    exact (hfold _ _ hdRc (hv.trans_le (min_le_left _ _))).1
  have hl:∀v:ℂ,‖v‖<R→‖d.tiltPoint (δ:ℂ) v‖<xCritical:=by
    intro v hv
    exact hlens δ hdRl v (hv.trans_le (min_le_right _ _))
  exact ⟨hl u hu,d.q_eq_planarInverse_of_lens P R δ hR hdR hqR h0 hf hl u hu⟩
end WP.Analysis
