import WPFormalization.Analysis.RealPrimitiveDerivative
import WPFormalization.Analysis.OriginComplexInverse
import WPFormalization.Analysis.NormalizedComplexExtension
import WPFormalization.Volumes.PrefactorIntegration
import WPFormalization.Marked.UnmarkedReduction
/-! The actual extraction phase near zero. The log-action is extended from its
proved real differential equation with its original initial value, then
composed with the genuine complex local inverse of X. Its restriction equals
the displayed extractionS, and its derivative at zero is exactly two. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma exists_origin_log_action_extension:
    ∃G:ℂ → ℂ,AnalyticAt ℂ G 0∧G 0=0∧deriv G 0=2∧
      ∀ᶠY:ℝ in 𝓝 0,0≤Y→
        G (Y:ℂ)=((Real.log (Z 0)-Real.log (Z Y):ℝ):ℂ):=by
  obtain ⟨Ω,hΩ,hcover,R,Q,Ahat,hR,hQ,hA,hKH,hmatch,hunit,hraw,hRcrit,hR'⟩:=
    common_holomorphic_normalized_kernel_data
  have h0:(0:ℝ)∈Icc (0:ℝ) y₀:=⟨le_rfl,y₀_pos.le⟩
  have h0Ω:(0:ℂ)∈Ω:=by simpa only[Complex.ofReal_zero] using hcover 0 h0
  have hA0:Ahat 0=(A 0:ℂ):=by simpa only[Complex.ofReal_zero] using (hmatch 0 h0).2.1
  have hR0:R 0=(r 0:ℂ):=by simpa only[Complex.ofReal_zero] using hraw 0 ⟨le_rfl,y₀_pos⟩
  have hne:Ahat 0*R 0≠0:=by
    rw[hA0,hR0,←Complex.ofReal_mul]
    exact_mod_cast (mul_pos (marked_A_pos 0 h0) (r_pos 0 ⟨le_rfl,y₀_pos⟩)).ne'
  let q:ℂ → ℂ:=fun z=>(Ahat z*R z)⁻¹
  have hq:AnalyticAt ℂ q 0:=((hA 0 h0Ω).mul (hR 0 h0Ω)).inv hne
  have hq0:q 0=2:=by
    dsimp[q]
    rw[hA0,hR0,A_zero_parameter,r_zero_parameter]
    push_cast
    field_simp <;> ring
  obtain ⟨r,hr,hball⟩:=Metric.eventually_nhds_iff.mp hq.eventually_analyticAt
  have hqball:AnalyticOnNhd ℂ q (Metric.ball (0:ℂ) r):=by
    intro z hz
    exact hball hz
  let b:ℝ:=y₀/2
  have hb:0<b:=half_pos y₀_pos
  have hby:b<y₀:=half_lt_self y₀_pos
  let f:ℝ → ℝ:=fun Y=>Real.log (Z 0)-Real.log (Z Y)
  have hf:ContinuousOn f (Icc (0:ℝ) b):=
    continuousOn_const.sub (logZ_continuousOn_parameter.mono (by intro Y hY;exact ⟨hY.1,hY.2.trans_lt hby⟩))
  have hdf(Y:ℝ) (hY:Y∈Ioo (0:ℝ) b):HasDerivAt (fun t:ℝ=>(f t:ℂ)) (q (Y:ℂ)) Y:=by
    have hYi:Y∈Ico (0:ℝ) y₀:=⟨hY.1.le,hY.2.trans hby⟩
    have hd:HasDerivAt f ((A Y*WP.r Y)⁻¹) Y:=by
      convert! (hasDerivAt_const Y (Real.log (Z 0))).sub
        (logZ_hasDerivAt_open_parameter Y ⟨hY.1,hYi.2⟩) using 1 <;> simp only[zero_sub,neg_div,neg_neg,one_div]
    have he:q (Y:ℂ)=(((A Y*WP.r Y)⁻¹:ℝ):ℂ):=by
      dsimp[q]
      rw[(hmatch Y ⟨hYi.1,hYi.2.le⟩).2.1,hraw Y hYi]
      push_cast
      rfl
    rw[he]
    exact hd.ofReal_comp
  obtain ⟨G,hG,hGd,hGmatch⟩:=real_primitive_complex_extension_with_derivative_on_ball 0 b hb f hf
    (Metric.ball (0:ℂ) r) q hqball hdf 0 ⟨le_rfl,hb.le⟩ r hr (by intro z hz;exact hz)
  have hzero:(0:ℂ)∈Metric.ball (0:ℂ) r:=Metric.mem_ball_self hr
  refine ⟨G,hG 0 hzero,?_,?_,?_⟩
  · simpa only[Complex.ofReal_zero,f,sub_self] using hGmatch 0 ⟨le_rfl,hb.le⟩ hzero
  · rw[(hGd 0 hzero).deriv,hq0]
  · have hrmem:∀ᶠY:ℝ in 𝓝 0,‖Y‖<r:=by
      filter_upwards[Metric.ball_mem_nhds (0:ℝ) hr] with Y hY
      simpa only[Metric.mem_ball,dist_zero_right] using hY
    filter_upwards[hrmem,eventually_lt_nhds hb] with Y hYr hYb hY0
    exact hGmatch Y ⟨hY0,hYb.le⟩ (by simpa only[Metric.mem_ball,Complex.ofReal_zero,dist_zero_right,Complex.norm_real] using hYr)
lemma exists_extractionS_origin_complex_extension:
    ∃S:ℂ → ℂ,AnalyticAt ℂ S 0∧S 0=0∧deriv S 0=2∧
      ∀ᶠx:ℝ in 𝓝 0,0≤x→S (x:ℂ)=(extractionS x:ℂ):=by
  obtain ⟨G,hG,hG0,hGd,hGmatch⟩:=exists_origin_log_action_extension
  obtain ⟨Y,hY,hY0,hYd,hYmatch⟩:=exists_origin_complex_inverse
  let S:ℂ → ℂ:=fun z=>G (Y z)
  have hS:AnalyticAt ℂ S 0:=by
    have hh:AnalyticAt ℂ G (Y 0):=by rw[hY0];exact hG
    exact hh.comp (f:=Y) hY
  have hS0:S 0=0:=by dsimp[S];rw[hY0,hG0]
  have hSd:deriv S 0=2:=by
    have hg:HasDerivAt G (deriv G 0) (Y 0):=by rw[hY0];exact hG.differentiableAt.hasDerivAt
    have hh:=hg.comp 0 hY.differentiableAt.hasDerivAt
    simpa only[Function.comp_def,S,hGd,hYd,mul_one] using hh.deriv
  have hInv:AnalyticAt ℝ inverseY 0:=by
    simpa only[XR_zero] using (inverseY_analytic_hasDerivAt_of_lt 0 y₀_pos).1
  have ht:Tendsto inverseY (𝓝 0) (𝓝 (0:ℝ)):=by
    simpa only[inverseY_zero_value] using hInv.continuousAt.tendsto
  refine ⟨S,hS,hS0,hSd,?_⟩
  filter_upwards[hYmatch,ht.eventually hGmatch,eventually_lt_nhds xCritical_pos_parameter] with x hy hg hx hx0
  have hix:inverseY x∈Ico (0:ℝ) y₀:=(inverseY_branch x ⟨hx0,hx⟩).1
  dsimp[S]
  rw[hy,hg hix.1]
  congr 1
  rw[extractionS,Real.log_div (marked_Z_pos 0 ⟨le_rfl,y₀_pos⟩).ne' (marked_Z_pos _ hix).ne']
end WP.Analysis
