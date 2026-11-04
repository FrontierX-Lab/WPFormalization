import WPFormalization.Volumes.ExtractionPhaseOrigin
import WPFormalization.Volumes.PrefactorIntegration
import WPFormalization.Analysis.ParameterInverse
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma extractionS_hasDerivAt_open (x:ℝ) (hx:x∈Ioo (0:ℝ) xCritical):
    HasDerivAt extractionS ((A (inverseY x)*r (inverseY x)*a (inverseY x))⁻¹) x:=by
  have hy:=inverseY_branch x ⟨hx.1.le,hx.2⟩
  have hYpos:0 < inverseY x:=by
    by_contra h
    have hz:inverseY x=0:=le_antisymm (not_lt.mp h) hy.1.1
    rw[hz,XR_zero] at hy
    linarith[hy.2,hx.1]
  have hdlog:=logZ_hasDerivAt_open_parameter (inverseY x) ⟨hYpos,hy.1.2⟩
  have hdcomp:=hdlog.comp x (inverseY_hasDerivAt_interior x ⟨hx.1.le,hx.2⟩)
  have hd:=(hasDerivAt_const x (Real.log (Z 0))).sub hdcomp
  have he:extractionS=ᶠ[𝓝 x] (fun t:ℝ=>Real.log (Z 0)-Real.log (Z (inverseY t))):=by
    filter_upwards[isOpen_Ioo.mem_nhds hx] with t ht
    have hty:inverseY t∈Ico (0:ℝ) y₀:=(inverseY_branch t ⟨ht.1.le,ht.2⟩).1
    exact Real.log_div (marked_Z_pos 0 ⟨le_rfl,y₀_pos⟩).ne' (marked_Z_pos _ hty).ne'
  convert! hd.congr_of_eventuallyEq he using 1
  simp only[zero_sub,neg_div,neg_mul,neg_neg,one_div,mul_inv_rev]
  ring
lemma extractionS_euler_eq_Psi (x:ℝ) (hx:x∈Ioo (0:ℝ) xCritical):
    x*deriv extractionS x=WP.Psi x:=by
  rw[(extractionS_hasDerivAt_open x hx).deriv]
  have hy:=inverseY_branch x ⟨hx.1.le,hx.2⟩
  rw[WP.Psi,density_J_formula_on_domain _ (stationaryParameterDomain_contains _ hy.1),J_sub_XR_eq_Aar (inverseY x) hy.1,hy.2]
  simp only[div_eq_mul_inv,mul_inv_rev]
  ring
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology
lemma extractionS_origin_complex_euler (S:ℂ → ℂ) (hS:AnalyticAt ℂ S 0)
    (hres:∀ᶠx:ℝ in 𝓝 0,0≤x→S (x:ℂ)=(extractionS x:ℂ)):
    ∀ᶠx:ℝ in 𝓝 0,0≤x→(x:ℂ)*deriv S (x:ℂ)=(WP.Psi x:ℂ):=by
  have ht:Tendsto (fun x:ℝ=>(x:ℂ)) (𝓝 0) (𝓝 (0:ℂ)):=by
    simpa only[Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto (x:=(0:ℝ))
  filter_upwards[ht.eventually hS.eventually_analyticAt,hres.eventually_nhds,
    eventually_lt_nhds xCritical_pos_parameter] with x hSx hloc hxx hx
  by_cases hx0:x=0
  · subst x
    simp only[Complex.ofReal_zero,zero_mul,Psi_zero_value]
  · have hxp:0<x:=lt_of_le_of_ne hx (Ne.symm hx0)
    have heq:(fun t:ℝ=>S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionS t:ℂ)):=by
      filter_upwards[hloc,eventually_gt_nhds hxp] with t ht htp
      exact ht htp.le
    have hsder:HasDerivAt (fun t:ℝ=>(extractionS t:ℂ)) (deriv S (x:ℂ)) x:=
      hSx.differentiableAt.hasDerivAt.comp_ofReal.congr_of_eventuallyEq heq.symm
    have hrder:HasDerivAt (fun t:ℝ=>(extractionS t:ℂ)) ((deriv extractionS x:ℝ):ℂ) x:=
      (extractionS_hasDerivAt_open x ⟨hxp,hxx⟩).differentiableAt.hasDerivAt.ofReal_comp
    rw[hsder.unique hrder,←Complex.ofReal_mul,extractionS_euler_eq_Psi x ⟨hxp,hxx⟩]
lemma exists_extractionS_origin_complex_phase:
    ∃S:ℂ → ℂ,AnalyticAt ℂ S 0∧S 0=0∧deriv S 0=2∧
      ∀ᶠx:ℝ in 𝓝 0,0≤x→S (x:ℂ)=(extractionS x:ℂ)∧
        (x:ℂ)*deriv S (x:ℂ)=(WP.Psi x:ℂ):=by
  obtain ⟨S,hS,hS0,hSd,hres⟩:=exists_extractionS_origin_complex_extension
  refine ⟨S,hS,hS0,hSd,?_⟩
  filter_upwards[hres,extractionS_origin_complex_euler S hS hres] with x hr he hx
  exact ⟨hr hx,he hx⟩
end WP.Analysis
