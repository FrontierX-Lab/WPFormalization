import WPFormalization.Volumes.StringFlowProof
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
noncomputable section
namespace WP.Analysis
open Filter
open scoped Topology
lemma exists_origin_complex_inverse:
    ∃Y:ℂ → ℂ,AnalyticAt ℂ Y 0∧Y 0=0∧deriv Y 0=1∧
      ∀ᶠx:ℝ in 𝓝 0,Y (x:ℂ)=(inverseY x:ℂ):=by
  have hX0:X 0=0:=by simp[X]
  have hX:AnalyticAt ℂ X 0:=X_differentiable.analyticAt 0
  have hd:deriv X 0≠0:=by rw[derivX_zero];exact one_ne_zero
  let Y:=hX.hasStrictDerivAt.localInverse X (deriv X 0) 0 hd
  have hY:AnalyticAt ℂ Y 0:=by
    have hh:=hX.analyticAt_localInverse hd
    simpa only[hX0] using hh
  have hY0:Y 0=0:=by
    have hh:=hX.hasStrictDerivAt.eventually_left_inverse hd |>.self_of_nhds
    simpa only[hX0] using hh
  have hYd:deriv Y 0=1:=by
    have hh:HasDerivAt Y (deriv X 0)⁻¹ (X 0):=(hX.hasStrictDerivAt.to_localInverse hd).hasDerivAt
    simpa only[hX0,derivX_zero,inv_one] using hh.deriv
  have hi:∀ᶠz:ℂ in 𝓝 0,Y (X z)=z:=hX.hasStrictDerivAt.eventually_left_inverse hd
  have hInv:AnalyticAt ℝ inverseY 0:=by
    simpa only[XR_zero] using (inverseY_analytic_hasDerivAt_of_lt 0 y₀_pos).1
  have ht:Tendsto (fun x:ℝ=>(inverseY x:ℂ)) (𝓝 0) (𝓝 (0:ℂ)):=by
    have hh:=Complex.continuous_ofReal.continuousAt.comp hInv.continuousAt |>.tendsto
    simpa only[Function.comp_def,inverseY_zero_value,Complex.ofReal_zero] using hh
  have hxr:∀ᶠx:ℝ in 𝓝 0,XR (inverseY x)=x:=by
    have hh:=XR_inverseY_eventually_of_lt 0 y₀_pos
    rw[XR_zero] at hh
    filter_upwards[hh] with x hx
    exact hx.1
  refine ⟨Y,hY,hY0,hYd,?_⟩
  filter_upwards[ht.eventually hi,hxr] with x hy hx
  have he:X (inverseY x:ℂ)=(x:ℂ):=by
    apply Complex.ext
    · exact hx
    · simpa only[Complex.ofReal_im] using X_im_ofReal (inverseY x)
  simpa only[he] using hy
end WP.Analysis
