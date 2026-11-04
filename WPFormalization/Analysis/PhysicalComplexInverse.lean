import WPFormalization.Analysis.OriginComplexInverse
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma exists_physical_complex_inverse (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):
    ∃Y:ℂ → ℂ,AnalyticAt ℂ Y (x:ℂ)∧Y (x:ℂ)=(inverseY x:ℂ)∧
      deriv Y (x:ℂ)=((a (inverseY x))⁻¹:ℝ)∧
      ∀ᶠt:ℝ in 𝓝 x,Y (t:ℂ)=(inverseY t:ℂ):=by
  have hy:=inverseY_branch x hx
  have he:X (inverseY x:ℂ)=(x:ℂ):=by
    apply Complex.ext
    · exact hy.2
    · simpa only[Complex.ofReal_im] using X_im_ofReal (inverseY x)
  have hX:AnalyticAt ℂ X (inverseY x:ℂ):=X_differentiable.analyticAt _
  have hd:deriv X (inverseY x:ℂ)≠0:=by
    rw[derivX_ofReal]
    exact_mod_cast (a_pos (inverseY x) hy.1).ne'
  let Y:=hX.hasStrictDerivAt.localInverse X (deriv X (inverseY x:ℂ)) (inverseY x:ℂ) hd
  have hY:AnalyticAt ℂ Y (x:ℂ):=by
    have hh:=hX.analyticAt_localInverse hd
    simpa only[he] using hh
  have hY0:Y (x:ℂ)=(inverseY x:ℂ):=by
    have hh:=hX.hasStrictDerivAt.eventually_left_inverse hd |>.self_of_nhds
    simpa only[he] using hh
  have hYd:deriv Y (x:ℂ)=((a (inverseY x))⁻¹:ℝ):=by
    have hh:HasDerivAt Y (deriv X (inverseY x:ℂ))⁻¹ (X (inverseY x:ℂ)):=
      (hX.hasStrictDerivAt.to_localInverse hd).hasDerivAt
    simpa only[he,derivX_ofReal,Complex.ofReal_inv] using hh.deriv
  have hi:∀ᶠz:ℂ in 𝓝 (inverseY x:ℂ),Y (X z)=z:=hX.hasStrictDerivAt.eventually_left_inverse hd
  have hInv:AnalyticAt ℝ inverseY x:=inverseY_analyticAt_interior x hx
  have ht:Tendsto (fun t:ℝ=>(inverseY t:ℂ)) (𝓝 x) (𝓝 (inverseY x:ℂ)):=by
    simpa only[Function.comp_def] using
      (Complex.continuous_ofReal.continuousAt.comp hInv.continuousAt).tendsto
  have hxr:∀ᶠt:ℝ in 𝓝 x,XR (inverseY t)=t:=by
    have hh:=XR_inverseY_eventually_of_lt (inverseY x) hy.1.2
    rw[hy.2] at hh
    filter_upwards[hh] with t ht
    exact ht.1
  refine ⟨Y,hY,hY0,hYd,?_⟩
  filter_upwards[ht.eventually hi,hxr] with t hy ht
  have he:X (inverseY t:ℂ)=(t:ℂ):=by
    apply Complex.ext
    · exact ht
    · simpa only[Complex.ofReal_im] using X_im_ofReal (inverseY t)
  simpa only[he] using hy
end WP.Analysis
