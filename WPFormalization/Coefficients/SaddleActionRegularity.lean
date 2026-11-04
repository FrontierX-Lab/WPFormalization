import WPFormalization.Analysis.SaddleInverseSupport
import WPFormalization.Coefficients.UniformSaddleMeanBounds
import WPFormalization.Coefficients.UniformSaddleLogAction
/-! Regularity and endpoint bounds for the actual unscaled kernel saddle action. -/
set_option autoImplicit false
noncomputable section
namespace WP.Coefficients
open Set

def unscaledLogPotential (z:ℝ):ℝ:=-Real.log (H 0 z).re

lemma unscaledLogPotential_hasDerivAt (z:ℝ)(hz:z∈Icc (0:ℝ) (r 0)):
    HasDerivAt unscaledLogPotential (kernelLogSlope (z:ℂ)).re z:=by
  have hdH:=Complex.reCLM.hasFDerivAt.comp_hasDerivAt z (H_differentiable 0 (z:ℂ)).hasDerivAt.comp_ofReal
  have hdF:HasDerivAt unscaledLogPotential (-((deriv (H 0) (z:ℂ)).re/(H 0 (z:ℂ)).re)) z:=
    (hdH.log (H_zero_re_pos z hz).ne').neg
  convert hdF using 1
  rw[kernelLogSlope_real]
  simp only[Complex.ofReal_re]
  ring

lemma unscaled_log_potential_bounds:
    ∃C:ℝ,0 < C∧∀z∈Icc (0:ℝ) (r 0),
      0 ≤ deriv unscaledLogPotential z∧deriv unscaledLogPotential z ≤ C:=by
  obtain ⟨C,hC,hb⟩:=unscaledMean_uniform_linear_variance_bounds
  refine ⟨C,hC,?_⟩
  intro z hz
  rw[(unscaledLogPotential_hasDerivAt z hz).deriv]
  by_cases hz0:z=0
  · subst z
    rw[Complex.ofReal_zero,kernelLogSlope_zero]
    have hC0:=hb 0 ⟨le_rfl,(r_pos 0 ⟨le_rfl,y₀_pos⟩).le⟩
    have h1:deriv unscaledMean 0=1/5:=by
      rw[(unscaledMean_hasDerivAt 0 ⟨le_rfl,(r_pos 0 ⟨le_rfl,y₀_pos⟩).le⟩).deriv,Complex.ofReal_zero,kernelComplexMean_deriv_zero]
      norm_num
    rw[h1] at hC0
    norm_num only[Complex.div_re,Complex.one_re,Complex.ofReal_re,Complex.one_im,Complex.ofReal_im,mul_zero,add_zero,zero_add,zero_div,sub_zero] at *
    norm_num at *
    exact hC0.2.2
  · have hzpos:0 < z:=lt_of_le_of_ne hz.1 (Ne.symm hz0)
    have hlo:0 ≤ unscaledMean z:=(hb z hz).1.trans' (div_nonneg hz.1 (by norm_num))
    have hup:unscaledMean z ≤ C*z:=(hb z hz).2.1
    rw[unscaledMean_eq_logSlope] at hlo hup
    constructor  <;> nlinarith only[hlo,hup,hzpos]

lemma saddleZeta_ordered_lipschitz (u v:ℝ)(hu:u∈Icc (0:ℝ) (3/2))
    (hv:v∈Icc (0:ℝ) (3/2))(huv:u ≤ v):
    0 ≤ saddleZeta v-saddleZeta u∧saddleZeta v-saddleZeta u ≤ 5*(v-u):=by
  have H:=Analysis.inverse_parameter_ordered_lipschitz unscaledMean saddleZeta (r 0) (3/2) (1/5)
    (by norm_num) (fun z hz=> (unscaledMean_hasDerivAt z hz).differentiableAt)
    unscaledMean_strictMonoOn unscaledMean_deriv_lower saddleZeta_spec u v hu hv huv
  exact ⟨H.1,by nlinarith only[H.2]⟩
end WP.Coefficients
