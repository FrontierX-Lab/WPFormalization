import WPFormalization.Statements.Coefficients
import WPFormalization.Analysis.HarmonicSumProbability
import WPFormalization.Analysis.HKernelZeroFree
import WPFormalization.Analysis.CoefficientSubstitution
import WPFormalization.Analysis.ParameterZeroValues
/-! Faithful uniform saddle estimate for the actual unscaled H(0) kernel: Basic. -/
noncomputable section
namespace WP
open Set
lemma unscaledMean_zero : unscaledMean 0=0:=by simp[unscaledMean]
lemma saddleZeta_zero : saddleZeta 0=0:=by
  let S:Set ℝ:={z:ℝ|z∈Icc (0:ℝ) (Real.pi^2/2)∧unscaledMean z=0}
  have hzero:(0:ℝ)∈S:=⟨⟨le_rfl,by positivity⟩,unscaledMean_zero⟩
  have hb:BddBelow S:=⟨0,fun z hz=>hz.1.1⟩
  apply le_antisymm
  · exact csInf_le hb hzero
  · exact le_csInf ⟨0,hzero⟩ (fun z hz=>hz.1.1)
lemma unscaledCoeff_zero (h:ℕ):unscaledCoeff h 0=1:=by
  simp[unscaledCoeff,realCoeff,coeff,H_zero,Analysis.derivX_zero]
lemma uniform_saddle_zero_exact (h:ℕ):
    Real.log (unscaledCoeff h 0)+(h:ℝ)*Real.log (H 0 (saddleZeta (((0:ℕ):ℝ)/h))).re+
      ((0:ℕ):ℝ)*Real.log (saddleZeta (((0:ℕ):ℝ)/h))=0:=by
  simp[unscaledCoeff_zero,saddleZeta_zero,H_zero,Analysis.derivX_zero]
lemma harmonicCoeff_zero_unscaled (h m:ℕ):
    harmonicCoeff 0 h m=(r 0)^m*unscaledCoeff h m:=by
  have he:(fun z:ℂ=>(barH 0 z)⁻¹^h)=(fun z:ℂ=>(H 0 ((r 0:ℂ)*z))⁻¹^h):=by
    funext z
    simp only[barH,ite_eq_right (ne_of_lt y₀_pos),a_zero,Complex.ofReal_one,Complex.ofReal_zero,div_one]
  unfold harmonicCoeff
  rw[he]
  exact Analysis.realCoeff_comp_mul_left (fun z:ℂ=>(H 0 z)⁻¹^h) (r 0) m
lemma unscaledCoeff_pos (h m:ℕ)(hh:0<h):0<unscaledCoeff h m:=by
  unfold unscaledCoeff
  rw[Analysis.realCoeff_inv_pow_eq_exp (H 0) (H_differentiable 0).continuous.continuousAt
    (by rw[H_zero,Analysis.derivX_zero];norm_num) h m]
  exact Analysis.H_negative_power_coeff_pos 0 ⟨le_rfl,y₀_pos⟩ (h:ℝ) (by exact_mod_cast hh) m
namespace Coefficients

def tiltedKernelPGF (z:ℝ)(w:ℂ):ℂ:=H 0 z/H 0 ((z:ℂ)*w)
def tiltedKernelMass (z:ℝ)(h m:ℕ):ℝ:=realCoeff (fun w:ℂ=>(tiltedKernelPGF z w)^h) m
lemma H_zero_real (z:ℝ):H 0 (z:ℂ)=((H 0 (z:ℂ)).re:ℂ):=by
  apply Complex.ext
  · rfl
  · have hi:=Analysis.entire_ofReal_im_zero_of_realCoefficients (H 0) (H_differentiable 0)
      (Analysis.H_realCoefficients_ofReal 0) z
    simpa only[Complex.ofReal_im] using hi
lemma tiltedKernelMass_eq_unscaled (z:ℝ)(h m:ℕ):
    tiltedKernelMass z h m=(H 0 z).re^h*z^m*unscaledCoeff h m:=by
  have he:(fun w:ℂ=>(tiltedKernelPGF z w)^h)=
      (fun w:ℂ=>Complex.ofReal ((H 0 z).re^h)*(H 0 ((z:ℂ)*w))⁻¹^h):=by
    funext w
    unfold tiltedKernelPGF
    rw[div_pow,div_eq_mul_inv,H_zero_real z,Complex.ofReal_pow]
    simp only[inv_pow,Complex.ofReal_re]
  unfold tiltedKernelMass
  rw[he,Analysis.realCoeff_const_mul,Analysis.realCoeff_comp_mul_left (fun w:ℂ=>(H 0 w)⁻¹^h) z m]
  change (H 0 z).re^h*(z^m*unscaledCoeff h m)=(H 0 z).re^h*z^m*unscaledCoeff h m
  ring
end Coefficients
end WP
