import WPFormalization.Analysis.GaussianFourier
import WPFormalization.Analysis.HarmonicL1
/-! A uniform lattice Gaussian error follows from the actual Fourier inversion
identity and an L1 characteristic-function error. This is a generic transfer
lemma, not an assumed local limit estimate for the WP model. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Complex
lemma gaussian_lattice_error_of_fourier_l1 (χ:ℝ→ℂ) (hχ:Integrable χ)
    (q a E:ℝ)
    (hinv:(a:ℂ)=((2*Real.pi:ℝ):ℂ)⁻¹*
      ∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*χ t)
    (hE:(∫t:ℝ,‖χ t-Complex.exp (-(t:ℂ)^2/2)‖)≤E):
    |a-Real.exp (-q^2/2)/Real.sqrt (2*Real.pi)|≤E/(2*Real.pi):=by
  let G:ℝ→ℂ:=fun t=>Complex.exp (-(t:ℂ)^2/2)
  have hG:Integrable G:=by
    have he:Integrable (fun t:ℝ=>Complex.exp (-((1:ℂ)/2)*(t:ℂ)^2)):=
      integrable_cexp_neg_mul_sq (by norm_num)
    convert he using 1
    funext t
    dsimp only[G]
    congr 1
    ring
  have hiχ:=real_fourier_phase_mul_integrable q χ hχ
  have hiG:=real_fourier_phase_mul_integrable q G hG
  have heq:((2*Real.pi:ℝ):ℂ)⁻¹*(∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*G t)=
      ((Real.exp (-q^2/2)/Real.sqrt (2*Real.pi):ℝ):ℂ):=by
    have hk:(fun t:ℝ=>Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*G t)=
        (fun t:ℝ=>Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*Complex.exp (-(1:ℂ)/2*(t:ℂ)^2)):=by
      funext t
      dsimp only[G]
      apply congrArg (fun z:ℂ=>Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*Complex.exp z)
      ring
    rw[hk]
    simpa only[mul_one,Complex.ofReal_one] using gaussian_fourier_normalized 1 q (by norm_num)

  have hdiff:((a-Real.exp (-q^2/2)/Real.sqrt (2*Real.pi):ℝ):ℂ)=
      ((2*Real.pi:ℝ):ℂ)⁻¹*(∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*(χ t-G t)):=by
    rw[Complex.ofReal_sub,hinv,←heq,←mul_sub,←integral_sub hiχ hiG]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun t=>by ring)
  have hnorm:(∫t:ℝ,‖Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*(χ t-G t)‖)=
      ∫t:ℝ,‖χ t-G t‖:=by
    congr 1
    funext t
    rw[norm_mul,real_fourier_phase_norm,one_mul]
  rw[←Real.norm_eq_abs,←Complex.norm_real,hdiff,norm_mul,norm_inv,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity:0<2*Real.pi)]
  apply (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity:(0:ℝ)≤(2*Real.pi)⁻¹)).trans
  rw[hnorm]
  convert mul_le_mul_of_nonneg_left hE (by positivity:(0:ℝ)≤(2*Real.pi)⁻¹) using 1 <;>ring
end WP.Analysis
