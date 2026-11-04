import WPFormalization.Analysis.HarmonicL1
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma fourier_coefficient_integrand_periodic (f:ℂ→ℂ)(n:ℕ) :
    Function.Periodic (fun t:ℝ=>Complex.exp (-(n:ℂ)*(t:ℂ)*Complex.I)*f (Complex.exp ((t:ℂ)*Complex.I))) (2*Real.pi) := by
  intro t
  have he : (((t+2*Real.pi):ℝ):ℂ)*Complex.I=(t:ℂ)*Complex.I+2*(Real.pi:ℂ)*Complex.I := by push_cast; ring
  have hp : Complex.exp ((((t+2*Real.pi):ℝ):ℂ)*Complex.I)=Complex.exp ((t:ℂ)*Complex.I) := by
    rw [he,Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]
  have hn : Complex.exp (-(n:ℂ)*(((t+2*Real.pi):ℝ):ℂ)*Complex.I)=Complex.exp (-(n:ℂ)*(t:ℂ)*Complex.I) := by
    have he : -(n:ℂ)*(((t+2*Real.pi):ℝ):ℂ)*Complex.I=-(n:ℂ)*(t:ℂ)*Complex.I-(n:ℂ)*(2*(Real.pi:ℂ)*Complex.I) := by push_cast; ring
    rw [he,Complex.exp_sub,Complex.exp_nat_mul,Complex.exp_two_pi_mul_I,one_pow,div_one]
  dsimp only
  rw [hp,hn]
lemma coeff_eq_symmetric_fourier_integral (f:ℂ→ℂ)
    (hf:DifferentiableOn ℂ f (Metric.closedBall 0 1))(n:ℕ) :
    WP.coeff f n = ((2*Real.pi:ℝ):ℂ)⁻¹ * ∫ θ:ℝ in (-Real.pi)..Real.pi,
      Complex.exp (-(n:ℂ)*(θ:ℂ)*Complex.I)*f (Complex.exp ((θ:ℂ)*Complex.I)) := by
  have h := (fourier_coefficient_integrand_periodic f n).intervalIntegral_add_eq 0 (-Real.pi)
  rw [zero_add,show -Real.pi+2*Real.pi=Real.pi by ring] at h
  rw [coeff_eq_fourier_integral f hf n,h]
end WP.Analysis

namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma harmonicSumMass_coeff_complex (Y:ℝ)(hY:Y∈Icc 0 y₀)(h m:ℕ) :
    WP.coeff (fun w=>harmonicPGF Y w^h) m=(harmonicSumMass Y h m:ℂ) := by
  have hA : AnalyticAt ℂ (harmonicPGF Y) 0 :=
    analyticAt_const.div ((barH_differentiable Y).analyticAt 0) (by rw [barH_zero Y hY]; exact one_ne_zero)
  have hR := realCoefficients_pow hA (harmonicPGF_realCoefficients Y hY) h
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using hR m
lemma harmonic_fourier_centering (Y:ℝ)(h m:ℕ)(t:ℝ) :
    Complex.exp (-(m:ℂ)*(t:ℂ)*Complex.I)*harmonicPGF Y (Complex.exp ((t:ℂ)*Complex.I))^h =
      Complex.exp (-(((m:ℝ)-3*(h:ℝ)/2:ℝ):ℂ)*(t:ℂ)*Complex.I)*centeredHarmonic Y (t:ℂ)^h := by
  unfold centeredHarmonic
  rw [mul_pow,←Complex.exp_nat_mul,←mul_assoc,←Complex.exp_add]
  congr 1 <;> congr 1 <;> push_cast <;> ring
lemma harmonicSumMass_symmetric_fourier_complex (Y:ℝ)(hY:Y∈Icc 0 y₀)(h m:ℕ) :
    (harmonicSumMass Y h m:ℂ) = ((2*Real.pi:ℝ):ℂ)⁻¹ * ∫t:ℝ in (-Real.pi)..Real.pi,
      Complex.exp (-(m:ℂ)*(t:ℂ)*Complex.I)*harmonicPGF Y (Complex.exp ((t:ℂ)*Complex.I))^h := by
  obtain ⟨η,hη,hzero⟩ := barH_uniform_zero_free
  have hdiff : DifferentiableOn ℂ (fun w=>harmonicPGF Y w^h) (Metric.closedBall 0 1) :=
    ((harmonicPGF_diffOn hη hzero Y hY).mono (Metric.closedBall_subset_closedBall (by linarith))).pow h
  rw [←harmonicSumMass_coeff_complex Y hY h m,coeff_eq_symmetric_fourier_integral _ hdiff m]
lemma harmonicSumMass_scaled_fourier (Y:ℝ)(hY:Y∈Icc 0 y₀)(h m:ℕ)(hh:0<h) :
    ((Real.sqrt (h:ℝ):ℝ):ℂ)*(harmonicSumMass Y h m:ℂ) =
      ((2*Real.pi:ℝ):ℂ)⁻¹ * ∫t:ℝ,
        Complex.exp (-(((((m:ℝ)-3*(h:ℝ)/2)/Real.sqrt (h:ℝ):ℝ):ℂ))*(t:ℂ)*Complex.I)*scaledHarmonicFourier Y h t := by
  let r := Real.sqrt (h:ℝ)
  let d := (m:ℝ)-3*(h:ℝ)/2
  let q := d/r
  let G (t:ℝ) : ℂ := Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*centeredHarmonic Y ((t/r:ℝ):ℂ)^h
  have hr : 0<r := Real.sqrt_pos.mpr (by exact_mod_cast hh)
  have hrc : (r:ℂ)≠0 := by exact_mod_cast ne_of_gt hr
  have hcomp : (fun t:ℝ=>Complex.exp (-(m:ℂ)*(t:ℂ)*Complex.I)*harmonicPGF Y (Complex.exp ((t:ℂ)*Complex.I))^h) =
      (fun t:ℝ=>G (r*t)) := by
    ext t
    rw [harmonic_fourier_centering]
    dsimp only [G]
    rw [show r*t/r=t by field_simp]
    congr 1
    congr 1
    dsimp [q,d]
    push_cast
    field_simp
    <;> ring
  have hInt := intervalIntegral.integral_comp_mul_left G (ne_of_gt hr) (a := -Real.pi) (b := Real.pi)
  rw [show r*(-Real.pi)=-(Real.pi*r) by ring,show r*Real.pi=Real.pi*r by ring] at hInt
  have hfull : (∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*scaledHarmonicFourier Y h t) =
      ∫t:ℝ in (-(Real.pi*r))..(Real.pi*r),G t := by
    have he : (fun t:ℝ=>Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*scaledHarmonicFourier Y h t) =
        (Icc (-(Real.pi*r)) (Real.pi*r)).indicator G := by
      ext t
      rw [scaledHarmonicFourier_indicator]
      change Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I) *
        (Icc (-(Real.pi*r)) (Real.pi*r)).indicator (fun t:ℝ=>centeredHarmonic Y ((t/r:ℝ):ℂ)^h) t =
        (Icc (-(Real.pi*r)) (Real.pi*r)).indicator G t
      by_cases ht:t∈Icc (-(Real.pi*r)) (Real.pi*r)
      · simp only [Set.indicator_of_mem ht,G]
      · simp only [Set.indicator_of_notMem ht,mul_zero]
    rw [he,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by nlinarith [mul_pos Real.pi_pos hr] : -(Real.pi*r)≤Real.pi*r)]
  change (r:ℂ)*(harmonicSumMass Y h m:ℂ) = ((2*Real.pi:ℝ):ℂ)⁻¹*(∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*scaledHarmonicFourier Y h t)
  rw [harmonicSumMass_symmetric_fourier_complex Y hY h m,hcomp,hInt,hfull]
  simp only [Complex.real_smul,Complex.ofReal_inv]
  field_simp
end WP.Analysis
