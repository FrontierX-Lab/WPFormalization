import WPFormalization.Analysis.AnalyticNegativeFourier
import WPFormalization.Analysis.HarmonicFourierScaling
/-! Exact circle inversion for every integer index, including vanishing negative
indices, followed by centering and variance rescaling. These are identities;
no local-limit or characteristic-function error estimate is assumed here. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Set Complex

def signedTaylorCoeff (f:ℂ→ℂ)(k:ℤ):ℂ:=if 0≤k then WP.coeff f k.toNat else 0

lemma signedTaylorCoeff_fourier (f:ℂ→ℂ)(R:ℝ)(hR:1<R)
    (hf:DifferentiableOn ℂ f (Metric.ball 0 R))(k:ℤ):
    signedTaylorCoeff f k=((2*Real.pi:ℝ):ℂ)⁻¹*
      ∫θ:ℝ in (-Real.pi)..Real.pi,Complex.exp (-(k:ℂ)*(θ:ℂ)*Complex.I)*f (Complex.exp ((θ:ℂ)*Complex.I)):=by
  by_cases hk:0≤k
  · rw[signedTaylorCoeff,ite_eq_left hk]
    have hd:DifferentiableOn ℂ f (Metric.closedBall 0 1):=hf.mono
      (Metric.closedBall_subset_ball (by linarith))
    have hcast:((k.toNat:ℕ):ℂ)=(k:ℂ):=by exact_mod_cast Int.toNat_of_nonneg hk
    simpa only[hcast] using coeff_eq_symmetric_fourier_integral f hd k.toNat
  · have hkneg:k<0:=lt_of_not_ge hk
    let m:ℕ:=(-k).toNat-1
    have hm:k=-((m+1:ℕ):ℤ):=by dsimp[m];omega
    have hcast:-(k:ℂ)=((m+1:ℕ):ℂ):=by exact_mod_cast (show -k=((m+1:ℕ):ℤ) by omega)
    have he:(fun θ:ℝ=>Complex.exp (-(k:ℂ)*(θ:ℂ)*Complex.I)*f (Complex.exp ((θ:ℂ)*Complex.I)))=
        (fun θ:ℝ=>Complex.exp ((θ:ℂ)*Complex.I)^(m+1)*f (Complex.exp ((θ:ℂ)*Complex.I))):=by
      funext θ
      rw[hcast,show ((m+1:ℕ):ℂ)*(θ:ℂ)*Complex.I=((m+1:ℕ):ℂ)*((θ:ℂ)*Complex.I) by ring,
        Complex.exp_nat_mul]
    rw[signedTaylorCoeff,ite_eq_right hk,he,analytic_circle_negative_fourier f R hR hf m,mul_zero]


/-- Centered, variance-scaled circle transform, extended by zero off its period. -/
def scaledCenteredFourier (f:ℂ→ℂ) (μ σ:ℝ) (t:ℝ):ℂ :=
  (Icc (-(Real.pi*σ)) (Real.pi*σ)).indicator
    (fun t:ℝ=>Complex.exp (-(μ:ℂ)*((t/σ:ℝ):ℂ)*Complex.I)*
      f (Complex.exp (((t/σ:ℝ):ℂ)*Complex.I))) t

lemma signedTaylorCoeff_scaled_fourier (f:ℂ→ℂ)(R:ℝ)(hR:1<R)
    (hf:DifferentiableOn ℂ f (Metric.ball 0 R))(μ σ:ℝ)(hσ:0<σ)(k:ℤ):
    (σ:ℂ)*signedTaylorCoeff f k=((2*Real.pi:ℝ):ℂ)⁻¹*
      ∫t:ℝ,Complex.exp (-((((k:ℝ)-μ)/σ:ℝ):ℂ)*(t:ℂ)*Complex.I)*
        scaledCenteredFourier f μ σ t:=by
  have hσc:(σ:ℂ)≠0:=by exact_mod_cast ne_of_gt hσ
  let q:ℝ:=((k:ℝ)-μ)/σ
  let G:ℝ→ℂ:=fun t=>Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*
    (Complex.exp (-(μ:ℂ)*((t/σ:ℝ):ℂ)*Complex.I)*
      f (Complex.exp (((t/σ:ℝ):ℂ)*Complex.I)))
  have hcomp:(fun t:ℝ=>Complex.exp (-(k:ℂ)*(t:ℂ)*Complex.I)*f (Complex.exp ((t:ℂ)*Complex.I)))=
      (fun t:ℝ=>G (σ*t)):=by
    funext t
    dsimp only[G]
    rw[show σ*t/σ=t by field_simp,←mul_assoc,←Complex.exp_add]
    congr 2
    dsimp[q]
    push_cast
    field_simp [hσc]
    <;>ring
  have hInt:=intervalIntegral.integral_comp_mul_left G (ne_of_gt hσ) (a := -Real.pi) (b := Real.pi)
  rw[show σ*(-Real.pi)=-(Real.pi*σ) by ring,show σ*Real.pi=Real.pi*σ by ring] at hInt
  have hfull:(∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*scaledCenteredFourier f μ σ t)=
      ∫t:ℝ in (-(Real.pi*σ))..(Real.pi*σ),G t:=by
    have he:(fun t:ℝ=>Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*scaledCenteredFourier f μ σ t)=
        (Icc (-(Real.pi*σ)) (Real.pi*σ)).indicator G:=by
      funext t
      by_cases ht:t∈Icc (-(Real.pi*σ)) (Real.pi*σ)
      · simp only[scaledCenteredFourier,Set.indicator_of_mem ht,G]
      · simp only[scaledCenteredFourier,Set.indicator_of_notMem ht,mul_zero]
    rw[he,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
      ←intervalIntegral.integral_of_le (by nlinarith[mul_pos Real.pi_pos hσ]:-(Real.pi*σ)≤Real.pi*σ)]
  change (σ:ℂ)*signedTaylorCoeff f k=((2*Real.pi:ℝ):ℂ)⁻¹*
    (∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*scaledCenteredFourier f μ σ t)
  rw[signedTaylorCoeff_fourier f R hR hf k,hcomp,hInt,hfull]
  simp only[Complex.real_smul,Complex.ofReal_inv]
  field_simp [hσc]

lemma scaledCenteredFourier_integrable (f:ℂ→ℂ)(hf:ContinuousOn f (Metric.sphere 0 1))
    (μ σ:ℝ):Integrable (scaledCenteredFourier f μ σ):=by
  let F:ℝ→ℂ:=fun t=>Complex.exp (-(μ:ℂ)*((t/σ:ℝ):ℂ)*Complex.I)*
    f (Complex.exp (((t/σ:ℝ):ℂ)*Complex.I))
  have hc:Continuous F:=by
    have he:Continuous (fun t:ℝ=>Complex.exp (((t/σ:ℝ):ℂ)*Complex.I)):=by fun_prop
    have hfcomp:Continuous (fun t:ℝ=>f (Complex.exp (((t/σ:ℝ):ℂ)*Complex.I))):=
      hf.comp_continuous he (fun t=>by
        simp only[Metric.mem_sphere,dist_zero_right,Complex.norm_exp]
        simp)
    exact (by fun_prop:Continuous (fun t:ℝ=>Complex.exp (-(μ:ℂ)*((t/σ:ℝ):ℂ)*Complex.I))).mul hfcomp
  exact (hc.integrableOn_Icc).integrable_indicator measurableSet_Icc
end WP.Analysis
