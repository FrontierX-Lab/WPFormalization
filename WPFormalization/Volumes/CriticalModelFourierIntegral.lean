import WPFormalization.Analysis.UniformMorseFiniteModel
import WPFormalization.Analysis.StationaryMatchingSupport
import WPFormalization.Volumes.CriticalModelGrowth
/-! Exact real scaling identifies the finite critical source divided by its base factor with the same centered model on the imaginary Fourier axis. -/
noncomputable section
open Set MeasureTheory
namespace WP.Analysis
lemma CriticalGaussianCoordinateData.finite_source_eq_centered_fourier_integral
    (d:CriticalGaussianCoordinateData) (Q:ℂ→ℂ) (p:ℕ) (f:ℕ→ℂ→ℂ)
    (δ:ℂ) (h T:ℝ) (J:ℕ) (hh:0<h) (hT:0≤T) :
    finiteMorseSourceIntegral (fun u:ℂ=>d.kernel.centeredPhase d.L d.q (δ,u))
        (fun s u=>d.preMorseAmplitude Q p f s (δ,u)) h (T/Real.sqrt h) J/
          HigherOrder.finiteMarkedFactor f h J ((y₀:ℂ)-δ)=
      ∫w:ℝ in Icc (-T) T,d.centeredFiniteMarkedModel Q p f h J δ (Complex.I*(w:ℂ)) := by
  let F:ℝ→ℂ:=fun u=>Complex.exp ((h:ℂ)*d.kernel.centeredPhase d.L d.q (δ,(u:ℂ)))*
    finiteMorseAmplitude (fun s u=>d.preMorseAmplitude Q p f s (δ,u)) h J (u:ℂ)
  have hs:0<Real.sqrt h:=Real.sqrt_pos.mpr hh
  have hτ:0<1/Real.sqrt h:=by positivity
  have hscale:=real_interval_integral_pos_rescale F (1/Real.sqrt h) (T/Real.sqrt h) hτ (by positivity)
  have hcut:(T/Real.sqrt h)/(1/Real.sqrt h)=T:=by field_simp[hs.ne']
  rw[hcut] at hscale
  have hscale':(∫w:ℝ in Icc (-T) T,F ((1/Real.sqrt h)*w))=
      finiteMorseSourceIntegral (fun u:ℂ=>d.kernel.centeredPhase d.L d.q (δ,u))
        (fun s u=>d.preMorseAmplitude Q p f s (δ,u)) h (T/Real.sqrt h) J := by
    rw[hscale,symmetric_set_integral_eq_interval _ (T/Real.sqrt h) (by positivity)]
    simp only[one_div,inv_inv,Complex.real_smul]
    rfl
  rw[←hscale',←integral_div]
  apply setIntegral_congr_fun measurableSet_Icc
  intro w hw
  dsimp only[CriticalGaussianCoordinateData.centeredFiniteMarkedModel,F]
  have hu:-Complex.I*(Complex.I*(w:ℂ))/(Real.sqrt h:ℂ)=(((1/Real.sqrt h)*w:ℝ):ℂ) := by
    calc _ = ((-Complex.I)*Complex.I)*(w:ℂ)/(Real.sqrt h:ℂ):=by ring
         _ = (w:ℂ)/(Real.sqrt h:ℂ):=by rw[neg_mul,Complex.I_mul_I,neg_neg,one_mul]
         _ = _:=by push_cast;ring
  rw[hu]
  rfl

lemma CriticalGaussianCoordinateData.shrinking_source_eq_centered_fourier_integral
    (d:CriticalGaussianCoordinateData) (Q:ℂ→ℂ) (p:ℕ) (f:ℕ→ℂ→ℂ)
    (δ:ℂ) (h τ:ℝ) (J:ℕ) (hh:0<h) (hτ:0≤τ) :
    finiteMorseSourceIntegral (fun u:ℂ=>d.kernel.centeredPhase d.L d.q (δ,u))
        (fun s u=>d.preMorseAmplitude Q p f s (δ,u)) h (τ/Real.sqrt (Real.sqrt h)) J/
          HigherOrder.finiteMarkedFactor f h J ((y₀:ℂ)-δ)=
      ∫w:ℝ in Icc (-(τ*Real.sqrt (Real.sqrt h))) (τ*Real.sqrt (Real.sqrt h)),
        d.centeredFiniteMarkedModel Q p f h J δ (Complex.I*(w:ℂ)) := by
  have he:=d.finite_source_eq_centered_fourier_integral Q p f δ h (τ*Real.sqrt (Real.sqrt h)) J hh (by positivity)
  have hscale:τ*Real.sqrt (Real.sqrt h)/Real.sqrt h=τ/Real.sqrt (Real.sqrt h) := by
    have hs:0<Real.sqrt (Real.sqrt h):=Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hh)
    have heq:Real.sqrt h=(Real.sqrt (Real.sqrt h))^2:=(Real.sq_sqrt (Real.sqrt_nonneg h)).symm
    calc _ = τ*Real.sqrt (Real.sqrt h)/(Real.sqrt (Real.sqrt h))^2:=congrArg (fun r:ℝ=>τ*Real.sqrt (Real.sqrt h)/r) heq
         _ = _:=by field_simp[hs.ne']
  rw[hscale] at he
  exact he
end WP.Analysis
