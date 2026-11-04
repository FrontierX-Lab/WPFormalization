import WPFormalization.Analysis.SourceScaledFourier
import WPFormalization.Analysis.FourierCentralModelTransfer
/-! Full coefficient comparison from a genuine central Fourier comparison,
two outer tails, a full L1 bound and the actual source prefactor difference. -/
noncomputable section
namespace WP.Analysis
open Set MeasureTheory
lemma coefficient_prefactor_full_model_error (F G:ℝ→ℂ)(A B:ℂ)
    (T E RF RG L D δ:ℝ)(hT:0≤T)(hF:Integrable F)(hG:Integrable G)
    (hpoint:∀t∈Icc (-T) T,‖F t-G t‖≤E)
    (htailF:(∫t:ℝ in (Icc (-T) T)ᶜ,‖F t‖)≤RF)
    (htailG:(∫t:ℝ in (Icc (-T) T)ᶜ,‖G t‖)≤RG)
    (hfull:(∫t:ℝ,‖F t‖)≤L)(hB:‖B‖≤D)(hAB:‖A-B‖≤δ):
    ‖A*(∫t:ℝ,F t)-B*(∫t:ℝ,G t)‖≤δ*L+D*(RF+RG+2*T*E):=by
  have hcentral:=coefficient_prefactor_local_model_error F G A B T E RF L D δ hT hF hG.integrableOn hpoint htailF hfull hB hAB
  have htail:‖(∫t:ℝ,G t)-(∫t:ℝ in Icc (-T) T,G t)‖≤RG:=by
    simpa only[sub_self,norm_zero,mul_zero,add_zero] using
      integral_sub_local_model_norm G G T 0 RG hT hG hG.integrableOn (fun t ht=>by simp) htailG
  have hmodel:‖B*(∫t:ℝ in Icc (-T) T,G t)-B*(∫t:ℝ,G t)‖≤D*RG:=by
    rw[←mul_sub,norm_mul,norm_sub_rev]
    exact mul_le_mul hB htail (norm_nonneg _) ((norm_nonneg _).trans hB)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add hcentral hmodel).trans_eq (by ring))
lemma source_coefficient_comparison (F G:ℂ→ℂ)(x R σ:ℝ)(k:ℕ)(Q:ℂ)
    (hx:0<x)(hxR:x<R)(hσ:0<σ)(hQ:Q≠0)(hFx:F (x:ℂ)≠0)(hGx:G (x:ℂ)≠0)
    (hF:AnalyticOnNhd ℂ F (Metric.ball 0 R))(hG:AnalyticOnNhd ℂ G (Metric.ball 0 R))
    (T E RF RG L D δ:ℝ)(hT:0≤T)
    (hpoint:∀t∈Icc (-T) T,‖scaledCenteredFourier (sourceCirclePGF F x) (k:ℝ) σ t-
      scaledCenteredFourier (sourceCirclePGF G x) (k:ℝ) σ t‖≤E)
    (htailF:(∫t:ℝ in (Icc (-T) T)ᶜ,‖scaledCenteredFourier (sourceCirclePGF F x) (k:ℝ) σ t‖)≤RF)
    (htailG:(∫t:ℝ in (Icc (-T) T)ᶜ,‖scaledCenteredFourier (sourceCirclePGF G x) (k:ℝ) σ t‖)≤RG)
    (hfull:(∫t:ℝ,‖scaledCenteredFourier (sourceCirclePGF F x) (k:ℝ) σ t‖)≤L)
    (hB:‖G (x:ℂ)/((x:ℂ)^k*(σ:ℂ)*Q)‖≤D)
    (hAB:‖F (x:ℂ)/((x:ℂ)^k*(σ:ℂ)*Q)-G (x:ℂ)/((x:ℂ)^k*(σ:ℂ)*Q)‖≤δ):
    ‖WP.coeff F k/Q-WP.coeff G k/Q‖≤(δ*L+D*(RF+RG+2*T*E))/(2*Real.pi):=by
  have hFi:=scaledCenteredFourier_integrable (sourceCirclePGF F x)
    (sourceCirclePGF_sphere_continuous F x R hx hxR hF) (k:ℝ) σ
  have hGi:=scaledCenteredFourier_integrable (sourceCirclePGF G x)
    (sourceCirclePGF_sphere_continuous G x R hx hxR hG) (k:ℝ) σ
  have he:=coefficient_prefactor_full_model_error
    (scaledCenteredFourier (sourceCirclePGF F x) (k:ℝ) σ)
    (scaledCenteredFourier (sourceCirclePGF G x) (k:ℝ) σ)
    (F (x:ℂ)/((x:ℂ)^k*(σ:ℂ)*Q)) (G (x:ℂ)/((x:ℂ)^k*(σ:ℂ)*Q))
    T E RF RG L D δ hT hFi hGi hpoint htailF htailG hfull hB hAB
  rw[source_coefficient_scaled_fourier F x R σ k Q hx hxR hσ hQ hFx hF,
    source_coefficient_scaled_fourier G x R σ k Q hx hxR hσ hQ hGx hG]
  have hid:∀A B I J:ℂ,A*((2*Real.pi:ℝ):ℂ)⁻¹*I-B*((2*Real.pi:ℝ):ℂ)⁻¹*J=
      ((2*Real.pi:ℝ):ℂ)⁻¹*(A*I-B*J):=by intros;ring
  rw[hid,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity:0<2*Real.pi)]
  exact (mul_le_mul_of_nonneg_left he (by positivity:(0:ℝ)≤(2*Real.pi)⁻¹)).trans_eq (by ring)
end WP.Analysis
