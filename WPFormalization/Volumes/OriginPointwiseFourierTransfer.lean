import WPFormalization.Volumes.OriginFourierPrefactors
import WPFormalization.Analysis.SourceCoefficientComparison
/-! The true marked coefficient and its same finite origin source are
compared from genuine centered Fourier errors and the two full tails.
No coefficient asymptotics are assumed by this local transfer. -/
noncomputable section
namespace WP.Analysis
open Set MeasureTheory
lemma actual_origin_coefficient_error_from_centered_fourier
    (P:PsiTheory)(g p k J:ℕ)(hp:1≤p)(hs:Stable g p)(hk:1≤k)
    (S Bc:ℂ→ℂ)(L:ℕ→ℂ→ℂ)(ρ x T E RF RG Cfull D ε:ℝ)
    (hh:0<(complexity g p:ℝ))(hρx:ρ<xCritical)(hx:x∈Ioo (0:ℝ) ρ)
    (hroot:(k:ℝ)=(complexity g p:ℝ)*Psi x)(hT:0≤T)(hE:0≤E)(hε:0≤ε)
    (hMa:AnalyticOnNhd ℂ (HigherOrder.normalizedFiniteMarkedModel P g p S Bc L J) (Metric.ball 0 ρ))
    (hM:HigherOrder.normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)≠0)
    (hB:‖HigherOrder.normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)/
      ((x:ℂ)^k*(Real.sqrt ((complexity g p:ℝ)*euler Psi x):ℂ)*
        ((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ))‖≤D)
    (hrel:‖HigherOrder.normalizedMarkedGenerating P g p (x:ℂ)/
      HigherOrder.normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)-1‖≤ε)
    (hpoint:∀w:ℂ,‖w‖≤T→
      ‖centeredMarkedGenerating P g p k x (Real.sqrt ((complexity g p:ℝ)*euler Psi x)) w-
        HigherOrder.centeredOriginFiniteModel P g p J S Bc L x w‖≤E)
    (hfull:(∫t:ℝ,‖scaledMarkedFourier P g p x t‖)≤Cfull)
    (htailF:(∫t:ℝ in (Icc (-T) T)ᶜ,‖scaledMarkedFourier P g p x t‖)≤RF)
    (htailG:(∫t:ℝ in (Icc (-T) T)ᶜ,
      ‖scaledCenteredFourier (sourceCirclePGF (HigherOrder.normalizedFiniteMarkedModel P g p S Bc L J) x)
        ((complexity g p:ℝ)*Psi x) (Real.sqrt ((complexity g p:ℝ)*euler Psi x)) t‖)≤RG):
    ‖WP.coeff (iteratedDeriv p (Phi P g)) k/(extractionQ g p k:ℂ)-
      WP.coeff (HigherOrder.normalizedFiniteMarkedModel P g p S Bc L J) k/
        ((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ)‖≤
      ((D*ε)*Cfull+D*(RF+RG+2*T*E))/(2*Real.pi):=by
  have hxc:x∈Ioo (0:ℝ) xCritical:=⟨hx.1,hx.2.trans hρx⟩
  have hv:0<euler Psi x:=mul_pos hx.1 (Psi_deriv_pos_interior x ⟨hx.1.le,hxc.2⟩)
  have hσ:0<Real.sqrt ((complexity g p:ℝ)*euler Psi x):=by positivity
  have hQ:0<extractionQ g p k:=extractionQ_pos_at_positive_saddle g p k hs x hh hk hxc hroot
  have hM0:0 < markedModel g p 0:=markedModel_pos_parameter g p hs 0 ⟨le_rfl,y₀_pos⟩
  have hQn:0<Real.pi*extractionQ g p k/markedModel g p 0:=by positivity
  have hN:HigherOrder.normalizedMarkedGenerating P g p (x:ℂ)≠0:=by
    rw[HigherOrder.normalizedMarkedGenerating_real P g p hs x ⟨hx.1.le,hxc.2⟩]
    exact_mod_cast (div_pos (mul_pos Real.pi_pos (markedF_positive_cusp_weight P g p hp hs x ⟨hx.1.le,hxc.2⟩)) hM0).ne'
  have hc:=source_coefficient_comparison
    (HigherOrder.normalizedMarkedGenerating P g p) (HigherOrder.normalizedFiniteMarkedModel P g p S Bc L J)
    x ρ (Real.sqrt ((complexity g p:ℝ)*euler Psi x)) k
    ((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ) hx.1 hx.2 hσ
    (by exact_mod_cast hQn.ne') hN hM
    (HigherOrder.normalizedMarkedGenerating_analytic_disk P g p ρ hρx.le) hMa
    T E RF RG Cfull D (D*ε) hT
    (by simpa only[normalizedMarkedGenerating_circlePGF P g p hs x,hroot,scaledMarkedFourier] using
      origin_model_scaled_fourier_central_comparison P g p k J S Bc L x T E hT hE hroot hpoint)
    (by simpa only[normalizedMarkedGenerating_circlePGF P g p hs x,hroot,scaledMarkedFourier] using htailF)
    (by simpa only[hroot] using htailG)
    (by simpa only[normalizedMarkedGenerating_circlePGF P g p hs x,hroot,scaledMarkedFourier] using hfull)
    hB (normalizedFiniteModel_prefactor_difference P g p k J S Bc L x D ε hM hB hε hrel)
  rwa[normalizedMarkedGenerating_coefficient_relativeQ P g p k hs] at hc
end WP.Analysis
