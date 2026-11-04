import WPFormalization.Volumes.ActualCoefficientFourier
import WPFormalization.Volumes.CompactModelFourierIntegral
import WPFormalization.Analysis.FourierCentralModelTransfer
/-! The actual relative-Q coefficient is compared with the given compact finite source using exact Fourier normalization, the exact finite-source rescaling, and a single base-factor error. Quantitative local and tail bounds are explicit inputs to this helper; the later actual client must instantiate them. -/
noncomputable section
namespace WP.Analysis
open Set MeasureTheory
set_option maxHeartbeats 1000000 in
lemma compact_actual_relativeQ_central_model_error
    (P:PsiTheory)(g p k J:ℕ)(hp:1≤p)(hs:Stable g p)
    (hk:1≤k)(hh:0<(complexity g p:ℝ))
    (Bc S l:ℂ→ℂ)(f:ℕ→ℂ→ℂ)(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)
    (hroot:(k:ℝ)=(complexity g p:ℝ)*WP.Psi (x))
    (T E R L M Zmax ε:ℝ)(hT:0≤T)(hM:0≤M)(hZmax:0≤Zmax)
    (hy:|(poissonNormalizer k)⁻¹|≤M)
    (hz:HigherOrder.finiteMarkedFactor f (complexity g p:ℝ) J ((inverseY x:ℝ):ℂ)≠0)
    (hz2:‖HigherOrder.finiteMarkedFactor f (complexity g p:ℝ) J ((inverseY x:ℝ):ℂ)‖≤Zmax)
    (hrel:‖((Real.pi*markedF P g p (x)/markedModel g p (inverseY x):ℝ):ℂ)/
      HigherOrder.finiteMarkedFactor f (complexity g p:ℝ) J ((inverseY x:ℝ):ℂ)-1‖≤ε)
    (hGi:IntegrableOn (fun t:ℝ=>compactCenteredFiniteModel P Bc S l f (complexity g p:ℝ) J
      (x:ℂ) (Complex.I*(t:ℂ))) (Icc (-T) T))
    (hpoint:∀t∈Icc (-T) T,‖scaledMarkedFourier P g p (x) t-
      compactCenteredFiniteModel P Bc S l f (complexity g p:ℝ) J (x:ℂ) (Complex.I*(t:ℂ))‖≤E)
    (htail:(∫t:ℝ in (Icc (-T) T)ᶜ,‖scaledMarkedFourier P g p (x) t‖)≤R)
    (hfull:(∫t:ℝ,‖scaledMarkedFourier P g p (x) t‖)≤L) :
    ‖((realCoeff (iteratedDeriv p (Phi P g)) k/extractionQ g p k:ℝ):ℂ)-
      (finiteMorseSourceIntegral (fun u:ℂ=>centeredExponentialPhase S l ((x:ℂ),u))
        (fun s u=>compactPremorseAmplitude P Bc l f s ((x:ℂ),u)) (complexity g p:ℝ)
          (T/Real.sqrt (complexity g p:ℝ)) J/(Real.sqrt (2*Real.pi):ℂ))*
        (((poissonNormalizer k)⁻¹:ℝ):ℂ)‖≤
      (Zmax*M/Real.sqrt (2*Real.pi))*(ε*L+R+2*T*E) := by
  let z:ℂ:=HigherOrder.finiteMarkedFactor f (complexity g p:ℝ) J ((inverseY x:ℝ):ℂ)
  let α:ℂ:=((Real.pi*markedF P g p x/markedModel g p (inverseY x):ℝ):ℂ)
  let y:ℂ:=(((poissonNormalizer k)⁻¹:ℝ):ℂ)
  let s:ℝ:=Real.sqrt (2*Real.pi)
  let A:ℂ:=α*y/(s:ℂ)
  let B:ℂ:=z*y/(s:ℂ)
  let C:ℝ:=Zmax*M/s
  have hs0:0<s:=by dsimp[s];positivity
  have hsn:(s:ℂ)≠0:=by exact_mod_cast hs0.ne'
  have hε:0≤ε:=(norm_nonneg _).trans hrel
  have hAi:((realCoeff (iteratedDeriv p (Phi P g)) k/extractionQ g p k:ℝ):ℂ)=
      A*∫t:ℝ,scaledMarkedFourier P g p x t := by
    have he:=actual_relativeQ_scaled_fourier_identity P g p k hp hs hk hh x hx hroot
    exact he
  have hb:‖B‖≤C:=by
    dsimp only[B,C,y]
    rw[norm_div,norm_mul,Complex.norm_of_nonneg hs0.le,Complex.norm_real,Real.norm_eq_abs]
    exact div_le_div_of_nonneg_right (mul_le_mul hz2 hy (abs_nonneg _) hZmax) hs0.le
  have hab:‖A-B‖≤C*ε:=by
    have heA:α-z=z*(α/z-1):=by
      calc _ = (α/z)*z-z:=by rw[div_mul_cancel₀ _ (show z≠0 from hz)]
           _ = _:=by ring
    have he:A-B=B*(α/z-1):=by
      dsimp only[A,B]
      calc _ = (α-z)*y/(s:ℂ):=by ring
           _ = (z*(α/z-1))*y/(s:ℂ):=by rw[heA]
           _ = _:=by ring
    rw[he,norm_mul]
    exact mul_le_mul hb hrel (norm_nonneg _) (by dsimp only[C];positivity)
  have hBi:(finiteMorseSourceIntegral (fun u:ℂ=>centeredExponentialPhase S l ((x:ℂ),u))
      (fun s u=>compactPremorseAmplitude P Bc l f s ((x:ℂ),u)) (complexity g p:ℝ)
      (T/Real.sqrt (complexity g p:ℝ)) J/(Real.sqrt (2*Real.pi):ℂ))*
        (((poissonNormalizer k)⁻¹:ℝ):ℂ)=
      B*∫t:ℝ in Icc (-T) T,compactCenteredFiniteModel P Bc S l f (complexity g p:ℝ) J (x:ℂ) (Complex.I*(t:ℂ)) := by
    have he:=compact_finite_source_eq_centered_fourier_integral P Bc S l f (x:ℂ) (complexity g p:ℝ) T J hh hT
    rw [PositiveConvolution.planarInverse_ofReal P x ⟨hx.1.le,hx.2⟩] at he
    have hsrc:= (div_eq_iff hz).mp he
    rw[hsrc]
    dsimp only[B,y,s,z]
    ring
  rw[hAi,hBi]
  have he:=coefficient_prefactor_local_model_error
    (scaledMarkedFourier P g p x)
    (fun t:ℝ=>compactCenteredFiniteModel P Bc S l f (complexity g p:ℝ) J (x:ℂ) (Complex.I*(t:ℂ)))
    A B T E R L C (C*ε) hT (scaledMarkedFourier_integrable P g p x hx) hGi hpoint htail hfull hb hab
  exact he.trans_eq (by dsimp[C];ring)
end WP.Analysis
