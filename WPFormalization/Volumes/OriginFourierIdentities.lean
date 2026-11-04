import WPFormalization.Analysis.SourceScaledFourier
import WPFormalization.Volumes.MarkedFourierIntegralTail
import WPFormalization.Volumes.OriginModelGaussianTail
import WPFormalization.Volumes.OriginTrueComparison
import WPFormalization.Volumes.SaddleCoefficientNormalization
import WPFormalization.Volumes.CriticalFourierGeometry
/-! The actual marked source, finite origin source and their centered
Fourier transforms share exact normalization. Outside the common period,
both Fourier transforms vanish, so a central comparison needs no extra
period-length restriction. -/
noncomputable section
namespace WP.Analysis
open Set MeasureTheory
lemma normalizedMarkedGenerating_circlePGF (P:PsiTheory)(g p:ℕ)(hs:Stable g p)(x:ℝ):
    sourceCirclePGF (HigherOrder.normalizedMarkedGenerating P g p) x=markedPGF P g p x:=by
  have hM:markedModel g p 0≠0:=(markedModel_pos_parameter g p hs 0 ⟨le_rfl,y₀_pos⟩).ne'
  let c:ℂ:=((Real.pi/markedModel g p 0:ℝ):ℂ)
  have hc:c≠0:=by dsimp[c];exact_mod_cast div_ne_zero Real.pi_ne_zero hM
  have hN:HigherOrder.normalizedMarkedGenerating P g p=(fun z:ℂ=>c*iteratedDeriv p (Phi P g) z):=by
    funext z
    unfold HigherOrder.normalizedMarkedGenerating
    dsimp[c]
    push_cast
    ring
  funext w
  rw[sourceCirclePGF,hN]
  exact mul_div_mul_left _ _ hc
lemma normalizedMarkedGenerating_coefficient_relativeQ (P:PsiTheory)(g p k:ℕ)(hs:Stable g p):
    WP.coeff (HigherOrder.normalizedMarkedGenerating P g p) k/
      ((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ)=
      WP.coeff (iteratedDeriv p (Phi P g)) k/(extractionQ g p k:ℂ):=by
  have hM:markedModel g p 0≠0:=(markedModel_pos_parameter g p hs 0 ⟨le_rfl,y₀_pos⟩).ne'
  let c:ℂ:=((Real.pi/markedModel g p 0:ℝ):ℂ)
  have hc:c≠0:=by dsimp[c];exact_mod_cast div_ne_zero Real.pi_ne_zero hM
  have hN:HigherOrder.normalizedMarkedGenerating P g p=(fun z:ℂ=>c*iteratedDeriv p (Phi P g) z):=by
    funext z
    unfold HigherOrder.normalizedMarkedGenerating
    dsimp[c]
    push_cast
    ring
  have hQ:((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ)=c*(extractionQ g p k:ℂ):=by
    dsimp[c]
    push_cast
    ring
  rw[hN,coeff_const_mul,hQ]
  exact mul_div_mul_left _ _ hc
lemma finite_origin_scaled_fourier_eq_on_period (P:PsiTheory)(g p J:ℕ)
    (S Bc:ℂ→ℂ)(L:ℕ→ℂ→ℂ)(x t:ℝ)
    (ht:t∈Icc (-(Real.pi*Real.sqrt ((complexity g p:ℝ)*euler Psi x)))
      (Real.pi*Real.sqrt ((complexity g p:ℝ)*euler Psi x))):
    scaledCenteredFourier (sourceCirclePGF (HigherOrder.normalizedFiniteMarkedModel P g p S Bc L J) x)
      ((complexity g p:ℝ)*Psi x) (Real.sqrt ((complexity g p:ℝ)*euler Psi x)) t=
      HigherOrder.centeredOriginFiniteModel P g p J S Bc L x (Complex.I*(t:ℂ)):=by
  rw[scaledCenteredFourier,Set.indicator_of_mem ht]
  unfold sourceCirclePGF HigherOrder.centeredOriginFiniteModel
  dsimp only
  have ha:Complex.I*(t:ℂ)/(Real.sqrt ((complexity g p:ℝ)*euler Psi x):ℂ)=
      (((t/Real.sqrt ((complexity g p:ℝ)*euler Psi x):ℝ):ℂ))*Complex.I:=by push_cast;ring
  rw[ha]
  congr 2
  push_cast
  ring
lemma origin_model_scaled_fourier_central_comparison (P:PsiTheory)(g p k J:ℕ)
    (S Bc:ℂ→ℂ)(L:ℕ→ℂ→ℂ)(x T E:ℝ)(hT:0≤T)(hE:0≤E)
    (hroot:(k:ℝ)=(complexity g p:ℝ)*Psi x)
    (hpoint:∀w:ℂ,‖w‖≤T→
      ‖centeredMarkedGenerating P g p k x (Real.sqrt ((complexity g p:ℝ)*euler Psi x)) w-
        HigherOrder.centeredOriginFiniteModel P g p J S Bc L x w‖≤E):
    ∀t∈Icc (-T) T,‖scaledMarkedFourier P g p x t-
      scaledCenteredFourier (sourceCirclePGF (HigherOrder.normalizedFiniteMarkedModel P g p S Bc L J) x)
        ((complexity g p:ℝ)*Psi x) (Real.sqrt ((complexity g p:ℝ)*euler Psi x)) t‖≤E:=by
  intro t ht
  by_cases hp:t∈Icc (-(Real.pi*Real.sqrt ((complexity g p:ℝ)*euler Psi x)))
      (Real.pi*Real.sqrt ((complexity g p:ℝ)*euler Psi x))
  · rw[scaledMarkedFourier_eq_centered_on_period P g p k x t hroot hp,
      finite_origin_scaled_fourier_eq_on_period P g p J S Bc L x t hp]
    apply hpoint
    rw[norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith[ht.1],ht.2⟩
  · simp only[scaledMarkedFourier,scaledCenteredFourier,Set.indicator_of_notMem hp,sub_self,norm_zero]
    exact hE
end WP.Analysis
