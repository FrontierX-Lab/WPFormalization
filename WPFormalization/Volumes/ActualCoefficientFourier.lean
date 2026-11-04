import WPFormalization.Volumes.SaddleModelNormalization
import WPFormalization.Analysis.PoissonNormalizer
import WPFormalization.Volumes.MarkedFourierInversion
/-! The original coefficient divided by the actual extractionQ equals its genuine scaled Fourier integral with the exact Poisson normalizer. All model and pi constants are proved from the original definitions. -/
noncomputable section
open Set MeasureTheory
namespace WP.Analysis
set_option maxHeartbeats 1000000 in
lemma actual_relativeQ_scaled_fourier_identity
    (P:PsiTheory)(g p k:ℕ)(hp:1≤p)(hs:Stable g p)(hk:1≤k)
    (hh:0<(complexity g p:ℝ))(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)
    (hroot:(k:ℝ)=(complexity g p:ℝ)*WP.Psi x) :
    ((realCoeff (iteratedDeriv p (Phi P g)) k/extractionQ g p k:ℝ):ℂ)=
      ((Real.pi*markedF P g p x/markedModel g p (inverseY x):ℝ):ℂ)*
        (((poissonNormalizer k)⁻¹:ℝ):ℂ)/(Real.sqrt (2*Real.pi):ℂ)*
        ∫t:ℝ,scaledMarkedFourier P g p x t := by
  let σ:ℝ:=Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x)
  let M:ℝ:=markedModel g p (inverseY x)
  let F:ℝ:=markedF P g p x
  have hv:0<WP.euler WP.Psi x:=mul_pos hx.1 (Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)
  have hσ:0<σ:=Real.sqrt_pos.mpr (mul_pos hh hv)
  have hF:F≠0:=(markedF_positive_cusp_weight P g p hp hs x ⟨hx.1.le,hx.2⟩).ne'
  have hY:inverseY x∈Ico (0:ℝ) y₀:=(inverseY_branch x ⟨hx.1.le,hx.2⟩).1
  have hM:M≠0:=(markedModel_pos_parameter g p hs (inverseY x) hY).ne'
  have hk0:0<(k:ℝ):=by exact_mod_cast (show 0<k by omega)
  have hpc:0<poissonCenter k:=by unfold poissonCenter;positivity
  have hsk:0<Real.sqrt (k:ℝ):=Real.sqrt_pos.mpr hk0
  have hq:=extractionQ_standardized_normalizer_exact g p k x hh hk hx hroot
  change extractionQ g p k*x^k*σ=M/Real.pi*poissonCenter k*Real.sqrt (k:ℝ) at hq
  have hQ:extractionQ g p k≠0:=by
    intro he
    rw[he,zero_mul,zero_mul] at hq
    have hn:M/Real.pi*poissonCenter k*Real.sqrt (k:ℝ)≠0:=mul_ne_zero (mul_ne_zero (div_ne_zero hM Real.pi_ne_zero) hpc.ne') hsk.ne'
    exact hn hq.symm
  have hg:0<complexity g p:=by exact_mod_cast hh
  have hfour:=cuspMass_scaled_fourier P g p hp hs hg x hx (k:ℤ)
  dsimp only at hfour
  simp only[Int.cast_natCast,hroot,sub_self,zero_div,Complex.ofReal_zero,neg_zero,zero_mul,
    Complex.exp_zero,one_mul,Int.natCast_nonneg,ite_true,Int.toNat_natCast] at hfour
  have hc:((realCoeff (iteratedDeriv p (Phi P g)) k/extractionQ g p k:ℝ):ℂ)=
      ((F/(extractionQ g p k*x^k*σ):ℝ):ℂ)*
        (((2*Real.pi:ℝ):ℂ)⁻¹*∫t:ℝ,scaledMarkedFourier P g p x t) := by
    rw[←hfour]
    dsimp only[cuspMass,F,σ]
    push_cast
    field_simp[show (markedF P g p x:ℂ)≠0 by exact_mod_cast hF,
      show ((Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x)):ℂ)≠0 by exact_mod_cast hσ.ne',
      show (extractionQ g p k:ℂ)≠0 by exact_mod_cast hQ,
      show (x:ℂ)≠0 by exact_mod_cast hx.1.ne']
    ring_nf
    field_simp[show ((Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x)):ℂ)≠0 by exact_mod_cast hσ.ne']
    exact (mul_div_cancel_right₀ _ (show ((Real.sqrt ((complexity g p:ℝ)*WP.euler WP.Psi x)):ℂ)≠0 by exact_mod_cast hσ.ne')).symm
  have hRoot:0<Real.sqrt (2*Real.pi):=by positivity
  have hnorm:F/(extractionQ g p k*x^k*σ)*(2*Real.pi)⁻¹=
      (Real.pi*F/M)*(poissonNormalizer k)⁻¹/Real.sqrt (2*Real.pi) := by
    rw[hq,poissonNormalizer_nat k hk,Real.sqrt_mul (by positivity:0≤2*Real.pi)]
    field_simp[hM,Real.pi_ne_zero,hpc.ne',hsk.ne',hRoot.ne']
    nlinarith[Real.sq_sqrt (by positivity:0≤2*Real.pi),Real.sq_sqrt (by positivity:0≤Real.pi*2)]
  calc _ = (((F/(extractionQ g p k*x^k*σ)*(2*Real.pi)⁻¹:ℝ):ℂ))*
      ∫t:ℝ,scaledMarkedFourier P g p x t := by rw[hc];push_cast;ring
       _ = _:=by rw[hnorm];push_cast;ring
end WP.Analysis
