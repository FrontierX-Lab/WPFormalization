import WPFormalization.Analysis.NormalizedComplexExtension
import WPFormalization.Analysis.ExtractionFactorization
import WPFormalization.Volumes.PlanarInverse
/-! A holomorphic extension of the actual normalized extraction amplitude.
The function is analytic at every physical cusp weight, equals extractionB
there, and has value one at zero. Positive real logarithms fix the branches;
no physical first-root continuation through the critical endpoint is asserted. -/
noncomputable section
namespace WP.Analysis
open Set Complex

lemma positive_amplitude_ratio_log (r r₀ b b₀ q:ℝ)
    (hr:0<r) (hr₀:0<r₀) (hb:0<b) (hb₀:0<b₀):
    Real.exp (q*Real.log (r/r₀)+(1/2:ℝ)*Real.log (b/b₀))=
      Real.rpow r q*Real.sqrt b/(Real.rpow r₀ q*Real.sqrt b₀):=by
  simp only [Real.rpow_eq_pow]
  rw[Real.exp_add,show q*Real.log (r/r₀)=Real.log (r/r₀)*q by ring,
    show (1/2:ℝ)*Real.log (b/b₀)=Real.log (b/b₀)*(1/2) by ring,
    ←Real.rpow_def_of_pos (div_pos hr hr₀),←Real.rpow_def_of_pos (div_pos hb hb₀),
    ←Real.sqrt_eq_rpow,Real.div_rpow hr.le hr₀.le,Real.sqrt_div hb.le]
  ring

lemma extractionB_complex_extension (P:PsiTheory) (p:ℕ):
    ∃Bc:ℂ→ℂ,Bc 0=1 ∧ ∀x∈Ico (0:ℝ) xCritical,
      AnalyticAt ℂ Bc (x:ℂ) ∧ Bc (x:ℂ)=(extractionB p x:ℂ):=by
  obtain ⟨Ω,hΩ,hcover,R,Q,Ahat,hR,hQ,hA,hkernels,hmatch,hunit,hraw,hRcrit,hRderiv⟩:=
    common_holomorphic_normalized_kernel_data
  let L:ℂ→ℂ:=fun z=>Complex.exp
    (((p:ℝ)/2:ℂ)*Complex.log (R z/(r 0:ℂ))+
      (1/2:ℂ)*Complex.log (Ahat z*Q z/((A 0*Theta 0:ℝ):ℂ)))
  let Bc:ℂ→ℂ:=fun z=>L (PositiveConvolution.planarInverse P z)
  have h0i:(0:ℝ)∈Ico (0:ℝ) y₀:=⟨le_rfl,y₀_pos⟩
  have h0c:(0:ℝ)∈Icc (0:ℝ) y₀:=⟨le_rfl,y₀_pos.le⟩
  have hr₀:=r_pos 0 h0i
  have ha₀:=marked_A_pos 0 h0c
  have ht₀:=marked_Theta_pos 0 h0c
  have hnR:(r 0:ℂ)≠0:=by exact_mod_cast hr₀.ne'
  have hnB:((A 0*Theta 0:ℝ):ℂ)≠0:=by exact_mod_cast (mul_pos ha₀ ht₀).ne'
  have hQr:∀Y∈Icc (0:ℝ) y₀,Q (Y:ℂ)=(Theta Y:ℂ):=by
    intro Y hY
    exact (hmatch Y hY).1
  have hRzero:R 0=(r 0:ℂ):=by simpa only[Complex.ofReal_zero] using hraw 0 h0i
  have hAzero:Ahat 0=(A 0:ℂ):=by simpa only[Complex.ofReal_zero] using (hmatch 0 h0c).2.1
  have hQzero:Q 0=(Theta 0:ℂ):=by simpa only[Complex.ofReal_zero] using hQr 0 h0c
  have hL0:L 0=1:=by
    dsimp only[L]
    rw[hRzero,hAzero,hQzero,←Complex.ofReal_mul,div_self hnR,div_self hnB,
      Complex.log_one,mul_zero,mul_zero,add_zero,Complex.exp_zero]
  refine ⟨Bc,?_,?_⟩
  · dsimp[Bc]
    rw[PositiveConvolution.planarInverse_zero P,hL0]
  · intro x hx
    have hb:=inverseY_branch x hx
    let Y:=inverseY x
    have hYi:Y∈Ico (0:ℝ) y₀:=hb.1
    have hYc:Y∈Icc (0:ℝ) y₀:=⟨hYi.1,hYi.2.le⟩
    have hplan:=PositiveConvolution.planarInverse_ofReal P x hx
    have hRy:R (Y:ℂ)=(r Y:ℂ):=hraw Y hYi
    have hAy:Ahat (Y:ℂ)=(A Y:ℂ):=(hmatch Y hYc).2.1
    have hQy:Q (Y:ℂ)=(Theta Y:ℂ):=hQr Y hYc
    have hry:=r_pos Y hYi
    have hay:=marked_A_pos Y hYc
    have hty:=marked_Theta_pos Y hYc
    have hUy:R (Y:ℂ)/(r 0:ℂ)∈Complex.slitPlane:=by
      rw[hRy,←Complex.ofReal_div,Complex.mem_slitPlane_iff]
      exact Or.inl (div_pos hry hr₀)
    have hBy:Ahat (Y:ℂ)*Q (Y:ℂ)/((A 0*Theta 0:ℝ):ℂ)∈Complex.slitPlane:=by
      rw[hAy,hQy,←Complex.ofReal_mul,←Complex.ofReal_div,Complex.mem_slitPlane_iff]
      exact Or.inl (div_pos (mul_pos hay hty) (mul_pos ha₀ ht₀))
    have hLa:AnalyticAt ℂ L (Y:ℂ):=by
      apply AnalyticAt.cexp
      apply AnalyticAt.add
      · exact analyticAt_const.mul ((hR _ (hcover Y hYc)).div_const.clog hUy)
      · exact analyticAt_const.mul (((hA _ (hcover Y hYc)).mul (hQ _ (hcover Y hYc))).div_const.clog hBy)
    refine ⟨hLa.comp_of_eq (PositiveConvolution.planarInverse_analyticAt P _
      (by rw[Complex.norm_of_nonneg hx.1];exact hx.2)) hplan,?_⟩
    change L (PositiveConvolution.planarInverse P (x:ℂ))=(extractionB p x:ℂ)
    rw[hplan]
    dsimp only[L]
    rw[hRy,hAy,hQy,←Complex.ofReal_div,←Complex.ofReal_mul,←Complex.ofReal_div,
      ←Complex.ofReal_log (div_pos hry hr₀).le,
      ←Complex.ofReal_log (div_pos (mul_pos hay hty) (mul_pos ha₀ ht₀)).le]
    have harg:((p:ℝ)/2:ℂ)*(Real.log (r Y/r 0):ℂ)+
        (1/2:ℂ)*(Real.log (A Y*Theta Y/(A 0*Theta 0)):ℂ)=
        (( ((p:ℝ)/2)*Real.log (r Y/r 0)+(1/2:ℝ)*Real.log (A Y*Theta Y/(A 0*Theta 0)) : ℝ):ℂ):=by
      push_cast
      ring
    rw[harg,←Complex.ofReal_exp,
      positive_amplitude_ratio_log _ _ _ _ _ hry hr₀ (mul_pos hay hty) (mul_pos ha₀ ht₀)]
    rfl
end WP.Analysis
