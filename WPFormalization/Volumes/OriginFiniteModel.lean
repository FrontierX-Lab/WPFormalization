import WPFormalization.Volumes.OriginMarkedAmplitude
import WPFormalization.Volumes.ExtractionPhaseOrigin
import WPFormalization.Volumes.MarkedGeneratingPositivity
import WPFormalization.Volumes.CriticalArcFourier
/-! The true normalized marked EGF and the actual finite marked model near zero.
Exact real normalization precedes all estimates. The P-only producer fixes the
original phase, extraction amplitude, canonical coefficients and optimal order,
and proves analytic model bounds and the actual real relative error together. -/
set_option maxHeartbeats 1000000
noncomputable section
namespace WP.HigherOrder
open Set Complex

def normalizedFiniteMarkedModel (P:PsiTheory) (g p:ℕ) (S Bc:ℂ→ℂ)
    (L:ℕ→ℂ→ℂ) (J:ℕ) (z:ℂ):ℂ:=
  Complex.exp ((complexity g p:ℂ)*S z)*Bc z*
    finiteMarkedFactor L (complexity g p:ℝ) J (PositiveConvolution.planarInverse P z)

def normalizedMarkedGenerating (P:PsiTheory) (g p:ℕ) (z:ℂ):ℂ:=
  (Real.pi:ℂ)*iteratedDeriv p (Phi P g) z/(markedModel g p 0:ℂ)

lemma normalizedMarkedGenerating_real (P:PsiTheory) (g p:ℕ) (hs:Stable g p)
    (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):
    normalizedMarkedGenerating P g p (x:ℂ)=((Real.pi*markedF P g p x/markedModel g p 0:ℝ):ℂ):=by
  have he:=PositiveConvolution.Phi_iteratedDeriv_ofReal P g p hs x hx
  have hre:shifted P g (List.replicate p 0) (inverseY x)=markedF P g p x:=by
    have ht:=congrArg Complex.re he
    simpa only[markedF,Complex.ofReal_re] using ht.symm
  unfold normalizedMarkedGenerating
  rw[he,hre,←Complex.ofReal_mul,←Complex.ofReal_div]

lemma normalizedFiniteMarkedModel_real (P:PsiTheory) (g p:ℕ) (hs:Stable g p)
    (S Bc:ℂ→ℂ) (L:ℕ→ℂ→ℂ) (J:ℕ)
    (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical)
    (hS:S (x:ℂ)=(extractionS x:ℂ)) (hB:Bc (x:ℂ)=(extractionB p x:ℂ))
    (hL:finiteMarkedFactor L (complexity g p:ℝ) J (inverseY x:ℂ)=
      (realFiniteMarkedFactor P p (complexity g p:ℝ) J (inverseY x):ℂ)):
    normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)=
      ((markedModel g p (inverseY x)/markedModel g p 0*
        realFiniteMarkedFactor P p (complexity g p:ℝ) J (inverseY x):ℝ):ℂ):=by
  have hb:=inverseY_branch x hx
  have hf:=Analysis.extraction_factorization_proof g p (inverseY x) hb.1
  rw[hb.2] at hf
  have hM0:markedModel g p 0≠0:=(markedModel_pos_parameter g p hs 0 ⟨le_rfl,y₀_pos⟩).ne'
  have hm:markedModel g p (inverseY x)/markedModel g p 0=
      Real.exp ((complexity g p:ℝ)*extractionS x)*extractionB p x:=by
    rw[hf]
    field_simp
  unfold normalizedFiniteMarkedModel
  rw[hS,hB,PositiveConvolution.planarInverse_ofReal P x hx,hL]
  rw[←Complex.ofReal_natCast,←Complex.ofReal_mul,←Complex.ofReal_exp,
    ←Complex.ofReal_mul,←Complex.ofReal_mul,hm]

lemma normalized_model_real_relative_error_identity (P:PsiTheory) (g p:ℕ)
    (hs:Stable g p) (S Bc:ℂ→ℂ) (L:ℕ→ℂ→ℂ) (J:ℕ)
    (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical)
    (hS:S (x:ℂ)=(extractionS x:ℂ)) (hB:Bc (x:ℂ)=(extractionB p x:ℂ))
    (hL:finiteMarkedFactor L (complexity g p:ℝ) J (inverseY x:ℂ)=
      (realFiniteMarkedFactor P p (complexity g p:ℝ) J (inverseY x):ℂ))
    (hP:realFiniteMarkedFactor P p (complexity g p:ℝ) J (inverseY x)≠0):
    ‖normalizedMarkedGenerating P g p (x:ℂ)/normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)-1‖=
      |(Real.pi*markedF P g p x/markedModel g p (inverseY x))/
        realFiniteMarkedFactor P p (complexity g p:ℝ) J (inverseY x)-1|:=by
  rw[normalizedMarkedGenerating_real P g p hs x hx,
    normalizedFiniteMarkedModel_real P g p hs S Bc L J x hx hS hB hL,
    ←Complex.ofReal_div,←Complex.ofReal_one,←Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs]
  have hb:=inverseY_branch x hx
  have hM0:markedModel g p 0≠0:=(markedModel_pos_parameter g p hs 0 ⟨le_rfl,y₀_pos⟩).ne'
  have hMY:markedModel g p (inverseY x)≠0:=(markedModel_pos_parameter g p hs (inverseY x) hb.1).ne'
  congr 1
  field_simp
end WP.HigherOrder

namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma finiteMarkedFactor_analyticOnNhd (Ω:Set ℂ) (L:ℕ→ℂ→ℂ) (h:ℝ) (J:ℕ)
    (hL:∀j,AnalyticOnNhd ℂ (L j) Ω):
    AnalyticOnNhd ℂ (finiteMarkedFactor L h J) Ω:=by
  intro z hz
  unfold finiteMarkedFactor
  apply Finset.analyticAt_fun_sum
  intro j hj
  exact (hL j z hz).div_const

lemma normalizedMarkedGenerating_analytic_disk (P:PsiTheory) (g p:ℕ) (R:ℝ) (hR:R≤xCritical):
    AnalyticOnNhd ℂ (normalizedMarkedGenerating P g p) (Metric.ball 0 R):=by
  intro z hz
  have hn:‖z‖<xCritical:=(show ‖z‖<R by simpa only[Metric.mem_ball,dist_zero_right] using hz).trans_le hR
  exact (analyticAt_const.mul (marked_generating_analytic_disk P g p z
    (by simpa only[Metric.mem_ball,dist_zero_right] using hn))).div_const

lemma normalizedMarkedGenerating_disk_domination (P:PsiTheory) (g p:ℕ)
    (hp:1≤p) (hs:Stable g p) (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical)
    (z:ℂ) (hz:‖z‖≤x):
    ‖normalizedMarkedGenerating P g p z‖≤‖normalizedMarkedGenerating P g p (x:ℂ)‖:=by
  unfold normalizedMarkedGenerating
  rw[norm_div,norm_div,norm_mul,norm_mul,marked_generating_norm_real P g p hp hs x hx]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (marked_generating_disk_domination P g p hp hs x hx z hz) (norm_nonneg _)) (norm_nonneg _)

lemma origin_normalized_model_data (P:PsiTheory) (p:ℕ) (hp:1≤p):
    ∃(S Bc:ℂ→ℂ)(L:ℕ→ℂ→ℂ)(κ a H ρ D E:ℝ),
      0<κ ∧ 0<a ∧ 0<H ∧ 0<ρ ∧ ρ<xCritical ∧ 0<D ∧ 0<E ∧
      S 0=0 ∧ Bc 0=1 ∧
      (∀j Y,Y∈Icc (0:ℝ) y₀→L j Y=(markedCoefficient P p j Y:ℂ)) ∧
      (∀x∈Icc (0:ℝ) ρ,S (x:ℂ)=(extractionS x:ℂ) ∧ Bc (x:ℂ)=(extractionB p x:ℂ)) ∧
      ∀g:ℕ,H≤(complexity g p:ℝ)→
        let h:ℝ:=complexity g p
        let J:=⌊κ*Real.sqrt h⌋₊
        (∀z:ℂ,‖z‖≤ρ→AnalyticAt ℂ (normalizedFiniteMarkedModel P g p S Bc L J) z ∧
          ‖normalizedFiniteMarkedModel P g p S Bc L J z‖≤D*Real.exp (D*h*‖z‖)) ∧
        (∀x∈Icc (0:ℝ) ρ,normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)≠0 ∧
          ‖normalizedMarkedGenerating P g p (x:ℂ)/normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)-1‖≤
            E*Real.exp (-a*Real.sqrt h)):=by
  obtain ⟨Ω,L,C,B,κ,a,H₀,hΩ,hcover,hC,hB,hκ,ha,hH₀,hLa,hL0,hLr,hLb,hmodel⟩:=
    optimal_marked_model_real_comparison P p hp
  obtain ⟨Bc,ρ₀,D₀,hρ₀,hρ₀x,hD₀,hBc0,hBcp,hlocal,hampA,hampB,hampR⟩:=
    origin_marked_amplitude_family_of_parameter_data P p Ω L C B hΩ hcover hC hB hLa hLr hLb
  obtain ⟨S,hSa,hS0,hSd,hSreal⟩:=Analysis.exists_extractionS_origin_complex_extension
  obtain ⟨rs,Cs,hrs,hCs,hSbound⟩:=Analysis.complex_analytic_zero_linear_bound S hSa hS0
  obtain ⟨rreal,hrreal,hSrealball⟩:=Metric.eventually_nhds_iff.mp hSreal
  let ρ:ℝ:=min ρ₀ (min rs (rreal/2))
  let D:ℝ:=Cs+4
  let H:ℝ:=max H₀ 1
  have hρ:0<ρ:=lt_min hρ₀ (lt_min hrs (by positivity))
  have hρle:ρ≤ρ₀:=min_le_left _ _
  have hρs:ρ≤rs:=(min_le_right _ _).trans (min_le_left _ _)
  have hρr:ρ<rreal:=lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
  have hρx:ρ<xCritical:=hρle.trans_lt hρ₀x
  have hD:0<D:=by dsimp[D];linarith
  have hH:0<H:=hH₀.trans_le (le_max_left _ _)
  have hSphys:∀x∈Icc (0:ℝ) ρ,S (x:ℂ)=(extractionS x:ℂ):=by
    intro x hx
    exact hSrealball (show dist x 0<rreal by rw[Real.dist_eq,sub_zero,abs_of_nonneg hx.1];exact hx.2.trans_lt hρr) hx.1
  refine ⟨S,Bc,L,κ,a,H,ρ,D,2*C,hκ,ha,hH,hρ,hρx,hD,by positivity,hS0,hBc0,hLr,?_,?_⟩
  · intro x hx
    exact ⟨hSphys x hx,(hBcp x ⟨hx.1,hx.2.trans_lt hρx⟩).2⟩
  · intro g hg
    dsimp only
    let h:ℝ:=complexity g p
    let J:=⌊κ*Real.sqrt h⌋₊
    have hh:0<h:=hH.trans_le hg
    have hg₀:H₀≤h:=(le_max_left _ _).trans hg
    have hh1:1≤h:=(le_max_right _ _).trans hg
    have hs:Stable g p:=by
      have hn:1≤complexity g p:=by exact_mod_cast (show (1:ℝ)≤(complexity g p:ℝ) from hh1)
      unfold Stable complexity at *;omega
    have hm:=hmodel g hg₀
    have hPana:=finiteMarkedFactor_analyticOnNhd Ω L h J hLa
    refine ⟨?_,?_⟩
    · intro z hz
      have hl:=hlocal z (hz.trans hρle)
      have hsbound:=hSbound z (hz.trans hρs)
      have hYca:=PositiveConvolution.planarInverse_analyticAt P z (hz.trans_lt hρx)
      have hPbound:‖finiteMarkedFactor L h J (PositiveConvolution.planarInverse P z)‖≤2:=
        (hm.1 _ hl.2.2).2.2.1
      have hAa:AnalyticAt ℂ (normalizedFiniteMarkedModel P g p S Bc L J) z:=
        ((analyticAt_const.mul hsbound.1).cexp.mul hl.1).mul ((hPana _ hl.2.2).comp hYca)
      refine ⟨hAa,?_⟩
      have hex:‖Complex.exp ((complexity g p:ℂ)*S z)‖≤Real.exp (D*h*‖z‖):=by
        apply (Complex.norm_exp_le_exp_norm _).trans
        apply Real.exp_le_exp.mpr
        rw[norm_mul,Complex.norm_natCast]
        have ht:=mul_le_mul_of_nonneg_left hsbound.2 (Nat.cast_nonneg (complexity g p): (0:ℝ)≤complexity g p)
        have hd:Cs≤D:=by dsimp[D];linarith
        have ht':Cs*‖z‖≤D*‖z‖:=mul_le_mul_of_nonneg_right hd (norm_nonneg _)
        nlinarith[mul_le_mul_of_nonneg_left ht' hh.le]
      unfold normalizedFiniteMarkedModel
      rw[norm_mul,norm_mul]
      have hprod:=mul_le_mul (mul_le_mul hex hl.2.1 (norm_nonneg _) (Real.exp_pos _).le)
        hPbound (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (by norm_num:(0:ℝ)≤2))
      have hd4:(4:ℝ)≤D:=by dsimp[D];linarith
      have ht:=mul_le_mul_of_nonneg_right hd4 (Real.exp_pos (D*h*‖z‖)).le
      nlinarith
    · intro x hx
      have hxi:x∈Ico (0:ℝ) xCritical:=⟨hx.1,hx.2.trans_lt hρx⟩
      have hy:=(inverseY_branch x hxi).1
      have hyc:inverseY x∈Icc (0:ℝ) y₀:=⟨hy.1,hy.2.le⟩
      have hPL:=hm.2.1 _ hyc
      have hPne:realFiniteMarkedFactor P p h J (inverseY x)≠0:=by
        intro he
        have hnonzero:finiteMarkedFactor L h J (inverseY x:ℂ)≠0:=(hm.1 _ (hcover _ hyc)).2.2.2
        apply hnonzero
        rw[hPL,he,Complex.ofReal_zero]
      have hbval: Bc (x:ℂ)=(extractionB p x:ℂ):=(hBcp x hxi).2
      have hmreal:=normalizedFiniteMarkedModel_real P g p hs S Bc L J x hxi (hSphys x hx) hbval hPL
      have hM0:markedModel g p 0≠0:=(markedModel_pos_parameter g p hs 0 ⟨le_rfl,y₀_pos⟩).ne'
      have hMY:markedModel g p (inverseY x)≠0:=(markedModel_pos_parameter g p hs _ hy).ne'
      refine ⟨?_,?_⟩
      · rw[hmreal]
        exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (div_ne_zero hMY hM0) hPne)
      · rw[normalized_model_real_relative_error_identity P g p hs S Bc L J x hxi (hSphys x hx) hbval hPL hPne]
        have ht:=hm.2.2 (inverseY x) hy
        simpa only[(inverseY_branch x hxi).2] using ht
end WP.HigherOrder
noncomputable section
