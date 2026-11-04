import WPFormalization.HigherOrder.FirstExtractedCriticalUnits
import WPFormalization.HigherOrder.FirstExtractedCorrection
import WPFormalization.HigherOrder.SecondCoefficientCoherence
import WPFormalization.HigherOrder.FirstCorrectionPrimitive
import WPFormalization.Volumes.ExtractionLogData
import WPFormalization.Analysis.DeltaExtensionLimit
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma extractionLogB_analyticAt (P : PsiTheory) (p : ℕ) (x:ℝ)
    (hx:x∈Ioo (0:ℝ) xCritical) :
    AnalyticAt ℝ (fun t=>Real.log (extractionB p t)) x := by
  obtain ⟨S,B,β,hS,hB,hSr,hBr,_⟩:=exists_actual_extraction_log_data P p x hx
  exact analyticAt_real_of_complex_trace B _ x hB hBr

/-- A harmless continuous ambient extension is used only to identify limUnder;
its positive-delta trace is the ORIGINAL marked coefficient. -/
def clampedFirstMarkedCorrection (p:ℕ) (z:ℂ) : ℂ :=
  (HigherOrder.firstMarkedCorrection p (max 0 (min y₀ (y₀-z.re))):ℝ)
lemma clampedFirstMarkedCorrection_zero (p:ℕ) :
    clampedFirstMarkedCorrection p 0 = (HigherOrder.firstEndpointConstant p:ℂ) := by
  simp only [clampedFirstMarkedCorrection,Complex.zero_re,sub_zero,min_self,
    max_eq_right y₀_pos.le,HigherOrder.firstMarkedCorrection_endpoint]
lemma clampedFirstMarkedCorrection_continuousAt (p:ℕ) :
    ContinuousAt (clampedFirstMarkedCorrection p) 0 := by
  let f : ℂ→ℝ := fun z=>max 0 (min y₀ (y₀-z.re))
  have hf : ContinuousAt f 0 := by fun_prop
  have hf0 : f 0=y₀ := by simp [f,y₀_pos.le]
  have hmem : ∀z:ℂ,f z∈Icc (0:ℝ) y₀ := by
    intro z
    constructor
    · exact le_max_left _ _
    · exact max_le y₀_pos.le (min_le_left _ _)
  have ht : Tendsto f (𝓝 0) (𝓝[Icc (0:ℝ) y₀] y₀) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa only [hf0] using hf.tendsto,Filter.Eventually.of_forall hmem⟩
  have hc := (HigherOrder.firstMarkedCorrection_continuousOn p y₀ ⟨y₀_pos.le,le_rfl⟩).tendsto.comp ht
  have hreal : ContinuousAt (fun z=>HigherOrder.firstMarkedCorrection p (f z)) 0 := by
    simpa only [ContinuousAt,Function.comp_def,hf0] using hc
  exact Complex.continuous_ofReal.continuousAt.comp hreal
lemma clampedFirstMarkedCorrection_physical (P:PsiTheory) (p:ℕ) (δ:ℝ)
    (hδ:δ∈Ioo (0:ℝ) y₀) :
    clampedFirstMarkedCorrection p (δ:ℂ)=(HigherOrder.markedCoefficient P p 1 (y₀-δ):ℂ) := by
  obtain ⟨hδp,hδy⟩ := hδ
  rw [clampedFirstMarkedCorrection]
  simp only [Complex.ofReal_re]
  rw [min_eq_right (by linarith : y₀-δ≤y₀),max_eq_right (by linarith : 0≤y₀-δ)]
  rw [HigherOrder.markedCoefficient_one_eq_firstMarkedCorrection P p (y₀-δ)
    ⟨by linarith,by linarith⟩]
end WP.Analysis

namespace WP.HigherOrder
open WP.Analysis
/- D.25: the actual one-sided CG3 limit has the paper's explicit value. -/
@[blueprint "eq:CG13"]
theorem first_extracted_correction_critical (P:PsiTheory) (p:ℕ) :
    extractedCoefficient P p 1 y₀ = -(p:ℝ)^2/8+p/2-37/60 := by
  obtain ⟨k⟩ := exists_criticalKernelUnits
  obtain ⟨Q,hQ,hQ0,hQphys⟩ := exists_criticalThetaUnit
  let B1 : ℂ→ℂ := k.scaledLogBUnit Q p
  let B2 : ℂ→ℂ := k.secondLogBUnit Q p
  let E : ℂ→ℂ := k.firstGaussianUnit B1 B2
  let F : ℂ→ℂ := fun z=>clampedFirstMarkedCorrection p z+E z
  have hEa : AnalyticAt ℂ E 0 := k.firstGaussianUnit_analytic B1 B2
    (k.scaledLogBUnit_analytic Q hQ hQ0 p) (k.secondLogBUnit_analytic Q hQ hQ0 p)
  have hE0 : E 0=((-((p:ℝ)^2+4*p)/40-1/15:ℝ):ℂ) :=
    k.firstGaussianUnit_zero p B1 B2 (by simpa [B1] using k.scaledLogBUnit_zero Q p)
      (k.secondLogBUnit_zero Q p)
  have hF : ContinuousAt F 0 := (clampedFirstMarkedCorrection_continuousAt p).add hEa.continuousAt
  have hphys := k.firstGaussianUnit_physical Q hQ hQ0 hQphys p (extractionLogB_analyticAt P p)
  have hevent : ∀ᶠδ:ℝ in 𝓝 0,0<δ→δ<y₀→F (δ:ℂ)=(rawExtractedCoefficient P p 1 (y₀-δ):ℂ) := by
    filter_upwards [hphys] with δ hE hδ hδy
    have hY : y₀-δ ∈ Ioo (0:ℝ) y₀ := ⟨by linarith,by linarith⟩
    have he := congrArg Complex.ofReal (first_extracted_correction P p (y₀-δ) hY)
    rw [extractedCoefficient,ite_eq_right (ne_of_gt hY.1),ite_eq_right (ne_of_lt hY.2)] at he
    dsimp only [F]
    rw [clampedFirstMarkedCorrection_physical P p δ ⟨hδ,hδy⟩]
    change (markedCoefficient P p 1 (y₀-δ):ℂ)+k.firstGaussianUnit (k.scaledLogBUnit Q p)
      (k.secondLogBUnit Q p) (δ:ℂ)=_
    rw [hE hδ]
    push_cast at he ⊢
    linear_combination -he
  obtain ⟨R0,hR0,hR⟩ := Metric.eventually_nhds_iff.mp hevent
  let R : ℝ := min R0 y₀
  have hRp : 0<R := lt_min hR0 y₀_pos
  have htrace : ∀δ∈Ioo (0:ℝ) R,F (δ:ℂ)=(rawExtractedCoefficient P p 1 (y₀-δ):ℂ) := by
    intro δ hδ
    apply hR (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hδ.1] using hδ.2.trans_le (min_le_left _ _)) hδ.1
    exact hδ.2.trans_le (min_le_right _ _)
  have hcrit := delta_extension_limit_real_trace (rawExtractedCoefficient P p 1) y₀ F R hRp hF htrace
  change F 0=(criticalExtractedCoefficient P p 1:ℂ) at hcrit
  rw [extractedCoefficient,ite_eq_right y₀_pos.ne',ite_eq_left (Eq.refl y₀)]
  apply Complex.ofReal_injective
  rw [←hcrit]
  dsimp only [F]
  rw [clampedFirstMarkedCorrection_zero,hE0,firstEndpointConstant]
  push_cast
  ring
end WP.HigherOrder
