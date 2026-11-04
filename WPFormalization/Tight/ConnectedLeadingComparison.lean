import WPFormalization.Tight.ConnectedFourierRealTrace
import WPFormalization.Tight.GeneratingFunctions
import WPFormalization.Tight.ShiftedPolynomial
import WPFormalization.Volumes.BoundaryLeadingComparison
noncomputable section
namespace WP.TightConnected
open Set

def tightLeadingError (P : PsiTheory) (g p : ℕ) (L : Fin p → ℝ)
    (Ybase x : ℝ) : ℝ :=
  Real.pi * (TightMoments.momentTightG P g p L (x : ℂ)).re /
    (markedModel g p (inverseY x) * ∏ i, boundaryFactor 0 (Ybase*(L i))) - 1

lemma tight_leading_error_of_three_errors (P : PsiTheory) (g p : ℕ)
    (hp : 1 ≤ p) (hs : Stable g p) (L : Fin p → ℝ) (Ybase x δ : ℝ)
    (hx : x ∈ Ico 0 xCritical) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hconv : |(TightMoments.momentTightG P g p L (x : ℂ)).re /
      (markedF P g p x * ∏ i, boundaryFactor 0 (tightParameterScale (inverseY x)*L i)) - 1| ≤ δ)
    (hmarked : |markedLeadingError P g p x| ≤ δ)
    (hfactor : |(∏ i, boundaryFactor 0 (tightParameterScale (inverseY x)*L i)) /
      (∏ i, boundaryFactor 0 (Ybase*(L i))) - 1| ≤ δ) :
    |tightLeadingError P g p L Ybase x| ≤ 7 * δ := by
  have hf : markedF P g p x ≠ 0 :=
    (markedF_positive_cusp_weight P g p hp hs x hx).ne'
  have hm : markedModel g p (inverseY x) ≠ 0 :=
    (markedModel_pos_parameter g p hs _ (inverseY_branch x hx).1).ne'
  have hb : (∏ i, boundaryFactor 0 (Ybase*(L i))) ≠ 0 :=
    (Finset.prod_pos (fun i _ => boundaryFactor_pos 0 (Ybase*(L i)))).ne'
  have hc : (∏ i, boundaryFactor 0 (tightParameterScale (inverseY x)*L i)) ≠ 0 :=
    (Finset.prod_pos (fun i _ => boundaryFactor_pos 0 (tightParameterScale (inverseY x)*(L i)))).ne'
  have ht := BoundaryConvolution.three_factor_relative_error
    ((TightMoments.momentTightG P g p L (x : ℂ)).re / (markedF P g p x * ∏ i, boundaryFactor 0 (tightParameterScale (inverseY x)*L i)))
    (Real.pi * markedF P g p x / markedModel g p (inverseY x))
    ((∏ i, boundaryFactor 0 (tightParameterScale (inverseY x)*L i)) / (∏ i, boundaryFactor 0 (Ybase*(L i))))
    δ hδ hδ1 hconv hmarked hfactor
  convert ht using 1
  congr 1
  dsimp only [tightLeadingError]
  field_simp

lemma tight_leading_relative_error (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (L₀ : ℝ) (hL₀ : 0 ≤ L₀) :
    ∃ C E H : ℝ, 0 < C ∧ 0 < E ∧ 0 < H ∧ 2 * E ≤ H ∧
      ∀ g : ℕ, 1 ≤ g → Stable g p → H ≤ (complexity g p : ℝ) →
      ∀ L : Fin p → ℝ, (∀ i, 0 ≤ L i) → ∀ Ybase x : ℝ,
      x ∈ Ico 0 xCritical → (∀ i, tightParameterScale (inverseY x)*L i ≤ L₀) → ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      C / g ≤ δ → E / (complexity g p : ℝ) ≤ δ →
      |(∏ i, boundaryFactor 0 (tightParameterScale (inverseY x)*L i)) /
        (∏ i, boundaryFactor 0 (Ybase*(L i))) - 1| ≤ δ →
      |tightLeadingError P g p L Ybase x| ≤ 7 * δ := by
  obtain ⟨C,hC,hconv⟩ := tightShiftedPolynomial_uniform_relative_error P p hp L₀ hL₀
  obtain ⟨E,H,hE,hH,hEH,hmarked⟩ := marked_leading_relative_error P p hp
  refine ⟨C,E,H,hC,hE,hH,hEH,?_⟩
  intro g hg hs hgh L hL Ybase x hx hscaled δ hδ hδ1 hCg hEh hfactor
  apply tight_leading_error_of_three_errors P g p hp hs L Ybase x δ hx hδ hδ1 _
    ((hmarked g hgh x hx).trans hEh) hfactor
  have hh := hconv g hg (inverseY x) (inverseY_branch x hx).1 L hL hscaled
  have hshift := string_flow_proof P g p hs (inverseY x) (inverseY_branch x hx).1
  rw [(inverseY_branch x hx).2] at hshift
  rw [hshift] at hh
  rw [TightMoments.momentTightG_ofReal P g p L x hx,Complex.ofReal_re]
  exact hh.trans hCg

lemma real_centered_tight_leading_identity (P : PsiTheory) (g p : ℕ)
    (hp : 1 ≤ p) (hs : Stable g p) (L : Fin p → ℝ) (Ybase x μ σ u : ℝ)
    (hx : x ∈ Ico 0 xCritical) (hxu : x * Real.exp (u / σ) ∈ Ico 0 xCritical) :
    centeredTightGenerating P g p L x μ σ (u : ℂ) =
      ((Real.exp (-μ * u / σ) * markedModel g p (inverseY (x * Real.exp (u / σ))) /
          markedModel g p (inverseY x) : ℝ) : ℂ) *
        (((1 + tightLeadingError P g p L Ybase (x * Real.exp (u / σ))) /
          (1 + tightLeadingError P g p L Ybase x) : ℝ) : ℂ) := by
  rw [centeredTightGenerating_ofReal P g p L x μ σ u hx hxu, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  have hf : (TightMoments.momentTightG P g p L (x : ℂ)).re ≠ 0 := (momentTightG_real_pos P g p hp hs L x hx).ne'
  have hm : markedModel g p (inverseY x) ≠ 0 :=
    (markedModel_pos_parameter g p hs _ (inverseY_branch x hx).1).ne'
  have hmt : markedModel g p (inverseY (x * Real.exp (u / σ))) ≠ 0 :=
    (markedModel_pos_parameter g p hs _ (inverseY_branch _ hxu).1).ne'
  have hb : (∏ i, boundaryFactor 0 (Ybase*(L i))) ≠ 0 :=
    (Finset.prod_pos (fun i _ => boundaryFactor_pos 0 (Ybase*(L i)))).ne'
  have hpineq : Real.pi ≠ 0 := Real.pi_ne_zero
  dsimp only [tightLeadingError]
  rw [TightMoments.momentTightG_ofReal P g p L x hx,
    TightMoments.momentTightG_ofReal P g p L (x*Real.exp (u/σ)) hxu,
    Complex.ofReal_re,Complex.ofReal_re]
  field_simp [Real.pi_ne_zero]
  <;> ring_nf
  <;> simp [Real.pi_ne_zero]

lemma tight_leading_slit_comparison (P : PsiTheory) (g p : ℕ)
    (hp : 1 ≤ p) (hs : Stable g p) (L : Fin p → ℝ) (Ybase δ : ℝ)
    (hδ : 0 < δ) (hsmall : 7 * δ ≤ 1 / 2)
    (x μ σ r G : ℝ) (hx : x ∈ Ico 0 xCritical) (hr : 0 < r) (hG : 0 < G)
    (he0 : |tightLeadingError P g p L Ybase x| ≤ 7 * δ)
    (hreltilt : ∀ u : ℝ, |u| < 16 * r →
      |tightLeadingError P g p L Ybase (x * Real.exp (u / σ))| ≤ 7 * δ)
    (M : ℂ → ℂ) (hM : AnalyticOnNhd ℂ M (Metric.ball 0 (16 * r)))
    (hMb : ∀ z : ℂ, ‖z‖ < 16 * r → ‖M z‖ ≤ G)
    (htilt : ∀ z : ℂ, ‖z‖ < 16 * r → x * Real.exp (z.re / σ) ∈ Ico 0 xCritical)
    (htrace : ∀ u : ℝ, |u| < 16 * r → M (u : ℂ) =
      ((Real.exp (-μ * u / σ) * markedModel g p (inverseY (x * Real.exp (u / σ))) /
        markedModel g p (inverseY x) : ℝ) : ℂ))
    (w : ℂ) (hw : ‖w‖ ≤ 3 * r / 2) :
    ‖centeredTightGenerating P g p L x μ σ w - M w‖ ≤ 4 * Real.sqrt (7 * δ) * G := by
  apply Analysis.centered_slit_comparison _ M r G (7 * δ) hr hG (by positivity) hsmall
    (centeredTightGenerating_analytic_disk P g p hp hs L x μ σ (16 * r) hx.1 (fun z hz => (htilt z hz).2))
    hM hMb
    (fun z hz => centeredTightGenerating_norm_domination P g p hp hs L x μ σ hx
      (momentTightG_real_pos P g p hp hs L x hx) z (htilt z hz))
    (tightLeadingError P g p L Ybase x : ℂ) _ _ w hw
  · simpa only [Complex.norm_real, Real.norm_eq_abs] using he0
  · intro u hu
    have huc : ‖(u : ℂ)‖ < 16 * r := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hu
    have hxu : x * Real.exp (u / σ) ∈ Ico 0 xCritical := by
      simpa only [Complex.ofReal_re] using htilt (u : ℂ) huc
    refine ⟨(tightLeadingError P g p L Ybase (x * Real.exp (u / σ)) : ℂ),?_,?_⟩
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using hreltilt u hu
    · rw [htrace u hu]
      simpa only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one] using
        real_centered_tight_leading_identity P g p hp hs L Ybase x μ σ u hx hxu

end WP.TightConnected
