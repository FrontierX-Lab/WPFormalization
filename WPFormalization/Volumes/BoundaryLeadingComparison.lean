import WPFormalization.Volumes.BoundaryFourierDomination
import WPFormalization.Volumes.BoundaryCenteredGenerating
import WPFormalization.Marked.ExternalStringUniformError
import WPFormalization.Volumes.LeadingMarkedComparison

/-! Internal real-axis and slit comparisons for the genuine boundary
generating function. All parameter-chart and small-error budgets remain
explicit, to be discharged by the uniform boundary producer. -/
noncomputable section
namespace WP.BoundaryConvolution
open Set

def boundaryLeadingError (P : PsiTheory) (g p : ℕ) (L : Fin p → ℝ)
    (Ybase x : ℝ) : ℝ :=
  Real.pi * (boundaryG P g p L (x : ℂ)).re /
    (markedModel g p (inverseY x) * ∏ i, boundaryFactor Ybase (L i)) - 1

lemma three_factor_relative_error (a b c δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ha : |a - 1| ≤ δ) (hb : |b - 1| ≤ δ) (hc : |c - 1| ≤ δ) :
    |a * b * c - 1| ≤ 7 * δ := by
  have hb2 : |b| ≤ 2 := by
    have hh := abs_sub_le b 1 0
    simp only [sub_zero, abs_one] at hh
    linarith
  have hc2 : |c| ≤ 2 := by
    have hh := abs_sub_le c 1 0
    simp only [sub_zero, abs_one] at hh
    linarith
  have he : a * b * c - 1 = (a - 1) * b * c + (b - 1) * c + (c - 1) := by ring
  rw [he]
  calc
    _ ≤ |(a - 1) * b * c| + |(b - 1) * c| + |c - 1| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |a - 1| * |b| * |c| + |b - 1| * |c| + |c - 1| := by rw [abs_mul, abs_mul, abs_mul]
    _ ≤ δ * 2 * 2 + δ * 2 + δ := by gcongr
    _ = 7 * δ := by ring

lemma boundary_leading_error_of_three_errors (P : PsiTheory) (g p : ℕ)
    (hp : 1 ≤ p) (hs : Stable g p) (L : Fin p → ℝ) (Ybase x δ : ℝ)
    (hx : x ∈ Ico 0 xCritical) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hconv : |(boundaryG P g p L (x : ℂ)).re /
      (markedF P g p x * ∏ i, boundaryFactor (inverseY x) (L i)) - 1| ≤ δ)
    (hmarked : |markedLeadingError P g p x| ≤ δ)
    (hfactor : |(∏ i, boundaryFactor (inverseY x) (L i)) /
      (∏ i, boundaryFactor Ybase (L i)) - 1| ≤ δ) :
    |boundaryLeadingError P g p L Ybase x| ≤ 7 * δ := by
  have hf : markedF P g p x ≠ 0 :=
    (markedF_positive_cusp_weight P g p hp hs x hx).ne'
  have hm : markedModel g p (inverseY x) ≠ 0 :=
    (markedModel_pos_parameter g p hs _ (inverseY_branch x hx).1).ne'
  have hb : (∏ i, boundaryFactor Ybase (L i)) ≠ 0 :=
    (Finset.prod_pos (fun i _ => boundaryFactor_pos Ybase (L i))).ne'
  have hc : (∏ i, boundaryFactor (inverseY x) (L i)) ≠ 0 :=
    (Finset.prod_pos (fun i _ => boundaryFactor_pos (inverseY x) (L i))).ne'
  have ht := three_factor_relative_error
    ((boundaryG P g p L (x : ℂ)).re / (markedF P g p x * ∏ i, boundaryFactor (inverseY x) (L i)))
    (Real.pi * markedF P g p x / markedModel g p (inverseY x))
    ((∏ i, boundaryFactor (inverseY x) (L i)) / (∏ i, boundaryFactor Ybase (L i)))
    δ hδ hδ1 hconv hmarked hfactor
  convert ht using 1
  congr 1
  dsimp only [boundaryLeadingError]
  field_simp

lemma boundary_leading_relative_error (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (L₀ : ℝ) (hL₀ : 0 ≤ L₀) :
    ∃ C E H : ℝ, 0 < C ∧ 0 < E ∧ 0 < H ∧ 2 * E ≤ H ∧
      ∀ g : ℕ, 1 ≤ g → Stable g p → H ≤ (complexity g p : ℝ) →
      ∀ L : Fin p → ℝ, (∀ i, L i ∈ Icc 0 L₀) → ∀ Ybase x : ℝ,
      x ∈ Ico 0 xCritical → ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      C / g ≤ δ → E / (complexity g p : ℝ) ≤ δ →
      |(∏ i, boundaryFactor (inverseY x) (L i)) /
        (∏ i, boundaryFactor Ybase (L i)) - 1| ≤ δ →
      |boundaryLeadingError P g p L Ybase x| ≤ 7 * δ := by
  obtain ⟨C,hC,hconv⟩ := stringBoundaryAmplitude_uniform_real_axis P p hp L₀ hL₀
  obtain ⟨E,H,hE,hH,hEH,hmarked⟩ := marked_leading_relative_error P p hp
  refine ⟨C,E,H,hC,hE,hH,hEH,?_⟩
  intro g hg hs hgh L hL Ybase x hx δ hδ hδ1 hCg hEh hfactor
  apply boundary_leading_error_of_three_errors P g p hp hs L Ybase x δ hx hδ hδ1 _
    ((hmarked g hgh x hx).trans hEh) hfactor
  have hh := hconv g hg (inverseY x) (inverseY_branch x hx).1 L hL
  have hshift := string_flow_proof P g p hs (inverseY x) (inverseY_branch x hx).1
  rw [(inverseY_branch x hx).2] at hshift
  rw [hshift] at hh
  rw [boundaryG_ofReal P g p hp hs L x hx, Complex.ofReal_re]
  simpa only [lengthTime] using hh.trans hCg

lemma centeredBoundaryGenerating_real (P : PsiTheory) (g p : ℕ)
    (L : Fin p → ℝ) (x μ σ u : ℝ) (hx : x ∈ Ico 0 xCritical)
    (hxu : x * Real.exp (u / σ) ∈ Ico 0 xCritical) :
    centeredBoundaryGenerating P g p L x μ σ (u : ℂ) =
      ((Real.exp (-μ * u / σ) * (boundaryG P g p L ((x * Real.exp (u / σ) : ℝ) : ℂ)).re /
        (boundaryG P g p L (x : ℂ)).re : ℝ) : ℂ) := by
  have hre (y : ℝ) (hy : y ∈ Ico 0 xCritical) :
      boundaryG P g p L (y : ℂ) = ((boundaryG P g p L (y : ℂ)).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using boundaryG_ofReal_im_zero P g p L y hy
  unfold centeredBoundaryGenerating
  rw [← Complex.ofReal_div, ← Complex.ofReal_exp, ← Complex.ofReal_mul, hre _ hxu, hre _ hx]
  have he : -(μ : ℂ) * (u : ℂ) / (σ : ℂ) = ((-μ * u / σ : ℝ) : ℂ) := by push_cast; ring
  rw [he, ← Complex.ofReal_exp]
  push_cast
  simp only [Complex.ofReal_re]
  ring

lemma real_centered_boundary_leading_identity (P : PsiTheory) (g p : ℕ)
    (hp : 1 ≤ p) (hs : Stable g p) (L : Fin p → ℝ) (Ybase x μ σ u : ℝ)
    (hx : x ∈ Ico 0 xCritical) (hxu : x * Real.exp (u / σ) ∈ Ico 0 xCritical) :
    centeredBoundaryGenerating P g p L x μ σ (u : ℂ) =
      ((Real.exp (-μ * u / σ) * markedModel g p (inverseY (x * Real.exp (u / σ))) /
          markedModel g p (inverseY x) : ℝ) : ℂ) *
        (((1 + boundaryLeadingError P g p L Ybase (x * Real.exp (u / σ))) /
          (1 + boundaryLeadingError P g p L Ybase x) : ℝ) : ℂ) := by
  rw [centeredBoundaryGenerating_real P g p L x μ σ u hx hxu, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  have hf : (boundaryG P g p L (x : ℂ)).re ≠ 0 := (boundaryG_real_pos P g p hp hs L x hx).ne'
  have hm : markedModel g p (inverseY x) ≠ 0 :=
    (markedModel_pos_parameter g p hs _ (inverseY_branch x hx).1).ne'
  have hmt : markedModel g p (inverseY (x * Real.exp (u / σ))) ≠ 0 :=
    (markedModel_pos_parameter g p hs _ (inverseY_branch _ hxu).1).ne'
  have hb : (∏ i, boundaryFactor Ybase (L i)) ≠ 0 :=
    (Finset.prod_pos (fun i _ => boundaryFactor_pos Ybase (L i))).ne'
  have hpineq : Real.pi ≠ 0 := Real.pi_ne_zero
  dsimp only [boundaryLeadingError]
  field_simp
  <;> ring

lemma boundary_leading_slit_comparison (P : PsiTheory) (g p : ℕ)
    (hp : 1 ≤ p) (hs : Stable g p) (L : Fin p → ℝ) (Ybase δ : ℝ)
    (hδ : 0 < δ) (hsmall : 7 * δ ≤ 1 / 2)
    (x μ σ r G : ℝ) (hx : x ∈ Ico 0 xCritical) (hr : 0 < r) (hG : 0 < G)
    (he0 : |boundaryLeadingError P g p L Ybase x| ≤ 7 * δ)
    (hreltilt : ∀ u : ℝ, |u| < 16 * r →
      |boundaryLeadingError P g p L Ybase (x * Real.exp (u / σ))| ≤ 7 * δ)
    (M : ℂ → ℂ) (hM : AnalyticOnNhd ℂ M (Metric.ball 0 (16 * r)))
    (hMb : ∀ z : ℂ, ‖z‖ < 16 * r → ‖M z‖ ≤ G)
    (htilt : ∀ z : ℂ, ‖z‖ < 16 * r → x * Real.exp (z.re / σ) ∈ Ico 0 xCritical)
    (htrace : ∀ u : ℝ, |u| < 16 * r → M (u : ℂ) =
      ((Real.exp (-μ * u / σ) * markedModel g p (inverseY (x * Real.exp (u / σ))) /
        markedModel g p (inverseY x) : ℝ) : ℂ))
    (w : ℂ) (hw : ‖w‖ ≤ 3 * r / 2) :
    ‖centeredBoundaryGenerating P g p L x μ σ w - M w‖ ≤ 4 * Real.sqrt (7 * δ) * G := by
  apply Analysis.centered_slit_comparison _ M r G (7 * δ) hr hG (by positivity) hsmall
    (centeredBoundaryGenerating_analytic_disk P g p L x μ σ (16 * r) hx.1 (fun z hz => (htilt z hz).2))
    hM hMb
    (fun z hz => centeredBoundaryGenerating_norm_domination P g p L x μ σ hx
      (boundaryG_real_pos P g p hp hs L x hx) z (htilt z hz))
    (boundaryLeadingError P g p L Ybase x : ℂ) _ _ w hw
  · simpa only [Complex.norm_real, Real.norm_eq_abs] using he0
  · intro u hu
    have huc : ‖(u : ℂ)‖ < 16 * r := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hu
    have hxu : x * Real.exp (u / σ) ∈ Ico 0 xCritical := by
      simpa only [Complex.ofReal_re] using htilt (u : ℂ) huc
    refine ⟨(boundaryLeadingError P g p L Ybase (x * Real.exp (u / σ)) : ℂ),?_,?_⟩
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using hreltilt u hu
    · rw [htrace u hu]
      simpa only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one] using
        real_centered_boundary_leading_identity P g p hp hs L Ybase x μ σ u hx hxu

end WP.BoundaryConvolution
