import WPFormalization.Volumes.BoundaryConvolutionIdentification
import WPFormalization.Volumes.PointMassFourier

/-! Exact positivity and universal Fourier domination for the genuine full
boundary generating function. These bounds retain the original lengths and
all external degrees; no Gaussian or local limit assertion is assumed. -/
noncomputable section
namespace WP.BoundaryConvolution
open Set Filter PositiveConvolution
open scoped Topology

lemma translationKernel_zero_degree_one_le (Y : ℝ) (hY : 0 ≤ Y) :
    1 ≤ (translationKernel 0 (Y:ℂ)).re := by
  have hs := translationKernel_real_hasSum 0 Y
  have hh := hs.summable.le_tsum 0 (fun j hj => by positivity)
  rw [hs.tsum_eq] at hh
  simpa using hh

lemma realTranslationWeight_zero_degree_pos (t : ℝ) (ht : 0 ≤ t)
    (Y : ℝ) (hY : 0 ≤ Y) : 0 < realTranslationWeight t 0 Y := by
  have hh := translationKernel_zero_degree_one_le (t*Y) (mul_nonneg ht hY)
  have he : realTranslationWeight t 0 Y = (translationKernel 0 ((t*Y:ℝ):ℂ)).re := by
    simp [realTranslationWeight,translationWeight]
  rw [he]
  linarith

lemma stringBoundaryAmplitude_pos (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p) (hs : Stable g p)
    (t : Fin p → ℝ) (ht : ∀ i, 0 ≤ t i) (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    0 < stringBoundaryAmplitude P g t 0 Y := by
  classical
  have hzero : (fun _ : Fin p => (0:ℕ)) ∈ externalDegreeBox p (dimension g (0+p)) := by simp
  have hsum := Finset.single_le_sum
    (f := fun b : Fin p → ℕ => externalMarkedAmplitude P g 0 b Y *
      ∏ i, realTranslationWeight (t i) (b i) Y)
    (fun b hb => mul_nonneg (externalMarkedAmplitude_nonneg P g hp 0 b Y hY)
      (Finset.prod_nonneg (fun i _ => realTranslationWeight_nonneg _ (ht i) _ _ hY.1))) hzero
  change _ ≤ stringBoundaryAmplitude P g t 0 Y at hsum
  apply lt_of_lt_of_le _ hsum
  apply mul_pos
  · simp only [externalMarkedAmplitude,List.replicate_zero,List.nil_append,List.ofFn_const]
    exact div_pos (shifted_zero_pos_nonempty P g p hp hs Y hY)
      (externalOddWeight_pos _)
  · exact Finset.prod_pos (fun i hi => realTranslationWeight_zero_degree_pos _ (ht i) _ hY.1)

lemma boundaryG_real_pos (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p) (hs : Stable g p)
    (L : Fin p → ℝ) (x : ℝ) (hx : x ∈ Ico 0 xCritical) :
    0 < (boundaryG P g p L (x:ℂ)).re := by
  rw [boundaryG_ofReal P g p hp hs L x hx,Complex.ofReal_re]
  exact stringBoundaryAmplitude_pos P g p hp hs _ (fun i => lengthTime_nonneg _) _
    (inverseY_branch x hx).1

lemma boundaryR_real_pos (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p) (hs : Stable g p)
    (L : Fin p → ℝ) (x : ℝ) (hx : x ∈ Ico 0 xCritical) :
    0 < (boundaryR P g p L (x:ℂ)).re := by
  rw [boundaryR_ofReal P g p hp hs L x hx,Complex.ofReal_re]
  exact mul_pos (pow_pos (a_pos _ (inverseY_branch x hx).1) _)
    (stringBoundaryAmplitude_pos P g p hp hs _ (fun i => lengthTime_nonneg _) _
      (inverseY_branch x hx).1)

lemma boundaryG_circle_domination (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p) (hs : Stable g p)
    (L : Fin p → ℝ) (x : ℝ) (hx : x ∈ Ico 0 xCritical)
    (z : ℂ) (hz : ‖z‖ ≤ x) :
    ‖boundaryG P g p L z‖/(boundaryG P g p L (x:ℂ)).re ≤
      ‖universalV P z/universalV P (x:ℂ)‖^(complexity g p) := by
  have hV : universalV P (x:ℂ) = Complex.ofReal ((a (inverseY x))⁻¹) :=
    planarThird_ofReal P x hx
  have hVp : 0 < (universalV P (x:ℂ)).re := by
    rw [hV,Complex.ofReal_re]
    exact inv_pos.mpr (a_pos _ (inverseY_branch x hx).1)
  have hVi : (universalV P (x:ℂ)).im=0 := by rw [hV,Complex.ofReal_im]
  have hRi : (boundaryR P g p L (x:ℂ)).im=0 := by
    rw [boundaryR_ofReal P g p hp hs L x hx,Complex.ofReal_im]
  exact positive_series_circle_domination (universalV P) (boundaryR P g p L) x (complexity g p)
    hx.1 hVp hVi (boundaryR_real_pos P g p hp hs L x hx) hRi
    (boundaryR_real_nonnegative_coefficients P g p L)
    (fun z hz => boundaryR_taylor P g p L z (hz.trans_lt hx.2)) z hz

end WP.BoundaryConvolution
