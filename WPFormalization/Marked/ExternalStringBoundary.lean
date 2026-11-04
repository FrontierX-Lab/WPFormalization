import WPFormalization.Marked.ExternalStringAnalytic
import WPFormalization.Volumes.BoundaryTranslationKernel
noncomputable section
namespace WP.BoundaryConvolution
open Set Filter
open scoped Topology
/-- The exact entire boundary weight on the real parameter axis. -/
def realTranslationWeight (t : ℝ) (b : ℕ) (Y : ℝ) : ℝ :=
  (translationWeight t b (Y:ℂ)).re
lemma realTranslationWeight_analyticAt (t : ℝ) (b : ℕ) (Y : ℝ) :
    AnalyticAt ℝ (realTranslationWeight t b) Y :=
  (translationWeight_analyticAt t b (Y:ℂ)).re_ofReal
lemma realTranslationWeight_hasDerivAt (t : ℝ) (b : ℕ) (Y : ℝ) :
    HasDerivAt (realTranslationWeight t b) (realTranslationWeight t (b+1) Y) Y :=
  (translationWeight_hasDerivAt t b (Y:ℂ)).real_of_complex
lemma realTranslationWeight_nonneg (t : ℝ) (ht : 0 ≤ t) (b : ℕ) (Y : ℝ) (hY : 0 ≤ Y) :
    0 ≤ realTranslationWeight t b Y := by
  have he : realTranslationWeight t b Y = t^b * (translationKernel b ((t*Y:ℝ):ℂ)).re := by
    simp [realTranslationWeight,translationWeight,←Complex.ofReal_pow,Complex.mul_re]
  rw [he]
  exact mul_nonneg (pow_nonneg ht _) (translationKernel_nonneg b (t*Y) (mul_nonneg ht hY))
lemma realTranslationWeight_zero (t : ℝ) (b : ℕ) :
    realTranslationWeight t b 0 = t^b / (b.factorial:ℝ) := by
  have hz := translationKernel_iteratedDeriv_zero b 0
  simp only [iteratedDeriv_zero,zero_add] at hz
  simp only [realTranslationWeight,translationWeight,Complex.ofReal_zero,mul_zero,hz]
  rw [←Complex.ofReal_natCast,←Complex.ofReal_inv,←Complex.ofReal_pow,←Complex.ofReal_mul,
    Complex.ofReal_re]
  ring

/-- The actual finite boundary insertion, including the arbitrary additional cusps. -/
def stringBoundaryAmplitude (P : PsiTheory) (g : ℕ) {p : ℕ} (t : Fin p → ℝ) (q : ℕ) (Y : ℝ) : ℝ :=
  externalStringAmplitude P g (fun i b => realTranslationWeight (t i) b) q Y

lemma stringBoundaryAmplitude_hasDerivAt (P : PsiTheory) (g : ℕ) (hg : 2 ≤ g)
    {p : ℕ} (t : Fin p → ℝ) (q : ℕ) (Y : ℝ) (ha : a Y ≠ 0) :
    HasDerivAt (stringBoundaryAmplitude P g t q)
      (a Y * stringBoundaryAmplitude P g t (q+1) Y) Y :=
  externalStringAmplitude_hasDerivAt P g hg _ q Y ha
    (fun i b => realTranslationWeight_hasDerivAt (t i) b Y)

/-- Genuine external boundary insertion string flow and its convergent EGF.
Every coefficient is the original finite shifted amplitude; no insertion-flow
or convergence hypothesis is part of this conclusion. -/
lemma stringBoundaryAmplitude_real_hasSum (P : PsiTheory) (g : ℕ) (hg : 2 ≤ g)
    {p : ℕ} (hp : 1 ≤ p) (t : Fin p → ℝ) (ht : ∀ i, 0 ≤ t i)
    (x : ℝ) (hx : x ∈ Ico 0 xCritical) :
    HasSum (fun q : ℕ => stringBoundaryAmplitude P g t q 0 / (q.factorial:ℝ) * x^q)
      (stringBoundaryAmplitude P g t 0 (inverseY x)) :=
  externalStringAmplitude_real_hasSum P g hg hp _
    (fun i b Y => realTranslationWeight_analyticAt (t i) b Y)
    (fun i b Y => realTranslationWeight_hasDerivAt (t i) b Y)
    (fun i b Y hY => realTranslationWeight_nonneg (t i) (ht i) b Y hY) x hx
end WP.BoundaryConvolution
