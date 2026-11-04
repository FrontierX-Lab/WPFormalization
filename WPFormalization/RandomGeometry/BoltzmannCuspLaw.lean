import WPFormalization.Tight.ConnectedPoissonPhi
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.Variance

noncomputable section
namespace WP.BoltzmannCusp
open Set MeasureTheory
open scoped ENNReal Topology

/-- Actual normalized coefficients of the unmarked volume series. -/
def weight (P : PsiTheory) (g : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  realCoeff (Phi P g) n * x^n / markedF P g 0 x

lemma weight_probability_data (P : PsiTheory) (g : ℕ) (hg : 2≤g)
    (hf0 : 0 < markedF P g 0 0) (x : ℝ) (hx : x∈Ico 0 xCritical)
    (hfx : 0 < markedF P g 0 x) :
    (∀ n,0≤weight P g x n) ∧ HasSum (weight P g x) 1 ∧
      ∀ z∈Icc (0:ℝ) 1,HasSum (fun n=>weight P g x n*z^n)
        (markedF P g 0 (x*z)/markedF P g 0 x) := by
  apply TightConnected.connected_probability_data _ _ _ hx.1
    (TightConnected.connected_phi_nonnegative_coefficients P g hg hf0) hfx
  intro z hz
  have hxz : x*z∈Ico (0:ℝ) xCritical :=
    ⟨mul_nonneg hx.1 hz.1,(mul_le_of_le_one_right hx.1 hz.2).trans_lt hx.2⟩
  have hs := marked_generating_hasSum P g 0 ((x*z:ℝ):ℂ)
    (by rw [Complex.norm_of_nonneg hxz.1];exact hxz.2)
  simpa only [iteratedDeriv_zero,markedF] using TightConnected.connected_real_taylor_hasSum _ _ hs

/-- A real nonnegative unit-mass sequence, as an actual Mathlib PMF. -/
def pmfOfWeights (w : ℕ→ℝ) (hw : ∀ n,0≤w n) (hs : HasSum w 1) : PMF ℕ :=
  ⟨fun n=>ENNReal.ofReal (w n),by
    convert (ENNReal.summable : Summable (fun n=>ENNReal.ofReal (w n))).hasSum using 1
    rw [←ENNReal.ofReal_tsum_of_nonneg hw hs.summable,hs.tsum_eq]
    simp⟩

lemma pmfOfWeights_apply (w : ℕ→ℝ) (hw : ∀ n,0≤w n) (hs : HasSum w 1) (n : ℕ) :
    pmfOfWeights w hw hs n = ENNReal.ofReal (w n) := rfl

lemma pmfOfWeights_toMeasure (w : ℕ→ℝ) (hw : ∀ n,0≤w n) (hs : HasSum w 1) :
    (pmfOfWeights w hw hs).toMeasure =
      Measure.sum (fun n=>ENNReal.ofReal (w n) • Measure.dirac n) := by
  ext s hs'
  rw [PMF.toMeasure_apply _ hs',Measure.sum_apply _ hs']
  apply tsum_congr
  intro n
  simp only [Measure.smul_apply,Measure.dirac_apply' _ hs',smul_eq_mul]
  by_cases hn : n∈s <;> simp [hn,pmfOfWeights] <;> rfl

lemma pmfOfWeights_integrable (w : ℕ→ℝ) (hw : ∀ n,0≤w n) (hs : HasSum w 1)
    (f : ℕ→ℝ) (hf : Summable (fun n=>w n*‖f n‖)) :
    Integrable f (pmfOfWeights w hw hs).toMeasure := by
  rw [pmfOfWeights_toMeasure]
  apply integrable_sum_dirac (fun n=>ENNReal.ofReal_ne_top)
  simpa only [ENNReal.toReal_ofReal (hw _)] using hf

lemma pmfOfWeights_integral (w : ℕ→ℝ) (hw : ∀ n,0≤w n) (hs : HasSum w 1)
    (f : ℕ→ℝ) :
    ∫ n,f n ∂(pmfOfWeights w hw hs).toMeasure = ∑' n,w n*f n := by
  rw [pmfOfWeights_toMeasure,integral_sum_dirac (fun n=>ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal (hw _),smul_eq_mul]

/-- The actual discrete law. Positivity is discharged uniformly for large genus below. -/
def law (P : PsiTheory) (g : ℕ) (hg : 2≤g) (hf0 : 0 < markedF P g 0 0)
    (x : ℝ) (hx : x∈Ico 0 xCritical) (hfx : 0 < markedF P g 0 x) :
    ProbabilityMeasure ℕ :=
  ⟨(pmfOfWeights (weight P g x) (weight_probability_data P g hg hf0 x hx hfx).1
    (weight_probability_data P g hg hf0 x hx hfx).2.1).toMeasure,inferInstance⟩

lemma law_singleton (P : PsiTheory) (g : ℕ) (hg : 2≤g) (hf0 : 0 < markedF P g 0 0)
    (x : ℝ) (hx : x∈Ico 0 xCritical) (hfx : 0 < markedF P g 0 x) (n : ℕ) :
    (law P g hg hf0 x hx hfx : Measure ℕ) {n}=ENNReal.ofReal (weight P g x n) := by
  exact PMF.toMeasure_apply_singleton _ n (measurableSet_singleton n)

lemma law_pgf (P : PsiTheory) (g : ℕ) (hg : 2≤g) (hf0 : 0 < markedF P g 0 0)
    (x : ℝ) (hx : x∈Ico 0 xCritical) (hfx : 0 < markedF P g 0 x)
    (z : ℝ) (hz : z∈Icc (0:ℝ) 1) :
    Integrable (fun n:ℕ=>z^n) (law P g hg hf0 x hx hfx : Measure ℕ) ∧
    ∫ n:ℕ,z^n ∂(law P g hg hf0 x hx hfx : Measure ℕ)=
      markedF P g 0 (x*z)/markedF P g 0 x := by
  have hd := weight_probability_data P g hg hf0 x hx hfx
  constructor
  · apply pmfOfWeights_integrable
    simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hz.1 _)] using (hd.2.2 z hz).summable
  · exact (pmfOfWeights_integral _ _ _ _).trans (hd.2.2 z hz).tsum_eq

lemma weight_zero (P : PsiTheory) (g : ℕ) (hf0 : markedF P g 0 0≠0) (n : ℕ) :
    weight P g 0 n=if n=0 then 1 else 0 := by
  by_cases hn : n=0
  · subst n
    simp only [weight,pow_zero,mul_one,ite_true]
    have he : realCoeff (Phi P g) 0=markedF P g 0 0 := by simp [realCoeff,coeff,markedF]
    rw [he,div_self hf0]
  · simp [weight,hn]

lemma law_zero (P : PsiTheory) (g : ℕ) (hg : 2≤g) (hf0 : 0 < markedF P g 0 0) :
    (law P g hg hf0 0 ⟨le_rfl,Analysis.xCritical_pos_parameter⟩ hf0 : Measure ℕ)=Measure.dirac 0 := by
  apply Measure.ext_of_singleton
  intro n
  change (pmfOfWeights _ _ _).toMeasure {n}=(Measure.dirac 0) {n}
  rw [PMF.toMeasure_apply_singleton _ n (measurableSet_singleton n)]
  change ENNReal.ofReal (weight P g 0 n)=(Measure.dirac 0) {n}
  rw [weight_zero P g hf0.ne']
  by_cases hn : n=0 <;> simp [hn]

end WP.BoltzmannCusp
namespace WP.BoltzmannCusp
open Set MeasureTheory
lemma law_integral (P:PsiTheory) (g:ℕ) (hg:2≤g) (hf0:0 < markedF P g 0 0)
    (x:ℝ) (hx:x∈Ico 0 xCritical) (hfx:0 < markedF P g 0 x) (f:ℕ→ℝ) :
    ∫n:ℕ,f n ∂(law P g hg hf0 x hx hfx:Measure ℕ)=∑'n,weight P g x n*f n :=
  pmfOfWeights_integral _ _ _ _
lemma law_integrable_of_bound (P:PsiTheory) (g:ℕ) (hg:2≤g) (hf0:0 < markedF P g 0 0)
    (x:ℝ) (hx:x∈Ico 0 xCritical) (hfx:0 < markedF P g 0 x) (f:ℕ→ℝ)
    (B:ℝ) (hB:∀n,|f n|≤B) : Integrable f (law P g hg hf0 x hx hfx:Measure ℕ) := by
  apply Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable B
  exact ae_of_all _ fun n=>by simpa only [Real.norm_eq_abs] using hB n
end WP.BoltzmannCusp
