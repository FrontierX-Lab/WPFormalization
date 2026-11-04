import WPFormalization.RandomGeometry.GeneralPlanarDensityIntensity
import WPFormalization.Probability.PoissonCountContinuity
import WPFormalization.Probability.NNRealWindowBasis

noncomputable section
namespace WP.RandomGeometry
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

/-- The rate of a length window after summing all planar cusp types. -/
def generalPlanarDensityLengthRate (P:PsiTheory) (l:ℝ≥0∞) (b:ℝ≥0) : ℝ≥0 :=
  (b*(generalPlanarTotalWeight P (planarDensitySaddle l))).toNNReal

/-- Cutoff K retains the actual types 0,...,K+1; its complement starts at K+2. -/
def generalPlanarDensityLengthTruncatedRate (P:PsiTheory) (l:ℝ≥0∞) (K:ℕ) (b:ℝ≥0) : ℝ≥0 :=
  ∑k:Fin (K+2),((b:ℝ)*generalPlanarDensityTypeWeight P l k.val).toNNReal

lemma general_planar_density_length_rate_coe (P:PsiTheory) (l:ℝ≥0∞) (b:ℝ≥0) :
    (generalPlanarDensityLengthRate P l b:ℝ) =
      (b:ℝ)*generalPlanarTotalWeight P (planarDensitySaddle l) := by
  apply Real.coe_toNNReal
  exact mul_nonneg b.coe_nonneg (general_planar_total_weight_nonneg P _ (planar_density_saddle_mem l).1)

theorem general_planar_density_length_truncated_rate_tendsto (P:PsiTheory) (l:ℝ≥0∞) (b:ℝ≥0) :
    Tendsto (fun K=>generalPlanarDensityLengthTruncatedRate P l K b) atTop
      (𝓝 (generalPlanarDensityLengthRate P l b)) := by
  apply NNReal.tendsto_coe.mp
  have hsum := (general_planar_density_type_weight_summable P l).mul_left (b:ℝ)
  have htop : Tendsto (fun K:ℕ=>K+2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop N] with K hK
    omega
  have ht := hsum.hasSum.tendsto_sum_nat.comp htop
  have hcoek (k:ℕ) : (((b:ℝ)*generalPlanarDensityTypeWeight P l k).toNNReal:ℝ) =
      (b:ℝ)*generalPlanarDensityTypeWeight P l k :=
    Real.coe_toNNReal _ (mul_nonneg b.coe_nonneg (general_planar_density_type_weight_nonneg P l k))
  simp only [generalPlanarDensityLengthTruncatedRate,NNReal.coe_sum,hcoek,general_planar_density_length_rate_coe]
  simp only [generalPlanarTotalWeight,generalPlanarDensityTypeWeight]
  simp only [Function.comp_def,tsum_mul_left,generalPlanarDensityTypeWeight] at ht
  convert ht using 1
  funext K
  exact Fin.sum_univ_eq_sum_range (fun k:ℕ=>(b:ℝ)*generalPlanarTypeWeight P k (planarDensitySaddle l)) (K+2)

theorem general_planar_density_length_truncated_poisson_law {d:ℕ} (P:PsiTheory)
    (l:ℝ≥0∞) (b:Fin d→ℝ≥0) :
    Probability.LawConverges
      (fun K=>Probability.productPoissonMeasure (fun i=>generalPlanarDensityLengthTruncatedRate P l K (b i)))
      (fun _ z=>z) (Probability.productPoissonMeasure (fun i=>generalPlanarDensityLengthRate P l (b i))) id := by
  exact Probability.product_poisson_law_tendsto _ _
    (fun i=>general_planar_density_length_truncated_rate_tendsto P l (b i))

/-- Genuine length intensity after summing all planar cusp types. -/
def generalPlanarDensityLengthIntensity (P:PsiTheory) (l:ℝ≥0∞) : Measure ℝ≥0 :=
  ENNReal.ofReal (generalPlanarTotalWeight P (planarDensitySaddle l)) • quadraticLengthIntensity

instance (P:PsiTheory) (l:ℝ≥0∞) : IsFiniteMeasureOnCompacts (generalPlanarDensityLengthIntensity P l) := by
  exact IsFiniteMeasureOnCompacts.smul quadraticLengthIntensity ENNReal.ofReal_ne_top

instance (P:PsiTheory) (l:ℝ≥0∞) : IsLocallyFiniteMeasure (generalPlanarDensityLengthIntensity P l) := by
  infer_instance

instance (P:PsiTheory) (l:ℝ≥0∞) : Measure.Regular (generalPlanarDensityLengthIntensity P l) := by
  exact Measure.Regular.smul ENNReal.ofReal_ne_top

instance (P:PsiTheory) (l:ℝ≥0∞) : NullSingletonClass (generalPlanarDensityLengthIntensity P l) := by
  constructor
  intro x
  simp only [generalPlanarDensityLengthIntensity,Measure.smul_apply,quadraticLengthIntensity_singleton,smul_zero]

lemma general_planar_density_length_intensity_Iic (P:PsiTheory) (l:ℝ≥0∞) (b:ℝ≥0) :
    generalPlanarDensityLengthIntensity P l (Iic b) =
      ENNReal.ofReal ((b:ℝ)^2*generalPlanarTotalWeight P (planarDensitySaddle l)) := by
  rw [generalPlanarDensityLengthIntensity,Measure.smul_apply,quadraticLengthIntensity_Iic]
  simp only [smul_eq_mul]
  rw [←ENNReal.ofReal_mul (general_planar_total_weight_nonneg P _ (planar_density_saddle_mem l).1),mul_comm]

lemma general_planar_density_length_intensity_Ioc (P:PsiTheory) (l:ℝ≥0∞) (a b:ℝ≥0) :
    generalPlanarDensityLengthIntensity P l (Ioc a b) =
      ENNReal.ofReal (((b:ℝ)^2-(a:ℝ)^2)*generalPlanarTotalWeight P (planarDensitySaddle l)) := by
  rw [generalPlanarDensityLengthIntensity,Measure.smul_apply,quadraticLengthIntensity_Ioc]
  simp only [smul_eq_mul]
  rw [←ENNReal.ofReal_mul (general_planar_total_weight_nonneg P _ (planar_density_saddle_mem l).1),mul_comm]

theorem general_planar_density_length_rational_basis (P:PsiTheory) (l:ℝ≥0∞) :
    Probability.ContinuityWindowBasis ℝ≥0 (generalPlanarDensityLengthIntensity P l) Probability.nnrealRationalWindows := by
  exact Probability.nnrealRationalWindows_basis _

end WP.RandomGeometry
