import WPFormalization.RandomGeometry.GeneralPlanarDensitySaddle
import WPFormalization.RandomGeometry.GeneralPlanarDensityWeights
import WPFormalization.RandomGeometry.QuadraticLengthIntensity
import Mathlib.MeasureTheory.Measure.Prod

noncomputable section
namespace WP.RandomGeometry
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

def generalPlanarDensityTypeWeight (P : PsiTheory) (l : ℝ≥0∞) (k : ℕ) : ℝ :=
  generalPlanarTypeWeight P k (planarDensitySaddle l)

lemma general_planar_density_type_weight_nonneg (P : PsiTheory) (l : ℝ≥0∞) (k : ℕ) :
    0 ≤ generalPlanarDensityTypeWeight P l k :=
  general_planar_type_weight_nonneg P k _ (planar_density_saddle_mem l).1

lemma general_planar_density_type_weight_summable (P : PsiTheory) (l : ℝ≥0∞) :
    Summable (generalPlanarDensityTypeWeight P l) :=
  general_planar_type_weight_summable P _ (planar_density_saddle_mem l)

@[simp] lemma general_planar_density_type_weight_zero (P : PsiTheory) (k : ℕ) :
    generalPlanarDensityTypeWeight P 0 k = if k=2 then 1 else 0 := by
  simp [generalPlanarDensityTypeWeight,general_planar_type_weight_at_zero]

@[simp] lemma general_planar_density_type_weight_top (P : PsiTheory) (k : ℕ) :
    generalPlanarDensityTypeWeight P ∞ k = generalPlanarTypeWeight P k xCritical := by
  simp [generalPlanarDensityTypeWeight]

theorem general_planar_type_weight_tendsto_density (P : PsiTheory) (k : ℕ)
    (n : ℕ → ℕ) (hn : Tendsto (fun g:ℕ => (n g:ℝ)/Real.sqrt g) atTop atTop)
    (l : ℝ≥0∞)
    (hl : Tendsto (fun g:ℕ => ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) :
    Tendsto (fun g => generalPlanarTypeWeight P k (primitiveSaddleX g (n g)))
      atTop (𝓝 (generalPlanarDensityTypeWeight P l k)) := by
  exact (general_planar_type_weight_continuous P k).continuousAt.tendsto.comp
    (primitive_saddle_tendsto_density_fast n hn l hl)

theorem general_planar_total_weight_tendsto_density (P : PsiTheory)
    (n : ℕ → ℕ) (hn : Tendsto (fun g:ℕ => (n g:ℝ)/Real.sqrt g) atTop atTop)
    (l : ℝ≥0∞)
    (hl : Tendsto (fun g:ℕ => ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) :
    Tendsto (fun g => generalPlanarTotalWeight P (primitiveSaddleX g (n g)))
      atTop (𝓝 (∑' k : ℕ,generalPlanarDensityTypeWeight P l k)) := by
  apply (general_planar_total_weight_continuousOn P _ (planar_density_saddle_mem l)).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨primitive_saddle_tendsto_density_fast n hn l hl,?_⟩)
  filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
  exact primitive_saddle_mem_closed g (n g) hg

/-- The finite measure of actual planar cusp types, with no mass on types
    zero and one, completed also at zero and infinite cusp density. -/
def generalPlanarDensityTypeMeasure (P : PsiTheory) (l : ℝ≥0∞) : Measure ℕ :=
  Measure.sum (fun k : ℕ => ENNReal.ofReal (generalPlanarDensityTypeWeight P l k) • Measure.dirac k)

@[simp] lemma general_planar_density_type_measure_singleton (P : PsiTheory) (l : ℝ≥0∞) (k : ℕ) :
    generalPlanarDensityTypeMeasure P l {k} = ENNReal.ofReal (generalPlanarDensityTypeWeight P l k) :=
  Measure.sum_smul_dirac_singleton

lemma general_planar_density_type_measure_univ (P : PsiTheory) (l : ℝ≥0∞) :
    generalPlanarDensityTypeMeasure P l univ =
      ENNReal.ofReal (∑' k : ℕ,generalPlanarDensityTypeWeight P l k) := by
  simp only [generalPlanarDensityTypeMeasure,Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply,Measure.dirac_apply_of_mem (mem_univ _),smul_eq_mul,mul_one]
  exact (ENNReal.ofReal_tsum_of_nonneg (general_planar_density_type_weight_nonneg P l)
    (general_planar_density_type_weight_summable P l)).symm

instance (P : PsiTheory) (l : ℝ≥0∞) : IsFiniteMeasure (generalPlanarDensityTypeMeasure P l) := by
  constructor
  rw [general_planar_density_type_measure_univ]
  exact ENNReal.ofReal_lt_top

@[simp] lemma general_planar_density_type_measure_zero (P : PsiTheory) :
    generalPlanarDensityTypeMeasure P 0 = Measure.dirac 2 := by
  apply Measure.ext_of_singleton
  intro k
  rw [general_planar_density_type_measure_singleton,general_planar_density_type_weight_zero]
  by_cases hk : k=2 <;> simp [hk,Measure.dirac_apply']

/-- The genuine marked intensity on scaled length and original cusp type. -/
def generalPlanarDensityIntensity (P : PsiTheory) (l : ℝ≥0∞) : Measure (ℝ≥0 × ℕ) :=
  quadraticLengthIntensity.prod (generalPlanarDensityTypeMeasure P l)

instance (P : PsiTheory) (l : ℝ≥0∞) : IsLocallyFiniteMeasure (generalPlanarDensityIntensity P l) := by
  unfold generalPlanarDensityIntensity
  infer_instance

instance (P : PsiTheory) (l : ℝ≥0∞) : Measure.Regular (generalPlanarDensityIntensity P l) := by
  infer_instance

lemma general_planar_density_intensity_rect (P : PsiTheory) (l : ℝ≥0∞)
    (B : Set ℝ≥0) (k : ℕ) :
    generalPlanarDensityIntensity P l (B ×ˢ {k}) =
      quadraticLengthIntensity B * ENNReal.ofReal (generalPlanarDensityTypeWeight P l k) := by
  rw [generalPlanarDensityIntensity,Measure.prod_prod,general_planar_density_type_measure_singleton]

lemma general_planar_density_intensity_all_types (P : PsiTheory) (l : ℝ≥0∞)
    (B : Set ℝ≥0) :
    generalPlanarDensityIntensity P l (B ×ˢ univ) =
      quadraticLengthIntensity B * ENNReal.ofReal (∑' k:ℕ,generalPlanarDensityTypeWeight P l k) := by
  rw [generalPlanarDensityIntensity,Measure.prod_prod,general_planar_density_type_measure_univ]

lemma general_planar_density_intensity_Iic (P : PsiTheory) (l : ℝ≥0∞) (b : ℝ≥0) (k : ℕ) :
    generalPlanarDensityIntensity P l (Iic b ×ˢ {k}) =
      ENNReal.ofReal ((b:ℝ)^2 * generalPlanarDensityTypeWeight P l k) := by
  rw [general_planar_density_intensity_rect,quadraticLengthIntensity_Iic,
    ←ENNReal.ofReal_mul (sq_nonneg _)]

lemma general_planar_density_intensity_Ioc (P : PsiTheory) (l : ℝ≥0∞) (a b : ℝ≥0) (k : ℕ) :
    generalPlanarDensityIntensity P l (Ioc a b ×ˢ {k}) =
      ENNReal.ofReal (((b:ℝ)^2-(a:ℝ)^2) * generalPlanarDensityTypeWeight P l k) := by
  rw [general_planar_density_intensity_rect,quadraticLengthIntensity_Ioc,
    ←ENNReal.ofReal_mul' (general_planar_density_type_weight_nonneg P l k)]

end WP.RandomGeometry
