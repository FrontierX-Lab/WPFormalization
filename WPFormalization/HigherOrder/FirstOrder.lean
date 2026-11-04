import WPFormalization.HigherOrder.Endpoint

/-! First coefficients of the fixed endpoint and marked formal constructions.
The endpoint coefficient is proved from the rational Painleve recurrence,
Bernoulli Gamma factor and finite insertion product. No asymptotic matching or
path-independence assumption occurs in this file. The remaining identification
of `transportCoefficient P p 1` with `transportGamma p` is a distinct obligation.
-/
noncomputable section
namespace WP.HigherOrder
open PowerSeries

/-- First formal exponential coefficient. -/
lemma finiteExp_one (f : Series) : PowerSeries.coeff 1 (finiteExp f) = PowerSeries.coeff 1 f := by
  simp [finiteExp, Finset.sum_range_succ]

lemma finiteLog_one (f : Series) : PowerSeries.coeff 1 (finiteLog f) = PowerSeries.coeff 1 f := by
  simp [finiteLog]

lemma shiftVariable_one (c : ℝ) : PowerSeries.coeff 1 (shiftVariable c) = 1 := by
  simp [shiftVariable]

/-- Finite changes of complexity preserve the first inverse-complexity coefficient. -/
lemma complexityShift_one (c : ℝ) (f : Series) :
    PowerSeries.coeff 1 (complexityShift c f) = PowerSeries.coeff 1 f := by
  unfold complexityShift
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (shiftVariable_constant c))]
  rw [finsum_eq_single _ 1]
  · simp [shiftVariable_one]
  · intro n hn
    rw [PowerSeries.coeff_one_pow, shiftVariable_constant]
    by_cases h0 : n = 0
    · simp [h0]
    · have h : n-1 ≠ 0 := by omega
      simp [zero_pow h]

lemma coeff_one_inv_unit (f : Series) (hf : constantCoeff f = 1) :
    PowerSeries.coeff 1 f⁻¹ = -PowerSeries.coeff 1 f := by
  rw [PowerSeries.coeff_inv]
  have h : Finset.HasAntidiagonal.antidiagonal (1 : ℕ) = {(0,1), (1,0)} := rfl
  rw [h]
  simp [hf, coeff_zero_eq_constantCoeff]

lemma coeff_one_linear_inv (a : ℝ) :
    PowerSeries.coeff 1 ((1+PowerSeries.C a*PowerSeries.X : Series)⁻¹) = -a := by
  rw [coeff_one_inv_unit _ (by simp)]
  simp

lemma endpointZ_one : PowerSeries.coeff 1 endpointZ = -1/8 := by
  norm_num [endpointZ, Finset.sum_range_succ, PowerSeries.coeff_one_mul,
    coeff_zero_eq_constantCoeff]

lemma gammaRatioLog_one : PowerSeries.coeff 1 (gammaRatioLog (3/2)) = 3/8 := by
  norm_num [gammaRatioLog, bernoulliPolynomialValue, Finset.sum_range_succ]

lemma gammaRatioSeries_one : PowerSeries.coeff 1 (gammaRatioSeries (3/2)) = 3/8 := by
  simpa [gammaRatioSeries,finiteExp_one] using gammaRatioLog_one

lemma binomial_one (a : ℝ) : PowerSeries.coeff 1 (binomial a) = a := by
  simp [binomial,PowerSeries.binomialSeries_coeff]

lemma endpointInsertion_one (p : ℕ) :
    PowerSeries.coeff 1 (endpointInsertion p) = (p : ℝ)/2-(p:ℝ)*(p-1)/10 := by
  let f : ℕ → Series := fun i =>
    (1+C (4*(i : ℝ)/5)*PowerSeries.X)*(1+C (i : ℝ)*PowerSeries.X)⁻¹
  have hf₀ : ∀ i, constantCoeff (f i) = 1 := by intro i; simp [f]
  have hf₁ : ∀ i, PowerSeries.coeff 1 (f i) = -(i:ℝ)/5 := by
    intro i
    change PowerSeries.coeff 1 ((1+C (4*(i:ℝ)/5)*PowerSeries.X)*
      (1+C (i:ℝ)*PowerSeries.X)⁻¹) = _
    rw [PowerSeries.coeff_one_mul,coeff_one_linear_inv]
    simp
    ring
  have hp₀ : ∀ p, constantCoeff (∏ i ∈ Finset.range p, f i) = 1 := by
    intro p
    simp [hf₀]
  have hp₁ : ∀ p, PowerSeries.coeff 1 (∏ i ∈ Finset.range p, f i) = -(p:ℝ)*(p-1)/10 := by
    intro p
    induction p with
    | zero => simp
    | succ p ih =>
      rw [Finset.prod_range_succ, PowerSeries.coeff_one_mul, ih, hp₀, hf₀, hf₁]
      push_cast
      ring
  unfold endpointInsertion
  change PowerSeries.coeff 1
    (PowerSeries.rescale (p:ℝ) (binomial (1/2)) * ∏ i ∈ Finset.range p, f i) = _
  rw [PowerSeries.coeff_one_mul, hp₀, hp₁, PowerSeries.coeff_rescale]
  have hr : constantCoeff (PowerSeries.rescale (p:ℝ) (binomial (1/2))) = 1 := by
    rw [← coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale]
    simp [coeff_zero_eq_constantCoeff]
  rw [hr,binomial_one]
  ring

/-- The fixed endpoint normalization yields exactly the paper's constant t_p. -/
lemma endpointLogCoefficient_one (p : ℕ) :
    endpointLogCoefficient p 1 = firstEndpointConstant p := by
  unfold endpointLogCoefficient endpointSeries
  rw [finiteLog_one, complexityShift_one]
  simp only [endpointAtH₀, PowerSeries.coeff_one_mul]
  simp only [map_mul, endpointZ_constant, gammaRatioSeries_constant,
    endpointInsertion_constant, endpointZ_one, gammaRatioSeries_one,
    endpointInsertion_one]
  simp only [constantCoeff_inv, map_add, map_one, map_mul, constantCoeff_C, constantCoeff_X,
    mul_zero, add_zero, inv_one]
  rw [coeff_one_linear_inv]
  unfold firstEndpointConstant
  ring

/-- The canonical first marked coefficient, with its actual transport integrand. -/
lemma markedCoefficient_one (P : PsiTheory) (p : ℕ) (Y : ℝ) :
    markedCoefficient P p 1 Y = firstEndpointConstant p -
      ∫ v in Y..y₀, transportCoefficient P p 1 v/(A v*r v) := by
  simp [markedCoefficient,finiteExp_one,markedLogSeries,
    logarithmicMarkedCoefficient,endpointLogCoefficient_one]

/-- The canonical first marked coefficient has endpoint value t_p. -/
lemma markedCoefficient_one_endpoint (P : PsiTheory) (p : ℕ) :
    markedCoefficient P p 1 y₀ = firstEndpointConstant p := by
  rw [markedCoefficient_one]
  simp

end WP.HigherOrder
