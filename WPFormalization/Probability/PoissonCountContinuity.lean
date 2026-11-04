import WPFormalization.Probability.LawConvergenceBadEvent
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

noncomputable section
namespace WP.Probability
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

lemma product_poisson_real_singleton {d:ℕ} (r : Fin d → ℝ≥0) (z : Fin d → ℕ) :
    (productPoissonMeasure r).real {z} =
      ∏ i:Fin d,Real.exp (-(r i:ℝ))*(r i:ℝ)^(z i)/(z i).factorial := by
  simp only [productPoissonMeasure,Measure.real,Measure.pi_singleton,ENNReal.toReal_prod,
    poissonMeasure_singleton]
  apply Finset.prod_congr rfl
  intro i hi
  exact ENNReal.toReal_ofReal (by positivity)

lemma probability_singleton_masses_summable {α:Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ] :
    Summable (fun x:α => μ.real {x}) := by
  apply ENNReal.summable_toReal
  have he := Measure.tsum_indicator_apply_singleton μ univ MeasurableSet.univ
  simpa only [indicator_univ] using he.trans_ne (measure_ne_top μ univ)

lemma product_poisson_mass_le_majorant {d:ℕ} (r : Fin d → ℝ≥0)
    (M:ℝ≥0) (hM:0<M) (hr:∀i,r i≤M) (z:Fin d→ℕ) :
    (productPoissonMeasure r).real {z} ≤
      Real.exp ((d:ℝ)*M)*(productPoissonMeasure (fun _:Fin d => M)).real {z} := by
  rw [product_poisson_real_singleton,product_poisson_real_singleton]
  have hcoord (i:Fin d) :
      Real.exp (-(r i:ℝ))*(r i:ℝ)^(z i)/(z i).factorial ≤
        Real.exp (M:ℝ)*(Real.exp (-(M:ℝ))*(M:ℝ)^(z i)/(z i).factorial) := by
    have he : Real.exp (M:ℝ)*Real.exp (-(M:ℝ)) = 1 := by rw [←Real.exp_add];simp
    calc
      _ ≤ 1*(M:ℝ)^(z i)/(z i).factorial := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact mul_le_mul (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (r i).coe_nonneg))
          (pow_le_pow_left₀ (r i).coe_nonneg (by exact_mod_cast hr i) _)
          (pow_nonneg (r i).coe_nonneg _) (by norm_num)
      _ = _ := by
        calc
          _ = (Real.exp (M:ℝ)*Real.exp (-(M:ℝ)))*(M:ℝ)^(z i)/(z i).factorial := by rw [he]
          _ = _ := by ring
  have hp := Finset.prod_le_prod₀ (s:=Finset.univ) (fun i _ => by positivity) (fun i _ => hcoord i)
  have he : (∏i:Fin d,Real.exp (M:ℝ)) = Real.exp ((d:ℝ)*M) := by
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.exp_nat_mul]
  simpa only [Finset.prod_mul_distrib,he] using hp

theorem product_poisson_law_tendsto {d:ℕ} (r : ℕ → Fin d → ℝ≥0)
    (r0 : Fin d → ℝ≥0) (hr : ∀i,Tendsto (fun j => r j i) atTop (𝓝 (r0 i))) :
    LawConverges (fun j => productPoissonMeasure (r j)) (fun _ z=>z)
      (productPoissonMeasure r0) (fun z=>z) := by
  intro f
  let M : ℝ≥0 := 1+∑i:Fin d,r0 i
  have hM : 0<M := by dsimp [M];positivity
  have hM0 (i:Fin d) : r0 i < M := by
    have hi : r0 i ≤ ∑k:Fin d,r0 k := Finset.single_le_sum (fun k _ => zero_le) (Finset.mem_univ i)
    dsimp [M]
    exact hi.trans_lt (lt_add_of_pos_left _ (by norm_num))
  have hevent : ∀ᶠ j in atTop,∀i,r j i≤M := by
    apply Filter.eventually_all.mpr
    intro i
    exact (hr i).eventually_le_const (hM0 i)
  let μM := productPoissonMeasure (fun _:Fin d => M)
  let bound : (Fin d→ℕ) → ℝ := fun z =>
    (Real.exp ((d:ℝ)*M)*‖f‖)*μM.real {z}
  have hs : Summable bound :=
    (probability_singleton_masses_summable μM).mul_left _
  have hterm (z:Fin d→ℕ) :
      Tendsto (fun j => (productPoissonMeasure (r j)).real {z}*f z)
        atTop (𝓝 ((productPoissonMeasure r0).real {z}*f z)) := by
    simp only [product_poisson_real_singleton]
    apply Tendsto.mul_const
    apply tendsto_finsetProd Finset.univ
    intro i hi
    have hrreal : Tendsto (fun j => (r j i:ℝ)) atTop (𝓝 (r0 i:ℝ)) := NNReal.continuous_coe.continuousAt.tendsto.comp (hr i)
    exact ((Real.continuous_exp.continuousAt.tendsto.comp hrreal.neg).mul
      (hrreal.pow (z i))).div_const _
  have hb : ∀ᶠ j in atTop,∀z:Fin d→ℕ,
      ‖(productPoissonMeasure (r j)).real {z}*f z‖ ≤ bound z := by
    filter_upwards [hevent] with j hj z
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (measureReal_nonneg)]
    have ha := product_poisson_mass_le_majorant (r j) M hM hj z
    calc
      _ ≤ (Real.exp ((d:ℝ)*M)*μM.real {z})*‖f‖ :=
        mul_le_mul ha (f.norm_coe_le_norm z) (norm_nonneg _) (by positivity)
      _ = bound z := by dsimp [bound];ring
  have ht := tendsto_tsum_of_dominated_convergence hs hterm hb
  have hIntegral (p:Fin d→ℝ≥0) : (∫z,f z ∂productPoissonMeasure p) =
      ∑' z:Fin d→ℕ,(productPoissonMeasure p).real {z}*f z := by
    simpa only [id_eq,smul_eq_mul] using integral_countable
      (boundedContinuousFunction_integrable_comp (productPoissonMeasure p) id measurable_id.aemeasurable f)
  simpa only [hIntegral] using ht

end WP.Probability
