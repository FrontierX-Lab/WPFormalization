import WPFormalization.Analysis.FiniteExpGevreyTwo
import WPFormalization.HigherOrder.LogMarkedRegularity
noncomputable section
namespace WP.Analysis
open PowerSeries Set
lemma gevreyTwo_real_truncation_abs_bound (a : ℕ → ℝ) (C B : ℝ)
    (hC : 0 ≤ C) (hB : 0 < B) (ha : ∀ n, |a n| ≤ C*B^n*(n.factorial:ℝ)^2)
    (K : ℕ) (h : ℝ) (hh : 0 < h) (hw : 2*B*((K:ℝ)+1)^2 ≤ h) :
    |∑ j ∈ Finset.range (K+1), a j/h^j| ≤ 2*C := by
  let f : WP.HigherOrder.Series := PowerSeries.mk a
  have hf : ∀ n, |PowerSeries.coeff n f| ≤ C*B^n*(n.factorial:ℝ)^2 := by
    simpa only [f,PowerSeries.coeff_mk] using ha
  have hz : ‖((1/h:ℝ):ℂ)‖ ≤ 1/(2*B*((K:ℝ)+1)^2) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh)]
    exact one_div_le_one_div_of_le (by positivity) hw
  have hb := truncatedSeriesPolynomial_gevreyTwo_norm_bound f C B hC hB hf K ((1/h:ℝ):ℂ) hz
  rw [truncatedSeriesPolynomial_real,Complex.norm_real,Real.norm_eq_abs] at hb
  simpa only [f,PowerSeries.coeff_mk,one_div_pow,div_eq_mul_inv,one_mul,inv_pow] using hb
end WP.Analysis
namespace WP.HigherOrder
open Set PowerSeries
lemma logarithmicMarkedTruncation_endpoint_variation (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ K : ℕ, ∀ h : ℝ, 0 < h →
      2*B*((K:ℝ)+1)^2 ≤ h → ∀ Y ∈ Icc (0:ℝ) y₀,
      |(∑ j ∈ Finset.range (K+1), logarithmicMarkedCoefficient P p j Y/h^j)-
        ∑ j ∈ Finset.range (K+1), endpointLogCoefficient p j/h^j| ≤ C*(y₀-Y) := by
  obtain ⟨C,B,hC,hB,hcont,hderiv,hcoef,hlip⟩ := logarithmicMarkedCoefficient_real_gevrey_regularity P p hp
  refine ⟨2*C,B,by positivity,hB,?_⟩
  intro K h hh hw Y hY
  have hδ : 0 ≤ y₀-Y := sub_nonneg.mpr hY.2
  have ha (n : ℕ) : |logarithmicMarkedCoefficient P p n Y-endpointLogCoefficient p n| ≤
      (C*(y₀-Y))*B^n*(n.factorial:ℝ)^2 := by
    by_cases hn : n=0
    · subst n
      simp only [logarithmicMarkedCoefficient,ite_true,endpointLogCoefficient_zero,sub_self,abs_zero]
      positivity
    · have he := hlip n (by omega) Y hY
      convert he using 1 <;> ring
  have hb := Analysis.gevreyTwo_real_truncation_abs_bound
    (fun n => logarithmicMarkedCoefficient P p n Y-endpointLogCoefficient p n)
    (C*(y₀-Y)) B (mul_nonneg hC.le (sub_nonneg.mpr hY.2)) hB ha K h hh hw
  simpa only [sub_div,Finset.sum_sub_distrib,mul_assoc] using hb
end WP.HigherOrder
