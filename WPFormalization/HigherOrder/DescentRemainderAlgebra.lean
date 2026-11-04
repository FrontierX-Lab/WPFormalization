import WPFormalization.HigherOrder.ScalarRemainderPairing
import WPFormalization.HigherOrder.ScalarScaledRemainders
/-! Actual one-marking descent after cross multiplication. Both the genuine scalar recurrence and its canonical formal identity are used. The positive actual cusp denominator leaves a linear sum of single remainders; no product of unknown errors appears. -/
noncomputable section
namespace WP.HigherOrder
lemma cross_product_remainder_bound (x y u v : ℝ) (f g a b : Series)
    (hactual : x * y = u * v) (hformal : f * g = a * b) (hy : 1 / 2 ≤ y)
    (L : ℕ) (t : ℝ) :
    |x - truncationValue f L t| ≤ 2 *
      (|u - truncationValue a L t| * |v| +
        ∑ i ∈ Finset.range L, |PowerSeries.coeff i a| * |t| ^ i *
          |v - truncationValue b (L - i) t| +
        ∑ i ∈ Finset.range L, |PowerSeries.coeff i f| * |t| ^ i *
          |y - truncationValue g (L - i) t|) := by
  have hprod := exact_product_remainder_identity x y f g L t
  rw [hactual, hformal] at hprod
  have hpair := exact_product_remainder_norm_le u v a b L t
  simp only [Real.norm_eq_abs] at hpair
  have heq : (x - truncationValue f L t) * y =
      (u * v - truncationValue (a * b) L t) -
        ∑ i ∈ Finset.range L, PowerSeries.coeff i f * t ^ i *
          (y - truncationValue g (L - i) t) := by linarith only [hprod]
  have hys : 1 / 2 ≤ |y| := by rw [abs_of_nonneg (by linarith)]; exact hy
  have hlower : |x - truncationValue f L t| ≤ 2 * |(x - truncationValue f L t) * y| := by
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hys (abs_nonneg (x - truncationValue f L t))]
  apply hlower.trans
  rw [heq]
  have hsum := Finset.abs_sum_le_sum_abs
    (fun i : ℕ => PowerSeries.coeff i f * t ^ i * (y - truncationValue g (L - i) t)) (Finset.range L)
  have hnorm := (abs_sub (u * v - truncationValue (a * b) L t)
    (∑ i ∈ Finset.range L, PowerSeries.coeff i f * t ^ i * (y - truncationValue g (L - i) t))).trans
    (add_le_add hpair hsum)
  simp only [abs_mul, abs_pow] at hnorm
  exact mul_le_mul_of_nonneg_left hnorm (by norm_num)

lemma actual_genus_one_cross_remainder_bound (P : PsiTheory) (g : ℕ) (hg : 2 ≤ g)
    (Y : ℝ) (hY : Y ∈ Set.Icc (0 : ℝ) y₀)
    (hc : 1 / 2 ≤ cuspCorrection P g 1 Y) (L : ℕ) (t : ℝ) :
    |genusCorrection P g 1 Y - truncationValue (formalGenus P Y 1) L t| ≤ 2 *
      (|genusCorrection P g 2 Y - truncationValue (complexityShift (-1) (formalGenus P Y 2)) L t| *
          |cuspCorrection P (g - 1) 3 Y| +
        ∑ i ∈ Finset.range L, |PowerSeries.coeff i (complexityShift (-1) (formalGenus P Y 2))| * |t| ^ i *
          |cuspCorrection P (g - 1) 3 Y - truncationValue (formalCusp P Y 3) (L - i) t| +
        ∑ i ∈ Finset.range L, |PowerSeries.coeff i (formalGenus P Y 1)| * |t| ^ i *
          |cuspCorrection P g 1 Y - truncationValue (formalCusp P Y 1) (L - i) t|) := by
  have hcy : cuspCorrection P g 1 Y ≠ 0 := by linarith
  have hactual : genusCorrection P g 1 Y * cuspCorrection P g 1 Y =
      genusCorrection P g 2 Y * cuspCorrection P (g - 1) 3 Y := by
    rw [actual_genus_one_descent P g hg Y hY]
    field_simp
  have hformal : formalGenus P Y 1 * formalCusp P Y 1 =
      complexityShift (-1) (formalGenus P Y 2) * formalCusp P Y 3 := by
    rw [formalGenus_one_descent_product]
    have he := PowerSeries.inv_mul_cancel (formalCusp P Y 1) (by simp)
    calc
      _ = (complexityShift (-1) (formalGenus P Y 2) * formalCusp P Y 3) *
          ((formalCusp P Y 1)⁻¹ * formalCusp P Y 1) := by ring
      _ = _ := by rw [he, mul_one]
  exact cross_product_remainder_bound _ _ _ _ _ _ _ _ hactual hformal hc L t
end WP.HigherOrder
