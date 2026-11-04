import WPFormalization.Analysis.PositiveProductCoefficients
import WPFormalization.Analysis.PositiveProducts
import WPFormalization.Analysis.WeightCoefficients
import WPFormalization.Analysis.KernelZeros
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma positive_product_multipliable (a : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (hSum : Summable (fun i : ℕ => (a i)⁻¹)) (z : ℂ) :
    Multipliable (fun i : ℕ => 1-z/(a i : ℂ)) := by
  have hN : Summable (fun i : ℕ => ‖-z/(a i : ℂ)‖) := by
    have he : (fun i : ℕ => ‖-z/(a i : ℂ)‖) = fun i => ‖z‖*(a i)⁻¹ := by
      funext i
      rw [norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (ha i)]
      ring
    rw [he]
    exact hSum.mul_left ‖z‖
  convert multipliable_one_add_of_summable hN using 1
  funext i
  ring
end WP.Analysis
namespace WP
open MeasureTheory Filter Set Complex
open scoped Topology
lemma weight_nonneg (Y : ℝ) (hY : Y ∈ Icc 0 y₀) (n : ℕ) : 0 ≤ weight Y n := by
  by_cases he : Y=y₀
  · subst Y
    simp only [weight,critical_kernels.2]
    split_ifs <;> norm_num
  · have hYi : Y∈Ico 0 y₀ := ⟨hY.1,lt_of_le_of_ne hY.2 he⟩
    obtain ⟨q,hMono,hPos,hFirst,hAll,hSimple,hProd⟩ := kernel_zeros.2.2.2.2.2 Y hYi
    have hr := r_pos Y hYi
    have hrc : (r Y : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
    let A (j : ℕ) : ℝ := q (j+1)/r Y
    have hAPos (j : ℕ) : 0 < A j := div_pos (hPos (j+1)) hr
    have hALower (j : ℕ) : A 0 ≤ A j :=
      div_le_div_of_nonneg_right (hMono.monotone (by omega : 0+1≤j+1)) hr.le
    have hQSum := Analysis.reciprocal_summable_of_positive_product q hPos (fun z => K Y z/(a Y : ℂ)) hProd
    have hASum : Summable (fun j : ℕ => (A j)⁻¹) := by
      convert (hQSum.comp_injective Nat.succ_injective).mul_left (r Y) using 1
      funext j
      simp only [A,inv_div,Function.comp_apply,Nat.succ_eq_add_one]
      ring
    have hBProd (w : ℂ) (hw : ‖w‖ < 1) :
        HasProd (fun j : ℕ => 1-w/(A j : ℂ)) (Analysis.deflatedBarK Y w) := by
      let F (j : ℕ) : ℂ := 1-(r Y : ℂ)*w/(q j : ℂ)
      have hTailEq (j : ℕ) : F (j+1)=1-w/(A j : ℂ) := by
        dsimp [F,A]
        push_cast
        field_simp
        <;> ring
      have hMP := Analysis.positive_product_multipliable A hAPos hASum w
      have hTail : HasProd (fun j : ℕ => F (j+1)) (∏' j : ℕ, (1-w/(A j : ℂ))) := by
        convert hMP.hasProd using 1
        funext j
        exact hTailEq j
      have hFull := HasProd.prod_range_mul (f := F) (k := 1) hTail
      simp only [Finset.prod_range_one] at hFull
      have hF0 : F 0=1-w := by
        dsimp [F]
        rw [hFirst]
        field_simp
      rw [hF0] at hFull
      have hOriginal : HasProd F (barK Y w) := by
        simpa only [F,barK,if_neg he] using hProd ((r Y : ℂ)*w)
      have hEq := hFull.unique hOriginal
      have hw1 : 1-w≠0 := by
        intro hzero
        have hwEq : w=1 := (sub_eq_zero.mp hzero).symm
        rw [hwEq,norm_one] at hw
        exact lt_irrefl _ hw
      have hBTail : (∏' j : ℕ, (1-w/(A j : ℂ)))=Analysis.deflatedBarK Y w := by
        apply mul_left_cancel₀ hw1
        exact hEq.trans (Analysis.deflatedBarK_identity Y hY w).symm
      have hLimit := hMP.hasProd
      rw [hBTail] at hLimit
      exact hLimit
    have hCoeff := Analysis.inverse_coeff_nonnegative_of_positive_product (Analysis.deflatedBarK Y)
      (Analysis.deflatedBarK_differentiable Y) (Analysis.deflatedBarK_zero Y hY)
      A (A 0) 1 (hAPos 0) zero_lt_one hALower hASum hBProd n
    rw [←Analysis.weightGenerating_coeff Y hY n]
    exact hCoeff.2
end WP
