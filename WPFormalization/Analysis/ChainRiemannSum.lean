import WPFormalization.Statements.Basic
import Mathlib.Analysis.SumIntegralComparisons

/-! Uniform left Riemann sums for a bounded antitone function.
The error is bounded by the total variation, independently of the number
of summands and the mesh parameter. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Set

lemma chain_antitone_riemann_sum (f : ℝ → ℝ) (hf : AntitoneOn f (Ici 0))
    (h : ℝ) (hh : 0 < h) (n : ℕ) :
    0 ≤ (∑ j ∈ Finset.range n, f ((j : ℝ)/h)) -
      h * ∫ v in (0 : ℝ)..(n : ℝ)/h, f v ∧
    (∑ j ∈ Finset.range n, f ((j : ℝ)/h)) -
      h * ∫ v in (0 : ℝ)..(n : ℝ)/h, f v ≤ f 0-f ((n : ℝ)/h) := by
  let F : ℝ → ℝ := fun v => f (v/h)
  have hF : AntitoneOn F (Icc 0 (0+(n : ℝ))) := by
    intro x hx y hy hxy
    exact hf (div_nonneg hx.1 hh.le) (div_nonneg hy.1 hh.le)
      ((div_le_div_iff_of_pos_right hh).mpr hxy)
  have hu := hF.integral_le_sum
  have hl := hF.sum_le_integral
  have hi : (∫ v in (0 : ℝ)..(n : ℝ), F v) =
      h * ∫ v in (0 : ℝ)..(n : ℝ)/h, f v := by
    simpa only [F,zero_div,smul_eq_mul] using
      (intervalIntegral.integral_comp_div f hh.ne' (a := 0) (b := (n : ℝ)))
  simp only [zero_add,F] at hu hl
  rw [hi] at hu hl
  have hs : (∑ j ∈ Finset.range n, f (((j+1 : ℕ) : ℝ)/h)) =
      (∑ j ∈ Finset.range n, f ((j : ℝ)/h))-f 0+f ((n : ℝ)/h) := by
    have he := Finset.sum_range_sub (fun j : ℕ => f ((j : ℝ)/h)) n
    simp only [Finset.sum_sub_distrib,Nat.cast_zero,zero_div] at he
    linarith
  rw [hs] at hl
  exact ⟨sub_nonneg.mpr hu,by linarith⟩

lemma chain_antitone_riemann_sum_abs (f : ℝ → ℝ) (hf : AntitoneOn f (Ici 0))
    (C : ℝ) (hC : ∀ v : ℝ, 0 ≤ v → f 0-f v ≤ C)
    (h : ℝ) (hh : 0 < h) (n : ℕ) :
    |(∑ j ∈ Finset.range n, f ((j : ℝ)/h)) -
      h * ∫ v in (0 : ℝ)..(n : ℝ)/h, f v| ≤ C := by
  obtain ⟨hp,hb⟩ := chain_antitone_riemann_sum f hf h hh n
  rw [abs_of_nonneg hp]
  exact hb.trans (hC _ (by positivity))

end WP.Analysis
