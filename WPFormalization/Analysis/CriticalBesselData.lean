import WPFormalization.Analysis.BesselSignBounds
import WPFormalization.Analysis.RealBessel
import WPFormalization.Analysis.PositiveRootInfimum
/-! The actual first Bessel zero and its simplicity in the X coordinate.
The proofs use actual factorial series, alternating bounds and the positive-root infimum. -/
noncomputable section
namespace WP
open Filter
open scoped Topology
lemma besselJ0_eq_derivX_square (t : ℂ) : besselJ₀ t = deriv X (t^2/4) := by
  have hf : Differentiable ℂ (deriv X) := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_X_differentiable 1
  rw [← Complex.taylorSeries_eq_of_entire' (c := 0) (z := t^2/4) hf,besselJ₀]
  apply tsum_congr
  intro n
  rw [← iteratedDeriv_succ',iteratedDeriv_X_succ_zero]
  simp only [sub_zero]
  have hp : (t/2)^(2*n) = (t^2/4)^n := by
    rw [pow_mul]
    congr 1
    ring
  rw [hp]
  ring
lemma derivX_positive_zero_exists : ∃ y : ℝ, 0 < y ∧ deriv X y = 0 := by
  have hc : Continuous a := by
    unfold a
    have hf : Continuous (deriv X) := by
      simpa only [iteratedDeriv_one] using (iteratedDeriv_X_differentiable 1).continuous
    exact Complex.continuous_re.comp (hf.comp Complex.continuous_ofReal)
  have ha0 : (0 : ℝ) < a 0 := by rw [a_zero]; norm_num
  obtain ⟨y,hy,hay⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 3/2) hc.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (a (3/2)) (a 0) from ⟨a_three_halves_neg.le,ha0.le⟩)
  have hy0 : y ≠ 0 := by
    intro he
    rw [he,a_zero] at hay
    norm_num at hay
  refine ⟨y,lt_of_le_of_ne hy.1 (Ne.symm hy0),?_⟩
  rw [derivX_ofReal,hay,Complex.ofReal_zero]
lemma y₀_pos : 0 < y₀ := by
  have hc : Continuous (fun y : ℝ => deriv X y) := by
    have hf : Continuous (deriv X) := by
      simpa only [iteratedDeriv_one] using (iteratedDeriv_X_differentiable 1).continuous
    exact hf.comp Complex.continuous_ofReal
  have h0 : deriv X (0 : ℂ) ≠ 0 := by
    have h : deriv X (0 : ℂ) = 1 := by simpa using iteratedDeriv_X_succ_zero 0
    rw [h]
    exact one_ne_zero
  exact Analysis.positive_zero_sInf_pos (fun y : ℝ => deriv X y) hc.continuousAt h0 derivX_positive_zero_exists
lemma derivX_y₀_zero : deriv X (y₀ : ℂ) = 0 := by
  let S := {y : ℝ | 0 < y ∧ deriv X y = 0}
  have hs : S.Nonempty := derivX_positive_zero_exists
  have hb : BddBelow S := ⟨0,fun y hy => hy.1.le⟩
  have hc : Continuous (fun y : ℝ => deriv X y) := by
    have hf : Continuous (deriv X) := by
      simpa only [iteratedDeriv_one] using (iteratedDeriv_X_differentiable 1).continuous
    exact hf.comp Complex.continuous_ofReal
  have hclosed : IsClosed {y : ℝ | deriv X y = 0} := isClosed_eq hc continuous_const
  have hsubset : closure S ⊆ {y : ℝ | deriv X y = 0} := closure_minimal (fun y hy => hy.2) hclosed
  exact hsubset (csInf_mem_closure hs hb)
lemma a_y₀_zero : a y₀ = 0 := by simp only [a,derivX_y₀_zero,Complex.zero_re]
lemma iteratedDeriv_two_X_y₀_neg : (iteratedDeriv 2 X (y₀ : ℂ)).re < 0 := by
  apply second_X_neg_interval
  exact ⟨y₀_pos.le,by linarith [y₀_lt_three_halves]⟩
lemma iteratedDeriv_two_X_y₀_ne_zero : iteratedDeriv 2 X (y₀ : ℂ) ≠ 0 := by
  intro h
  have hn := iteratedDeriv_two_X_y₀_neg
  rw [h,Complex.zero_re] at hn
  exact lt_irrefl _ hn
end WP
