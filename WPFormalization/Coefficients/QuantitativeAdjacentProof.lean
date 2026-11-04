import WPFormalization.Coefficients.AdjacentSmallDegreeError
import WPFormalization.Coefficients.AdjacentBulkActualRates
/-! The complete original quantitative all-degree adjacent theorem, combining the proved actual small and bulk sectors. Both original rate exponents and their quantifier dependence are retained. -/
set_option autoImplicit false
noncomputable section
namespace WP
open Coefficients
lemma quantitative_adjacent_proof (P : PsiTheory) :
    (∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ k : ℕ, k < 3*g-2 →
      adjacentError P g k ≤ C*Real.rpow g (-1/8 : ℝ)) ∧
    (∀ ε ∈ Set.Ioo (0 : ℝ) 3, ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀,
      ∀ k : ℕ, ε*g ≤ k → k < 3*g-2 → adjacentError P g k ≤ C*Real.rpow g (-1/4 : ℝ)) :=by
  constructor
  · obtain ⟨Cs,hCs,Gs,hsmall⟩:=adjacentError_small_degree_rate P
    obtain ⟨Cb,hCb,Gb,hbulk⟩:=adjacentError_three_quarter_bulk_rate P
    refine ⟨Cs+Cb,add_pos hCs hCb,max Gs Gb,?_⟩
    intro g hg k hk
    have hs:Gs ≤ g:=(le_max_left _ _).trans hg
    have hb:Gb ≤ g:=(le_max_right _ _).trans hg
    have hp:0 ≤ (g:ℝ)^(-1/8:ℝ):=Real.rpow_nonneg (Nat.cast_nonneg g) _
    by_cases hsmallk:(k:ℝ) ≤ (g:ℝ)^(3/4:ℝ)
    · exact (hsmall g hs k hk hsmallk).trans (mul_le_mul_of_nonneg_right (by linarith only[hCb]) hp)
    · exact (hbulk g hb k (le_of_not_ge hsmallk) hk).trans
        (mul_le_mul_of_nonneg_right (by linarith only[hCs]) hp)
  · intro ε hε
    exact adjacentError_positive_density_rate P ε hε.1
end WP
