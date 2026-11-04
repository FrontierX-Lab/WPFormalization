import WPFormalization.Coefficients.BottomLogBoundCore
import WPFormalization.Coefficients.BottomLogElementary
/-! Original C.23, with all admissible degrees and the original quadratic/log-squared error. -/
set_option autoImplicit false
noncomputable section
namespace WP
open Coefficients
lemma bottom_log_bound_proof (P : PsiTheory) : ∃ C : ℝ, 0 < C ∧
    ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ k : ℕ, k ≤ 3*g-2 →
      0 ≤ Real.log (volumeModel P g 1/bracketB P g k) ∧
      Real.log (volumeModel P g 1/bracketB P g k) ≤
        C*(Real.log (g+1))^2+C*(k+1 : ℝ)^2/g :=by
  obtain ⟨A,B,D,E,hA,hB,hD,hE,G,hpre⟩:=bottom_log_bound_preliminary P
  obtain ⟨C,hC,habs⟩:=absorb_bottom_log_errors A B D E hA hB hD hE
  refine ⟨C,hC,max G 1,?_⟩
  intro g hg k hk
  have hgG:G ≤ g:=(le_max_left _ _).trans hg
  have hg1:1 ≤ g:=(le_max_right _ _).trans hg
  have hgR:(1:ℝ) ≤ g:=by exact_mod_cast hg1
  have hg0:(0:ℝ) < g:=by linarith only[hgR]
  refine ⟨log_volume_one_over_bracket_nonneg P g k hg1 hk,?_⟩
  have hlog:=genus_log_complexity_bounds g hg1
  have hquad:=one_boundary_saddle_defect_degree_bound g k hg1 hk
  have hL:=mul_le_mul_of_nonneg_left hlog.2.1 hA.le
  have hL2:=mul_le_mul_of_nonneg_left hlog.2.2 hD.le
  have hQ:=mul_le_mul_of_nonneg_left hquad hB.le
  have hp:=hpre g hgG hg1 k hk
  have ht:0 ≤ (k+1:ℝ)^2/g:=div_nonneg (sq_nonneg _) hg0.le
  have ha:=habs ((g:ℝ)+1) ((k+1:ℝ)^2/g) (by linarith only[hgR]) ht
  have hp':Real.log (volumeModel P g 1/bracketB P g k) ≤
      E+2*A*Real.log ((g:ℝ)+1)+4*D*(Real.log ((g:ℝ)+1))^2+B*((k+1:ℝ)^2/g):=by
    nlinarith only[hp,hL,hL2,hQ]
  have hend:=hp'.trans ha
  convert hend using 1 <;>ring
end WP
