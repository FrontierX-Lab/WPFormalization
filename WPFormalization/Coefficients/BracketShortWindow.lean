import WPFormalization.Analysis.SequenceRatioWindow
import WPFormalization.Coefficients.BracketAdjacentStructure
import WPFormalization.Statements.BracketDifferences
/-! Actual bracket adjacent ratios in a fixed square-root genus window, using the proved C.8 differences. -/
set_option autoImplicit false
noncomputable section
namespace WP.Coefficients
lemma bracketAdjacentRatio_short_window (P:PsiTheory):
    ∃A:ℝ,0 < A∧∀g:ℕ,1 ≤ g →∀k:ℕ,k < 3*g-2 → A*((k:ℝ)+1)^2 ≤ g →
      0 ≤ bracketAdjacentRatio P g k-1∧bracketAdjacentRatio P g k-1 ≤ A*((k:ℝ)+1)/g:=by
  obtain ⟨C,hC,hb⟩:=bracket_differences P
  let A:ℝ:=4*C+1
  have hA:0 < A:=by dsimp[A];positivity
  refine ⟨A,hA,?_⟩
  intro g hg k hk hw
  have hgR:(0:ℝ) < g:=by exact_mod_cast (show 0 < g by omega)
  let u:ℕ→ℝ:=fun j=>bracketB P g j/volumeModel P g 1
  have hzero:u 0=1:=(hb g hg).1
  have hdiff:∀j:ℕ,j < 3*g-2 →0 ≤ u j-u (j+1)∧u j-u (j+1) ≤ (C/g)*((j:ℝ)+1):=by
    intro j hj
    have H:=(hb g hg).2 j hj
    refine ⟨H.1,?_⟩
    convert H.2 using 1 <;>ring
  have hww:(C/g)*((k:ℝ)+1)*((k:ℝ)+2) ≤ 1:=by
    have hCA:2*C ≤ A:=by dsimp[A];linarith only[hC]
    have H1:=mul_le_mul_of_nonneg_left
      (show (k:ℝ)+2 ≤ 2*((k:ℝ)+1) by linarith only[show (0:ℝ) ≤ (k:ℝ) from Nat.cast_nonneg k])
      (mul_nonneg hC.le (by positivity:(0:ℝ) ≤ (k:ℝ)+1))
    have H2:=mul_le_mul_of_nonneg_right hCA (sq_nonneg ((k:ℝ)+1))
    have H:C*((k:ℝ)+1)*((k:ℝ)+2) ≤ (g:ℝ):=by nlinarith only[H1,H2,hw]
    have hd:C*((k:ℝ)+1)*((k:ℝ)+2)/g ≤ 1:=(div_le_one hgR).mpr H
    convert hd using 1 <;>ring
  have H:=Analysis.sequence_adjacent_ratio_short_window u (C/g) (3*g-2) k hzero hdiff hk hww
  have hV:volumeModel P g 1≠0:=by
    have hpos:=bracketB_pos_admissible P g 0 hg (by omega)
    have he:volumeModel P g 1=bracketB P g 0:=by simp[volumeModel,bracketB]
    rw[he]
    exact hpos.ne'
  have hu:u k/u (k+1)=bracketAdjacentRatio P g k:=by
    dsimp[u,bracketAdjacentRatio]
    exact div_div_div_cancel_right₀ hV _ _
  rw[hu] at H
  refine ⟨H.1,H.2.trans ?_⟩
  have hCA:2*C ≤ A:=by dsimp[A];linarith only[hC]
  have hmul:=mul_le_mul_of_nonneg_right hCA (div_nonneg (by positivity:0 ≤ (k:ℝ)+1) hgR.le)
  convert hmul using 1 <;>ring
end WP.Coefficients
