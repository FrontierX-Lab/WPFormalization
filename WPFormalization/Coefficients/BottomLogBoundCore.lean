import WPFormalization.Coefficients.OneBoundaryScaleBound
import WPFormalization.Coefficients.UnscaledProbabilityRate
import WPFormalization.Intersection.ProfileMonotone
/-! Actual bracket positivity, monotonicity, and logarithmic comparison with the fixed-radius tilted mass. -/
set_option autoImplicit false
noncomputable section
namespace WP.Coefficients
open Set
lemma bracketB_pos_admissible (P:PsiTheory)(g k:ℕ)(hg:1 ≤ g)(hk:k ≤ 3*g-2):
    0 < bracketB P g k:=by
  have hpos:=normalized_pos_valid_nonempty P g [k] (by simp)
    (by simp only[List.length_singleton];unfold Stable;omega)
    (by simp only[List.sum_singleton,List.length_singleton,dimension];omega) 0 ⟨le_rfl,y₀_pos.le⟩
  rw[bracketB_eq_normalized_zero P g k hg hk]
  exact mul_pos (by positivity) hpos

lemma bracketB_le_volume_one (P:PsiTheory)(g k:ℕ)(hg:1 ≤ g)(hk:k ≤ 3*g-2):
    bracketB P g k ≤ volumeModel P g 1:=by
  have hs:Stable g [k].length:=by simp only[List.length_singleton];unfold Stable;omega
  have H:=normalized_le_all_zero P g [k] hs 0 ⟨le_rfl,y₀_pos.le⟩
  simp only[List.length_singleton,List.replicate_succ,List.replicate_zero] at H
  have he:volumeModel P g 1=bracketB P g 0:=by simp[volumeModel,bracketB]
  rw[he,bracketB_eq_normalized_zero P g k hg hk,bracketB_eq_normalized_zero P g 0 hg (by omega)]
  exact mul_le_mul_of_nonneg_left H (by positivity)

lemma log_volume_one_over_bracket_nonneg (P:PsiTheory)(g k:ℕ)(hg:1 ≤ g)(hk:k ≤ 3*g-2):
    0 ≤ Real.log (volumeModel P g 1/bracketB P g k):=by
  apply Real.log_nonneg
  exact (one_le_div (bracketB_pos_admissible P g k hg hk)).mpr (bracketB_le_volume_one P g k hg hk)

lemma log_volume_one_over_bracket_identity (P:PsiTheory)(g k:ℕ)(hg:1 ≤ g)(hk:k ≤ 3*g-2):
    Real.log (volumeModel P g 1/bracketB P g k)=
      Real.log (volumeModel P g 1/oneBoundaryBracketScale g)-
      Real.log (tiltedKernelMass (r 0) (complexity g 1) (3*g-2-k))-
      Real.log (ratio P g [k] 0):=by
  have hB:=bracketB_pos_admissible P g k hg hk
  have hV:0 < volumeModel P g 1:=(hB.trans_le (bracketB_le_volume_one P g k hg hk))
  have hM:=oneBoundaryBracketModel_pos g k hg
  have hS:=oneBoundaryBracketScale_pos g hg
  have hprob:=tiltedKernelMass_pos (r 0) (r_pos 0 ⟨le_rfl,y₀_pos⟩) le_rfl
    (complexity g 1) (3*g-2-k) (by unfold complexity;omega)
  rw[←bracketB_div_oneBoundaryBracketModel P g k hg hk]
  rw[Real.log_div hV.ne' hB.ne',Real.log_div hV.ne' hS.ne',Real.log_div hB.ne' hM.ne',
    oneBoundaryBracketModel_probability g k hg hk,Real.log_mul hS.ne' hprob.ne']
  ring

lemma bottom_log_bound_preliminary (P:PsiTheory):
    ∃A B D E:ℝ,0 < A∧0 < B∧0 < D∧0 ≤ E∧∃G:ℕ,∀g:ℕ,G ≤ g →1 ≤ g →∀k:ℕ,k ≤ 3*g-2 →
      Real.log (volumeModel P g 1/bracketB P g k) ≤ E+
        A*Real.log ((complexity g 1:ℝ)+1)+D*(Real.log ((complexity g 1:ℝ)+1))^2+
        B*(complexity g 1:ℝ)*(3/2-((3*g-2-k:ℕ):ℝ)/complexity g 1)^2:=by
  obtain ⟨A,B,hA,hB,hprob⟩:=tiltedKernelMass_fixed_radius_log_bound
  obtain ⟨D,hD,harm⟩:=harmonic_comparison P 1 (by norm_num)
  obtain ⟨V,hV,G,hvol⟩:=volume_one_le_bracket_scale P
  refine ⟨A,B,D,|Real.log V|,hA,hB,hD,abs_nonneg _,G,?_⟩
  intro g hg hg1 k hk
  have hs:Stable g 1:=by unfold Stable;omega
  have hm:2*(3*g-2-k) ≤ 3*complexity g 1:=by unfold complexity;omega
  have hp:=hprob (complexity g 1) (3*g-2-k) (by unfold complexity;omega) hm
  have hd:=harm g [k] rfl hs (by simp only[List.sum_singleton,dimension];omega) 0 ⟨le_rfl,y₀_pos.le⟩
  have hscale:=oneBoundaryBracketScale_pos g hg1
  have hbracket:=bracketB_pos_admissible P g k hg1 hk
  have hvolpos:0 < volumeModel P g 1:=hbracket.trans_le (bracketB_le_volume_one P g k hg1 hk)
  have hlog:Real.log (volumeModel P g 1/oneBoundaryBracketScale g) ≤ |Real.log V|:=by
    apply (Real.log_le_log (div_pos hvolpos hscale) ((div_le_iff₀ hscale).mpr (hvol g hg hg1))).trans
    exact le_abs_self _
  rw[log_volume_one_over_bracket_identity P g k hg1 hk]
  linarith only[hp,hd.1,hlog]
end WP.Coefficients
