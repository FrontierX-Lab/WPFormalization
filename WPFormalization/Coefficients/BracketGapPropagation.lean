import WPFormalization.Coefficients.BracketAdjacentStructure
import WPFormalization.Coefficients.AdjacentDiscreteSecants
import WPFormalization.Analysis.WeightedGapPropagation
/-! The original C.7 adjacent mixed-intersection monotonicity propagates an actual bracket gap through a short forward block. -/
set_option autoImplicit false
noncomputable section
namespace WP.Coefficients
open Set
lemma bracketAdjacentRatio_gap_propagates (P:PsiTheory)(g k j:ℕ)(r:ℝ)
    (hg:1 ≤ g)(hj:j < 3*g-2)(hkj:k ≤ j)(hr:0 ≤ r)(hr1:r ≤ 1)
    (hstep:(j:ℝ)-(k:ℝ) ≤ r*((k:ℝ)+1)/12)
    (hgap:1+r ≤ bracketAdjacentRatio P g k):
    1+r/2 ≤ bracketAdjacentRatio P g j:=by
  have hk:k < 3*g-2:=by omega
  have hpos:=bracketAdjacentRatio_pos P g j hg hj
  have hw:=oneBoundaryRatioWeight_pos g k hk
  have hwj:=oneBoundaryRatioWeight_pos g j hj
  have hmono:bracketAdjacentRatio P g k*oneBoundaryRatioWeight g k ≤
      bracketAdjacentRatio P g j*oneBoundaryRatioWeight g j:=by
    have H:=(mixedJ_ratio_monotone P g hg) hk hj hkj
    rw[bracketAdjacentRatio_eq_mixedJ P g k hg hk,bracketAdjacentRatio_eq_mixedJ P g j hg hj]
    have he1:Real.pi^2*(mixedJ P g k/mixedJ P g (k+1))/(2*oneBoundaryRatioWeight g k)*
        oneBoundaryRatioWeight g k=(Real.pi^2/2)*(mixedJ P g k/mixedJ P g (k+1)):=by field_simp <;>ring
    have he2:Real.pi^2*(mixedJ P g j/mixedJ P g (j+1))/(2*oneBoundaryRatioWeight g j)*
        oneBoundaryRatioWeight g j=(Real.pi^2/2)*(mixedJ P g j/mixedJ P g (j+1)):=by field_simp <;>ring
    rw[he1,he2]
    exact mul_le_mul_of_nonneg_left H (by positivity)
  have hfactor:2*(j:ℝ)+3 ≤ (1+r/6)*(2*(k:ℝ)+3):=by
    have H:=mul_nonneg hr (show (0:ℝ) ≤ (k:ℝ)+2 by positivity)
    nlinarith only[hstep,H]
  have hmk:((3*g-2-j:ℕ):ℝ) ≤ ((3*g-2-k:ℕ):ℝ):=by
    exact_mod_cast (show 3*g-2-j ≤ 3*g-2-k by omega)
  have hweight:oneBoundaryRatioWeight g j ≤ (1+r/6)*oneBoundaryRatioWeight g k:=by
    unfold oneBoundaryRatioWeight
    calc
      _ ≤ (2*(j:ℝ)+3)*((3*g-2-k:ℕ):ℝ):=
        mul_le_mul_of_nonneg_left hmk (by positivity)
      _ ≤ ((1+r/6)*(2*(k:ℝ)+3))*((3*g-2-k:ℕ):ℝ):=
        mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg _)
      _ = _:=by ring
  exact Analysis.weighted_ratio_gap_lower _ _ _ _ _ hw hpos.le hr hr1 hgap hmono hweight
end WP.Coefficients
