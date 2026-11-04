import WPFormalization.Coefficients.BracketDifferencesProof
import WPFormalization.Coefficients.OneBoundaryModelComparison
import WPFormalization.Coefficients.UniformSaddleProbability
/-! The original one-boundary bracket model equals a common explicit scale times the actual tilted coefficient mass. -/
set_option autoImplicit false
noncomputable section
namespace WP.Coefficients
open Set

def oneBoundaryBracketModel (g k:ℕ):ℝ:=
  (4:ℝ)^(3*g-2)*model g [k] 0

def oneBoundaryBracketScale (g:ℕ):ℝ:=
  Real.pi^2*Real.Gamma (complexity g 1)*(4*Real.pi^2)^(complexity g 1-1)

lemma oneBoundaryBracketModel_pos (g k:ℕ)(hg:1 ≤ g):0 < oneBoundaryBracketModel g k:=by
  have hs:Stable g [k].length:=by simp only[List.length_singleton];unfold Stable;omega
  exact mul_pos (by positivity) (model_pos g [k] 0 hs ⟨le_rfl,y₀_pos.le⟩)

lemma bracketB_div_oneBoundaryBracketModel (P:PsiTheory)(g k:ℕ)(hg:1 ≤ g)(hk:k ≤ 3*g-2):
    bracketB P g k/oneBoundaryBracketModel g k=ratio P g [k] 0:=by
  rw[bracketB_eq_normalized_zero P g k hg hk]
  unfold oneBoundaryBracketModel ratio
  exact mul_div_mul_left _ _ (by positivity:(4:ℝ)^(3*g-2)≠0)

lemma oneBoundaryBracketModel_probability (g k:ℕ)(hg:1 ≤ g)(hk:k ≤ 3*g-2):
    oneBoundaryBracketModel g k=
      oneBoundaryBracketScale g*tiltedKernelMass (r 0) (complexity g 1) (3*g-2-k):=by
  have hh:1 ≤ complexity g 1:=by unfold complexity;omega
  have hN:3*g-2=g+(complexity g 1-1):=by unfold complexity;omega
  have hhS:complexity g 1=complexity g 1-1+1:=by omega
  have hHc:H 0 (r 0)=((3/Real.pi^2:ℝ):ℂ):=by
    rw[r_zero_parameter,H_zero_pi_value]
    push_cast
    rfl
  have hH:(H 0 (r 0)).re=3/Real.pi^2:=by
    rw[hHc,Complex.ofReal_re]
  have hdef:deficit g [k]=3*g-2-k:=by
    simp only[deficit,List.length_singleton,List.sum_singleton,dimension]
    omega
  have hpi:(Real.pi^2:ℝ)≠0:=pow_ne_zero _ Real.pi_ne_zero
  unfold oneBoundaryBracketModel oneBoundaryBracketScale
  simp only[model,show (0:ℝ)≠y₀ from ne_of_lt y₀_pos,ite_false,a_zero,one_pow,one_mul,
    List.length_singleton,hdef,harmonicCoeff_zero_unscaled,tiltedKernelMass_eq_unscaled,hH]
  have h4:(4:ℝ)^(3*g-2)=(4:ℝ)^g*4^(complexity g 1-1):=by rw[hN,pow_add]
  have hπ:(Real.pi^2)^(complexity g 1)=Real.pi^2*(Real.pi^2)^(complexity g 1-1):=by
    conv_lhs=>rw[hhS,pow_succ]
    ring
  rw[h4,mul_pow,div_pow,hπ]
  field_simp
  <;>ring
end WP.Coefficients
