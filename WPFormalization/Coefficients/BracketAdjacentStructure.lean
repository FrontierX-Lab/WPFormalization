import WPFormalization.Coefficients.BottomLogBoundCore
/-! Exact original bracket, boundary coefficient and mixed-intersection adjacent ratio identities. -/
set_option autoImplicit false
noncomputable section
namespace WP.Coefficients

def bracketAdjacentRatio (P:PsiTheory)(g k:ℕ):ℝ:=bracketB P g k/bracketB P g (k+1)
def oneBoundaryRatioWeight (g k:ℕ):ℝ:=(2*(k:ℝ)+3)*((3*g-2-k:ℕ):ℝ)

lemma bracketAdjacentRatio_pos (P:PsiTheory)(g k:ℕ)(hg:1 ≤ g)(hk:k < 3*g-2):
    0 < bracketAdjacentRatio P g k:=
  div_pos (bracketB_pos_admissible P g k hg (by omega)) (bracketB_pos_admissible P g (k+1) hg (by omega))

lemma bracketAdjacentRatio_ge_one (P:PsiTheory)(g k:ℕ)(hg:1 ≤ g)(hk:k < 3*g-2):
    1 ≤ bracketAdjacentRatio P g k:=by
  have hm:=normalized_cons_raise_le P g k [] (by simp only[List.length_cons,List.length_nil];unfold Stable;omega)
    0 ⟨le_rfl,y₀_pos.le⟩
  change normalized P g [k+1] 0 ≤ normalized P g [k] 0 at hm
  have hb:bracketB P g (k+1) ≤ bracketB P g k:=by
    rw[bracketB_eq_normalized_zero P g (k+1) hg (by omega),bracketB_eq_normalized_zero P g k hg (by omega)]
    exact mul_le_mul_of_nonneg_left hm (by positivity)
  exact (one_le_div (bracketB_pos_admissible P g (k+1) hg (by omega))).mpr hb

lemma oneBoundaryRatioWeight_pos (g k:ℕ)(hk:k < 3*g-2):0 < oneBoundaryRatioWeight g k:=by
  unfold oneBoundaryRatioWeight
  have hm:0 < (3*g-2-k:ℕ):=by omega
  have hmR:(0:ℝ) < ((3*g-2-k:ℕ):ℝ):=by exact_mod_cast hm
  positivity

lemma bracketAdjacentRatio_eq_mixedJ (P:PsiTheory)(g k:ℕ)(hg:1 ≤ g)(hk:k < 3*g-2):
    bracketAdjacentRatio P g k=Real.pi^2*(mixedJ P g k/mixedJ P g (k+1))/(2*oneBoundaryRatioWeight g k):=by
  have hm:3*g-2-k=(3*g-2-(k+1))+1:=by omega
  have hf:((3*g-2-k).factorial:ℝ)=((3*g-2-k:ℕ):ℝ)*((3*g-2-(k+1)).factorial:ℝ):=by
    have hfN:(3*g-2-k).factorial=(3*g-2-k)*(3*g-2-(k+1)).factorial:=by
      rw[hm,Nat.factorial_succ]
    exact_mod_cast hfN
  have ho:(oddFactorial (k+1):ℝ)=(oddFactorial k:ℝ)*(2*(k:ℝ)+3):=by
    rw[oddFactorial_succ]
    push_cast
    ring
  have hp:(2*Real.pi^2:ℝ)^(3*g-2-k)=(2*Real.pi^2:ℝ)^(3*g-2-(k+1))*(2*Real.pi^2):=by
    conv_lhs=>rw[hm,pow_succ]
  have hB:=bracketB_pos_admissible P g (k+1) hg (by omega)
  have ho0:(oddFactorial k:ℝ)≠0:=by exact_mod_cast oddFactorial_ne_zero k
  have hf0:((3*g-2-(k+1)).factorial:ℝ)≠0:=by exact_mod_cast Nat.factorial_ne_zero _
  have hm0:((3*g-2-k:ℕ):ℝ)≠0:=by exact_mod_cast (show 3*g-2-k≠0 by omega)
  have hk0:(2*(k:ℝ)+3)≠0:=by positivity
  unfold bracketAdjacentRatio mixedJ oneBoundaryRatioWeight
  rw[hf,ho,hp,pow_succ]
  field_simp
  <;>ring

lemma boundaryA_adjacent_eq_four_bracketAdjacentRatio (P:PsiTheory)(g k:ℕ):
    boundaryA P g k/boundaryA P g (k+1)=4*bracketAdjacentRatio P g k:=by
  unfold boundaryA bracketAdjacentRatio
  rw[pow_succ]
  have h4:(4:ℝ)^k≠0:=by positivity
  field_simp
  <;>ring
end WP.Coefficients
