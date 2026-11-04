import WPFormalization.HigherOrder.LinearRemainderAlgebra
import WPFormalization.Statements.Coefficients
import WPFormalization.Marked.Positivity
import WPFormalization.HigherOrder.HierarchyIdentities
/-! Exact actual merger/handle W prefactors and their finite remainder
pairings with the genuine canonical formal atoms. The X prefix keeps
all scalar errors at orders below the parent order. Neither an actual
error recurrence nor any completed remainder bound is assumed. -/
noncomputable section
open Set
namespace WP.HigherOrder
lemma merger_prefactor_eq_cusp (P:PsiTheory) (g p:ℕ) (hg:2 ≤ g) (hp:2 ≤ p)
    (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    W P g (p-1) Y/W P g p Y =
      A Y/((complexity g p:ℝ)-1)*cuspCorrection P g (p-1) Y :=by
  have hA:A Y≠0:=A_ne_zero_closed Y hY
  have hW:W P g p Y≠0:=(W_pos P g p (by omega) (by unfold Stable;omega) Y hY).ne'
  have hNat:complexity g (p-1)=complexity g p-1:=by unfold complexity;omega
  have hh:1 ≤ complexity g p:=by unfold complexity;omega
  have hhR:(1:ℝ)<complexity g p:=by exact_mod_cast (show 1<complexity g p by unfold complexity;omega)
  have hcc:(complexity g (p-1):ℝ)=(complexity g p:ℝ)-1:=by rw[hNat,Nat.cast_sub hh,Nat.cast_one]
  unfold cuspCorrection
  rw[show p-1+1=p by omega,hcc]
  field_simp[hA,hW,show (complexity g p:ℝ)-1≠0 by linarith]

lemma handle_prefactor_eq_cusp_genus (P:PsiTheory) (g p:ℕ) (hg:2 ≤ g) (hp:1 ≤ p)
    (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    W P (g-1) (p+1) Y/W P g p Y =
      A Y/((complexity g p:ℝ)-1)*cuspCorrection P (g-1) (p+1) Y*genusCorrection P g p Y :=by
  have hA:A Y≠0:=A_ne_zero_closed Y hY
  have hW:W P g p Y≠0:=(W_pos P g p hp (by unfold Stable;omega) Y hY).ne'
  have hWn:W P (g-1) (p+2) Y≠0:=(W_pos P (g-1) (p+2) (by omega) (by unfold Stable;omega) Y hY).ne'
  have hNat:complexity (g-1) (p+1)=complexity g p-1:=by unfold complexity;omega
  have hh:1 ≤ complexity g p:=by unfold complexity;omega
  have hhR:(1:ℝ)<complexity g p:=by exact_mod_cast (show 1<complexity g p by unfold complexity;omega)
  have hcc:(complexity (g-1) (p+1):ℝ)=(complexity g p:ℝ)-1:=by rw[hNat,Nat.cast_sub hh,Nat.cast_one]
  rw[genusCorrection_of_pos P g p Y (by omega)]
  unfold cuspCorrection
  rw[show p+1+1=p+2 by omega,hcc]
  field_simp[hA,hW,hWn,show (complexity g p:ℝ)-1≠0 by linarith]
lemma merger_atom_remainder_bound (P:PsiTheory) (g p L:ℕ) (d:List ℕ)
    (hg:2 ≤ g) (hp:2 ≤ p) (hL:1 ≤ L) (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    |(W P g (p-1) Y/W P g p Y)*profile P g d Y-
      truncationValue (PowerSeries.C (A Y)*complexityShift 1
        (PowerSeries.X*(formalCusp P Y (p-1)*formalProfile P Y d))) L (1/(complexity g p:ℝ))| ≤
      |A Y|/|(complexity g p:ℝ)-1| *
        |cuspCorrection P g (p-1) Y*profile P g d Y-
          truncationValue (formalCusp P Y (p-1)*formalProfile P Y d) (L-1) (1/((complexity g p:ℝ)-1))|+
      |A Y| *|truncationValue (PowerSeries.X*(formalCusp P Y (p-1)*formalProfile P Y d)) L (1/((complexity g p:ℝ)-1))-
        truncationValue (complexityShift 1 (PowerSeries.X*(formalCusp P Y (p-1)*formalProfile P Y d))) L (1/(complexity g p:ℝ))|:=by
  rw[merger_prefactor_eq_cusp P g p hg hp Y hY]
  simpa only[mul_assoc] using loss_one_remainder_bound (cuspCorrection P g (p-1) Y) (profile P g d Y)
    (A Y) 1 (complexity g p:ℝ) (formalCusp P Y (p-1)) (formalProfile P Y d) L hL
lemma handle_atom_remainder_bound (P:PsiTheory) (g p L:ℕ) (d:List ℕ)
    (hg:2 ≤ g) (hp:1 ≤ p) (hL:1 ≤ L) (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    let Fc:=formalCusp P Y (p+1)
    let Fe:=formalProfile P Y d
    let FG:=formalGenus P Y p
    let F:=PowerSeries.C (2*A Y)*complexityShift 1 (PowerSeries.X*(Fc*Fe))
    let x:=2*A Y/((complexity g p:ℝ)-1)*(cuspCorrection P (g-1) (p+1) Y*profile P (g-1) d Y)
    |2*(W P (g-1) (p+1) Y/W P g p Y)*profile P (g-1) d Y-
      truncationValue (F*FG) L (1/(complexity g p:ℝ))| ≤
      |x-truncationValue F L (1/(complexity g p:ℝ))| *|genusCorrection P g p Y|+
      ∑i∈Finset.range (L-1),|PowerSeries.coeff (i+1) F| *|1/(complexity g p:ℝ)|^(i+1)*
        |genusCorrection P g p Y-truncationValue FG (L-(i+1)) (1/(complexity g p:ℝ))|:=by
  dsimp only
  rw[handle_prefactor_eq_cusp_genus P g p hg hp Y hY]
  have hf:PowerSeries.coeff 0 (PowerSeries.C (2*A Y)*complexityShift 1
      (PowerSeries.X*(formalCusp P Y (p+1)*formalProfile P Y d)))=0:=by
    simp only[PowerSeries.coeff_zero_eq_constantCoeff,map_mul,PowerSeries.constantCoeff_C,
      complexityShift_constant,PowerSeries.constantCoeff_X,zero_mul,mul_zero]
  convert zero_constant_left_product_remainder_norm_le
    (2*A Y/((complexity g p:ℝ)-1)*(cuspCorrection P (g-1) (p+1) Y*profile P (g-1) d Y))
    (genusCorrection P g p Y) (1/(complexity g p:ℝ))
    (PowerSeries.C (2*A Y)*complexityShift 1 (PowerSeries.X*(formalCusp P Y (p+1)*formalProfile P Y d)))
    (formalGenus P Y p) L hL hf using 1
  congr 2
  ring
end WP.HigherOrder
