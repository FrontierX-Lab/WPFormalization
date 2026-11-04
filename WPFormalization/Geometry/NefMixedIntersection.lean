import WPFormalization.External.NefIntersection
import WPFormalization.Geometry.Bridge
import WPFormalization.Statements.Coefficients
/-! The original mixedJ normalization equals the actual mixed intersection; generic nef Teissier then applies. -/
set_option autoImplicit false
noncomputable section
universe u
namespace WP.Geometry
open WP.External Set
lemma mixedJ_eq_geometric_integral (P:PsiTheory)(R:IntersectionRealization.{u} P)
    (g k:ℕ)(hg:1 ≤ g)(hk:k ≤ 3*g-2):
    mixedJ P g k=(R.classes g 1).integral
      ((R.classes g 1).kappa₁^(3*g-2-k)*(R.classes g 1).psi 0^k):=by
  have hs:Stable g 1:=by unfold Stable;omega
  have hd:dimension g 1=3*g-2:=by unfold dimension;omega
  have hsum:∑i:Fin 1,k ≤ dimension g 1:=by simpa only[Fin.sum_univ_one,hd] using hk
  have he:=geometricBracket_eq_model P R g 1 (fun _=>k) hs hsum
  have hg':bracketB P g k=(oddFactorial k:ℝ)*(4:ℝ)^k*(2*Real.pi^2)^(3*g-2-k)*
      ((R.classes g 1).integral ((R.classes g 1).kappa₁^(3*g-2-k)*(R.classes g 1).psi 0^k)/
        ((3*g-2-k).factorial:ℝ)):=by
    simpa only[geometricBracket,Fin.sum_univ_one,Fin.prod_univ_one,
      mixedIntegral,hd,List.ofFn_const,List.replicate_succ,List.replicate_zero,bracketB,hs,hk,and_self,ite_true]
      using he.symm
  have ho:(oddFactorial k:ℝ)≠0:=by exact_mod_cast oddFactorial_ne_zero k
  have hf:((3*g-2-k).factorial:ℝ)≠0:=by exact_mod_cast Nat.factorial_ne_zero _
  have hp:(2*Real.pi^2:ℝ)^(3*g-2-k)≠0:=by positivity
  have h4:(4:ℝ)^k≠0:=by positivity
  unfold mixedJ
  rw[hg']
  field_simp

lemma mixed_log_concavity_of_nef_realization (P:PsiTheory)(g:ℕ)
    (R:OnePointNefRealization.{u} P g)(k:ℕ)(hg:1 ≤ g)(hk:1 ≤ k)(ht:k < 3*g-2):
    mixedJ P g (k-1)*mixedJ P g (k+1) ≤ mixedJ P g k^2:=by
  rw[mixedJ_eq_geometric_integral P R.realization g (k-1) hg (by omega),
    mixedJ_eq_geometric_integral P R.realization g (k+1) hg (by omega),
    mixedJ_eq_geometric_integral P R.realization g k hg (by omega)]
  have hd:dimension g 1=3*g-2:=by unfold dimension;omega
  have H:=R.calculus.teissier _ _ R.kappa_nef R.psi_nef k hk (by simpa only[hd] using ht)
  simpa only[hd] using H
end WP.Geometry
