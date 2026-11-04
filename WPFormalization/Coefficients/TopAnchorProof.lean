import WPFormalization.Statements.Coefficients
import WPFormalization.External.IntersectionEstimates
/-! The exact top two one-boundary coefficients, from DVV and the original shift. -/
noncomputable section
namespace WP
open Set
set_option autoImplicit false

lemma top_anchor_psi_single_zero (P:PsiTheory)(g:ℕ):P.psi g [0]=0:=by
  apply P.vanish
  right
  right
  norm_num
  omega

lemma top_anchor_dvv_two_singleton (P:PsiTheory)(g k:ℕ)(hg:1≤g):
    15*(oddFactorial k:ℝ)*P.psi g [2,(k:ℤ)]=
      (2*(k:ℝ)+1)*(oddFactorial (k+1):ℝ)*P.psi g [(k+1:ℕ)]+
        (1/2:ℝ)*(oddFactorial k:ℝ)*P.psi (g-1) [0,0,(k:ℤ)]:=by
  have hg0:g≠0:=by omega
  have h:=P.dvv g 2 [(k:ℤ)] (by simp) (by unfold complexity;simpa using (show 2≤2*g by omega))
  have hs:(2:ℤ)+(k:ℤ)-1=((k+1:ℕ):ℤ):=by omega
  have hsk:((2:ℤ)+(k:ℤ)).toNat-1=k+1:=by omega
  have hpow:({0}:Finset ℕ).powerset={∅,{0}}:=by decide
  have ho0:oddFactorial 0=1:=by decide
  have ho2:oddFactorial 2=15:=by decide
  norm_num [dvvRHS,weighted,doubleWeight,selected,Finset.sum_range_succ,hg0,ho0,ho2,
    hs,hsk,top_anchor_psi_single_zero,Finset.sum_add_distrib,hpow] at h
  convert h using 1 <;>push_cast <;>ring


lemma top_anchor_two_zero_string (P:PsiTheory)(g k:ℕ)(hg:1≤g):
    P.psi g [0,0,(k:ℤ)]=P.psi g [(k:ℤ)-2]:=by
  have hneg:P.psi g [-1,(k:ℤ)]=0:=by
    apply P.vanish
    right
    left
    exact ⟨-1,by simp,by norm_num⟩
  have hs₁:=P.string g [0,(k:ℤ)] (by unfold Stable;norm_num;omega)
  have hs₂:=P.string g [(k:ℤ)-1] (by unfold Stable;norm_num;omega)
  norm_num [Finset.sum_range_succ] at hs₁ hs₂
  rw[hneg] at hs₁
  have he:(k:ℤ)-1-1=(k:ℤ)-2:=by ring
  rw[he] at hs₂
  linarith only[hs₁,hs₂]


lemma top_anchor_nonseparating_value (P:PsiTheory)(g:ℕ)(hg:1≤g):
    P.psi (g-1) [0,0,((3*g-3:ℕ):ℤ)]=
      24*(g:ℝ)*P.psi g [((3*g-2:ℕ):ℤ)]:=by
  by_cases hg1:g=1
  · subst g
    norm_num[P.base₀,P.base₁]
  · have hg2:2≤g:=by omega
    have hc:((3*g-3:ℕ):ℤ)-2=((3*(g-1)-2:ℕ):ℤ):=by omega
    have hcur:P.psi g [((3*g-2:ℕ):ℤ)]=1/((24:ℝ)^g*g.factorial):=by
      simpa [pure] using one_point P g hg
    have hprev:P.psi (g-1) [((3*(g-1)-2:ℕ):ℤ)]=1/((24:ℝ)^(g-1)*(g-1).factorial):=by
      simpa [pure] using one_point P (g-1) (by omega)
    rw[top_anchor_two_zero_string P (g-1) (3*g-3) (by omega),hc,hprev,hcur]
    have heq:(g-1)+1=g:=by omega
    have hp:(24:ℝ)^g=(24:ℝ)^(g-1)*24:=by
      calc
        _=(24:ℝ)^((g-1)+1):=congrArg (fun n:ℕ=>(24:ℝ)^n) heq.symm
        _=_:=pow_succ _ _
    have hf:g.factorial=g*(g-1).factorial:=by
      simpa only[heq] using Nat.factorial_succ (g-1)
    have hfr:(g.factorial:ℝ)=(g:ℝ)*((g-1).factorial:ℝ):=by exact_mod_cast hf
    rw[hp,hfr]
    have hg0:(g:ℝ)≠0:=by exact_mod_cast (show g≠0 by omega)
    field_simp
    <;>ring

lemma top_anchor_psi_formula (P:PsiTheory)(g:ℕ)(hg:1≤g):
    15*P.psi g [2,((3*g-3:ℕ):ℤ)]=
      ((6*(g:ℝ)-3)*(6*g-5)+12*g)*P.psi g [((3*g-2:ℕ):ℤ)]:=by
  let k:ℕ:=3*g-3
  have h:=top_anchor_dvv_two_singleton P g k hg
  have hn:k+1=3*g-2:=by dsimp[k];omega
  have hc:(k:ℝ)=3*(g:ℝ)-3:=by
    have hi:k+3=3*g:=by dsimp[k];omega
    have hir:(k:ℝ)+3=3*(g:ℝ):=by exact_mod_cast hi
    linarith only[hir]
  have ho:(oddFactorial (k+1):ℝ)=(oddFactorial k:ℝ)*(2*(k:ℝ)+3):=by
    rw[oddFactorial_succ]
    push_cast
    ring
  rw[ho,hn,top_anchor_nonseparating_value P g hg] at h
  have hnodd:(oddFactorial k:ℝ)≠0:=by exact_mod_cast oddFactorial_ne_zero k
  have he:(oddFactorial k:ℝ)*(15*P.psi g [2,(k:ℤ)])=
      (oddFactorial k:ℝ)*(((2*(k:ℝ)+1)*(2*k+3)+12*g)*P.psi g [((3*g-2:ℕ):ℤ)]):=by
    nlinarith only[h]
  have hcancel:=mul_left_cancel₀ hnodd he
  change 15*P.psi g [2,(k:ℤ)]=_
  rw[hc] at hcancel
  convert hcancel using 1 <;>ring


lemma top_anchor_mixedJ_shifted (P:PsiTheory)(g k:ℕ)(hg:1≤g):
    mixedJ P g k=shifted P g [k] 0*((3*g-2-k).factorial:ℝ)/(oddFactorial k:ℝ):=by
  have hd:dimension g 1=3*g-2:=by unfold dimension;omega
  have hm:deficit g [k]=3*g-2-k:=by simp only[deficit,List.length_singleton,List.sum_singleton,hd]
  have ho:(oddFactorial k:ℝ)≠0:=by exact_mod_cast oddFactorial_ne_zero k
  have hp:(2*Real.pi^2:ℝ)^(3*g-2-k)≠0:=by positivity
  have h4:(4:ℝ)^k≠0:=by positivity
  unfold mixedJ bracketB mixedBracket
  simp only[List.sum_singleton,hm]
  field_simp
  <;>ring

lemma top_anchor_shifted_top (P:PsiTheory)(g:ℕ)(hg:1≤g):
    shifted P g [3*g-2] 0=(oddFactorial (3*g-2):ℝ)*pure P g [3*g-2]:=by
  have hs:Stable g [3*g-2].length:=by simp only[List.length_singleton];unfold Stable;omega
  have hd:[3*g-2].sum≤dimension g [3*g-2].length:=by simp only[List.sum_singleton,List.length_singleton];unfold dimension;omega
  have hm:deficit g [3*g-2]=0:=by simp only[deficit,List.length_singleton,List.sum_singleton,dimension];omega
  unfold shifted
  rw[ite_eq_left ⟨hs,hd⟩,hm]
  simp [backgrounds_zero,backgroundDegrees,a_zero]

lemma top_anchor_shifted_next (P:PsiTheory)(g:ℕ)(hg:1≤g):
    shifted P g [3*g-3] 0=(oddFactorial (3*g-3):ℝ)*pure P g [3*g-3,2]:=by
  have hs:Stable g [3*g-3].length:=by simp only[List.length_singleton];unfold Stable;omega
  have hd:[3*g-3].sum≤dimension g [3*g-3].length:=by simp only[List.sum_singleton,List.length_singleton];unfold dimension;omega
  have hm:deficit g [3*g-3]=1:=by simp only[deficit,List.length_singleton,List.sum_singleton,dimension];omega
  have hX:(iteratedDeriv 2 X 0).re= -1:=by rw[iteratedDeriv_X_zero_re 2 (by norm_num)];norm_num
  unfold shifted
  rw[ite_eq_left ⟨hs,hd⟩,hm]
  norm_num [backgrounds_one,backgroundDegrees,a_zero,hX,List.finRange_succ,
    Fin.prod_univ_one,Fin.sum_univ_one]

lemma top_anchor_mixedJ_top (P:PsiTheory)(g:ℕ)(hg:1≤g):
    mixedJ P g (3*g-2)=pure P g [3*g-2]:=by
  rw[top_anchor_mixedJ_shifted P g _ hg,top_anchor_shifted_top P g hg]
  have ho:(oddFactorial (3*g-2):ℝ)≠0:=by exact_mod_cast oddFactorial_ne_zero _
  simp only[Nat.sub_self,Nat.factorial_zero,Nat.cast_one,mul_one]
  exact mul_div_cancel_left₀ _ ho

lemma top_anchor_mixedJ_next (P:PsiTheory)(g:ℕ)(hg:1≤g):
    mixedJ P g (3*g-3)=pure P g [3*g-3,2]:=by
  have hn:3*g-2-(3*g-3)=1:=by omega
  rw[top_anchor_mixedJ_shifted P g _ hg,top_anchor_shifted_next P g hg,hn]
  have ho:(oddFactorial (3*g-3):ℝ)≠0:=by exact_mod_cast oddFactorial_ne_zero _
  simp only[Nat.factorial_one,Nat.cast_one,mul_one]
  exact mul_div_cancel_left₀ _ ho

lemma top_anchor_mixedJ_ratio (P:PsiTheory)(g:ℕ)(hg:1≤g):
    mixedJ P g (3*g-3)/mixedJ P g (3*g-2)=(12*(g:ℝ)^2-12*g+5)/5:=by
  rw[top_anchor_mixedJ_top P g hg,top_anchor_mixedJ_next P g hg]
  have he:=top_anchor_psi_formula P g hg
  have hsym:P.psi g [2,((3*g-3:ℕ):ℤ)]=P.psi g [((3*g-3:ℕ):ℤ),2]:=
    P.symmetry g _ _ (List.Perm.swap _ _ [])
  rw[hsym] at he
  have hcur:pure P g [3*g-2]=1/((24:ℝ)^g*g.factorial):=one_point P g hg
  have hpos:0<pure P g [3*g-2]:=by rw[hcur];positivity
  change 15*pure P g [3*g-3,2]=((6*(g:ℝ)-3)*(6*g-5)+12*g)*pure P g [3*g-2] at he
  apply (div_eq_iff (ne_of_gt hpos)).2
  nlinarith only[he]

lemma top_anchor_boundaryA_shifted (P:PsiTheory)(g k:ℕ):
    boundaryA P g k=(2*Real.pi^2:ℝ)^(deficit g [k])*shifted P g [k] 0:=by
  have h4:(4:ℝ)^k≠0:=by positivity
  unfold boundaryA bracketB mixedBracket
  simp only[List.sum_singleton]
  field_simp
  <;>ring

lemma top_anchor_boundaryA_ratio (P:PsiTheory)(g:ℕ)(hg:1≤g):
    boundaryA P g (3*g-3)/boundaryA P g (3*g-2)=
      2*Real.pi^2*(12*(g:ℝ)^2-12*g+5)/(5*(6*(g:ℝ)-3)):=by
  have ht:deficit g [3*g-2]=0:=by simp only[deficit,List.length_singleton,List.sum_singleton,dimension];omega
  have hn:deficit g [3*g-3]=1:=by simp only[deficit,List.length_singleton,List.sum_singleton,dimension];omega
  rw[top_anchor_boundaryA_shifted,top_anchor_boundaryA_shifted,ht,hn,pow_zero,pow_one,one_mul,
    top_anchor_shifted_next P g hg,top_anchor_shifted_top P g hg]
  have hc:pure P g [3*g-2]≠0:=by rw[one_point P g hg];positivity
  have ho:(oddFactorial (3*g-3):ℝ)≠0:=by exact_mod_cast oddFactorial_ne_zero _
  have hnindex:(3*g-3)+1=3*g-2:=by omega
  have ho':(oddFactorial (3*g-2):ℝ)=(oddFactorial (3*g-3):ℝ)*(6*(g:ℝ)-3):=by
    rw[←hnindex,oddFactorial_succ]
    push_cast
    have hi:(3*g-3:ℕ)+3=3*g:=by omega
    have hir:(3*g-3:ℕ)+3=3*(g:ℝ):=by exact_mod_cast hi
    nlinarith only[hir]
  have hr:=top_anchor_mixedJ_ratio P g hg
  rw[top_anchor_mixedJ_top P g hg,top_anchor_mixedJ_next P g hg] at hr
  have hdiv:(6*(g:ℝ)-3)≠0:=by
    have hgr:(1:ℝ)≤g:=by exact_mod_cast hg
    linarith only[hgr]
  rw[ho']
  have hre:= (div_eq_iff hc).1 hr
  field_simp
  <;>nlinarith only[hre]
end WP
