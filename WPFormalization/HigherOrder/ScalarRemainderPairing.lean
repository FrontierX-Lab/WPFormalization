import WPFormalization.HigherOrder.HierarchyIdentities
import WPFormalization.HigherOrder.TriangularLocality
import WPFormalization.HigherOrder.FiniteRemainderAlgebra
import WPFormalization.HigherOrder.LinearRemainderAlgebra
import WPFormalization.Marked.Positivity
import WPFormalization.Marked.TopologyTailDefinitions
/-! Actual scalar recurrences paired with their canonical finite targets.
The p=1 descent uses the true next-marking genus and actual cusp quotient.
The KdV full symmetric sum is oriented exactly into twice the low-loss mass
and the existing central tail; its canonical cutoff uses the true finite
algorithm. The resulting ratio-error sum is a proved identity and norm
bound, not an assumed recurrence or a completed uniform C.3 remainder. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.HigherOrder
open Set PowerSeries

lemma actual_genus_one_descent (P:PsiTheory)(g:ℕ)(hg:2≤g)(Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀):
    genusCorrection P g 1 Y=genusCorrection P g 2 Y*
      cuspCorrection P (g-1) 3 Y/(cuspCorrection P g 1 Y):=by
  have hs1:Stable g 1:=by unfold Stable;omega
  have hs2:Stable g 2:=by unfold Stable;omega
  have hsc3:Stable (g-1) 3:=by unfold Stable;omega
  have hsc4:Stable (g-1) 4:=by unfold Stable;omega
  have hw1:W P g 1 Y≠0:=(W_pos P g 1 (by omega) hs1 Y hY).ne'
  have hw2:W P g 2 Y≠0:=(W_pos P g 2 (by omega) hs2 Y hY).ne'
  have hw3:W P (g-1) 3 Y≠0:=(W_pos P (g-1) 3 (by omega) hsc3 Y hY).ne'
  have hw4:W P (g-1) 4 Y≠0:=(W_pos P (g-1) 4 (by omega) hsc4 Y hY).ne'
  have hc:complexity (g-1) 3=complexity g 1:=by unfold complexity;omega
  have hh:0<(complexity g 1:ℝ):=by
    have hn:0<complexity g 1:=by unfold complexity;omega
    exact_mod_cast hn
  have hA:A Y≠0:=A_ne_zero_closed Y hY
  rw[genusCorrection_of_pos P g 1 Y (by omega),genusCorrection_of_pos P g 2 Y (by omega),
    cuspCorrection,cuspCorrection,hc]
  field_simp[hw1,hw2,hw3,hw4,hA,hh.ne']

lemma formalGenus_one_descent_product (P:PsiTheory)(Y:ℝ):
    formalGenus P Y 1=complexityShift (-1) (formalGenus P Y 2)*
      (formalCusp P Y 3*(formalCusp P Y 1)⁻¹):=by
  rw[formalGenus_descent P Y 1 (by omega)]
  simp only[descendGenus,Nat.reduceAdd,mul_assoc]

lemma actual_genus_one_remainder_pairing (P:PsiTheory)(g:ℕ)(hg:2≤g)
    (Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀)(L:ℕ)(t:ℝ):
    genusCorrection P g 1 Y-truncationValue (formalGenus P Y 1) L t=
      (genusCorrection P g 2 Y-truncationValue (complexityShift (-1) (formalGenus P Y 2)) L t)*
        (cuspCorrection P (g-1) 3 Y*(cuspCorrection P g 1 Y)⁻¹)+
      ∑a∈Finset.range L,PowerSeries.coeff a (complexityShift (-1) (formalGenus P Y 2))*t^a*
        (cuspCorrection P (g-1) 3 Y*(cuspCorrection P g 1 Y)⁻¹-
          truncationValue (formalCusp P Y 3*(formalCusp P Y 1)⁻¹) (L-a) t):=by
  rw[actual_genus_one_descent P g hg Y hY,formalGenus_one_descent_product]
  simpa only[div_eq_mul_inv,mul_assoc] using exact_product_remainder_identity
    (genusCorrection P g 2 Y) (cuspCorrection P (g-1) 3 Y*(cuspCorrection P g 1 Y)⁻¹)
    (complexityShift (-1) (formalGenus P Y 2)) (formalCusp P Y 3*(formalCusp P Y 1)⁻¹) L t

lemma actual_genus_kdv_identity (P:PsiTheory)(g p:ℕ)(hg:1≤g)(hp:2≤p)
    (Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀):
    genusCorrection P g p Y=profile P g (1::List.replicate (p-1) 0) Y-
      3/2*∑j∈Finset.range (g+1),∑s∈Finset.range (p-1),
        (Nat.choose (p-2) s:ℝ)*W P j (s+2) Y*W P (g-j) (p-s) Y/W P g p Y:=by
  have hs:Stable g p:=by unfold Stable;omega
  have hw:W P g p Y≠0:=(W_pos P g p (by omega) hs Y hY).ne'
  have hn:normalized P g (List.replicate p 0) Y≠0:=by
    intro hz
    apply hw
    simp only[W,hz,mul_zero]
  have hlen:(1::List.replicate (p-1) 0).length=p:=by simp;omega
  have hsum:(∑j∈Finset.range (g+1),∑s∈Finset.range (p-1),
      (Nat.choose (p-2) s:ℝ)*W P j (s+2) Y*W P (g-j) (p-s) Y/W P g p Y)=
      (∑j∈Finset.range (g+1),∑s∈Finset.range (p-1),
        (Nat.choose (p-2) s:ℝ)*normalized P j (List.replicate (s+2) 0) Y*
          normalized P (g-j) (List.replicate (p-s) 0) Y)/normalized P g (List.replicate p 0) Y:=by
    rw[Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    rw[Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s hs
    have hjg:j≤g:=by have hh:=Finset.mem_range.mp hj;omega
    have hpow:(4:ℝ)^j*4^(g-j)=4^g:=by rw[←pow_add,Nat.add_sub_of_le hjg]
    unfold W
    have h4:(4:ℝ)^g≠0:=by positivity
    field_simp[hn,h4]
    linear_combination (Nat.choose (p-2) s:ℝ)*normalized P j (List.replicate (s+2) 0) Y*
      normalized P (g-j) (List.replicate (p-s) 0) Y*hpow
  have hpow:(4:ℝ)^g=4^(g-1)*4:=by rw[←pow_succ,Nat.sub_add_cancel hg]
  have hk:=shifted_kdv P g p hg hp Y hY
  rw[profile,hlen,hsum,genusCorrection_of_pos P g p Y (by omega),W,W]
  rw[hpow]
  have h4:(4:ℝ)^(g-1)≠0:=by positivity
  field_simp[hn,h4]
  nlinarith[hk]

lemma double_sum_range_reflect (f:ℕ→ℕ→ℝ)(g n:ℕ):
    (∑j∈Finset.range (g+1),∑s∈Finset.range (n+1),f (g-j) (n-s))=
      ∑j∈Finset.range (g+1),∑s∈Finset.range (n+1),f j s:=by
  calc
    _ = ∑j∈Finset.range (g+1),∑s∈Finset.range (n+1),f j (n-s):=by
      simpa only[Nat.add_sub_cancel] using Finset.sum_range_reflect
        (fun j=>∑s∈Finset.range (n+1),f j (n-s)) (g+1)
    _ = _:=by
      apply Finset.sum_congr rfl
      intro j hj
      simpa only[Nat.add_sub_cancel] using Finset.sum_range_reflect (f j) (n+1)

lemma symmetric_complexity_split (f:ℕ→ℕ→ℝ)(g n L:ℕ)(hL:2*L≤2*g+n)
    (hf:∀j≤g,∀s≤n,f (g-j) (n-s)=f j s):
    (∑j∈Finset.range (g+1),∑s∈Finset.range (n+1),f j s)=
      2*(∑j∈Finset.range (g+1),∑s∈Finset.range (n+1),if 2*j+s<L then f j s else 0)+
      ∑j∈Finset.range (g+1),∑s∈Finset.range (n+1),
        if L≤2*j+s ∧ L≤2*(g-j)+(n-s) then f j s else 0:=by
  have hhigh:(∑j∈Finset.range (g+1),∑s∈Finset.range (n+1),
      if 2*(g-j)+(n-s)<L then f j s else 0)=
      ∑j∈Finset.range (g+1),∑s∈Finset.range (n+1),if 2*j+s<L then f j s else 0:=by
    rw[←double_sum_range_reflect (fun j s=>if 2*(g-j)+(n-s)<L then f j s else 0) g n]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro s hs
    have hjg:j≤g:=by have he:=Finset.mem_range.mp hj;omega
    have hsn:s≤n:=by have he:=Finset.mem_range.mp hs;omega
    rw[show g-(g-j)=j by omega,show n-(n-s)=s by omega,hf j hjg s hsn]
  have hpoint(j s:ℕ)(hj:j∈Finset.range (g+1))(hs:s∈Finset.range (n+1)):
      f j s=(if 2*j+s<L then f j s else 0)+(if 2*(g-j)+(n-s)<L then f j s else 0)+
        (if L≤2*j+s ∧ L≤2*(g-j)+(n-s) then f j s else 0):=by
    have hjg:j≤g:=by have he:=Finset.mem_range.mp hj;omega
    have hsn:s≤n:=by have he:=Finset.mem_range.mp hs;omega
    have hsum:(2*j+s)+(2*(g-j)+(n-s))=2*g+n:=by omega
    by_cases ha:2*j+s<L
    · have hb:¬2*(g-j)+(n-s)<L:=by omega
      simp only[ite_eq_left ha,ite_eq_right hb,ite_eq_right (show ¬(L≤2*j+s ∧ L≤2*(g-j)+(n-s)) by omega),add_zero]
    · by_cases hb:2*(g-j)+(n-s)<L
      · simp only[ite_eq_right ha,ite_eq_left hb,ite_eq_right (show ¬(L≤2*j+s ∧ L≤2*(g-j)+(n-s)) by omega),zero_add,add_zero]
      · simp only[ite_eq_right ha,ite_eq_right hb,ite_eq_left (show L≤2*j+s ∧ L≤2*(g-j)+(n-s) by omega),zero_add]
  have hall:(∑j∈Finset.range (g+1),∑s∈Finset.range (n+1),f j s)=
      (∑j∈Finset.range (g+1),∑s∈Finset.range (n+1),if 2*j+s<L then f j s else 0)+
      (∑j∈Finset.range (g+1),∑s∈Finset.range (n+1),if 2*(g-j)+(n-s)<L then f j s else 0)+
      (∑j∈Finset.range (g+1),∑s∈Finset.range (n+1),if L≤2*j+s ∧ L≤2*(g-j)+(n-s) then f j s else 0):=by
    rw[←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw[←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    exact hpoint j s hj hs
  rw[hhigh] at hall
  linarith

lemma markedSplitTerm_kdv_symm (P:PsiTheory)(g p j s:ℕ)(hp:2≤p)(hj:j≤g)(hs:s≤p-2)(Y:ℝ):
    markedSplitTerm P g p 2 (g-j) (p-2-s) Y=markedSplitTerm P g p 2 j s Y:=by
  unfold markedSplitTerm
  rw[show p-2-s+2=p-s by omega,show p-(p-2-s)=s+2 by omega,show g-(g-j)=j by omega,
    Nat.choose_symm hs]
  ring

lemma kdv_full_split_orientation (P:PsiTheory)(g p L:ℕ)(hp:2≤p)(hL:2*L≤complexity g p)(Y:ℝ):
    (∑j∈Finset.range (g+1),∑s∈Finset.range (p-1),markedSplitTerm P g p 2 j s Y)=
      2*(∑j∈Finset.range (g+1),∑s∈Finset.range (p-1),
        if 2*j+s<L then markedSplitTerm P g p 2 j s Y else 0)+markedSplitLossTail P g p 2 L Y:=by
  have he:=symmetric_complexity_split (fun j s=>markedSplitTerm P g p 2 j s Y) g (p-2) L
    (by unfold complexity at hL;omega) (fun j hj s hs=>markedSplitTerm_kdv_symm P g p j s hp hj hs Y)
  have hpn:p-2+1=p-1:=by omega
  simpa only[hpn,markedSplitLossTail,markedSplitLossTailGenus] using he


lemma genusSeries_coeff_cutoff (P:PsiTheory)(Y:ℝ)(F:HierarchyJet)(profiles:List ℕ→Series)
    (p n K:ℕ)(hn:n≤K):
    PowerSeries.coeff n (genusSeries P Y F profiles K p)=
      PowerSeries.coeff n (genusSeries P Y F profiles n p):=by
  let term:ℕ→ℕ→Series:=fun j s=>
    PowerSeries.C ((Nat.choose (p-2) s:ℝ)*smallW P Y j (List.replicate (s+2) 0))*ratioSeries Y F p j s
  have hz(j s:ℕ)(hr:n<2*j+s):PowerSeries.coeff n (term j s)=0:=by
    dsimp[term]
    rw[PowerSeries.coeff_C_mul,ratioSeries_coeff,ite_eq_right (by omega),mul_zero]
  have hcut(j s:ℕ):PowerSeries.coeff n
      (if Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s≤K then term j s else 0)=
      PowerSeries.coeff n (if Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s≤n then term j s else 0):=by
    by_cases hr:2*j+s≤n
    · have he:(Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s≤K)↔
          (Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s≤n):=by
        simp only[hr,hr.trans hn,and_true]
      simp only[he]
    · have he:¬(Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s≤n):=by tauto
      rw[ite_eq_right he]
      by_cases hc:Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s≤K
      · rw[ite_eq_left hc,hz j s (by omega),map_zero]
      · rw[ite_eq_right hc]
  have hsum:PowerSeries.coeff n
      (∑j∈Finset.range (K+1),∑s∈Finset.range (p-1),
        if Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s≤K then term j s else 0)=
      PowerSeries.coeff n (∑j∈Finset.range (n+1),∑s∈Finset.range (p-1),
        if Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s≤n then term j s else 0):=by
    simp only[map_sum]
    simp_rw[hcut]
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hjn
    apply Finset.sum_eq_zero
    intro s hs
    have hjgt:n<j:=by
      have he:¬j<n+1:=by simpa only[Finset.mem_range] using hjn
      omega
    rw[ite_eq_right (by omega),map_zero]
  dsimp only[genusSeries]
  rw[map_sub,map_sub,PowerSeries.coeff_C_mul,PowerSeries.coeff_C_mul]
  exact congrArg (fun x=>PowerSeries.coeff n (profiles (1::List.replicate (p-1) 0))-3*x) hsum

lemma formalGenus_kdv_truncation (P:PsiTheory)(Y:ℝ)(p L:ℕ)(hp:2≤p)(hL:1≤L)(t:ℝ):
    truncationValue (formalGenus P Y p) L t=
      truncationValue (genusSeries P Y
        ⟨formalProfile P Y,formalCusp P Y,formalGenus P Y⟩ (formalProfile P Y) (L-1) p) L t:=by
  unfold truncationValue
  apply Finset.sum_congr rfl
  intro n hn
  rw[formalGenus_kdv_coefficient P Y p hp n]
  have hnL:n≤L-1:=by have he:=Finset.mem_range.mp hn;omega
  rw[genusSeries_coeff_cutoff P Y _ _ p n (L-1) hnL]


def truncationValueAddHom (L:ℕ)(t:ℝ):Series→+ℝ where
  toFun:=fun f=>truncationValue f L t
  map_zero':=by simp[truncationValue]
  map_add':=by intro f g;simp[truncationValue,map_add,add_mul,Finset.sum_add_distrib]

lemma truncationValue_sub (f g:Series)(L:ℕ)(t:ℝ):
    truncationValue (f-g) L t=truncationValue f L t-truncationValue g L t:=
  (truncationValueAddHom L t).map_sub f g

lemma truncationValue_sum {ι:Type*}(s:Finset ι)(f:ι→Series)(L:ℕ)(t:ℝ):
    truncationValue (∑i∈s,f i) L t=∑i∈s,truncationValue (f i) L t:=by
  exact map_sum (truncationValueAddHom L t) f s

lemma truncationValue_zero (L:ℕ)(t:ℝ):truncationValue (0:Series) L t=0:=by simp[truncationValue]

def kdvFormalLowSeries (P:PsiTheory)(Y:ℝ)(p L:ℕ):Series:=
  ∑j∈Finset.range L,∑s∈Finset.range (p-1),
    if Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s<L then
      PowerSeries.C ((Nat.choose (p-2) s:ℝ)*smallW P Y j (List.replicate (s+2) 0))*
        ratioSeries Y (formalHierarchyJet P Y) p j s else 0

def kdvActualLowMass (P:PsiTheory)(g p L:ℕ)(Y:ℝ):ℝ:=
  ∑j∈Finset.range L,∑s∈Finset.range (p-1),
    if Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s<L then markedSplitTerm P g p 2 j s Y else 0

lemma formalGenus_kdv_truncation_paired (P:PsiTheory)(Y:ℝ)(p L:ℕ)(hp:2≤p)(hL:1≤L)(t:ℝ):
    truncationValue (formalGenus P Y p) L t=
      truncationValue (formalProfile P Y (1::List.replicate (p-1) 0)) L t-
        3*truncationValue (kdvFormalLowSeries P Y p L) L t:=by
  rw[formalGenus_kdv_truncation P Y p L hp hL t]
  have he:genusSeries P Y (formalHierarchyJet P Y) (formalProfile P Y) (L-1) p=
      formalProfile P Y (1::List.replicate (p-1) 0)-PowerSeries.C 3*kdvFormalLowSeries P Y p L:=by
    unfold genusSeries kdvFormalLowSeries formalHierarchyJet
    have hi(r:ℕ):r≤L-1↔r<L:=by omega
    simp only[Nat.sub_add_cancel hL,hi]
  simp only[formalHierarchyJet] at he
  rw[he,truncationValue_sub,truncationValue_C_mul]

lemma markedSplitTerm_low_indicator (P:PsiTheory)(g p L j s:ℕ)(Y:ℝ):
    (if 2*j+s<L then markedSplitTerm P g p 2 j s Y else 0)=
      if Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s<L then markedSplitTerm P g p 2 j s Y else 0:=by
  by_cases hz:2*j+s=0
  · have hj:j=0:=by omega
    have hs:s=0:=by omega
    subst j
    subst s
    have hw:W P 0 2 Y=0:=W_unstable P 0 2 (by norm_num[Stable]) Y
    simp[markedSplitTerm,hw,Stable]
  · have hpos:1≤2*j+s:=by omega
    have hs:Stable j (s+2):=by unfold Stable;omega
    simp only[hs,hpos,true_and]

lemma kdv_low_crop (P:PsiTheory)(g p L:ℕ)(hLg:L≤g+1)(Y:ℝ):
    (∑j∈Finset.range (g+1),∑s∈Finset.range (p-1),
      if 2*j+s<L then markedSplitTerm P g p 2 j s Y else 0)=kdvActualLowMass P g p L Y:=by
  simp_rw[markedSplitTerm_low_indicator]
  unfold kdvActualLowMass
  symm
  apply Finset.sum_subset (Finset.range_mono hLg)
  intro j hj hjL
  have hjge:L≤j:=by
    have he:¬j<L:=by simpa only[Finset.mem_range] using hjL
    omega
  apply Finset.sum_eq_zero
  intro s hs
  rw[ite_eq_right (by omega)]

lemma actual_genus_kdv_oriented (P:PsiTheory)(g p L:ℕ)(hg:1≤g)(hp:2≤p)(hL:1≤L)
    (hLg:L≤g+1)(hLoss:2*L≤complexity g p)(Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀):
    genusCorrection P g p Y=profile P g (1::List.replicate (p-1) 0) Y-
      3*kdvActualLowMass P g p L Y-(3/2)*markedSplitLossTail P g p 2 L Y:=by
  have he:=actual_genus_kdv_identity P g p hg hp Y hY
  change genusCorrection P g p Y=profile P g (1::List.replicate (p-1) 0) Y-
    3/2*(∑j∈Finset.range (g+1),∑s∈Finset.range (p-1),markedSplitTerm P g p 2 j s Y) at he
  rw[kdv_full_split_orientation P g p L hp hLoss Y,kdv_low_crop P g p L hLg Y] at he
  calc
    _ = _:=he
    _ = _:=by ring

lemma actual_genus_kdv_remainder_pairing (P:PsiTheory)(g p L:ℕ)(hg:1≤g)(hp:2≤p)(hL:1≤L)
    (hLg:L≤g+1)(hLoss:2*L≤complexity g p)(Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀)(t:ℝ):
    genusCorrection P g p Y-truncationValue (formalGenus P Y p) L t=
      (profile P g (1::List.replicate (p-1) 0) Y-
        truncationValue (formalProfile P Y (1::List.replicate (p-1) 0)) L t)-
      3*(kdvActualLowMass P g p L Y-truncationValue (kdvFormalLowSeries P Y p L) L t)-
      (3/2)*markedSplitLossTail P g p 2 L Y:=by
  rw[actual_genus_kdv_oriented P g p L hg hp hL hLg hLoss Y hY,
    formalGenus_kdv_truncation_paired P Y p L hp hL t]
  ring

lemma kdv_low_remainder_pairing (P:PsiTheory)(g p L:ℕ)(Y t:ℝ):
    kdvActualLowMass P g p L Y-truncationValue (kdvFormalLowSeries P Y p L) L t=
      ∑j∈Finset.range L,∑s∈Finset.range (p-1),
        if Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s<L then
          (Nat.choose (p-2) s:ℝ)*W P j (s+2) Y*
            (W P (g-j) (p-s) Y/W P g p Y-
              truncationValue (ratioSeries Y (formalHierarchyJet P Y) p j s) L t) else 0:=by
  unfold kdvActualLowMass kdvFormalLowSeries
  simp_rw[truncationValue_sum]
  rw[←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw[←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hc:Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s<L
  · rw[ite_eq_left hc,ite_eq_left hc,ite_eq_left hc,truncationValue_C_mul]
    have hw:smallW P Y j (List.replicate (s+2) 0)=W P j (s+2) Y:=rfl
    rw[hw,markedSplitTerm]
    ring
  · rw[ite_eq_right hc,ite_eq_right hc,ite_eq_right hc,truncationValue_zero,sub_self]

lemma actual_genus_kdv_remainder_bound (P:PsiTheory)(g p L:ℕ)(hg:1≤g)(hp:2≤p)(hL:1≤L)
    (hLg:L≤g+1)(hLoss:2*L≤complexity g p)(Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀)(t:ℝ):
    |genusCorrection P g p Y-truncationValue (formalGenus P Y p) L t|≤
      |profile P g (1::List.replicate (p-1) 0) Y-
        truncationValue (formalProfile P Y (1::List.replicate (p-1) 0)) L t|+
      3*(∑j∈Finset.range L,∑s∈Finset.range (p-1),
        if Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s<L then
          |(Nat.choose (p-2) s:ℝ)*W P j (s+2) Y| *
            |W P (g-j) (p-s) Y/W P g p Y-
              truncationValue (ratioSeries Y (formalHierarchyJet P Y) p j s) L t| else 0)+
      (3/2)*|markedSplitLossTail P g p 2 L Y|:=by
  rw[actual_genus_kdv_remainder_pairing P g p L hg hp hL hLg hLoss Y hY t]
  have hm:|kdvActualLowMass P g p L Y-truncationValue (kdvFormalLowSeries P Y p L) L t|≤
      ∑j∈Finset.range L,∑s∈Finset.range (p-1),
        if Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s<L then
          |(Nat.choose (p-2) s:ℝ)*W P j (s+2) Y| *
            |W P (g-j) (p-s) Y/W P g p Y-
              truncationValue (ratioSeries Y (formalHierarchyJet P Y) p j s) L t| else 0:=by
    rw[kdv_low_remainder_pairing]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro s hs
    by_cases hc:Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s<L
    · rw[ite_eq_left hc,ite_eq_left hc,abs_mul]
    · rw[ite_eq_right hc,ite_eq_right hc,abs_zero]
  have he:|((profile P g (1::List.replicate (p-1) 0) Y-
      truncationValue (formalProfile P Y (1::List.replicate (p-1) 0)) L t)-
      3*(kdvActualLowMass P g p L Y-truncationValue (kdvFormalLowSeries P Y p L) L t))-
      (3/2)*markedSplitLossTail P g p 2 L Y|≤
      |profile P g (1::List.replicate (p-1) 0) Y-
        truncationValue (formalProfile P Y (1::List.replicate (p-1) 0)) L t|+
      3*|kdvActualLowMass P g p L Y-truncationValue (kdvFormalLowSeries P Y p L) L t|+
      (3/2)*|markedSplitLossTail P g p 2 L Y|:=by
    exact (abs_sub _ _).trans (add_le_add
      ((abs_sub _ _).trans_eq (by rw[abs_mul,abs_of_pos (by norm_num:(0:ℝ)<3)]))
      (by rw[abs_mul,abs_of_pos (by norm_num:(0:ℝ)<3/2)]))
  exact he.trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hm (by norm_num:(0:ℝ)≤3))) le_rfl)
end WP.HigherOrder
