import WPFormalization.HigherOrder.ShiftRemainder
import WPFormalization.HigherOrder.CuspRemainderAlgebra
import WPFormalization.HigherOrder.CuspRemainderIdentity
import WPFormalization.Analysis.NormalizedMomentScale
/-! The genuine all-order cusp step in the finite-genus induction.
The actual child profile remainder is paired with its own complexity h+1;
C.4, the real normalized signed-b moments, and the uniform inverse-A bound
are all instantiated. Only the current profile induction hypothesis
remains in the public uniform step. This does not assert the full C.3 target. -/
noncomputable section
namespace WP.HigherOrder
lemma actual_cusp_remainder_hasSum_all (P:PsiTheory) (g p L:ℕ) (hs:Stable g p)
    (Y t:ℝ) (hY:Y∈Set.Icc (0:ℝ) y₀) :
    HasSum (fun d:ℕ=>(A Y)⁻¹*bCoeff Y d*
      (profile P g (d::List.replicate p 0) Y-
        truncationValue (complexityShift (-1) (formalProfile P Y (d::List.replicate p 0))) L t))
      (cuspCorrection P g p Y-truncationValue (formalCusp P Y p) L t) :=by
  let f:ℕ→ℝ:=fun d=>(A Y)⁻¹*bCoeff Y d*(profile P g (d::List.replicate p 0) Y-
    truncationValue (complexityShift (-1) (formalProfile P Y (d::List.replicate p 0))) L t)
  have h0:f 0=0:=by simp[f,bCoeff]
  have hh:HasSum (fun d:ℕ=>f (d+1))
      (cuspCorrection P g p Y-truncationValue (formalCusp P Y p) L t):=
    actual_cusp_remainder_hasSum P g p L hs Y t hY
  have hi:=(hasSum_nat_add_iff (f:=f) 1).mp hh
  simpa only[Finset.sum_range_one,h0,add_zero] using hi

lemma actual_cusp_remainder_normalized_step (P:PsiTheory) (g p L:ℕ) (hp:1 ≤ p)
    (hs:Stable g p) (hL:1 ≤ L) (Y:ℝ) (hY:Y∈Set.Icc (0:ℝ) y₀)
    (M E Cm δ:ℝ) (hM:2 ≤ M) (hE:0 ≤ E) (hCm:0 ≤ Cm) (hδ:δ ≤ 1)
    (hh:0<(complexity g p:ℝ)) (hsmall:scalarOrderWeight M L p^2/(complexity g p:ℝ) ≤ δ)
    (e:ℕ→ℝ) (he:∀i:ℕ,0 ≤ e i)
    (hcoef:∀i:ℕ,i<L→∀d:ℕ,|profileCoefficient P Y (d::List.replicate p 0) i| ≤
      e i*(scalarOrderWeight M L p+d+1)^(2*i))
    (hprofile:∀d:ℕ,|profile P g (d::List.replicate p 0) Y-
      truncationValue (formalProfile P Y (d::List.replicate p 0)) L (1/((complexity g p:ℝ)+1))| ≤
      E*(scalarOrderWeight M L p+d+1)^(2*L)/((complexity g p:ℝ)+1)^L)
    (hmom:∀i:ℕ,i ≤ L→Summable (fun d:ℕ=>|bCoeff Y d| *(scalarOrderWeight M L p+d+1)^(2*i)) ∧
      (∑'d:ℕ,|bCoeff Y d| *(scalarOrderWeight M L p+d+1)^(2*i)) ≤ Cm*scalarOrderWeight M L p^(2*i)) :
    |cuspCorrection P g p Y-truncationValue (formalCusp P Y p) L (1/(complexity g p:ℝ))| ≤
      |(A Y)⁻¹| *Cm*scalarOrderWeight M L p^(2*L)/(complexity g p:ℝ)^L*
        (E+Real.exp (2*δ)*(∑i∈Finset.range L,e i/((L-i).factorial:ℝ))) :=by
  let h:ℝ:=complexity g p
  let S:=scalarOrderWeight M L p
  have hpR:(1:ℝ) ≤ p:=by exact_mod_cast hp
  have hLR:(1:ℝ) ≤ L:=by exact_mod_cast hL
  have hMS:2*(L:ℝ) ≤ S:=by
    have hm:=mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg L : (0:ℝ) ≤ L)
    dsimp[S,scalarOrderWeight]
    linarith
  have hS:0<S:=by linarith
  have hpref (d:ℕ) :
      |profile P g (d::List.replicate p 0) Y-
        truncationValue (complexityShift (-1) (formalProfile P Y (d::List.replicate p 0))) L (1/h)| ≤
      (E/h^L)*(S+d+1)^(2*L)+(Real.exp (2*δ)*S^(2*L)/h^L)*
        ∑i∈Finset.range L,(e i/(S^(2*i)*((L-i).factorial:ℝ)))*(S+d+1)^(2*i):=by
    let e':ℕ→ℝ:=fun i=>e i*(S+d+1)^(2*i)/S^(2*i)
    have he':∀i:ℕ,0 ≤ e' i:=by intro i;have hei:=he i;dsimp[e'];positivity
    have hf:∀i:ℕ,i<L→|PowerSeries.coeff i (formalProfile P Y (d::List.replicate p 0))| ≤ e' i*S^(2*i):=by
      intro i hi
      simp only[formalProfile,PowerSeries.coeff_mk]
      apply (hcoef i hi d).trans_eq
      dsimp[e']
      field_simp[hS.ne'] <;> rfl
    have hshift:=shift_truncation_remainder_bound (formalProfile P Y (d::List.replicate p 0)) e' L hL
      (-1) S h δ (by norm_num;exact_mod_cast hL) hMS hh hsmall hδ he' hf
    norm_num only[sub_neg_eq_add] at hshift
    have hprof:=hprofile d
    have hprof':|profile P g (d::List.replicate p 0) Y-
        truncationValue (formalProfile P Y (d::List.replicate p 0)) L (1/(h+1))| ≤
        (E/h^L)*(S+d+1)^(2*L):=by
      have hden:h^L ≤ (h+1)^L:=pow_le_pow_left₀ hh.le (by linarith) _
      have ht:E*(S+d+1)^(2*L)/(h+1)^L ≤ E*(S+d+1)^(2*L)/h^L:=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hh _) hden
      exact hprof.trans (ht.trans_eq (by ring))
    have hsplit:profile P g (d::List.replicate p 0) Y-
        truncationValue (complexityShift (-1) (formalProfile P Y (d::List.replicate p 0))) L (1/h)=
      (profile P g (d::List.replicate p 0) Y-
        truncationValue (formalProfile P Y (d::List.replicate p 0)) L (1/(h+1)))+
      (truncationValue (formalProfile P Y (d::List.replicate p 0)) L (1/(h+1))-
        truncationValue (complexityShift (-1) (formalProfile P Y (d::List.replicate p 0))) L (1/h)):=by ring
    rw[hsplit]
    apply (abs_add_le _ _).trans
    apply (add_le_add hprof' hshift).trans_eq
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    dsimp[e']
    ring
  have hactual:=actual_cusp_remainder_hasSum_all P g p L hs Y (1/h) hY
  apply weighted_cusp_remainder_algebra (bCoeff Y) _ _ |(A Y)⁻¹| E (Real.exp (2*δ)) S h Cm e L
    (abs_nonneg _) hE (Real.exp_pos _).le hS hh hCm he hactual hmom
  intro d
  rw[abs_mul,abs_mul]
  apply (mul_le_mul_of_nonneg_left (hpref d) (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq
  simp only[mul_add,Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i hi
    ring

lemma actual_cusp_uniform_remainder_step (P:PsiTheory) :
    ∃D B:ℝ,∃M₀:ℕ,0<D ∧ 0<B ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀g p L:ℕ,1 ≤ p→Stable g p→1 ≤ L→1 ≤ complexity g p→
    ∀Y∈Set.Icc (0:ℝ) y₀,scalarOrderWeight (M:ℝ) L p^2/(complexity g p:ℝ) ≤ 1→
    ∀E:ℝ,0 ≤ E→
    (∀d:ℕ,|profile P g (d::List.replicate p 0) Y-
      truncationValue (formalProfile P Y (d::List.replicate p 0)) L (1/(complexity g (p+1):ℝ))| ≤
      E*profileOrderWeight (M:ℝ) L (d::List.replicate p 0)^(2*L)/(complexity g (p+1):ℝ)^L)→
    |cuspCorrection P g p Y-truncationValue (formalCusp P Y p) L (1/(complexity g p:ℝ))| ≤
      D*(E+∑i∈Finset.range L,B^i/((L-i).factorial:ℝ))*
        scalarOrderWeight (M:ℝ) L p^(2*L)/(complexity g p:ℝ)^L :=by
  obtain ⟨C,B,Mb,hC,hB,hMb,hprof,hscal⟩:=canonical_real_coefficient_bounds P
  obtain ⟨Cm,Mmom,hCm,hMmom,hmoment⟩:=Analysis.canonical_growing_order_scale_bounds
  obtain ⟨a,ha,hA⟩:=singleMarking_A_uniform_lower
  let M₀:ℕ:=max Mb ⌈Mmom⌉₊
  have hM₀:2 ≤ M₀:=hMb.trans (le_max_left _ _)
  let D:ℝ:=Cm/a*(1+C*Real.exp 2)
  have hD:0<D:=by dsimp[D];positivity
  refine ⟨D,B,M₀,hD,hB,hM₀,?_⟩
  intro M hM g p L hp hs hL hh Y hY hsmall E hE hprofile
  have hMtwo:2 ≤ M:=hM₀.trans hM
  have hMR:(2:ℝ) ≤ M:=by exact_mod_cast hMtwo
  have hMbM:Mb ≤ M:=(le_max_left _ _).trans hM
  have hMbMR:(Mb:ℝ) ≤ M:=by exact_mod_cast hMbM
  have hMmomM:Mmom ≤ (M:ℝ):=(Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans hM))
  have hhR:(0:ℝ)<complexity g p:=by exact_mod_cast (show 0<complexity g p by omega)
  have hComp:complexity g (p+1)=complexity g p+1:=by unfold complexity Stable at *;omega
  have hCompR:(complexity g (p+1):ℝ)=(complexity g p:ℝ)+1:=by rw[hComp,Nat.cast_add,Nat.cast_one]
  have hcoef (i:ℕ) (hi:i<L) (d:ℕ):
      |profileCoefficient P Y (d::List.replicate p 0) i| ≤
      (C*B^i)*(scalarOrderWeight (M:ℝ) L p+d+1)^(2*i):=by
    have hb:=hprof i (d::List.replicate p 0) (by simp) Y hY
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (by unfold profileOrderWeight;positivity)
    have hm:=mul_le_mul hMbMR (show (i:ℝ) ≤ L by exact_mod_cast hi.le)
      (Nat.cast_nonneg i : (0:ℝ) ≤ i) (Nat.cast_nonneg M : (0:ℝ) ≤ M)
    simp only[profileOrderWeight,scalarOrderWeight,List.sum_cons,List.sum_replicate,nsmul_zero,
      add_zero,List.length_cons,List.length_replicate,Nat.cast_add,Nat.cast_one]
    linarith
  have hprofile':∀d:ℕ,|profile P g (d::List.replicate p 0) Y-
      truncationValue (formalProfile P Y (d::List.replicate p 0)) L (1/((complexity g p:ℝ)+1))| ≤
      E*(scalarOrderWeight (M:ℝ) L p+d+1)^(2*L)/((complexity g p:ℝ)+1)^L:=by
    intro d
    have hd:=hprofile d
    rw[hCompR] at hd
    convert hd using 2
    simp only[profileOrderWeight,scalarOrderWeight,List.sum_cons,List.sum_replicate,nsmul_zero,
      add_zero,List.length_cons,List.length_replicate,Nat.cast_add,Nat.cast_one]
    ring
  have hMom (i:ℕ) (hi:i ≤ L):
      Summable (fun d:ℕ=>|bCoeff Y d| *(scalarOrderWeight (M:ℝ) L p+d+1)^(2*i)) ∧
      (∑'d:ℕ,|bCoeff Y d| *(scalarOrderWeight (M:ℝ) L p+d+1)^(2*i)) ≤ Cm*scalarOrderWeight (M:ℝ) L p^(2*i):=by
    have hh':=hmoment (M:ℝ) hMmomM L 0 p (2*i) hp (by omega) Y hY
    constructor
    · simpa only[bCoeff_eq_canonicalDilatonCoefficient,scalarOrderWeight,Nat.cast_zero,zero_add,mul_comm] using hh'.2.1
    · simpa only[bCoeff_eq_canonicalDilatonCoefficient,scalarOrderWeight,Nat.cast_zero,zero_add,mul_comm] using hh'.2.2.2
  have hcusp:=actual_cusp_remainder_normalized_step P g p L hp hs hL Y hY (M:ℝ) E Cm 1 hMR hE hCm.le
    le_rfl hhR hsmall (fun i=>C*B^i) (fun i=>by positivity) hcoef hprofile' hMom
  norm_num only[mul_one] at hcusp
  have hsum:(∑i∈Finset.range L,C*B^i/((L-i).factorial:ℝ))=
      C*(∑i∈Finset.range L,B^i/((L-i).factorial:ℝ)):=by
    rw[Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw[hsum] at hcusp
  have hAp:0<A Y:=ha.trans_le (hA Y hY)
  have hAi:|(A Y)⁻¹| ≤ 1/a:=by
    rw[abs_inv,abs_of_pos hAp,←one_div]
    exact one_div_le_one_div_of_le ha (hA Y hY)
  have hsum0:0 ≤ ∑i∈Finset.range L,B^i/((L-i).factorial:ℝ):=Finset.sum_nonneg (fun i hi=>by positivity)
  have hbase:(E+Real.exp 2*(C*(∑i∈Finset.range L,B^i/((L-i).factorial:ℝ)))) ≤
      (1+C*Real.exp 2)*(E+∑i∈Finset.range L,B^i/((L-i).factorial:ℝ)):=by
    have hcross:=mul_nonneg (mul_nonneg hC.le (Real.exp_pos 2).le) hE
    nlinarith
  have hSS:0 ≤ scalarOrderWeight (M:ℝ) L p^(2*L)/(complexity g p:ℝ)^L:=by
    apply div_nonneg (pow_nonneg (by unfold scalarOrderWeight;positivity) _) (pow_nonneg hhR.le _)
  apply hcusp.trans
  have hcoeff:|(A Y)⁻¹| *Cm ≤ Cm/a:=by
    convert mul_le_mul_of_nonneg_right hAi hCm.le using 1 <;>ring
  have hproduct:=mul_le_mul hcoeff hbase (by positivity)
    (by positivity:0 ≤ Cm/a)
  have hfinal:=mul_le_mul_of_nonneg_right hproduct hSS
  dsimp[D]
  convert hfinal using 1 <;>ring

lemma finite_exp_geometric_convolution_bound (B:ℝ) (hB:0 ≤ B) (L:ℕ) :
    (∑i∈Finset.range L,B^i/((L-i).factorial:ℝ)) ≤ (2*max B 1)^L:=by
  let R:=max B 1
  have hR:1 ≤ R:=le_max_right _ _
  have hR0:0 ≤ R:=by linarith
  have hterm (i:ℕ) (hi:i∈Finset.range L):B^i/((L-i).factorial:ℝ) ≤ R^L:=by
    have hp:B^i ≤ R^L:=(pow_le_pow_left₀ hB (le_max_left _ _) _).trans
      (pow_le_pow_right₀ hR (Finset.mem_range.mp hi).le)
    have hfac:(1:ℝ) ≤ (L-i).factorial:=by exact_mod_cast (Nat.factorial_pos (L-i))
    apply (div_le_iff₀ (by positivity)).2
    nlinarith[pow_nonneg hR0 L]
  calc
    _ ≤ ∑i∈Finset.range L,R^L:=Finset.sum_le_sum hterm
    _=(L:ℝ)*R^L:=by simp only[Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    _ ≤ (2:ℝ)^L*R^L:=mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Nat.le_of_lt L.lt_two_pow_self)) (pow_nonneg hR0 _)
    _=_:=by rw[←mul_pow]

lemma actual_cusp_uniform_remainder_step_exponential (P:PsiTheory) :
    ∃D B:ℝ,∃M₀:ℕ,0<D ∧ 0<B ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀g p L:ℕ,1 ≤ p→Stable g p→1 ≤ L→1 ≤ complexity g p→
    ∀Y∈Set.Icc (0:ℝ) y₀,scalarOrderWeight (M:ℝ) L p^2/(complexity g p:ℝ) ≤ 1→
    ∀E:ℝ,0 ≤ E→
    (∀d:ℕ,|profile P g (d::List.replicate p 0) Y-
      truncationValue (formalProfile P Y (d::List.replicate p 0)) L (1/(complexity g (p+1):ℝ))| ≤
      E*profileOrderWeight (M:ℝ) L (d::List.replicate p 0)^(2*L)/(complexity g (p+1):ℝ)^L)→
    |cuspCorrection P g p Y-truncationValue (formalCusp P Y p) L (1/(complexity g p:ℝ))| ≤
      D*(E+B^L)*scalarOrderWeight (M:ℝ) L p^(2*L)/(complexity g p:ℝ)^L :=by
  obtain ⟨D,B,M₀,hD,hB,hM,hs⟩:=actual_cusp_uniform_remainder_step P
  refine ⟨D,2*max B 1,M₀,hD,by positivity,hM,?_⟩
  intro M hM' g p L hp hst hL hh Y hY hsmall E hE hprofile
  have he:=hs M hM' g p L hp hst hL hh Y hY hsmall E hE hprofile
  apply he.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by unfold scalarOrderWeight;positivity)
  apply mul_le_mul_of_nonneg_left _ hD.le
  exact add_le_add le_rfl (finite_exp_geometric_convolution_bound B hB.le L)
end WP.HigherOrder
