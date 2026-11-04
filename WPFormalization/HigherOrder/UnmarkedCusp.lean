import WPFormalization.HigherOrder.CuspRemainderStep
import WPFormalization.HigherOrder.RecursiveRemainderProof
import WPFormalization.Analysis.GevreyTwoWindow
import WPFormalization.Analysis.FiniteExpGevreyTwo
/-! The actual p=0 cusp ratio used by Eq.11.7. The nonempty child profiles
come from the proved C.3 theorem; the signed dilaton moments are controlled
at the zero state using a strictly positive order scale. No p=0 clause is
inferred from C.3's p>=1 statement. The final error is Gevrey two uniformly
on the closed physical parameter interval. -/
noncomputable section
namespace WP.HigherOrder
lemma actual_cusp_remainder_normalized_step_nonnegative (P:PsiTheory) (g p L:ℕ)
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

lemma dilaton_moments_zero_state:
    ∃C M₀:ℝ,0<C ∧ 0<M₀ ∧ ∀M:ℝ,M₀≤M→∀L:ℕ,1≤L→∀i:ℕ,i≤L→
      ∀Y∈Set.Icc (0:ℝ) y₀,
      Summable (fun d:ℕ=>|bCoeff Y d| *(M*L+d+1)^(2*i)) ∧
      (∑'d:ℕ,|bCoeff Y d| *(M*L+d+1)^(2*i))≤C*(M*L)^(2*i):=by
  obtain ⟨B,hB,hbound⟩:=barH_radius_two_coefficient_bound
  let α:ℝ:=Real.log 2/2
  have hα:0<α:=by dsimp[α];positivity
  have hexp:Real.exp α<2:=by
    calc Real.exp α<Real.exp (Real.log 2):=Real.exp_lt_exp.mpr (by dsimp[α];linarith[Real.log_pos (by norm_num : (1:ℝ)<2)])
         _=2:=Real.exp_log (by norm_num)
  obtain ⟨C,hC,hdata⟩:=Analysis.geometric_normalized_scale_bound 2 (2*B/3) α
    (by norm_num) (by positivity) hα hexp
  refine ⟨C,2/α,hC,by positivity,?_⟩
  intro M hM L hL i hi Y hY
  have hM0:0<M:=(by positivity : (0:ℝ)<2/α).trans_le hM
  have hL0:(0:ℝ)<L:=by exact_mod_cast (show 0<L by omega)
  have hMa:2≤α*M:=by have hh:=(div_le_iff₀ hα).mp hM; nlinarith
  have hia:(2*i:ℕ)≤α*(M*L):=by
    have hh:=mul_le_mul_of_nonneg_right hMa hL0.le
    have hiR:(i:ℝ)≤L:=by exact_mod_cast hi
    push_cast
    nlinarith
  have hcoeff:∀d:ℕ,|bCoeff Y d|≤(2*B/3)/(2:ℝ)^d:=by
    intro d
    rw[bCoeff_eq_canonicalDilatonCoefficient]
    cases d with
    | zero=>simp[canonicalDilatonCoefficient];positivity
    | succ d=>
      simp only[canonicalDilatonCoefficient,show 1≤d+1 by omega,ite_true,Nat.add_sub_cancel,
        abs_div,abs_of_pos (by norm_num:(0:ℝ)<3)]
      apply (div_le_div_of_nonneg_right (hbound Y hY d) (by norm_num:(0:ℝ)≤3)).trans_eq
      rw[pow_succ]
      ring
  have he:=hdata (bCoeff Y) hcoeff (2*i) (M*L) (mul_pos hM0 hL0) hia
  simpa only[mul_comm] using he
lemma unmarked_cusp_weighted_uniform_error (P:PsiTheory):
    ∃C B:ℝ,∃M:ℕ,0<C ∧ 0<B ∧ 2≤M ∧ ∀g L:ℕ,2≤g→1≤L→
      ∀Y∈Set.Icc (0:ℝ) y₀,(M*L:ℝ)^2/(complexity g 0:ℝ)≤1→
      |cuspCorrection P g 0 Y-truncationValue (formalCusp P Y 0) L (1/(complexity g 0:ℝ))|≤
        C*B^L*(M*L:ℝ)^(2*L)/(complexity g 0:ℝ)^L:=by
  obtain ⟨Cp,Bp,Mp,hCp,hBp,hMp,hprof,_⟩:=canonical_uniform_recursive_remainders P
  obtain ⟨Cc,Bc,Mc,hCc,hBc,hMc,hcoef,_⟩:=canonical_real_coefficient_bounds P
  obtain ⟨Cm,Mmom,hCm,hMmom,hmoment⟩:=dilaton_moments_zero_state
  obtain ⟨a,ha,hA⟩:=singleMarking_A_uniform_lower
  let M:ℕ:=max (max Mp Mc) ⌈Mmom⌉₊
  have hMpM:Mp≤M:=(le_max_left _ _).trans (le_max_left _ _)
  have hMcM:Mc≤M:=(le_max_right _ _).trans (le_max_left _ _)
  have hM2:2≤M:=hMp.trans hMpM
  have hMpMR:(Mp:ℝ)≤M:=by exact_mod_cast hMpM
  have hMcMR:(Mc:ℝ)≤M:=by exact_mod_cast hMcM
  have hMmomM:Mmom≤(M:ℝ):=(Nat.le_ceil _).trans (by exact_mod_cast (le_max_right (max Mp Mc) ⌈Mmom⌉₊))
  let B:ℝ:=Bp+2*max Bc 1+1
  let C:ℝ:=Cm/a*(Cp+Real.exp 2*Cc)
  have hB:0<B:=by dsimp[B];positivity
  have hC:0<C:=by dsimp[C];positivity
  refine ⟨C,B,M,hC,hB,hM2,?_⟩
  intro g L hg hL Y hY hsmall
  have hs:Stable g 0:=by unfold Stable;omega
  have hsc:1≤complexity g 0:=by unfold complexity;omega
  have hh:(0:ℝ)<complexity g 0:=by exact_mod_cast (show 0<complexity g 0 by omega)
  have hComp:complexity g 1=complexity g 0+1:=by unfold complexity;omega
  have hCompR:(complexity g 1:ℝ)=(complexity g 0:ℝ)+1:=by rw[hComp,Nat.cast_add,Nat.cast_one]
  have hcoef' (i:ℕ)(hi:i<L)(d:ℕ):
      |profileCoefficient P Y [d] i|≤(Cc*Bc^i)*(scalarOrderWeight (M:ℝ) L 0+d+1)^(2*i):=by
    have he:=hcoef i [d] (by simp) Y hY
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (by unfold profileOrderWeight;positivity)
    simp only[profileOrderWeight,scalarOrderWeight,List.sum_cons,List.sum_nil,List.length_cons,
      List.length_nil,Nat.cast_zero,Nat.cast_one,add_zero,zero_add]
    have hm:=mul_le_mul hMcMR (show (i:ℝ)≤L by exact_mod_cast hi.le)
      (Nat.cast_nonneg i) (Nat.cast_nonneg M)
    linarith
  have hprofile' (d:ℕ):
      |profile P g [d] Y-truncationValue (formalProfile P Y [d]) L (1/((complexity g 0:ℝ)+1))|≤
        (Cp*Bp^L)*(scalarOrderWeight (M:ℝ) L 0+d+1)^(2*L)/((complexity g 0:ℝ)+1)^L:=by
    have hs1:Stable g [d].length:=by simp only[List.length_cons,List.length_nil];unfold Stable;omega
    have he:=hprof g [d] (by simp) hs1 (by simp only[List.length_cons,List.length_nil];unfold complexity;omega) L hL Y hY
    simp only[List.length_cons,List.length_nil,zero_add] at he
    have heq:truncationValue (formalProfile P Y [d]) L (1/(complexity g 1:ℝ))=
        ∑j∈Finset.range L,profileCoefficient P Y [d] j/(complexity g 1:ℝ)^j:=by
      simp only[truncationValue,formalProfile,PowerSeries.coeff_mk,div_pow,one_pow,mul_one_div]
    rw[←heq,hCompR] at he
    apply he.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (by unfold profileOrderWeight;positivity)
    simp only[profileOrderWeight,scalarOrderWeight,List.sum_cons,List.sum_nil,List.length_cons,
      List.length_nil,Nat.cast_zero,Nat.cast_one,add_zero,zero_add]
    have hm:=mul_le_mul_of_nonneg_right hMpMR (Nat.cast_nonneg L)
    linarith
  have hMom (i:ℕ)(hi:i≤L):
      Summable (fun d:ℕ=>|bCoeff Y d| *(scalarOrderWeight (M:ℝ) L 0+d+1)^(2*i)) ∧
      (∑'d:ℕ,|bCoeff Y d| *(scalarOrderWeight (M:ℝ) L 0+d+1)^(2*i))≤
        Cm*scalarOrderWeight (M:ℝ) L 0^(2*i):=by
    simpa only[scalarOrderWeight,Nat.cast_zero,zero_add] using hmoment M hMmomM L hL i hi Y hY
  have hMR:(2:ℝ)≤M:=by exact_mod_cast hM2
  have he:=actual_cusp_remainder_normalized_step_nonnegative P g 0 L hs hL Y hY
    M (Cp*Bp^L) Cm 1 hMR (by positivity) hCm.le le_rfl hh
    (by simpa only[scalarOrderWeight,Nat.cast_zero,zero_add] using hsmall)
    (fun i=>Cc*Bc^i) (fun i=>by positivity)
    (by simpa only[List.replicate_zero] using hcoef')
    (by simpa only[List.replicate_zero] using hprofile') hMom
  have hAi:|(A Y)⁻¹|≤1/a:=by
    rw[abs_inv,abs_of_pos (ha.trans_le (hA Y hY)),←one_div]
    exact one_div_le_one_div_of_le ha (hA Y hY)
  have hsum:(∑i∈Finset.range L,(Cc*Bc^i)/((L-i).factorial:ℝ))≤
      Cc*(2*max Bc 1)^L:=by
    rw[show (∑i∈Finset.range L,(Cc*Bc^i)/((L-i).factorial:ℝ))=
      Cc*(∑i∈Finset.range L,Bc^i/((L-i).factorial:ℝ)) by rw[Finset.mul_sum];apply Finset.sum_congr rfl;intros;ring]
    exact mul_le_mul_of_nonneg_left (finite_exp_geometric_convolution_bound Bc hBc.le L) hCc.le
  have hBpB:Bp≤B:=by dsimp[B];linarith[le_max_right Bc 1]
  have hBcB:2*max Bc 1≤B:=by dsimp[B];linarith
  have hbase:Cp*Bp^L+Real.exp (2*1)*(∑i∈Finset.range L,(Cc*Bc^i)/((L-i).factorial:ℝ))≤
      (Cp+Real.exp 2*Cc)*B^L:=by
    norm_num only[mul_one]
    calc _≤Cp*B^L+Real.exp 2*(Cc*B^L):=by
           apply add_le_add
           · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hBp.le hBpB L) hCp.le
           · apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
             exact hsum.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hBcB L) hCc.le)
         _=_:=by ring
  apply he.trans
  have hcoefmax:|(A Y)⁻¹| *Cm≤Cm/a:=by convert mul_le_mul_of_nonneg_right hAi hCm.le using 1 <;>ring
  have hpref:=mul_le_mul hcoefmax hbase (by positivity) (by positivity:0≤Cm/a)
  have hnn:0≤ scalarOrderWeight (M:ℝ) L 0^(2*L)/(complexity g 0:ℝ)^L:=by
    apply div_nonneg (pow_nonneg (by unfold scalarOrderWeight;positivity) _) (pow_nonneg hh.le _)
  calc
    _ = (|(A Y)⁻¹| *Cm*(Cp*Bp^L+Real.exp (2*1)*∑i∈Finset.range L,Cc*Bc^i/((L-i).factorial:ℝ)))*
        (scalarOrderWeight (M:ℝ) L 0^(2*L)/(complexity g 0:ℝ)^L):=by ring
    _ ≤ (Cm/a*((Cp+Real.exp 2*Cc)*B^L))*
        (scalarOrderWeight (M:ℝ) L 0^(2*L)/(complexity g 0:ℝ)^L):=mul_le_mul_of_nonneg_right hpref hnn
    _ = _:=by simp only[scalarOrderWeight,Nat.cast_zero,zero_add,C];ring
lemma scaled_order_power_factorial_sq (M:ℝ)(hM:0≤M)(L:ℕ):
    (M*L)^(2*L)≤(M^2*(Real.exp 1)^2)^L*(L.factorial:ℝ)^2:=by
  have he:=pow_le_pow_left₀ (pow_nonneg (Nat.cast_nonneg L) L)
    (Analysis.order_pow_le_exp_factorial L) 2
  calc
    _=(M^2)^L*((L:ℝ)^L)^2:=by simp only[mul_pow,pow_mul];ring
    _≤(M^2)^L*((Real.exp 1)^L*(L.factorial:ℝ))^2:=
      mul_le_mul_of_nonneg_left he (by positivity)
    _=_:=by simp only[mul_pow,pow_mul];ring

lemma unmarked_cusp_uniform_gevrey_two (P:PsiTheory):
    ∃C B c H:ℝ,0<C ∧ 0<B ∧ 0<c ∧ 0<H ∧ ∀g K:ℕ,2≤g→
      H≤(complexity g 0:ℝ)→(K:ℝ)≤c*Real.sqrt (complexity g 0:ℝ)→
      ∀Y∈Set.Icc (0:ℝ) y₀,
      |cuspCorrection P g 0 Y-
        ∑j∈Finset.range (K+1),cuspCoefficient P Y 0 j/(complexity g 0:ℝ)^j|≤
          C*B^(K+1)*((K+1).factorial:ℝ)^2/(complexity g 0:ℝ)^(K+1):=by
  obtain ⟨C,B,M,hC,hB,hM,herr⟩:=unmarked_cusp_weighted_uniform_error P
  have hMR:(0:ℝ)<M:=by exact_mod_cast (show 0<M by omega)
  obtain ⟨c,H,hc,hc1,hH,hwindow⟩:=Analysis.gevreyTwo_cauchy_window ((M:ℝ)^2/4) 1
    (by positivity) (by norm_num)
  refine ⟨C,B*((M:ℝ)^2*(Real.exp 1)^2),c,H,hC,by positivity,hc,hH,?_⟩
  intro g K hg hh hK Y hY
  have hh0:(0:ℝ)<complexity g 0:=hH.trans_le hh
  have hw:=hwindow (complexity g 0:ℝ) hh K hK
  have hsmall:((M:ℝ)*(K+1:ℕ))^2/(complexity g 0:ℝ)≤1:=by
    apply (div_le_one hh0).mpr
    push_cast at hw ⊢
    nlinarith
  have he:=herr g (K+1) hg (by omega) Y hY hsmall
  have hpoly:truncationValue (formalCusp P Y 0) (K+1) (1/(complexity g 0:ℝ))=
      ∑j∈Finset.range (K+1),cuspCoefficient P Y 0 j/(complexity g 0:ℝ)^j:=by
    simp only[truncationValue,formalCusp,PowerSeries.coeff_mk,div_pow,one_pow,mul_one_div]
  rw[hpoly] at he
  apply he.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply (mul_le_mul_of_nonneg_left (scaled_order_power_factorial_sq M hMR.le (K+1))
    (show 0≤C*B^(K+1) by positivity)).trans_eq
  rw[mul_pow]
  ring
end WP.HigherOrder
