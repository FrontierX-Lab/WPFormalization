import WPFormalization.HigherOrder.CuspRemainderStep
import WPFormalization.HigherOrder.CanonicalCoefficientScales
import WPFormalization.HigherOrder.LinearRemainderAtoms
import WPFormalization.HigherOrder.LossOneRemainder
import WPFormalization.HigherOrder.ProductRemainderBounds
import WPFormalization.HigherOrder.ProductCoefficientBounds
import WPFormalization.Marked.GenusExtensions
/-! The actual merger atom at every order, with C.4 and the uniform A bound
instantiated. Lower-order actual cusp/profile errors enter linearly; the
known shift forcing is an explicit finite factorial convolution. The
parent scale S and child scale T remain separate for kernel integration.
This is an induction step for one atom, not the full profile remainder. -/
noncomputable section
namespace WP.HigherOrder
lemma actual_merger_atom_uniform_remainder_step (P:PsiTheory) :
    ∃A₀ C B:ℝ,∃M₀:ℕ,0<A₀ ∧ 0<C ∧ 0<B ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀g p L:ℕ,2 ≤ g→2 ≤ p→2 ≤ L→∀d:List ℕ,d.length=p-1→
    ∀S T:ℝ,2*(L:ℝ) ≤ S→scalarOrderWeight (M:ℝ) (L-1) (p-1) ≤ T→
    profileOrderWeight (M:ℝ) (L-1) d ≤ T→
    S^2/(complexity g p:ℝ) ≤ 1→∀Y∈Set.Icc (0:ℝ) y₀,
    ∀Cq:ℝ,0 ≤ Cq→∀E:ℕ→ℝ,(∀i:ℕ,0 ≤ E i)→
    (|cuspCorrection P g (p-1) Y-truncationValue (formalCusp P Y (p-1)) (L-1) (1/((complexity g p:ℝ)-1))| ≤
      Cq*T^(2*(L-1))/((complexity g p:ℝ)-1)^(L-1))→
    (∀j:ℕ,1 ≤ j→j ≤ L-1→|profile P g d Y-truncationValue (formalProfile P Y d) j (1/((complexity g p:ℝ)-1))| ≤
      E j*T^(2*j)/((complexity g p:ℝ)-1)^j)→
    |(W P g (p-1) Y/W P g p Y)*profile P g d Y-
      truncationValue (PowerSeries.C (A Y)*complexityShift 1
        (PowerSeries.X*(formalCusp P Y (p-1)*formalProfile P Y d))) L (1/(complexity g p:ℝ))| ≤
      (A₀*Real.exp 2/(complexity g p:ℝ)^L)*
      ((Cq+∑i∈Finset.range (L-1),(C*B^i)*E (L-1-i))*T^(2*(L-1))+
        S^(2*(L-1))*(∑i∈Finset.range (L-1),(2*C^2)*(2*max B 1)^i*T^(2*i)/(S^(2*i)*((L-1-i).factorial:ℝ)))) :=by
  obtain ⟨C,B,M₀,hC,hB,hM₀,hcoef⟩:=canonical_coefficients_on_common_scale P
  obtain ⟨A₀,hA₀,hUpper⟩:=genusExtension_A_uniform_upper
  refine ⟨A₀,C,B,M₀,hA₀,hC,hB,hM₀,?_⟩
  intro M hM g p L hg hp hL d hlen S T hS hTs hTp hsmall Y hY Cq hCq E hE hCusp hProfile
  have hd:1 ≤ d.length:=by omega
  have hpc:1 ≤ p-1:=by omega
  have hMtwo:2 ≤ M:=hM₀.trans hM
  have hT0:0 ≤ T:=(show 0 ≤ scalarOrderWeight (M:ℝ) (L-1) (p-1) by unfold scalarOrderWeight;positivity).trans hTs
  have hhR:(1:ℝ)<complexity g p:=by exact_mod_cast (show 1<complexity g p by unfold complexity;omega)
  have hn:0<(complexity g p:ℝ)-1:=by linarith
  have hq:1 ≤ L-1:=by omega
  have hdata (i:ℕ) (hi:i ≤ L-1):
      |PowerSeries.coeff i (formalCusp P Y (p-1))| ≤ C*B^i*T^(2*i) ∧
      |PowerSeries.coeff i (formalGenus P Y (p-1))| ≤ C*B^i*T^(2*i) ∧
      |PowerSeries.coeff i (formalProfile P Y d)| ≤ C*B^i*T^(2*i):=
    hcoef M hM (p-1) hpc d hd (L-1) T hTs hTp i hi Y hY
  have hy:|profile P g d Y| ≤ 1:=by
    have hb:=(profile_monotone P g d (by unfold Stable;omega) 0 (by omega) Y hY).2
    simpa only[abs_of_nonneg hb.1] using hb.2
  have hprod:=product_remainder_scaled_bound (cuspCorrection P g (p-1) Y) (profile P g d Y)
    (formalCusp P Y (p-1)) (formalProfile P Y d) (L-1) hq T ((complexity g p:ℝ)-1) Cq
    (fun i=>C*B^i) E hT0 hn hCq (fun i=>by positivity) hE hy hCusp
    (fun i hi=>(hdata i hi.le).1) hProfile
  have hprodcoeff (i:ℕ) (hi:i<L-1):
      |PowerSeries.coeff i (formalCusp P Y (p-1)*formalProfile P Y d)| ≤
      ((2*C^2)*(2*max B 1)^i)*T^(2*i):=by
    exact product_coeff_scaled_exponential _ _ i C B T hC.le hB.le hT0
      (fun j hj=>(hdata j (hj.trans hi.le)).1) (fun j hj=>(hdata j (hj.trans hi.le)).2.2)
  have ha:|A Y| ≤ A₀:=by
    have hAp:0<A Y:=by unfold A;exact div_pos (Analysis.barH_one_re_pos Y hY) (by norm_num)
    rw[abs_of_pos hAp]
    exact hUpper Y hY
  have hR0:0 ≤ Cq+∑i∈Finset.range (L-1),(C*B^i)*E (L-1-i):=by
    apply add_nonneg hCq
    exact Finset.sum_nonneg (fun i hi=>mul_nonneg (by positivity) (hE _))
  have hb:=loss_one_atom_remainder_scaled_bound (cuspCorrection P g (p-1) Y) (profile P g d Y)
    (A Y) A₀ 1 S T (complexity g p:ℝ) 1
    (Cq+∑i∈Finset.range (L-1),(C*B^i)*E (L-1-i)) (formalCusp P Y (p-1)) (formalProfile P Y d)
    (fun i=>(2*C^2)*(2*max B 1)^i) L (by omega) hA₀.le ha (by norm_num;exact_mod_cast (show 1 ≤ L by omega))
    hS hT0 (by linarith) hsmall le_rfl hR0 (fun i=>by positivity)
    (by convert hprod using 1 <;>ring) hprodcoeff
  rw[merger_prefactor_eq_cusp P g p hg hp Y hY]
  simpa only[mul_one,mul_assoc] using hb

lemma actual_merger_atom_remainder_step_exponential (P:PsiTheory) :
    ∃D B:ℝ,∃M₀:ℕ,0<D ∧ 0<B ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀g p L:ℕ,2 ≤ g→2 ≤ p→2 ≤ L→∀d:List ℕ,d.length=p-1→
    ∀S T:ℝ,2*(L:ℝ) ≤ S→S ≤ T→scalarOrderWeight (M:ℝ) (L-1) (p-1) ≤ T→
    profileOrderWeight (M:ℝ) (L-1) d ≤ T→S^2/(complexity g p:ℝ) ≤ 1→∀Y∈Set.Icc (0:ℝ) y₀,
    ∀Cq:ℝ,0 ≤ Cq→∀E:ℕ→ℝ,(∀i:ℕ,0 ≤ E i)→
    (|cuspCorrection P g (p-1) Y-truncationValue (formalCusp P Y (p-1)) (L-1) (1/((complexity g p:ℝ)-1))| ≤
      Cq*T^(2*(L-1))/((complexity g p:ℝ)-1)^(L-1))→
    (∀j:ℕ,1 ≤ j→j ≤ L-1→|profile P g d Y-truncationValue (formalProfile P Y d) j (1/((complexity g p:ℝ)-1))| ≤
      E j*T^(2*j)/((complexity g p:ℝ)-1)^j)→
    |(W P g (p-1) Y/W P g p Y)*profile P g d Y-
      truncationValue (PowerSeries.C (A Y)*complexityShift 1
        (PowerSeries.X*(formalCusp P Y (p-1)*formalProfile P Y d))) L (1/(complexity g p:ℝ))| ≤
      D*T^(2*(L-1))/(complexity g p:ℝ)^L*
        (Cq+∑i∈Finset.range (L-1),B^i*E (L-1-i)+B^L) :=by
  obtain ⟨A₀,C,B,M₀,hA₀,hC,hB,hM₀,hs⟩:=actual_merger_atom_uniform_remainder_step P
  let Bp:=2*max B 1
  let B':=2*max Bp 1
  let K:=1+C+2*C^2
  have hBp:0<Bp:=by dsimp[Bp];positivity
  have hB':0<B':=by dsimp[B'];positivity
  have hBBp:B ≤ Bp:=by dsimp[Bp];linarith[le_max_left B 1,le_max_right B 1]
  have hBpB':Bp ≤ B':=by dsimp[B'];linarith[le_max_left Bp 1,le_max_right Bp 1]
  have hB'1:1 ≤ B':=by dsimp[B'];linarith[le_max_right Bp 1]
  have hK:0<K:=by dsimp[K];positivity
  refine ⟨A₀*Real.exp 2*K,B',M₀,by positivity,hB',hM₀,?_⟩
  intro M hM g p L hg hp hL d hlen S T hS hST hTs hTp hsmall Y hY Cq hCq E hE hCs hPs
  have hSp:0<S:=by
    have hLR:(2:ℝ) ≤ L:=by exact_mod_cast hL
    linarith
  have hT:0 ≤ T:=hSp.le.trans hST
  have hh:(0:ℝ)<complexity g p:=by exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have hb:=hs M hM g p L hg hp hL d hlen S T hS hTs hTp hsmall Y hY Cq hCq E hE hCs hPs
  have hmixed:=mixed_scale_convolution_bound S T hSp hST (L-1)
    (fun i=>(2*C^2)*Bp^i) (fun i=>by positivity)
  have hforce:(∑i∈Finset.range (L-1),(2*C^2)*Bp^i/((L-1-i).factorial:ℝ)) ≤ (2*C^2)*B'^L:=by
    have heq:(∑i∈Finset.range (L-1),(2*C^2)*Bp^i/((L-1-i).factorial:ℝ))=
        (2*C^2)*(∑i∈Finset.range (L-1),Bp^i/((L-1-i).factorial:ℝ)):=by
      rw[Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw[heq]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (finite_exp_geometric_convolution_bound Bp hBp.le (L-1)).trans
      (by change B'^(L-1) ≤ B'^L; exact pow_le_pow_right₀ hB'1 (by omega))
  have hconv:(∑i∈Finset.range (L-1),(C*B^i)*E (L-1-i)) ≤
      C*(∑i∈Finset.range (L-1),B'^i*E (L-1-i)):=by
    rw[Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hpB:=pow_le_pow_left₀ hB.le (hBBp.trans hBpB') i
    convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpB hC.le) (hE (L-1-i)) using 1 <;>ring
  have hconv0:0 ≤ ∑i∈Finset.range (L-1),B'^i*E (L-1-i):=Finset.sum_nonneg (fun i hi=>mul_nonneg (by positivity) (hE _))
  have hforcing:(Cq+∑i∈Finset.range (L-1),(C*B^i)*E (L-1-i))+
      (∑i∈Finset.range (L-1),(2*C^2)*Bp^i/((L-1-i).factorial:ℝ)) ≤
      K*(Cq+∑i∈Finset.range (L-1),B'^i*E (L-1-i)+B'^L):=by
    have hK1:(1:ℝ) ≤ K:=by dsimp[K];nlinarith
    have hKC:C ≤ K:=by dsimp[K];nlinarith
    have hK2:2*C^2 ≤ K:=by dsimp[K];linarith
    have h1:=mul_le_mul_of_nonneg_right hK1 hCq
    have h2:=mul_le_mul_of_nonneg_right hKC hconv0
    have h3:=mul_le_mul_of_nonneg_right hK2 (pow_nonneg hB'.le L)
    nlinarith
  have hscaled:=mul_le_mul_of_nonneg_right hforcing (pow_nonneg hT (2*(L-1)))
  let Ro:=Cq+∑i∈Finset.range (L-1),(C*B^i)*E (L-1-i)
  let Fo:=∑i∈Finset.range (L-1),(2*C^2)*Bp^i/((L-1-i).factorial:ℝ)
  let Rn:=Cq+∑i∈Finset.range (L-1),B'^i*E (L-1-i)+B'^L
  have hmixscaled:Ro*T^(2*(L-1))+
      S^(2*(L-1))*(∑i∈Finset.range (L-1),(2*C^2)*Bp^i*T^(2*i)/(S^(2*i)*((L-1-i).factorial:ℝ))) ≤
      Ro*T^(2*(L-1))+T^(2*(L-1))*Fo:=add_le_add le_rfl hmixed
  have hscaled':Ro*T^(2*(L-1))+T^(2*(L-1))*Fo ≤ K*Rn*T^(2*(L-1)):=by
    convert hscaled using 1 <;>dsimp[Ro,Fo,Rn]<;>ring
  have hcomb:=hmixscaled.trans hscaled'
  have hfinal:=mul_le_mul_of_nonneg_left hcomb (show 0 ≤ A₀*Real.exp 2/(complexity g p:ℝ)^L by positivity)
  apply hb.trans
  convert hfinal using 1 <;> dsimp[Bp,Ro,Fo,Rn] <;>ring

end WP.HigherOrder
