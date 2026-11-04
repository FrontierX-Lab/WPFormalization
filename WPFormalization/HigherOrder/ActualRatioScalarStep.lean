import WPFormalization.HigherOrder.ActualRatioFactorStep
import WPFormalization.HigherOrder.RatioScalarConvolution
import WPFormalization.Marked.DilatonRefinement
/-! The actual C.14 core and large-component ratio have uniform
single-remainder estimates from strictly lower-order scalar induction data.
All constants precede the loss/order, markings, state and closed parameter.
The loss r is retained in S^(2(L-r))/h^L; no whole-ratio error is assumed. -/
noncomputable section
namespace WP.HigherOrder
open Set PowerSeries
lemma actual_large_component_core_previous_scalar_step (P:PsiTheory) :
    ∃ D B:ℝ,∃M₀:ℕ,0<D ∧ 0<B ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀g p j s L:ℕ,j ≤ g→s<p→Stable (g-j) (p-s)→1 ≤ 2*j+s→2*j+s<L→
    ∀Y∈Icc (0:ℝ) y₀,
    scalarOrderWeight (M:ℝ) L p^2/(complexity g p:ℝ) ≤ 1→
    ∀EC EG:ℕ→ℝ,(∀m,0 ≤ EC m)→(∀m,0 ≤ EG m)→
    (∀g' p' m:ℕ,1 ≤ p'→Stable g' p'→1 ≤ m→m<L→
      |cuspCorrection P g' p' Y-truncationValue (formalCusp P Y p') m (1/(complexity g' p':ℝ))| ≤
        EC m*scalarOrderWeight (M:ℝ) m p'^(2*m)/(complexity g' p':ℝ)^m)→
    (∀g' p' m:ℕ,1 ≤ p'→Stable g' p'→1 ≤ m→m<L→
      |genusCorrection P g' p' Y-truncationValue (formalGenus P Y p') m (1/(complexity g' p':ℝ))| ≤
        EG m*scalarOrderWeight (M:ℝ) m p'^(2*m)/(complexity g' p':ℝ)^m)→
    |actualLargeRatioCore P g p j s Y-
      truncationValue (ratioCoreSeries (formalHierarchyJet P Y) p j s) (L-(2*j+s)) (1/(complexity g p:ℝ))| ≤
      D^(2*j+s)*scalarOrderWeight (M:ℝ) L p^(2*(L-(2*j+s)))/(complexity g p:ℝ)^(L-(2*j+s))*
        ((∑i∈Finset.range (L-(2*j+s)),B^i*(EC (L-(2*j+s)-i)+EG (L-(2*j+s)-i)))+B^(L-(2*j+s))) := by
  obtain ⟨C,B,D,M₀,hC,hB,hD,hM₀,hstep⟩:=actual_ratio_factor_uniform_step P
  obtain ⟨V,hV,hV1,hactual⟩:=actualLargeRatioFactor_abs_uniform P
  let D':=max D 1
  let Z:=max (2*C) V
  let Dfinal:=D'*(2*Z)^2
  have hD'1:1 ≤ D':=le_max_right _ _
  have hZ:1 ≤ Z:=hV1.trans (le_max_right _ _)
  have hDp:0<D':=by linarith
  have hZp:0<Z:=by linarith
  have hDfinal:0<Dfinal:=by dsimp[Dfinal];positivity
  refine ⟨Dfinal,2*B,M₀,hDfinal,by linarith,hM₀,?_⟩
  intro M hM g p j s L hj hs hstable hr1 hr Y hY hsmall EC EG hEC hEG hcusp hgenus
  let S:=scalarOrderWeight (M:ℝ) L p
  let h:ℝ:=complexity g p
  let r:=2*j+s
  let q:=L-r
  let n:=r+j
  have hp:1 ≤ p:=by omega
  have hL:1 ≤ L:=by omega
  have hq:1 ≤ q:=by dsimp[q,r];omega
  have hh:0<h:=by
    dsimp[h]
    have hn:0<complexity g p:=by unfold complexity Stable at *;omega
    exact_mod_cast hn
  have hM2:(2:ℝ) ≤ M:=by exact_mod_cast hM₀.trans hM
  have hS:2*(L:ℝ) ≤ S:=by
    have hm:=mul_le_mul_of_nonneg_right hM2 (Nat.cast_nonneg L : (0:ℝ) ≤ L)
    dsimp[S,scalarOrderWeight]
    linarith[Nat.cast_nonneg (α:=ℝ) p]
  have hS0:0 ≤ S:=by have :=Nat.cast_nonneg (α:=ℝ) L;linarith
  have hfac:=hstep M hM g p j s L hj hs hstable hr1 hr Y hY hsmall EC EG hEC hEG hcusp hgenus
  have hX:∀a<n,|actualLargeRatioFactor P g p j s Y a| ≤ V:=
    hactual g p j s L Y hY S hj hs hstable hL hr.le hS hsmall
  have hcoef:∀a<n,∀i<q,|PowerSeries.coeff i (formalLargeRatioFactor (formalHierarchyJet P Y) p j s a)| ≤ C*B^i*S^(2*i):=
    fun a ha=> (hfac a ha).1
  have herr:∀a<n,∀m:ℕ,1 ≤ m→m ≤ q→
      |actualLargeRatioFactor P g p j s Y a-
        truncationValue (formalLargeRatioFactor (formalHierarchyJet P Y) p j s a) m (1/h)| ≤
        D'*(EC m+EG m+B^m)*S^(2*m)/h^m:=by
    intro a ha m hm hmq
    apply ((hfac a ha).2 m hm hmq).trans
    have hECm:=hEC m
    have hEGm:=hEG m
    apply div_le_div_of_nonneg_right _ (pow_nonneg hh.le _)
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hS0 _)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hb:=finite_product_uniform_scalar_remainder (actualLargeRatioFactor P g p j s Y)
    (formalLargeRatioFactor (formalHierarchyJet P Y) p j s) n q r hq hr1 (by dsimp[n,r];omega)
    C B V D' S h hC.le hB hV1 hD'1 hS0 hh EC EG hEC hEG hX hcoef herr
  change |(∏a∈Finset.range ((2*j+s)+j),actualLargeRatioFactor P g p j s Y a)-
      truncationValue (∏a∈Finset.range ((2*j+s)+j),formalLargeRatioFactor (formalHierarchyJet P Y) p j s a) q (1/h)| ≤ _ at hb
  rw[actualLargeRatioFactor_product,formalLargeRatioFactor_product] at hb
  convert hb using 1 <;> (try dsimp[Dfinal,Z,S,h,q,r]) <;>ring


lemma actual_large_component_ratio_previous_scalar_step (P:PsiTheory) :
    ∃ D B:ℝ,∃M₀:ℕ,0<D ∧ 0<B ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀g p j s L:ℕ,j ≤ g→s<p→Stable (g-j) (p-s)→1 ≤ 2*j+s→2*j+s<L→
    ∀Y∈Icc (0:ℝ) y₀,
    scalarOrderWeight (M:ℝ) L p^2/(complexity g p:ℝ) ≤ 1→
    ∀EC EG:ℕ→ℝ,(∀m,0 ≤ EC m)→(∀m,0 ≤ EG m)→
    (∀g' p' m:ℕ,1 ≤ p'→Stable g' p'→1 ≤ m→m<L→
      |cuspCorrection P g' p' Y-truncationValue (formalCusp P Y p') m (1/(complexity g' p':ℝ))| ≤
        EC m*scalarOrderWeight (M:ℝ) m p'^(2*m)/(complexity g' p':ℝ)^m)→
    (∀g' p' m:ℕ,1 ≤ p'→Stable g' p'→1 ≤ m→m<L→
      |genusCorrection P g' p' Y-truncationValue (formalGenus P Y p') m (1/(complexity g' p':ℝ))| ≤
        EG m*scalarOrderWeight (M:ℝ) m p'^(2*m)/(complexity g' p':ℝ)^m)→
    |W P (g-j) (p-s) Y/W P g p Y-
      truncationValue (ratioSeries Y (formalHierarchyJet P Y) p j s) L (1/(complexity g p:ℝ))| ≤
      D^(2*j+s)*scalarOrderWeight (M:ℝ) L p^(2*(L-(2*j+s)))/(complexity g p:ℝ)^L*
        ((∑i∈Finset.range (L-(2*j+s)),B^i*(EC (L-(2*j+s)-i)+EG (L-(2*j+s)-i)))+B^(L-(2*j+s))) := by
  obtain ⟨C,B,D,M₀,hC,hB,hD,hM₀,hstep⟩:=actual_ratio_factor_uniform_step P
  obtain ⟨V,hV,hV1,hactual⟩:=actualLargeRatioFactor_abs_uniform P
  obtain ⟨Ba,hBa,hA⟩:=dilaton_A_abs_uniform
  let D':=max D 1
  let Z:=max (2*C) V
  let Dfinal:=Ba*(D'*(2*Z)^2)
  have hD'1:1 ≤ D':=le_max_right _ _
  have hZ:1 ≤ Z:=hV1.trans (le_max_right _ _)
  have hDp:0<D':=by linarith
  have hZp:0<Z:=by linarith
  have hDfinal:0<Dfinal:=by dsimp[Dfinal];positivity
  refine ⟨Dfinal,2*B,M₀,hDfinal,by linarith,hM₀,?_⟩
  intro M hM g p j s L hj hs hstable hr1 hr Y hY hsmall EC EG hEC hEG hcusp hgenus
  let S:=scalarOrderWeight (M:ℝ) L p
  let h:ℝ:=complexity g p
  let r:=2*j+s
  let q:=L-r
  let n:=r+j
  have hp:1 ≤ p:=by omega
  have hL:1 ≤ L:=by omega
  have hq:1 ≤ q:=by dsimp[q,r];omega
  have hh:0<h:=by
    dsimp[h]
    have hn:0<complexity g p:=by unfold complexity Stable at *;omega
    exact_mod_cast hn
  have hM2:(2:ℝ) ≤ M:=by exact_mod_cast hM₀.trans hM
  have hS:2*(L:ℝ) ≤ S:=by
    have hm:=mul_le_mul_of_nonneg_right hM2 (Nat.cast_nonneg L : (0:ℝ) ≤ L)
    dsimp[S,scalarOrderWeight]
    linarith[Nat.cast_nonneg (α:=ℝ) p]
  have hS0:0 ≤ S:=by have :=Nat.cast_nonneg (α:=ℝ) L;linarith
  have hfac:=hstep M hM g p j s L hj hs hstable hr1 hr Y hY hsmall EC EG hEC hEG hcusp hgenus
  have hX:∀a<n,|actualLargeRatioFactor P g p j s Y a| ≤ V:=
    hactual g p j s L Y hY S hj hs hstable hL hr.le hS hsmall
  have hcoef:∀a<n,∀i<q,|PowerSeries.coeff i (formalLargeRatioFactor (formalHierarchyJet P Y) p j s a)| ≤ C*B^i*S^(2*i):=
    fun a ha=> (hfac a ha).1
  have herr:∀a<n,∀m:ℕ,1 ≤ m→m ≤ q→
      |actualLargeRatioFactor P g p j s Y a-
        truncationValue (formalLargeRatioFactor (formalHierarchyJet P Y) p j s a) m (1/h)| ≤
        D'*(EC m+EG m+B^m)*S^(2*m)/h^m:=by
    intro a ha m hm hmq
    apply ((hfac a ha).2 m hm hmq).trans
    have hECm:=hEC m
    have hEGm:=hEG m
    apply div_le_div_of_nonneg_right _ (pow_nonneg hh.le _)
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hS0 _)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hb:=finite_product_uniform_scalar_remainder (actualLargeRatioFactor P g p j s Y)
    (formalLargeRatioFactor (formalHierarchyJet P Y) p j s) n q r hq hr1 (by dsimp[n,r];omega)
    C B V D' S h hC.le hB hV1 hD'1 hS0 hh EC EG hEC hEG hX hcoef herr
  change |(∏a∈Finset.range ((2*j+s)+j),actualLargeRatioFactor P g p j s Y a)-
      truncationValue (∏a∈Finset.range ((2*j+s)+j),formalLargeRatioFactor (formalHierarchyJet P Y) p j s a) q (1/h)| ≤ _ at hb
  rw[actualLargeRatioFactor_product,formalLargeRatioFactor_product] at hb
  have hpref:=large_component_product_remainder_pairing P g p j s L (formalHierarchyJet P Y) 1 1 hr.le Y hY hj hs hstable
  simp only[mul_one] at hpref
  rw[hpref]
  have hknown:0 ≤ (∑i∈Finset.range q,(2*B)^i*(EC (q-i)+EG (q-i)))+(2*B)^q:=by
    apply add_nonneg
    · exact Finset.sum_nonneg (fun i hi=>mul_nonneg (by positivity) (add_nonneg (hEC _) (hEG _)))
    · positivity
  have haPow:|A Y|^r ≤ Ba^r:=pow_le_pow_left₀ (abs_nonneg _) (hA Y hY) r
  have hpows:h^r*h^q=h^L:=by rw[←pow_add];congr 1;dsimp[q,r];omega
  have hbMul:=mul_le_mul_of_nonneg_left hb (by positivity:0 ≤ |A Y|^r/h^r)
  apply hbMul.trans
  have hAstep:=mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right haPow (pow_nonneg hh.le r))
    (mul_nonneg (mul_nonneg (pow_nonneg (by positivity:0 ≤ D'*(2*Z)^2) r) (by positivity:0 ≤ S^(2*q)/h^q)) hknown)
  apply hAstep.trans_eq
  change Ba^r/h^r*((D'*(2*Z)^2)^r*(S^(2*q)/h^q)*_) = _
  rw[←hpows,mul_pow]
  dsimp[Dfinal,r,q,S,h]
  ring

end WP.HigherOrder
