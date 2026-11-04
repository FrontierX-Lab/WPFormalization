import WPFormalization.HigherOrder.ActualRatioScalarStep
import WPFormalization.HigherOrder.ActualShiftedProfileStep
import WPFormalization.Marked.DilatonRefinement
/-! The actual large component ratio times an actual child profile is
controlled by strictly lower-order cusp, genus and profile remainders.
The true C.14 factor array is extended by the prescribed shifted child,
so there is still one unknown error in each finite-product term. The
parent scale is small, and the child degree scale T>=S is unrestricted. -/
noncomputable section
namespace WP.HigherOrder
open Set PowerSeries

lemma actual_large_component_profile_previous_step (P:PsiTheory) :
    ∃D B:ℝ,∃M₀:ℕ,0<D ∧ 0<B ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀g p j s L:ℕ,j ≤ g→s<p→Stable (g-j) (p-s)→1 ≤ 2*j+s→2*j+s<L→
    ∀d:List ℕ,d.length=p-s→∀S T:ℝ,
    scalarOrderWeight (M:ℝ) L p ≤ S→S ≤ T→S^2/(complexity g p:ℝ) ≤ 1→
    profileOrderWeight (M:ℝ) (L-(2*j+s)) d ≤ T→
    ∀Y∈Icc (0:ℝ) y₀,∀EC EG EP:ℕ→ℝ,
    (∀m,0 ≤ EC m)→(∀m,0 ≤ EG m)→(∀m,0 ≤ EP m)→
    (∀g' p' m:ℕ,1 ≤ p'→Stable g' p'→1 ≤ m→m<L→
      |cuspCorrection P g' p' Y-truncationValue (formalCusp P Y p') m (1/(complexity g' p':ℝ))| ≤
        EC m*scalarOrderWeight (M:ℝ) m p'^(2*m)/(complexity g' p':ℝ)^m)→
    (∀g' p' m:ℕ,1 ≤ p'→Stable g' p'→1 ≤ m→m<L→
      |genusCorrection P g' p' Y-truncationValue (formalGenus P Y p') m (1/(complexity g' p':ℝ))| ≤
        EG m*scalarOrderWeight (M:ℝ) m p'^(2*m)/(complexity g' p':ℝ)^m)→
    (∀g':ℕ,∀d':List ℕ,1 ≤ d'.length→Stable g' d'.length→∀m:ℕ,1 ≤ m→m<L→
      |profile P g' d' Y-truncationValue (formalProfile P Y d') m (1/(complexity g' d'.length:ℝ))| ≤
        EP m*profileOrderWeight (M:ℝ) m d'^(2*m)/(complexity g' d'.length:ℝ)^m)→
    |(W P (g-j) (p-s) Y/W P g p Y)*profile P (g-j) d Y-
      truncationValue (ratioSeries Y (formalHierarchyJet P Y) p j s*
        complexityShift ((2*j+s:ℕ):ℝ) (formalProfile P Y d)) L (1/(complexity g p:ℝ))| ≤
      D^(2*j+s)*T^(2*(L-(2*j+s)))/(complexity g p:ℝ)^L*
        ((∑i∈Finset.range (L-(2*j+s)),B^i*(EC (L-(2*j+s)-i)+EG (L-(2*j+s)-i)+EP (L-(2*j+s)-i)))+
          B^(L-(2*j+s))) := by
  obtain ⟨Cf,Bf,Df,Mf,hCf,hBf,hDf,hMf,hfactor⟩:=actual_ratio_factor_uniform_step P
  obtain ⟨Cp,Bp,Dp,Mp,hCp,hBp,hDp,hMp,hprofileStep⟩:=actual_shifted_profile_previous_step P
  obtain ⟨V,hV,hV1,hactual⟩:=actualLargeRatioFactor_abs_uniform P
  obtain ⟨Ba,hBa,hA⟩:=dilaton_A_abs_uniform
  let C:=max Cf Cp
  let B:=max Bf Bp
  let D:=max 1 (max Df Dp)
  let Z:=max (2*C) V
  let K:=D*(2*Z)^2
  let M₀:=max Mf Mp
  have hC:0<C:=hCf.trans_le (le_max_left _ _)
  have hB:1 ≤ B:=hBf.trans (le_max_left _ _)
  have hD:1 ≤ D:=le_max_left _ _
  have hDf':Df ≤ D:=(le_max_left Df Dp).trans (le_max_right _ _)
  have hDp':Dp ≤ D:=(le_max_right Df Dp).trans (le_max_right _ _)
  have hZ:1 ≤ Z:=hV1.trans (le_max_right _ _)
  have hDp0:0<D:=by linarith
  have hZp:0<Z:=by linarith
  have hK:0<K:=by dsimp[K];positivity
  refine ⟨Ba*K,2*B,M₀,by positivity,by linarith,hMf.trans (le_max_left _ _),?_⟩
  intro M hM g p j s L hj hs hstable hr1 hr d hd S T hscalarS hST hsmall hweight Y hY EC EG EP hEC hEG hEP hcusp hgenus hprofile
  have hMfM:Mf ≤ M:=(le_max_left _ _).trans hM
  have hMpM:Mp ≤ M:=(le_max_right _ _).trans hM
  let S₀:=scalarOrderWeight (M:ℝ) L p
  let h:ℝ:=complexity g p
  let r:=2*j+s
  let q:=L-r
  let n:=r+j
  let u:=complexityShift (r:ℝ) (formalProfile P Y d)
  let x:=profile P (g-j) d Y
  have hp:1 ≤ p:=by omega
  have hL:1 ≤ L:=by omega
  have hq:1 ≤ q:=by dsimp[q,r];omega
  have hqL:q<L:=by dsimp[q,r];omega
  have hM2:(2:ℝ) ≤ M:=by exact_mod_cast (hMf.trans hMfM)
  have hS₀:2*(L:ℝ) ≤ S₀:=by
    have hm:=mul_le_mul_of_nonneg_right hM2 (Nat.cast_nonneg L : (0:ℝ) ≤ L)
    dsimp[S₀,scalarOrderWeight]
    linarith[Nat.cast_nonneg (α:=ℝ) p]
  have hS₀0:0 ≤ S₀:=by have :=Nat.cast_nonneg (α:=ℝ) L;linarith
  have hS0:0 ≤ S:=hS₀0.trans hscalarS
  have hT0:0 ≤ T:=hS0.trans hST
  have hS₀T:S₀ ≤ T:=hscalarS.trans hST
  have hS:2*(L:ℝ) ≤ S:=hS₀.trans hscalarS
  have hh:0<h:=by
    dsimp[h]
    have hn:0<complexity g p:=by unfold complexity Stable at *;omega
    exact_mod_cast hn
  have hscalarSmall:S₀^2/h ≤ 1:=(div_le_div_of_nonneg_right
    (pow_le_pow_left₀ hS₀0 hscalarS 2) hh.le).trans hsmall
  have hdn:1 ≤ d.length:=by rw[hd];omega
  have hds:Stable (g-j) d.length:=by rwa[hd]
  have hcomp:(complexity (g-j) d.length:ℝ)=h-(r:ℝ):=by
    have hn:complexity (g-j) d.length+r=complexity g p:=by rw[hd];dsimp[r];unfold complexity Stable at *;omega
    have hR:(complexity (g-j) d.length:ℝ)+(r:ℝ)=h:=by dsimp[h];exact_mod_cast hn
    linarith
  have hrC:|(r:ℝ)| ≤ L:=by rw[abs_of_nonneg (Nat.cast_nonneg _)];exact_mod_cast hr.le
  have hfac:=hfactor M hMfM g p j s L hj hs hstable hr1 hr Y hY hscalarSmall EC EG hEC hEG hcusp hgenus
  have hprof:=hprofileStep M hMpM (g-j) d hdn hds L q hq hqL (r:ℝ) S T h hrC hS hST hh hsmall hcomp hweight
    Y hY EP hEP (fun m hm hmq=>hprofile (g-j) d hdn hds m hm (by omega))
  have hXprof:|x| ≤ 1:=by
    have hb:=normalized_profile_bounds P (g-j) d hds hdn Y hY
    change 0 ≤ x ∧ x ≤ 1 at hb
    rw[abs_of_nonneg hb.1]
    exact hb.2
  have hX:∀a<n+1,|actualRatioProfileFactor P g p j s Y x a| ≤ V:=by
    intro a ha
    by_cases han:a<n
    · rw[actualRatioProfileFactor,ite_eq_left han]
      exact hactual g p j s L Y hY S₀ hj hs hstable hL hr.le hS₀ hscalarSmall a han
    · rw[actualRatioProfileFactor,ite_eq_right han]
      exact hXprof.trans hV1
  have hcoeff:∀a<n+1,∀i<q,|PowerSeries.coeff i (formalRatioProfileFactor (formalHierarchyJet P Y) p j s u a)| ≤ C*B^i*T^(2*i):=by
    intro a ha i hi
    by_cases han:a<n
    · rw[formalRatioProfileFactor,ite_eq_left han]
      apply ((hfac a han).1 i hi).trans
      exact mul_le_mul (mul_le_mul (le_max_left _ _)
        (pow_le_pow_left₀ (by linarith) (le_max_left _ _) i) (by positivity) hC.le)
        (pow_le_pow_left₀ hS₀0 hS₀T (2*i)) (pow_nonneg hS₀0 _) (by positivity)
    · rw[formalRatioProfileFactor,ite_eq_right han]
      apply (hprof.1 i hi).trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul (le_max_right _ _)
        (pow_le_pow_left₀ (by linarith) (le_max_right _ _) i) (by positivity) hC.le) (pow_nonneg hT0 _)
  have herr:∀a<n+1,∀m:ℕ,1 ≤ m→m ≤ q→
      |actualRatioProfileFactor P g p j s Y x a-
        truncationValue (formalRatioProfileFactor (formalHierarchyJet P Y) p j s u a) m (1/h)| ≤
        D*((EC m+EG m)+EP m+B^m)*T^(2*m)/h^m:=by
    intro a ha m hm hmq
    have hECm:=hEC m
    have hEGm:=hEG m
    have hEPm:=hEP m
    by_cases han:a<n
    · have hanRaw:a<(2*j+s)+j:=han
      simp only[actualRatioProfileFactor,formalRatioProfileFactor,ite_eq_left hanRaw]
      apply ((hfac a han).2 m hm hmq).trans
      apply div_le_div_of_nonneg_right _ (pow_nonneg hh.le _)
      have hsum:EC m+EG m+Bf^m ≤ EC m+EG m+EP m+B^m:=by
        have hb:=pow_le_pow_left₀ (by linarith:0 ≤ Bf) (le_max_left Bf Bp) m
        linarith
      exact mul_le_mul (mul_le_mul hDf' hsum (by positivity) hDp0.le)
        (pow_le_pow_left₀ hS₀0 hS₀T (2*m)) (pow_nonneg hS₀0 _) (by positivity)
    · have hanRaw:¬a<(2*j+s)+j:=han
      simp only[actualRatioProfileFactor,formalRatioProfileFactor,ite_eq_right hanRaw]
      apply (hprof.2 m hm hmq).trans
      apply div_le_div_of_nonneg_right _ (pow_nonneg hh.le _)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hT0 _)
      have hsum:EP m+Bp^m ≤ EC m+EG m+EP m+B^m:=by
        have hb:=pow_le_pow_left₀ (by linarith:0 ≤ Bp) (le_max_right Bf Bp) m
        linarith
      exact mul_le_mul hDp' hsum (by positivity) hDp0.le
  have hb:=finite_product_uniform_scalar_remainder (actualRatioProfileFactor P g p j s Y x)
    (formalRatioProfileFactor (formalHierarchyJet P Y) p j s u) (n+1) q r hq hr1 (by dsimp[n,r];omega)
    C B V D T h hC.le hB hV1 hD hT0 hh (fun m=>EC m+EG m) EP
    (fun m=>add_nonneg (hEC m) (hEG m)) hEP hX hcoeff herr
  change |(∏a∈Finset.range ((2*j+s)+j+1),actualRatioProfileFactor P g p j s Y x a)-
      truncationValue (∏a∈Finset.range ((2*j+s)+j+1),formalRatioProfileFactor (formalHierarchyJet P Y) p j s u a) q (1/h)| ≤ _ at hb
  rw[actualRatioProfileFactor_product,formalRatioProfileFactor_product] at hb
  have hpref:=large_component_product_remainder_pairing P g p j s L (formalHierarchyJet P Y) u x hr.le Y hY hj hs hstable
  rw[hpref]
  have hknown:0 ≤ (∑i∈Finset.range q,(2*B)^i*((EC (q-i)+EG (q-i))+EP (q-i)))+(2*B)^q:=by
    apply add_nonneg
    · exact Finset.sum_nonneg (fun i hi=>mul_nonneg (by positivity) (add_nonneg (add_nonneg (hEC _) (hEG _)) (hEP _)))
    · positivity
  have haPow:|A Y|^r ≤ Ba^r:=pow_le_pow_left₀ (abs_nonneg _) (hA Y hY) r
  have hpows:h^r*h^q=h^L:=by rw[←pow_add];congr 1;dsimp[q,r];omega
  have hbMul:=mul_le_mul_of_nonneg_left hb (by positivity:0 ≤ |A Y|^r/h^r)
  apply hbMul.trans
  have hAstep:=mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right haPow (pow_nonneg hh.le r))
    (mul_nonneg (mul_nonneg (pow_nonneg hK.le r) (by positivity:0 ≤ T^(2*q)/h^q)) hknown)
  apply hAstep.trans_eq
  change Ba^r/h^r*(K^r*(T^(2*q)/h^q)*_) = _
  rw[←hpows,mul_pow]
  dsimp[K,Z,r,q,h,u,x]
  ring

end WP.HigherOrder
