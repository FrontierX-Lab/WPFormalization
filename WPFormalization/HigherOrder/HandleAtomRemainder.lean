import WPFormalization.HigherOrder.ZeroConstantProductRemainder
import WPFormalization.HigherOrder.MergerAtomRemainder
import WPFormalization.Marked.UniformCorrectionBounds
/-! Actual handle atoms at every order. A virtual merger at the same parent
complexity controls the shifted inner cusp/profile product; the zero
constant leaves only lower-order genus errors. The uniform actual genus
bound and C.4 are instantiated, without an assumed error recurrence. -/
noncomputable section
namespace WP.HigherOrder
lemma actual_handle_atom_remainder_step_exponential (P:PsiTheory) :
    ∃D B:ℝ,∃M₀:ℕ,0<D ∧ 0<B ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀g p L:ℕ,3 ≤ g→1 ≤ p→2 ≤ L→∀d:List ℕ,d.length=p+1→
    ∀S T:ℝ,2*(L:ℝ) ≤ S→S ≤ T→scalarOrderWeight (M:ℝ) (L-1) (p+1) ≤ T→
    profileOrderWeight (M:ℝ) (L-1) d ≤ T→S^2/(complexity g p:ℝ) ≤ 1→∀Y∈Set.Icc (0:ℝ) y₀,
    ∀Cq:ℝ,0 ≤ Cq→∀E H:ℕ→ℝ,(∀i:ℕ,0 ≤ E i)→(∀i:ℕ,0 ≤ H i)→
    (|cuspCorrection P (g-1) (p+1) Y-truncationValue (formalCusp P Y (p+1)) (L-1) (1/((complexity g p:ℝ)-1))| ≤
      Cq*T^(2*(L-1))/((complexity g p:ℝ)-1)^(L-1))→
    (∀j:ℕ,1 ≤ j→j ≤ L-1→|profile P (g-1) d Y-truncationValue (formalProfile P Y d) j (1/((complexity g p:ℝ)-1))| ≤
      E j*T^(2*j)/((complexity g p:ℝ)-1)^j)→
    (∀j:ℕ,1 ≤ j→j ≤ L-1→|genusCorrection P g p Y-truncationValue (formalGenus P Y p) j (1/(complexity g p:ℝ))| ≤
      H j*T^(2*j)/(complexity g p:ℝ)^j)→
    |2*(W P (g-1) (p+1) Y/W P g p Y)*profile P (g-1) d Y-
      truncationValue ((PowerSeries.C (2*A Y)*complexityShift 1
        (PowerSeries.X*(formalCusp P Y (p+1)*formalProfile P Y d)))*formalGenus P Y p) L (1/(complexity g p:ℝ))| ≤
      D*T^(2*(L-1))/(complexity g p:ℝ)^L*
        (Cq+∑i∈Finset.range (L-1),B^i*E (L-1-i)+∑i∈Finset.range (L-1),B^i*H (L-1-i)+B^L) :=by
  obtain ⟨Da,Ba,Ma,hDa,hBa,hMa,hAtom⟩:=actual_merger_atom_remainder_step_exponential P
  obtain ⟨C,Bc,Mc,hC,hBc,hMc,hcoef⟩:=canonical_coefficients_on_common_scale P
  obtain ⟨A₀,hA₀,hAb⟩:=genusExtension_A_uniform_upper
  obtain ⟨G₀,hG₀,hGb⟩:=genusCorrection_abs_uniform P
  let Bp:=2*max Bc 1
  let Bf:=2*max Bp 1
  let Cf:=2*A₀*(2*C^2)
  let B:=max Ba Bf
  let D:=2*Da*G₀+Cf+1
  let M₀:=max Ma Mc
  have hBp:0<Bp:=by dsimp[Bp];positivity
  have hBf:0<Bf:=by dsimp[Bf];positivity
  have hCf:0<Cf:=by dsimp[Cf];positivity
  have hB:0<B:=hBa.trans_le (le_max_left _ _)
  have hD:0<D:=by dsimp[D];positivity
  have hM₀:2 ≤ M₀:=hMa.trans (le_max_left _ _)
  refine ⟨D,B,M₀,hD,hB,hM₀,?_⟩
  intro M hM g p L hg hp hL d hlen S T hS hST hTs hTp hsmall Y hY Cq hCq E H hE hH hCs hPs hGs
  have hMtwo:2 ≤ M:=hM₀.trans hM
  have hT1:1 ≤ T:=by
    apply LE.le.trans _ hTs
    dsimp[scalarOrderWeight]
    have hm:0 ≤ (M:ℝ)*(L-1:ℕ):=by positivity
    have hpR:(1:ℝ) ≤ p:=by exact_mod_cast hp
    norm_num only[Nat.cast_add,Nat.cast_one]
    linarith
  have hT0:0 ≤ T:=by linarith
  have hc:complexity (g-1) (p+2)=complexity g p:=by unfold complexity;omega
  have hcR:(complexity (g-1) (p+2):ℝ)=(complexity g p:ℝ):=by rw[hc]
  have hpn:p+2-1=p+1:=by omega
  have hb:=hAtom M ((le_max_left _ _).trans hM) (g-1) (p+2) L (by omega) (by omega) hL d
    (by omega) S T hS hST (by simpa only[hpn] using hTs) hTp (by simpa only[hc] using hsmall)
    Y hY Cq hCq E hE (by simpa only[hpn,hc] using hCs) (by simpa only[hc] using hPs)
  let h:ℝ:=complexity g p
  let F:=PowerSeries.C (2*A Y)*complexityShift 1 (PowerSeries.X*(formalCusp P Y (p+1)*formalProfile P Y d))
  let x:=2*A Y/(h-1)*(cuspCorrection P (g-1) (p+1) Y*profile P (g-1) d Y)
  have hh:0<h:=by dsimp[h];exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have hmerge:W P (g-1) (p+1) Y/W P (g-1) (p+2) Y=
      A Y/(h-1)*cuspCorrection P (g-1) (p+1) Y:=by
    simpa only[hpn,hc,h] using merger_prefactor_eq_cusp P (g-1) (p+2) (by omega) (by omega) Y hY
  have hF2:F=PowerSeries.C 2*(PowerSeries.C (A Y)*complexityShift 1
      (PowerSeries.X*(formalCusp P Y (p+1)*formalProfile P Y d))):=by
    dsimp[F]
    rw[map_mul]
    ring
  have hx:|x-truncationValue F L (1/h)| ≤
      (2*Da)*(Cq+∑i∈Finset.range (L-1),Ba^i*E (L-1-i)+Ba^L)*T^(2*(L-1))/h^L:=by
    have heq:x-truncationValue F L (1/h)=2*((W P (g-1) (p+1) Y/W P (g-1) (p+2) Y)*profile P (g-1) d Y-
        truncationValue (PowerSeries.C (A Y)*complexityShift 1
          (PowerSeries.X*(formalCusp P Y (p+1)*formalProfile P Y d))) L (1/h)):=by
      rw[hF2,truncationValue_C_mul,hmerge]
      dsimp[x]
      ring
    rw[heq,abs_mul,abs_of_pos (by norm_num:(0:ℝ)<2)]
    convert mul_le_mul_of_nonneg_left hb (by norm_num:(0:ℝ) ≤ 2) using 1 <;>
      simp only[hpn,hc,h] <;>ring
  have hdata (i:ℕ) (hi:i ≤ L-1):
      |PowerSeries.coeff i (formalCusp P Y (p+1))| ≤ C*Bc^i*T^(2*i) ∧
      |PowerSeries.coeff i (formalGenus P Y (p+1))| ≤ C*Bc^i*T^(2*i) ∧
      |PowerSeries.coeff i (formalProfile P Y d)| ≤ C*Bc^i*T^(2*i):=
    hcoef M ((le_max_right _ _).trans hM) (p+1) (by omega) d (by omega) (L-1) T hTs hTp i hi Y hY
  have hAc:|2*A Y| ≤ 2*A₀:=by
    rw[abs_mul,abs_of_pos (by norm_num:(0:ℝ)<2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have hAp:0<A Y:=by unfold A;exact div_pos (Analysis.barH_one_re_pos Y hY) (by norm_num)
    simpa only[abs_of_pos hAp] using hAb Y hY
  have hFcoef (i:ℕ) (hi:i<L-1):|PowerSeries.coeff (i+1) F| ≤ Cf*Bf^i*T^(2*i):=by
    have hprod (j:ℕ) (hj:j ≤ i):|PowerSeries.coeff j (formalCusp P Y (p+1)*formalProfile P Y d)| ≤
        (2*C^2)*Bp^j*T^(2*j):=by
      exact product_coeff_scaled_exponential _ _ j C Bc T hC.le hBc.le hT0
        (fun k hk=>(hdata k (hk.trans (hj.trans hi.le))).1)
        (fun k hk=>(hdata k (hk.trans (hj.trans hi.le))).2.2)
    have hshift:=complexityShift_one_X_coeff_scaled _ i (2*C^2) Bp T (by positivity) hBp.le hT1 hprod
    dsimp[F]
    rw[PowerSeries.coeff_C_mul,abs_mul]
    convert mul_le_mul hAc hshift (abs_nonneg _) (by positivity:0 ≤ 2*A₀) using 1 <;> dsimp[Cf,Bf] <;>ring
  have hF0:PowerSeries.coeff 0 F=0:=by
    dsimp[F]
    simp only[PowerSeries.coeff_zero_eq_constantCoeff,map_mul,PowerSeries.constantCoeff_C,
      complexityShift_constant,PowerSeries.constantCoeff_X,zero_mul,mul_zero]
  have hR:0 ≤ (2*Da)*(Cq+∑i∈Finset.range (L-1),Ba^i*E (L-1-i)+Ba^L):=by
    exact mul_nonneg (by positivity) (add_nonneg (add_nonneg hCq (Finset.sum_nonneg (fun i hi=>mul_nonneg (by positivity) (hE _)))) (by positivity))
  have hraw:=zero_constant_product_scaled_step x (genusCorrection P g p Y) F (formalGenus P Y p) L hL
    T h ((2*Da)*(Cq+∑i∈Finset.range (L-1),Ba^i*E (L-1-i)+Ba^L)) Cf Bf G₀ H
    hT0 hh hR hCf.le hBf.le hG₀.le hH hF0 (hGb g p hp (by unfold Stable;omega) Y hY) hx hFcoef
    (by simpa only[h] using hGs)
  have hactual:x*genusCorrection P g p Y=2*(W P (g-1) (p+1) Y/W P g p Y)*profile P (g-1) d Y:=by
    rw[handle_prefactor_eq_cusp_genus P g p (by omega) hp Y hY]
    dsimp[x,h]
    ring
  rw[hactual] at hraw
  have hconvE:(∑i∈Finset.range (L-1),Ba^i*E (L-1-i)) ≤ ∑i∈Finset.range (L-1),B^i*E (L-1-i):=by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hBa.le (le_max_left _ _) i) (hE _)
  have hconvH:(∑i∈Finset.range (L-1),Bf^i*H (L-1-i)) ≤ ∑i∈Finset.range (L-1),B^i*H (L-1-i):=by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hBf.le (le_max_right _ _) i) (hH _)
  have hpB:Ba^L ≤ B^L:=pow_le_pow_left₀ hBa.le (le_max_left _ _) _
  let RE:=∑i∈Finset.range (L-1),B^i*E (L-1-i)
  let RH:=∑i∈Finset.range (L-1),B^i*H (L-1-i)
  have hRE:0 ≤ RE:=Finset.sum_nonneg (fun i hi=>mul_nonneg (by positivity) (hE _))
  have hRH:0 ≤ RH:=Finset.sum_nonneg (fun i hi=>mul_nonneg (by positivity) (hH _))
  have hforce:G₀*((2*Da)*(Cq+∑i∈Finset.range (L-1),Ba^i*E (L-1-i)+Ba^L))+
      Cf*∑i∈Finset.range (L-1),Bf^i*H (L-1-i) ≤ D*(Cq+RE+RH+B^L):=by
    have hinnerCmp:Cq+(∑i∈Finset.range (L-1),Ba^i*E (L-1-i))+Ba^L ≤ Cq+RE+B^L:=add_le_add (add_le_add le_rfl hconvE) hpB
    have h1:=mul_le_mul_of_nonneg_left hinnerCmp (show 0 ≤ 2*Da*G₀ by positivity)
    have h2:=mul_le_mul_of_nonneg_left hconvH hCf.le
    have hD1:2*Da*G₀ ≤ D:=by dsimp[D];linarith
    have hD2:Cf ≤ D:=by
      dsimp[D]
      have hm:0 ≤ 2*Da*G₀:=by positivity
      linarith
    have h3:=mul_le_mul_of_nonneg_right hD1 (show 0 ≤ Cq+RE+B^L by positivity)
    have h4:=mul_le_mul_of_nonneg_right hD2 hRH
    nlinarith
  apply hraw.trans
  have hb:=mul_le_mul_of_nonneg_left hforce (show 0 ≤ T^(2*(L-1))/h^L by positivity)
  convert hb using 1 <;>dsimp[h,F,RE,RH] <;>ring
end WP.HigherOrder
