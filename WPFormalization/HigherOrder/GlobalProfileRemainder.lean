import WPFormalization.HigherOrder.ProfileAdjacentRemainder
import WPFormalization.HigherOrder.LargeWeightScales
/-! The global profile row of the four-stage actual remainder induction.
All signed child source estimates, every-coordinate residuals, the fixed
path telescope and the full large-weight branch are instantiated. Only
strict previous-order stage bounds enter; all genera, excess degrees and
all truncation orders L >= 2 remain in the domain. -/
noncomputable section
namespace WP.HigherOrder
open Set
lemma global_profile_remainder_stage (P:PsiTheory) :
    ∃D B:ℝ,∃M₀:ℕ,0<D ∧ 1 ≤ B ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀L:ℕ,2 ≤ L→∀e:ℕ→ℝ,(∀q,0 ≤ e q)→
    (∀q:ℕ,1 ≤ q→q<L→∀s,RemainderStageBound P M s q (e q))→
    RemainderStageBound P M 0 L (D*((∑i∈Finset.Icc 1 L,B^i*e (L-i))+B^L)):=by
  obtain ⟨Ds,Bs,δ₀,Ms,hDs,hBs,hδ₀,hδ1,hMs,hedge⟩:=profile_adjacent_remainder_step P
  obtain ⟨Cl,Bl,Ml,hCl,hBl,hMl,hlarge⟩:=canonical_large_weight_remainders_all_scales P δ₀ hδ₀
  let B:=max Bs Bl
  let D:=Ds+Cl
  have hB:1 ≤ B:=hBs.trans (le_max_left _ _)
  have hD:0<D:=by dsimp[D];positivity
  refine ⟨D,B,max Ms Ml,hD,hB,hMs.trans (le_max_left _ _),?_⟩
  intro M hM L hL e he hprev g d hd hs hh Y hY
  have hMsM:Ms ≤ M:=(le_max_left _ _).trans hM
  have hMlM:Ml ≤ M:=(le_max_right _ _).trans hM
  have hM0:0 ≤ (M:ℝ):=Nat.cast_nonneg _
  let S:=profileOrderWeight (M:ℝ) L d
  let h:ℝ:=complexity g d.length
  let V:=∑i∈Finset.Icc 1 L,B^i*e (L-i)
  let Vs:=∑i∈Finset.Icc 1 L,Bs^i*e (L-i)
  have hS:0 ≤ S:=by dsimp[S,profileOrderWeight];positivity
  have hhR:0<h:=by dsimp[h];exact_mod_cast (show 0<complexity g d.length by omega)
  have hV:0 ≤ V:=Finset.sum_nonneg (fun i hi=>mul_nonneg (pow_nonneg (show 0 ≤ B by linarith) _) (he _))
  have hVs:0 ≤ Vs:=Finset.sum_nonneg (fun i hi=>mul_nonneg (pow_nonneg (show 0 ≤ Bs by linarith) _) (he _))
  have hconv:Vs ≤ V:=by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (le_max_left _ _) i) (he _)
  have hpowS:Bs^L ≤ B^L:=pow_le_pow_left₀ (by linarith) (le_max_left _ _) L
  have hpowL:Bl^L ≤ B^L:=pow_le_pow_left₀ hBl.le (le_max_right _ _) L
  by_cases hsmall:S^2/h<δ₀
  · have hedge' (i:ℕ) (hi:i∈Finset.range d.length) (u:ℕ) (hu:u∈Finset.range d[i]!):
        |(profile P g (beforeCoordinate d i (u+1)) Y-profile P g (beforeCoordinate d i u) Y)-
          canonicalAdjacentTruncation P Y L i (beforeCoordinate d i u) (1/h)| ≤
        (Ds*(Vs+Bs^L))*profileOrderWeight (M:ℝ) L (beforeCoordinate d i u)^(2*L-1)*(1/h)^L:=by
      have hi':i<d.length:=Finset.mem_range.mp hi
      have hvsum:((beforeCoordinate d i u).sum:ℝ) ≤ d.sum:=by
        exact_mod_cast beforeCoordinate_sum_le d i u hi' (Finset.mem_range.mp hu).le
      have hw:profileOrderWeight (M:ℝ) L (beforeCoordinate d i u) ≤ S:=by
        dsimp[S,profileOrderWeight]
        rw[beforeCoordinate_length]
        linarith
      have hw0:0 ≤ profileOrderWeight (M:ℝ) L (beforeCoordinate d i u):=by unfold profileOrderWeight;positivity
      have hsmallv:profileOrderWeight (M:ℝ) L (beforeCoordinate d i u)^2/(complexity g (beforeCoordinate d i u).length:ℝ)<δ₀:=by
        rw[beforeCoordinate_length]
        exact (div_le_div_of_nonneg_right (pow_le_pow_left₀ hw0 hw 2) hhR.le).trans_lt hsmall
      have hb:=hedge M hMsM L hL e he hprev g (beforeCoordinate d i u)
        (by simpa only[beforeCoordinate_length] using hd) (by simpa only[beforeCoordinate_length] using hs)
        (by simpa only[beforeCoordinate_length] using hh) Y hY hsmallv i (by simpa only[beforeCoordinate_length] using hi')
      rw[raiseDegree_beforeCoordinate d i u hi'] at hb
      convert hb using 1 <;>simp only[beforeCoordinate_length,div_pow,one_pow,h,Vs] <;>ring
    have hb:=profile_remainder_bound_of_path_edges P g L (by omega) d hd hs Y (1/h) (M:ℝ)
      (Ds*(Vs+Bs^L)) hY (one_div_pos.mpr hhR).le hM0 (by positivity) hedge'
    have hsbound:|profile P g d Y-truncationValue (formalProfile P Y d) L (1/h)| ≤
        Ds*(Vs+Bs^L)*S^(2*L)/h^L:=by
      convert hb using 1 <;>simp only[div_pow,one_pow,S] <;>ring
    apply hsbound.trans
    have hDsD:Ds ≤ D:=by dsimp[D];linarith
    have hcoeff:Ds*(Vs+Bs^L) ≤ D*(V+B^L):=mul_le_mul hDsD (add_le_add hconv hpowS) (by positivity) hD.le
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hS _)) (pow_nonneg hhR.le _)
  · have hδ:δ₀ ≤ S^2/h:=le_of_not_gt hsmall
    have hb:|profile P g d Y-truncationValue (formalProfile P Y d) L (1/h)| ≤ Cl*Bl^L*S^(2*L)/h^L:=by
      have ht:=(hlarge M hMlM).1 g d hd hs hh L (by omega) Y hY hδ
      simpa only[truncationValue_at_inverse,formalProfile,PowerSeries.coeff_mk,h,S] using ht
    apply hb.trans
    have hClD:Cl ≤ D:=by dsimp[D];linarith
    have hp:Cl*Bl^L ≤ D*B^L:=mul_le_mul hClD hpowL (pow_nonneg hBl.le _) hD.le
    have hcoeff:Cl*Bl^L ≤ D*(V+B^L):=by nlinarith
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hS _)) (pow_nonneg hhR.le _)
end WP.HigherOrder
