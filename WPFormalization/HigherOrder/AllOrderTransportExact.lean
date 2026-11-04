import WPFormalization.Volumes.SecondTransportProof
import WPFormalization.Volumes.PrefactorIntegration
import WPFormalization.HigherOrder.Endpoint
import WPFormalization.HigherOrder.FiniteRemainderAlgebra
import WPFormalization.HigherOrder.FirstScalarCoefficients
import WPFormalization.Marked.SingleMarkingProfile
/-! Exact actual marked logarithmic transport through the inverse cusp, and exact pairing with the prescribed finite canonical transport polynomial. -/
noncomputable section
namespace WP
open Set

lemma markedF_log_scaled_eq_cusp_inverse (P:PsiTheory)(g p:ℕ)(hp:1 ≤ p)
    (hs:Stable g p)(Y:ℝ)(hY:Y∈Ico (0:ℝ) y₀) :
    A Y*r Y*deriv (fun t=>Real.log (markedF P g p (XR t))) Y=
      (complexity g p:ℝ)*(cuspCorrection P g p Y)⁻¹ := by
  have hs':Stable g (p+1):=by unfold Stable at *;omega
  have hYc:Y∈Icc (0:ℝ) y₀:=⟨hY.1,hY.2.le⟩
  have hWp:=W_pos P g p hp hs Y hYc
  have hWc:=W_pos P g (p+1) (by omega) hs' Y hYc
  have hA:A Y≠0:=(Analysis.marked_A_pos Y hYc).ne'
  have hh:(complexity g p:ℝ)≠0:=by
    exact_mod_cast (show complexity g p≠0 by unfold complexity Stable at *;omega)
  rw[markedF_log_scaled_eq_inverse_of_W_pos P g p hs Y hY hWp hWc]
  unfold cuspCorrection
  field_simp[hWp.ne',hWc.ne',hA,hh]

lemma prefactorLogError_hasDerivAt_inverse_cusp (P:PsiTheory)(g p:ℕ)(hp:1 ≤ p)
    (hs:Stable g p)(Y:ℝ)(hY:Y∈Ioo (0:ℝ) y₀) :
    HasDerivAt (prefactorLogError P g p)
      (((complexity g p:ℝ)*((cuspCorrection P g p Y)⁻¹-1-transportBeta p Y/(complexity g p:ℝ)))/(A Y*r Y)) Y := by
  have hd:=prefactorLogError_hasDerivAt P g p hp hs Y hY
  rw[markedF_log_scaled_eq_cusp_inverse P g p hp hs Y ⟨hY.1.le,hY.2⟩] at hd
  have hh:(complexity g p:ℝ)≠0:=by
    exact_mod_cast (show complexity g p≠0 by unfold complexity Stable at *;omega)
  convert hd using 1
  field_simp[hh]
  ring

end WP
namespace WP.HigherOrder
open PowerSeries
lemma truncationValue_two_leading (f:Series)(L:ℕ)(t:ℝ) :
    truncationValue f (L+2) t=PowerSeries.coeff 0 f+PowerSeries.coeff 1 f*t+
      ∑j∈Finset.range L,PowerSeries.coeff (j+2) f*t^(j+2) := by
  rw[truncationValue,show L+2=2+L by omega,Finset.sum_range_add]
  simp only[Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,mul_one,zero_add,pow_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw[Nat.add_comm 2 j]

lemma inverseCusp_coeff_one_eq_beta (P:PsiTheory)(p:ℕ)(Y:ℝ)(hY:Y∈Set.Icc (0:ℝ) y₀) :
    PowerSeries.coeff 1 ((formalCusp P Y p)⁻¹)=transportBeta p Y := by
  rw[coeff_one_inv_unit _ (formalCusp_constant P Y p)]
  simp only[formalCusp,PowerSeries.coeff_mk,cuspCoefficient_one P p Y hY,neg_neg]

def transportTruncation (P:PsiTheory)(p L:ℕ)(Y h:ℝ):ℝ :=
  ∑j∈Finset.range L,transportCoefficient P p (j+1) Y/h^(j+1)

lemma inverseCusp_truncation_transport_identity (P:PsiTheory)(p L:ℕ)(Y h:ℝ)
    (hY:Y∈Set.Icc (0:ℝ) y₀)(hh:h≠0) :
    h*(truncationValue ((formalCusp P Y p)⁻¹) (L+2) (1/h)-1-transportBeta p Y/h)=
      transportTruncation P p L Y h := by
  rw[truncationValue_two_leading,PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.constantCoeff_inv,
    formalCusp_constant,inv_one,inverseCusp_coeff_one_eq_beta P p Y hY]
  simp only[div_pow,one_pow,mul_one_div]
  have he:h*(1+transportBeta p Y/h+
      (∑j∈Finset.range L,PowerSeries.coeff (j+2) ((formalCusp P Y p)⁻¹)/h^(j+2))-1-transportBeta p Y/h)=
      ∑j∈Finset.range L,h*(PowerSeries.coeff (j+2) ((formalCusp P Y p)⁻¹)/h^(j+2)):=by
    rw[←Finset.mul_sum]
    ring
  rw[he]
  unfold transportTruncation
  apply Finset.sum_congr rfl
  intro j hj
  unfold transportCoefficient
  rw[show j+2=(j+1)+1 by omega,pow_succ]
  field_simp[hh]

lemma prefactorLogError_transport_defect_identity (P:PsiTheory)(g p L:ℕ)(hp:1 ≤ p)(hs:Stable g p)
    (Y:ℝ)(hY:Y∈Set.Ioo (0:ℝ) y₀) :
    (A Y*r Y)*deriv (prefactorLogError P g p) Y-transportTruncation P p L Y (complexity g p:ℝ)=
      (complexity g p:ℝ)*((cuspCorrection P g p Y)⁻¹-
        truncationValue ((formalCusp P Y p)⁻¹) (L+2) (1/(complexity g p:ℝ))) := by
  have hh:(complexity g p:ℝ)≠0:=by exact_mod_cast (show complexity g p≠0 by unfold complexity Stable at *;omega)
  have hAr:A Y*r Y≠0:=mul_ne_zero (Analysis.marked_A_pos Y ⟨hY.1.le,hY.2.le⟩).ne' (r_pos Y ⟨hY.1.le,hY.2⟩).ne'
  rw[(WP.prefactorLogError_hasDerivAt_inverse_cusp P g p hp hs Y hY).deriv,
    ←inverseCusp_truncation_transport_identity P p L Y _ ⟨hY.1.le,hY.2.le⟩ hh]
  have hAne: A Y≠0:=(Analysis.marked_A_pos Y ⟨hY.1.le,hY.2.le⟩).ne'
  have hrne: r Y≠0:=(r_pos Y ⟨hY.1.le,hY.2⟩).ne'
  field_simp[hAne,hrne,hh]
  <;>ring

end WP.HigherOrder
