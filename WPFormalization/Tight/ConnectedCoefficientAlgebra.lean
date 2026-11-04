import WPFormalization.Tight.ConnectedFourierCoefficient
import WPFormalization.Analysis.TaylorReality
noncomputable section
namespace WP.TightConnected
open Set

lemma connected_realCoeff_deriv (f:ℂ→ℂ) (n:ℕ) :
    realCoeff (deriv f) n=((n:ℝ)+1)*realCoeff f (n+1) := by
  have hh := congrArg (fun q:PowerSeries ℝ=>PowerSeries.coeff n q) (Analysis.realTaylor_deriv f)
  simpa only [Analysis.realTaylor_coeff,PowerSeries.coeff_derivative,Nat.cast_add,Nat.cast_one,mul_comm] using hh

/-- Exact original F.5 coefficient identity for the canonical tight numerator
and the genuine unmarked volume denominator. Physical L remains fixed. -/
lemma connected_coefficient_ratio_mass_identity (P:PsiTheory) (g gn p:ℕ)
    (hp:1≤p) (hsg:Stable g 1) (hsn:Stable gn p) (L:Fin p→ℝ)
    (n:ℕ) (hn:1≤n) (x:ℝ) (hx:x∈Ioo (0:ℝ) xCritical)
    (hm:cuspMass P g 1 (n-1) x≠0) :
    realCoeff (TightMoments.momentTightG P gn p L) n/realCoeff (Phi P g) n=
      ((n:ℝ)/x)*((TightMoments.momentTightG P gn p L (x:ℂ)).re/markedF P g 1 x)*
        (tightMass P gn p L n x/cuspMass P g 1 (n-1) x) := by
  have hF : markedF P g 1 x≠0 :=
    (markedF_positive_cusp_weight P g 1 (by omega) hsg x ⟨hx.1.le,hx.2⟩).ne'
  have hG : (TightMoments.momentTightG P gn p L (x:ℂ)).re≠0 :=
    (momentTightG_real_pos P gn p hp hsn L x ⟨hx.1.le,hx.2⟩).ne'
  have hc : realCoeff (iteratedDeriv 1 (Phi P g)) (n-1)=(n:ℝ)*realCoeff (Phi P g) n := by
    rw [iteratedDeriv_one,connected_realCoeff_deriv]
    have he : n-1+1=n := by omega
    rw [he]
    have hnc : ((n-1:ℕ):ℝ)+1=(n:ℝ) := by exact_mod_cast he
    rw [hnc]
  have hc0 : realCoeff (Phi P g) n≠0 := by
    intro hz
    apply hm
    unfold cuspMass
    rw [hc,hz,mul_zero,zero_mul,zero_div]
  have hxp : x^(n-1)≠0 := pow_ne_zero _ hx.1.ne'
  have hnp : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have hxpow : x^n=x^(n-1)*x := by rw [←pow_succ];congr 1;omega
  unfold tightMass cuspMass
  rw [hc,hxpow]
  field_simp [hF,hG,hc0,hxp,hnp,hx.1.ne']
  <;>ring
end WP.TightConnected
