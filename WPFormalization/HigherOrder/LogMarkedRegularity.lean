import WPFormalization.HigherOrder.EndpointFormalGevrey
import WPFormalization.HigherOrder.TransportQuotientBounds
import WPFormalization.HigherOrder.LogMarkedPrimitiveRegular
import WPFormalization.HigherOrder.EndpointGevreyMatching
/-! Actual logarithmic marked coefficients have uniform closed-interval Gevrey-two bounds and endpoint Lipschitz bounds. Real FTC and the genuine discrete pure-psi endpoint expansion are instantiated. -/
noncomputable section
namespace WP.HigherOrder
open Set Filter PowerSeries
open scoped Topology
lemma logarithmicMarkedCoefficient_real_gevrey_regularity (P:PsiTheory)(p:ℕ)(hp:1 ≤ p):
    ∃C B:ℝ,0<C ∧0<B ∧
      (∀j:ℕ,ContinuousOn (logarithmicMarkedCoefficient P p j) (Icc (0:ℝ) y₀)) ∧
      (∀j:ℕ,1 ≤ j→∀Y∈Ioo (0:ℝ) y₀,HasDerivAt (logarithmicMarkedCoefficient P p j)
        (transportCoefficient P p j Y/(A Y*r Y)) Y) ∧
      (∀j:ℕ,∀Y∈Icc (0:ℝ) y₀,|logarithmicMarkedCoefficient P p j Y| ≤ C*B^j*(j.factorial:ℝ)^2) ∧
      (∀j:ℕ,1 ≤ j→∀Y∈Icc (0:ℝ) y₀,|logarithmicMarkedCoefficient P p j Y-endpointLogCoefficient p j| ≤
        C*B^j*(j.factorial:ℝ)^2*(y₀-Y)) := by
  obtain ⟨V,Cq,Bq,hV,hVconv,hcover,hCq,hBq,hquot⟩:=ComplexCanonical.common_transport_quotient_gevrey_two P p hp
  obtain ⟨Ce,Be,hCe,hBe,hend⟩:=endpointLogCoefficient_factorial_bound p
  let B:=max Bq Be
  let C:=Ce+Cq*(y₀+1)
  have hB:0<B:=hBq.trans_le (le_max_left _ _)
  have hy0:0<y₀:=y₀_pos
  have hC:0<C:=by dsimp[C];positivity
  have hCqC:Cq ≤ C:=by dsimp[C];nlinarith[y₀_pos]
  have hdata(j:ℕ)(hj:1 ≤ j):
      ContinuousOn (logarithmicMarkedCoefficient P p j) (Icc (0:ℝ) y₀) ∧
      (∀Y∈Ioo (0:ℝ) y₀,HasDerivAt (logarithmicMarkedCoefficient P p j)
        (transportCoefficient P p j Y/(A Y*r Y)) Y) ∧
      (∀Y∈Icc (0:ℝ) y₀,|logarithmicMarkedCoefficient P p j Y-endpointLogCoefficient p j| ≤
        Cq*Bq^j*(j.factorial:ℝ)^2*(y₀-Y)):=by
    obtain ⟨F,hFa,hFr,hFb⟩:=hquot j hj
    let q:ℝ→ℝ:=fun Y=>(F (Y:ℂ)).re
    have hqc:ContinuousOn q (Icc (0:ℝ) y₀):=by
      intro Y hY
      have ht:ContinuousAt (fun y:ℝ=>F (y:ℂ)) Y:=by
        simpa only[Function.comp_def] using (hFa (Y:ℂ) (hcover Y hY)).continuousAt.comp Complex.continuous_ofReal.continuousAt
      exact (Complex.continuous_re.continuousAt.comp ht).continuousWithinAt
    have hqr:∀Y∈Ico (0:ℝ) y₀,q Y=transportCoefficient P p j Y/(A Y*r Y):=by
      intro Y hY
      dsimp[q]
      rw[hFr Y hY]
      rfl
    have hqb:∀Y∈Icc (0:ℝ) y₀,|q Y| ≤ Cq*Bq^j*(j.factorial:ℝ)^2:=by
      intro Y hY
      exact (Complex.abs_re_le_norm _).trans (hFb (Y:ℂ) (hcover Y hY))
    have hreg:=logarithmicMarkedCoefficient_regular_of_quotient P p j hj q hqc hqr
    refine ⟨hreg.1,hreg.2,?_⟩
    intro Y hY
    exact logarithmicMarkedCoefficient_endpoint_lipschitz_of_quotient P p j hj q hqr _ (by positivity) hqb Y hY
  have hqBase(j:ℕ):Cq*Bq^j*(j.factorial:ℝ)^2 ≤ Cq*B^j*(j.factorial:ℝ)^2:=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hBq.le (le_max_left _ _) _) hCq.le) (sq_nonneg _)
  have heBase(j:ℕ):|endpointLogCoefficient p j| ≤ Ce*B^j*(j.factorial:ℝ)^2:=by
    have hf:(1:ℝ) ≤ j.factorial:=by exact_mod_cast (Nat.factorial_pos j)
    apply (hend j).trans
    have hp:=pow_le_pow_left₀ hBe.le (le_max_right Bq Be) j
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp hCe.le) (by nlinarith:(j.factorial:ℝ) ≤ (j.factorial:ℝ)^2)
      (by positivity) (by positivity)
  refine ⟨C,B,hC,hB,?_,?_,?_,?_⟩
  · intro j
    by_cases hj:j=0
    · subst j
      have hz:logarithmicMarkedCoefficient P p 0=(fun _:ℝ=>0):=by funext Y;simp[logarithmicMarkedCoefficient]
      rw[hz]
      exact continuousOn_const
    · exact (hdata j (by omega)).1
  · intro j hj
    exact (hdata j hj).2.1
  · intro j Y hY
    by_cases hj:j=0
    · subst j
      simp only[logarithmicMarkedCoefficient,ite_true,abs_zero]
      positivity
    have hreg:=(hdata j (by omega)).2.2 Y hY
    have hsplit:|logarithmicMarkedCoefficient P p j Y| ≤
        |logarithmicMarkedCoefficient P p j Y-endpointLogCoefficient p j|+|endpointLogCoefficient p j|:=by
      simpa only[sub_add_cancel] using abs_add_le (logarithmicMarkedCoefficient P p j Y-endpointLogCoefficient p j) (endpointLogCoefficient p j)
    have hδ:0 ≤ y₀-Y:=sub_nonneg.mpr hY.2
    have hδUpper:y₀-Y ≤ y₀:=by linarith[hY.1]
    have hMq:=hqBase j
    have hLip:Cq*Bq^j*(j.factorial:ℝ)^2*(y₀-Y) ≤ Cq*B^j*(j.factorial:ℝ)^2*y₀:=
      mul_le_mul hMq hδUpper hδ (by positivity)
    apply hsplit.trans ((add_le_add (hreg.trans hLip) (heBase j)).trans _)
    have hcoef:Cq*y₀+Ce ≤ C:=by dsimp[C];linarith
    have ht:=mul_le_mul_of_nonneg_right hcoef (by positivity:0 ≤ B^j*(j.factorial:ℝ)^2)
    convert ht using 1 <;>ring
  · intro j hj Y hY
    apply ((hdata j hj).2.2 Y hY).trans
    have hMq:=hqBase j
    have hCC:=mul_le_mul_of_nonneg_right hCqC (by positivity:0 ≤ B^j*(j.factorial:ℝ)^2)
    have hM:Cq*Bq^j*(j.factorial:ℝ)^2 ≤ C*B^j*(j.factorial:ℝ)^2:=hMq.trans (by convert hCC using 1 <;>ring)
    exact mul_le_mul_of_nonneg_right hM (sub_nonneg.mpr hY.2)
end WP.HigherOrder
