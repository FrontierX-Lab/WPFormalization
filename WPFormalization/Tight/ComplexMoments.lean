import WPFormalization.Tight.MomentNormalization
/-! Complex universal moment polynomial and its exact real restriction. -/
noncomputable section
namespace WP.TightMoments
open Set Filter
open scoped Topology

def complexMomentAmplitude (P:PsiTheory) (g:ℕ) (d:List ℕ) (M:ℕ→ℂ):ℂ:=
  if Stable g d.length ∧ d.sum≤dimension g d.length then
    ∑l∈backgrounds (deficit g d),(pure P g (d++backgroundDegrees l):ℂ)*
      (∏i:Fin (deficit g d),(-M (i.val+1))^(l i)/(l i).factorial)/
        M 0^(complexity g d.length+∑i,l i)
  else 0

def complexMomentPolynomial (P:PsiTheory) (g p:ℕ) (M:ℕ→ℂ) (L:Fin p→ℝ):ℂ:=
  ∑d∈degreeTuples g p,complexMomentAmplitude P g (List.ofFn d) M*
    ∏i,(L i:ℂ)^(2*d i)/((2:ℂ)^(d i)*(d i).factorial)

lemma complexMomentAmplitude_ofReal (P:PsiTheory) (g:ℕ) (d:List ℕ) (M:ℕ→ℝ):
    complexMomentAmplitude P g d (fun j=>(M j:ℂ))=(momentAmplitude P g d M:ℂ):=by
  unfold complexMomentAmplitude momentAmplitude
  split_ifs
  · push_cast
    rfl
  · simp
lemma complexMomentPolynomial_ofReal (P:PsiTheory) (g p:ℕ) (M:ℕ→ℝ) (L:Fin p→ℝ):
    complexMomentPolynomial P g p (fun j=>(M j:ℂ)) L=(momentPolynomial P g p M L:ℂ):=by
  unfold complexMomentPolynomial momentPolynomial
  simp_rw [complexMomentAmplitude_ofReal]
  push_cast
  rfl
lemma complexMomentAmplitude_analyticAt (P:PsiTheory) (g:ℕ) (d:List ℕ)
    (M:ℕ→ℂ→ℂ) (z:ℂ) (ha:∀j,AnalyticAt ℂ (M j) z) (h0:M 0 z≠0):
    AnalyticAt ℂ (fun t=>complexMomentAmplitude P g d (fun j=>M j t)) z:=by
  unfold complexMomentAmplitude
  split_ifs
  · apply Finset.analyticAt_fun_sum
    intro l hl
    apply AnalyticAt.div
    · apply AnalyticAt.mul analyticAt_const
      apply Finset.analyticAt_fun_prod
      intro i hi
      exact ((ha _).neg.pow _).div_const
    · exact (ha 0).pow _
    · exact pow_ne_zero _ h0
  · exact analyticAt_const
lemma complexMomentPolynomial_analyticAt (P:PsiTheory) (g p:ℕ)
    (M:ℕ→ℂ→ℂ) (L:Fin p→ℝ) (z:ℂ) (ha:∀j,AnalyticAt ℂ (M j) z) (h0:M 0 z≠0):
    AnalyticAt ℂ (fun t=>complexMomentPolynomial P g p (fun j=>M j t) L) z:=by
  apply Finset.analyticAt_fun_sum
  intro d hd
  exact (complexMomentAmplitude_analyticAt P g _ M z ha h0).mul analyticAt_const

end WP.TightMoments
