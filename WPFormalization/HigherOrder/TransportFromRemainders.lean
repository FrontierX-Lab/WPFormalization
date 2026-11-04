import WPFormalization.HigherOrder.RecursiveRemainderProof
import WPFormalization.HigherOrder.TransportCoefficientComplex
/-! The proved actual uniform remainders supply the critical transport identities.
No unproved remainder premise remains in these producers. One complex neighborhood
works for every p and j in the quotient extension; its quantitative Gevrey norm
is a separate downstream proof obligation. -/

noncomputable section
namespace WP.HigherOrder
open Set
lemma critical_formalCusp (P:PsiTheory) (p:ℕ) (hp:1 ≤ p) :
    formalCusp P y₀ p=(1+PowerSeries.C (-(p:ℝ)/5)*PowerSeries.X)⁻¹:=
  critical_formalCusp_of_recursiveRemainder P (canonical_uniform_recursive_remainders P) p hp
lemma transportCoefficient_critical (P:PsiTheory) (p j:ℕ) (hp:1 ≤ p) (hj:1 ≤ j) :
    transportCoefficient P p j y₀=0:=
  transportCoefficient_critical_of_recursiveRemainder P (canonical_uniform_recursive_remainders P) p j hp hj
namespace ComplexCanonical
lemma transportCoefficient_family_quotient_extension (P:PsiTheory) :
    ∃V:Set ℂ,IsOpen V ∧ Convex ℝ V ∧ (∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈V) ∧
      ∀p:ℕ,1 ≤ p→∀j:ℕ,1 ≤ j→∃F:ℂ→ℂ,AnalyticOnNhd ℂ F V ∧
        ∀Y∈Ico (0:ℝ) y₀,F (Y:ℂ)=
          ((WP.HigherOrder.transportCoefficient P p j Y/(A Y*r Y):ℝ):ℂ):=
  transportCoefficient_family_quotient_extension_of_recursiveRemainder P (canonical_uniform_recursive_remainders P)
end ComplexCanonical
end WP.HigherOrder
