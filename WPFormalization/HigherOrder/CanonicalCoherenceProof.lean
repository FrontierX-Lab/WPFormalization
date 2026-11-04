import WPFormalization.HigherOrder.RecursiveRemainderProof
import WPFormalization.HigherOrder.CanonicalAdjacentFromRemainder
import WPFormalization.HigherOrder.ComplexCanonicalCoherence
import WPFormalization.Statements.CoefficientBounds
/-! Genuine canonical path compatibility after supplying the proved actual remainder.
These results have no unproved paper-goal premise. The complex increment is the
prescribed coefficient of the already constructed order-(K-1) jet.
The remaining finite-data part of C.3 is a separate obligation. -/

noncomputable section
namespace WP.HigherOrder
open Set

theorem canonical_adjacent_compatibility (P:PsiTheory) : CanonicalAdjacentCompatibility P:=
  canonical_adjacent_compatibility_of_recursiveRemainder P (canonical_uniform_recursive_remainders P)

theorem canonical_coefficient_path_independent (P:PsiTheory)
    (p K:ℕ) (hp:1 ≤ p) (hK:0<K) (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀)
    (v w:ℕ→List ℕ) (i j:ℕ→ℕ) (n m:ℕ)
    (hvlen:∀s < n,(v s).length=p) (hwlen:∀s < m,(w s).length=p)
    (hi:∀s < n,i s<(v s).length) (hj:∀s < m,j s<(w s).length)
    (hv:∀s < n,v (s+1)=raiseDegree (v s) (i s))
    (hw:∀s < m,w (s+1)=raiseDegree (w s) (j s))
    (hstart:v 0=w 0) (hend:v n=w m) :
    (∑s∈Finset.range n,adjacentCoefficient P Y (formalHierarchyJet P Y) K (i s) (v s))=
      ∑s∈Finset.range m,adjacentCoefficient P Y (formalHierarchyJet P Y) K (j s) (w s):=
  canonical_coefficient_path_independent_of_adjacent P (canonical_adjacent_compatibility P)
    p K hp hK Y hY v w i j n m hvlen hwlen hi hj hv hw hstart hend

theorem canonical_common_complex_domain_coherence (P:PsiTheory) :
    ∃ (Ω:Set ℂ) (R:ℂ→ℂ),IsOpen Ω ∧ Convex ℝ Ω ∧
      (∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧
      (∀j:ℕ,∀d:List ℕ,1 ≤ d.length→
        AnalyticOnNhd ℂ (fun z=>ComplexCanonical.profileCoefficient P R z d j) Ω) ∧
      (∀j p:ℕ,1 ≤ p→
        AnalyticOnNhd ℂ (fun z=>ComplexCanonical.cuspCoefficient P R z p j) Ω ∧
        AnalyticOnNhd ℂ (fun z=>ComplexCanonical.genusCoefficient P R z p j) Ω) ∧
      (∀j:ℕ,∀d:List ℕ,1 ≤ d.length→∀Y∈Icc (0:ℝ) y₀,
        ComplexCanonical.profileCoefficient P R (Y:ℂ) d j=(profileCoefficient P Y d j:ℂ)) ∧
      (∀K:ℕ,0<K→∀d:List ℕ,1 ≤ d.length→∀i:ℕ,i<d.length→∀z∈Ω,
        ComplexCanonical.profileCoefficient P R z (raiseDegree d i) K-
          ComplexCanonical.profileCoefficient P R z d K=
          ComplexCanonical.adjacentCoefficient P R z (ComplexCanonical.hierarchyJet P R z (K-1)) K i d):=by
  obtain ⟨Ω,R,C,B,M,hΩ,hΩv,hcover,hC,hB,hM,hR,hunit,hraw,hR0,hR',hkernel,
    hprofA,hscalA,hprofR,hscalR,hprofB,hscalB⟩:=
      ComplexCanonical.canonicalCoefficientBoundsTarget_proof P
  refine ⟨Ω,R,hΩ,hΩv,hcover,hprofA,hscalA,hprofR,?_⟩
  intro K hK d hd i hi z hz
  exact ComplexCanonical.canonical_adjacent_on_complex_domain_of_recursiveRemainder P
    (canonical_uniform_recursive_remainders P) Ω hΩv hcover R hprofA hprofR K hK d hd i hi z hz
end WP.HigherOrder
