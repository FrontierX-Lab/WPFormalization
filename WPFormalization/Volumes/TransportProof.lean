import WPFormalization.Marked.ShiftedTransport
import WPFormalization.Volumes.StringFlowProof

/-! The original transport equation from the actual Phi EGF.
The derivative uses complex analyticity of Phi, including a full real neighborhood
at Y=0; string flow is used only to substitute the values at the point. -/
noncomputable section
namespace WP
lemma transport_equation_proof (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Set.Ico (0:ℝ) y₀,
      |A Y*r Y*deriv (fun t => Real.log (markedF P g p (XR t))) Y-
        ((complexity g p:ℝ)+transportBeta p Y)|≤C/complexity g p := by
  obtain ⟨C,hC,G,hbound⟩ := shifted_transport_proof P p hp
  refine ⟨C,hC,2+G,?_⟩
  intro g hg Y hY
  have hs : Stable g p := by unfold Stable;omega
  have hs' : Stable g (p+1) := by unfold Stable;omega
  rw [(markedF_parameter_log_hasDerivAt P g p hp hs Y hY).deriv]
  rw [←string_flow_proof P g p hs Y hY,←string_flow_proof P g (p+1) hs' Y hY]
  simpa only [transportBeta,dilatonBeta] using hbound g (by omega) Y hY
end WP
