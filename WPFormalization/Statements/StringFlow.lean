import WPFormalization.Volumes.StringFlowProof

/-! Original string-flow identity for the actual cusp generating function. -/
noncomputable section
namespace WP

/- Eq.4.7 on the numerical interface. Unstable genus-zero derivatives are excluded. -/
/- Blueprint label(s): eq:H8
Paper v3: 4.7 [PDF 20]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:H8"]
theorem string_flow (P : PsiTheory) (g n : ℕ) (hst : Stable g n)
    (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    shifted P g (List.replicate n 0) Y = markedF P g n (XR Y) := by
  exact string_flow_proof P g n hst Y hY

end WP
