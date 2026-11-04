import WPFormalization.Statements.Volumes

noncomputable section
namespace WP
/- The universal positive factor in §9.1, constructed from the same numerical Phi. -/
/- Blueprint label(s): lem:convolution
Paper v3: 9.1 [PDF 40]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "lem:convolution"]
def universalV (P : PsiTheory) (z : ℂ) : ℂ := iteratedDeriv 3 (Phi P 0) z

/- Blueprint label(s): lem:convolution
Paper v3: 9.1 [PDF 40]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "lem:convolution"]
def convolutionR (P : PsiTheory) (g p : ℕ) (z : ℂ) : ℂ :=
  iteratedDeriv p (Phi P g) z / universalV P z^(complexity g p)

end WP
