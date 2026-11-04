import WPFormalization.Statements.Volumes

/-! Original diagonal-chain profile and factorial normalization. -/
noncomputable section
namespace WP

/- Eq.1.10 / WC1, with its specified continuous planar endpoint. -/
/- Blueprint label(s): eq:WC1
Paper v3: 1.8 [PDF 8]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:WC1"]
def chainProfile (t : ℝ) : ℝ :=
  if t = 1 then -2*Real.log (2*xCritical) else
    ∫ u in (0 : ℝ)..t, Real.log (4*Delta (densityY (2*u/(1-u)))/Real.pi^2)

def normalizedVolume (P : PsiTheory) (g n : ℕ) : ℝ :=
  volumeModel P g n/((2*g+n-3).factorial*(4*Real.pi^2)^(2*g+n-3))

end WP
