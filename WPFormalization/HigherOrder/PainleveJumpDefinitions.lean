import WPFormalization.External.PainleveAnalyticData

/-! The actual positive-real Boutroux coordinate and normalized GIKM jump.
These are definitions from Appendix C.9, with the GIKM Stokes convention.
No jump expansion or Borel identification is assumed here. -/
noncomputable section
namespace WP.HigherOrder

/-- The original PI coordinate corresponding to a positive Boutroux variable. -/
def painleveJumpCoordinate (ξ : ℝ) : ℝ :=
  Real.rpow (ξ / External.painleveAction) (4/5 : ℝ)

/-- The actual adjacent-solution jump in the paper's normalization. -/
def normalizedPainleveJump (G : External.PainleveAnalytic.GIKMData) (ξ : ℝ) : ℂ :=
  let Z := painleveJumpCoordinate ξ
  (G.u 1 (Z : ℂ) - G.u 0 (Z : ℂ)) /
    (-External.PainleveAnalytic.S₁ * Complex.exp (-(ξ : ℂ)) *
      (Real.rpow Z (-1/8 : ℝ) : ℂ))

/-- Its real part is sufficient for the real endpoint coefficient contour. -/
def realNormalizedPainleveJump (G : External.PainleveAnalytic.GIKMData) (ξ : ℝ) : ℝ :=
  (normalizedPainleveJump G ξ).re

end WP.HigherOrder
