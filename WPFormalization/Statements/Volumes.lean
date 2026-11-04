import WPFormalization.Statements.Marked

/-! Conditional volume model. `volumeModel` is the finite intersection transform;
it is NOT declared equal to the geometric WP volume. The realization is a separate,
currently blocked objective. No geometric probability statements are asserted here. -/
noncomputable section
namespace WP
open Filter Asymptotics
open scoped Topology

/- Cusp volume in the constrained numerical model. -/
/- Blueprint label(s): eq:intro-Phi
Paper v3: 1.1 [PDF 4]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:intro-Phi"]
def volumeModel (P : PsiTheory) (g n : ℕ) : ℝ := mixedBracket P g (List.replicate n 0)

/- Eq.1.1 in the numerical interface. -/
/- Blueprint label(s): eq:intro-Phi
Paper v3: 1.1 [PDF 4]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:intro-Phi"]
def Phi (P : PsiTheory) (g : ℕ) (x : ℂ) : ℂ :=
  ∑' n : ℕ, (volumeModel P g n : ℂ) / (2*Real.pi^2 : ℂ)^(dimension g n) * x^n/n.factorial

def markedF (P : PsiTheory) (g p : ℕ) (x : ℝ) : ℝ := (iteratedDeriv p (Phi P g) x).re

/- Eq.1.5. n=0, n=1 and the k=0 continuity convention are explicit branches. -/
/- Blueprint label(s): eq:intro-leading
Paper v3: 1.5 [PDF 5]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:intro-leading"]
def leadingVolume (g n : ℕ) : ℝ :=
  if n = 0 then
    Real.Gamma (2*(g : ℝ)-2)*(4*Real.pi^2)^(2*g-3)/Real.sqrt (Real.pi*g)
  else
    let h : ℝ := 2*(g : ℝ)-1
    let k : ℕ := n-1
    let Y := densityY (2*k/h)
    let x := XR Y
    (2*Real.pi^2)^(dimension g n)*Real.Gamma h /
      (Real.pi*4^g*Real.sqrt (Real.pi*h)) * varpi Y / (Real.sqrt 2*action Y)^(2*g-1) *
      (if k = 0 then 1 else ((k : ℝ)/(Real.exp 1*x))^k*Real.sqrt (k/(h*euler Psi x)))

/- Eq.7.8's explicit transport coefficient, independent of g. -/
/- Blueprint label(s): eq:PF8
Paper v3: 7.8 [PDF 36]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:PF8"]
def transportBeta (p : ℕ) (Y : ℝ) : ℝ :=
  A Y*((7-2*(p : ℝ))/4*Theta Y-moment₁ Y+2-p)-1/2

/- Eq.10.1, explicit extraction phase and normalized amplitude. -/
/- Blueprint label(s): eq:CE1
Paper v3: 10.1 [PDF 46]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:CE1"]
def extractionS (x : ℝ) : ℝ := Real.log (Z 0 / Z (inverseY x))
/- Blueprint label(s): eq:CE1
Paper v3: 10.1 [PDF 46]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:CE1"]
def extractionB (p : ℕ) (x : ℝ) : ℝ :=
  let Y := inverseY x
  Real.rpow (r Y) ((p : ℝ)/2)*Real.sqrt (A Y*Theta Y) /
    (Real.rpow (r 0) ((p : ℝ)/2)*Real.sqrt (A 0*Theta 0))

/- Blueprint label(s): eq:CG1
Paper v3: 10.3 [PDF 47]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:CG1"]
def poissonCenter (k : ℕ) : ℝ := Real.exp (-(k : ℝ)) * (k : ℝ)^k/k.factorial
/- Eq.10.3, explicit k=0 continuous value. -/
/- Blueprint label(s): eq:CG1
Paper v3: 10.3 [PDF 47]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:CG1"]
def extractionQ (g p k : ℕ) : ℝ :=
  let h := complexity g p
  let Y := densityY (2*(k : ℝ)/h)
  let x := XR Y
  markedModel g p Y / Real.pi *
    (if k = 0 then 1 else x⁻¹^k*poissonCenter k*Real.sqrt ((k : ℝ)/(h*euler Psi x)))

/- Eq.9.4, law given directly by coefficients, with no arbitrary probability function. -/
/- Blueprint label(s): eq:TL37
Paper v3: 9.4 [PDF 41]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:TL37"]
def cuspMass (P : PsiTheory) (g p k : ℕ) (x : ℝ) : ℝ :=
  realCoeff (iteratedDeriv p (Phi P g)) k * x^k / markedF P g p x


end WP
