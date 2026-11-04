import WPFormalization.Statements.Volumes

/-! All-degree coefficients and endpoint estimates, conditional on the numerical psi interface. -/
noncomputable section
namespace WP
open Filter
open scoped Topology

/- b is the bracket; a is the coefficient multiplying L^(2k)/(2k+1)!, NOT the raw monomial coefficient. -/
/- Blueprint label(s): eq:C23
Paper v3: 13.23 [PDF 55]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:C23"]
def bracketB (P : PsiTheory) (g k : ℕ) : ℝ := mixedBracket P g [k]
/- Blueprint label(s): eq:C18
Paper v3: 13.18 [PDF 55]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:C18"]
def boundaryA (P : PsiTheory) (g k : ℕ) : ℝ := bracketB P g k / (4 : ℝ)^k
/- Blueprint label(s): eq:C7
Paper v3: 13.7 [PDF 53]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "eq:C7"]
def mixedJ (P : PsiTheory) (g k : ℕ) : ℝ :=
  bracketB P g k * (3*g-2-k).factorial /
    ((oddFactorial k : ℝ)*4^k*(2*Real.pi^2)^(3*g-2-k))

/-- Exact relative error of the all-degree saddle prediction. -/
def adjacentError (P : PsiTheory) (g k : ℕ) : ℝ :=
  |(boundaryA P g k/boundaryA P g (k+1))/(4*Real.pi^2/(trigSaddle g k)^2)-1|

/- Unscaled Y=0 kernel mean and its inverse on [0,3/2]. -/
/- Blueprint label(s): lem:uniform-saddle
Paper v3: E.2 [PDF 98]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:uniform-saddle"]
def unscaledMean (z : ℝ) : ℝ := -z*(deriv (H 0) z).re/(H 0 z).re
/- Blueprint label(s): lem:uniform-saddle
Paper v3: E.2 [PDF 98]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:uniform-saddle"]
def saddleZeta (u : ℝ) : ℝ := sInf {z : ℝ | z ∈ Set.Icc 0 (Real.pi^2/2) ∧ unscaledMean z = u}
/- Blueprint label(s): lem:uniform-saddle
Paper v3: E.2 [PDF 98]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "lem:uniform-saddle"]
def unscaledCoeff (h m : ℕ) : ℝ := realCoeff (fun z => (H 0 z)⁻¹^h) m

/- First-order normalized cusp/genus quantities, Eq.C.13, without formal-series placeholders. -/
/- Blueprint label(s): lem:first-order
Paper v3: C.6 [PDF 81]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "lem:first-order", blueprint "eq:FE1"]
def cuspCorrection (P : PsiTheory) (g p : ℕ) (Y : ℝ) : ℝ :=
  (complexity g p : ℝ)/A Y*W P g p Y/W P g (p+1) Y
/- Blueprint label(s): lem:first-order
Paper v3: C.6 [PDF 81]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "lem:first-order", blueprint "eq:FE1"]
def genusCorrection (P : PsiTheory) (g p : ℕ) (Y : ℝ) : ℝ :=
  if g=0 then 0 else W P (g-1) (p+2) Y/W P g p Y

/- Appendix C.3 sets the invalid negative-genus numerator to zero. -/
@[simp] lemma genusCorrection_zero (P : PsiTheory) (p : ℕ) (Y : ℝ) :
    genusCorrection P 0 p Y=0 := by simp [genusCorrection]

lemma genusCorrection_of_pos (P : PsiTheory) (g p : ℕ) (Y : ℝ) (hg : 0<g) :
    genusCorrection P g p Y=W P (g-1) (p+2) Y/W P g p Y := by
  simp only [genusCorrection,if_neg (by omega : g≠0)]

/- Eq.13.14, including both continuous endpoint values via 0 log 0 = 0. -/
/- Blueprint label(s): lem:log-comparison
Paper v3: E.3 [PDF 98]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "lem:log-comparison"]
def logDegreeProfile (α : ℝ) : ℝ :=
  let z := saddleZeta ((3-α)/2)
  show ℝ from -2*Real.log (H 0 z).re-(3-α)*Real.log z+(3-α)*Real.log (3-α)+
    3*Real.log 6-α*Real.log (2*α)-2*(3-α)

/- Blueprint label(s): lem:log-comparison
Paper v3: E.3 [PDF 98]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "lem:log-comparison"]
def logComparisonG (P : PsiTheory) (g k : ℕ) : ℝ :=
  Real.log (mixedJ P g k/(mixedJ P g (3*g-2)*(g : ℝ)^(2*(3*g-2-k))))

end WP
