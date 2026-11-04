import WPFormalization.HigherOrder.SecondProfile
import WPFormalization.HigherOrder.EndpointFormal

/-! Canonical marked logarithmic and exponential coefficients from the actual
triangular cusp construction and the fixed Painleve endpoint series. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries

/-- γ_{p,j} from the true inverse cusp series, Eq.C.34. -/
def transportCoefficient (P : PsiTheory) (p j : ℕ) (Y : ℝ) : ℝ :=
  PowerSeries.coeff (j+1) ((formalCusp P Y p)⁻¹)

/-- The actual coefficients a_{p,j} of Eq.C.38. -/
def logarithmicMarkedCoefficient (P : PsiTheory) (p j : ℕ) (Y : ℝ) : ℝ :=
  if j = 0 then 0 else endpointLogCoefficient p j -
    ∫ v in Y..y₀, transportCoefficient P p j v/(A v*r v)

/-- The zero-constant formal logarithm prescribed by the transport integral. -/
def markedLogSeries (P : PsiTheory) (p : ℕ) (Y : ℝ) : Series :=
  PowerSeries.mk (fun i => logarithmicMarkedCoefficient P p i Y)

@[simp] theorem markedLogSeries_constant (P : PsiTheory) (p : ℕ) (Y : ℝ) :
    constantCoeff (markedLogSeries P p Y) = 0 := by
  simp [markedLogSeries,logarithmicMarkedCoefficient]

/-- The actual L_{p,j} of Eq.C.38: finite formal exponentiation of the
zero-constant `markedLogSeries`. -/
def markedCoefficient (P : PsiTheory) (p j : ℕ) (Y : ℝ) : ℝ :=
  PowerSeries.coeff j (finiteExp (markedLogSeries P p Y))

@[simp] theorem markedCoefficient_zero (P : PsiTheory) (p : ℕ) (Y : ℝ) :
    markedCoefficient P p 0 Y = 1 := by
  simp [markedCoefficient,finiteExp]

@[simp] theorem logarithmicMarkedCoefficient_endpoint (P : PsiTheory) (p j : ℕ) (hj : j ≠ 0) :
    logarithmicMarkedCoefficient P p j y₀ = endpointLogCoefficient p j := by
  simp [logarithmicMarkedCoefficient,hj]

/- Eq.11.7 using the actual canonical cusp and marked coefficient families. -/
@[blueprint "eq:AV7"]
def canonicalUnmarkedSeries (P : PsiTheory) : Series :=
  unmarkedProduct (formalCusp P 0 0) (PowerSeries.mk (fun j => markedCoefficient P 1 j 0))

@[blueprint "eq:AV7"]
def unmarkedCoefficient (P : PsiTheory) (j : ℕ) : ℝ :=
  PowerSeries.coeff j (canonicalUnmarkedSeries P)

@[simp] theorem unmarkedCoefficient_zero (P : PsiTheory) : unmarkedCoefficient P 0 = 1 := by
  rw [unmarkedCoefficient, coeff_zero_eq_constantCoeff]
  simp [canonicalUnmarkedSeries,unmarkedProduct]

end WP.HigherOrder
