import WPFormalization.Statements.Basic

/-! Finite formal operations used in Appendix C and Section 10.
All coefficients are computed from finite sums or Mathlib's formal series operations;
no convergence of the inverse-complexity series is postulated. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries

abbrev Series := PowerSeries ℝ

/-- The variable t/(1-c t), corresponding to complexity h-c. -/
def shiftVariable (c : ℝ) : Series := PowerSeries.X * (1-C c*PowerSeries.X)⁻¹

/-- Composition with the actual zero-constant rational series t/(1-c t). -/
def complexityShift (c : ℝ) (f : Series) : Series := f.subst (shiftVariable c)

@[simp] theorem shiftVariable_constant (c : ℝ) : constantCoeff (shiftVariable c) = 0 := by
  simp [shiftVariable]

@[simp] theorem complexityShift_constant (c : ℝ) (f : Series) :
    constantCoeff (complexityShift c f) = constantCoeff f := by
  exact PowerSeries.constantCoeff_subst_of_constantCoeff_zero (shiftVariable_constant c) f

@[simp] theorem shiftVariable_zero : shiftVariable 0 = PowerSeries.X := by
  simp [shiftVariable]

@[simp] theorem complexityShift_zero (f : Series) : complexityShift 0 f = f := by
  simp [complexityShift]

/-- Replace precisely one formal coefficient. -/
def setCoeff (f : Series) (k : ℕ) (x : ℝ) : Series :=
  PowerSeries.mk (fun j => if j = k then x else PowerSeries.coeff j f)

@[simp] theorem setCoeff_same (f : Series) (k : ℕ) (x : ℝ) :
    PowerSeries.coeff k (setCoeff f k x) = x := by simp [setCoeff]

theorem setCoeff_other (f : Series) (k j : ℕ) (x : ℝ) (h : j ≠ k) :
    PowerSeries.coeff j (setCoeff f k x) = PowerSeries.coeff j f := by simp [setCoeff,h]

@[simp] theorem setCoeff_constant (f : Series) (k : ℕ) (x : ℝ) (h : k ≠ 0) :
    constantCoeff (setCoeff f k x) = constantCoeff f := by
  simpa only [← coeff_zero_eq_constantCoeff] using setCoeff_other f k 0 x (Ne.symm h)

/-- A coefficientwise sum. Its convergence, when needed analytically, is a separate obligation. -/
def coefficientSum (f : ℕ → Series) : Series :=
  PowerSeries.mk (fun k => ∑' l : ℕ, PowerSeries.coeff k (f l))

@[simp] theorem coefficientSum_coeff (f : ℕ → Series) (k : ℕ) :
    PowerSeries.coeff k (coefficientSum f) = ∑' l : ℕ, PowerSeries.coeff k (f l) := by simp [coefficientSum]

/-- Finite coefficient formula for the formal exponential of a series with
zero constant coefficient. On that domain only powers 0,...,n contribute in
degree n. Outside that domain this is merely the displayed finite operation,
and is not the exponential of a nonzero constant term. -/
def finiteExp (f : Series) : Series :=
  PowerSeries.mk (fun n => ∑ j ∈ Finset.range (n+1), PowerSeries.coeff n (f^j)/(j.factorial : ℝ))

@[simp] theorem finiteExp_constant (f : Series) : constantCoeff (finiteExp f) = 1 := by
  simp [finiteExp, ← coeff_zero_eq_constantCoeff]

/-- Generalized binomial coefficients, in particular (1+t)^(1/2). -/
def binomial (a : ℝ) : Series := PowerSeries.binomialSeries ℝ a

@[simp] theorem binomial_constant (a : ℝ) : constantCoeff (binomial a) = 1 := by
  simp [binomial]

/-- Equation 11.7: the true finite formal product once the cusp and marked series are supplied.
The second factor uses the shift h -> h-1, with c=1. -/
def unmarkedProduct (cusp₀ marked₁ : Series) : Series :=
  binomial (1/2) * complexityShift 1 cusp₀ * marked₁

theorem unmarkedProduct_constant (cusp₀ marked₁ : Series)
    (hc : constantCoeff cusp₀ = 1) (hm : constantCoeff marked₁ = 1) :
    constantCoeff (unmarkedProduct cusp₀ marked₁) = 1 := by
  simp [unmarkedProduct,hc,hm]

end WP.HigherOrder
