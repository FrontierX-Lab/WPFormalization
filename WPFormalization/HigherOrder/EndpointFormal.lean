import WPFormalization.HigherOrder.FiniteSeries

/-! Canonical endpoint formal coefficients from the Painleve I equations and the
finite normalization formula Eq.C.37. The coefficients are explicitly generated;
no endpoint asymptotic or Stokes estimate is assumed here. Their identification
with the exact endpoint E_{g,p} is a separate paper theorem. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries

/-- Zero-instanton recurrence from -u''/6+u²=Z, u₀=1.
The coefficient table is truncated and extended by zero at every finite stage. -/
def zeroInstantonTable : ℕ → ℕ → ℚ
  | 0 => fun k => if k = 0 then 1 else 0
  | n+1 => fun k => if k = n+1 then
      ((25*(n : ℚ)^2-1)/48)*zeroInstantonTable n n -
        (1/2 : ℚ)*∑ j ∈ Finset.Icc 1 n,
          zeroInstantonTable n j*zeroInstantonTable n (n+1-j)
    else zeroInstantonTable n k

def zeroInstantonCoefficient (g : ℕ) : ℚ := zeroInstantonTable g g

@[simp] theorem zeroInstantonCoefficient_zero : zeroInstantonCoefficient 0 = 1 := by
  norm_num [zeroInstantonCoefficient,zeroInstantonTable]
@[simp] theorem zeroInstantonCoefficient_one : zeroInstantonCoefficient 1 = -1/48 := by
  norm_num [zeroInstantonCoefficient,zeroInstantonTable]

/-- Coefficient of ξ^(-2g) in the equation J_{ξξ}-2J_ξ+Q(ξ)J=0.
Here action²=192/25 and the g=1 coefficient is 1/4 exactly. -/
def jumpPotential (g : ℕ) : ℚ :=
  if g = 0 then 0 else
    (if g = 1 then 3*(192/25 : ℚ)/256 else 0)-zeroInstantonCoefficient g*(192/25 : ℚ)^g

@[simp] theorem jumpPotential_one : jumpPotential 1 = 1/4 := by
  norm_num [jumpPotential]

/-- The normalized jump coefficients v_j of Appendix C.9.
This recursion is obtained by formal coefficient comparison in the linearized
Painleve equation; the analytic jump's asymptotic identification is NOT assumed. -/
def jumpTable : ℕ → ℕ → ℚ
  | 0 => fun k => if k = 0 then 1 else 0
  | n+1 => fun k => if k = n+1 then
      -(((n+1 : ℕ) : ℚ)*n*jumpTable n n +
        ∑ g ∈ Finset.Icc 1 ((n+2)/2), jumpPotential g*jumpTable n (n+2-2*g)) /
        (2*(n+1 : ℕ))
    else jumpTable n k

def jumpCoefficient (j : ℕ) : ℚ := jumpTable j j

@[simp] theorem jumpCoefficient_zero : jumpCoefficient 0 = 1 := by
  norm_num [jumpCoefficient,jumpTable]
@[simp] theorem jumpCoefficient_one : jumpCoefficient 1 = -1/8 := by
  norm_num [jumpCoefficient,jumpTable,jumpPotential,Finset.sum_Icc_succ_top]

/-- Re-expansion of Σ v_j Γ(ν-j)/Γ(ν), with ν=h₀+3/2, in t=h₀⁻¹.
Only j≤n can contribute to coefficient n. -/
def endpointZ : Series := PowerSeries.mk (fun n =>
  ∑ j ∈ Finset.range (n+1), (jumpCoefficient j : ℝ)*
    PowerSeries.coeff n ((PowerSeries.X : Series)^j *
      ∏ a ∈ Finset.range j, (1+C (1/2-(a : ℝ))*PowerSeries.X)⁻¹))

@[simp] theorem endpointZ_constant : constantCoeff endpointZ = 1 := by
  norm_num [endpointZ, ← coeff_zero_eq_constantCoeff]

/-- Bernoulli polynomial B_n(a), with Mathlib's B₁=-1/2 convention. -/
def bernoulliPolynomialValue (n : ℕ) (a : ℚ) : ℚ :=
  ∑ k ∈ Finset.range (n+1), (Nat.choose n k : ℚ)*bernoulli k*a^(n-k)

/-- Formal log Γ(h₀+α)/(Γ(h₀)h₀^α). -/
def gammaRatioLog (a : ℚ) : Series := PowerSeries.mk (fun n =>
  if n = 0 then 0 else
    ((-1 : ℝ)^(n+1) *
      (bernoulliPolynomialValue (n+1) a-bernoulliPolynomialValue (n+1) 0) /
      ((n : ℝ)*(n+1))))

@[simp] theorem gammaRatioLog_constant (a : ℚ) : constantCoeff (gammaRatioLog a) = 0 := by
  simp [gammaRatioLog, ← coeff_zero_eq_constantCoeff]

def gammaRatioSeries (a : ℚ) : Series := finiteExp (gammaRatioLog a)

@[simp] theorem gammaRatioSeries_constant (a : ℚ) : constantCoeff (gammaRatioSeries a) = 1 := by
  simp [gammaRatioSeries]

/-- Exact finite insertion factor R_p(h₀), Eq.C.37. -/
def endpointInsertion (p : ℕ) : Series :=
  PowerSeries.rescale (p : ℝ) (binomial (1/2)) *
    ∏ i ∈ Finset.range p,
      (1+C (4*(i : ℝ)/5)*PowerSeries.X) * (1+C (i : ℝ)*PowerSeries.X)⁻¹

@[simp] theorem endpointInsertion_constant (p : ℕ) : constantCoeff (endpointInsertion p) = 1 := by
  have hr : constantCoeff (PowerSeries.rescale (p : ℝ) (binomial (1/2))) = 1 := by
    rw [← coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale]
    simp [coeff_zero_eq_constantCoeff]
  rw [endpointInsertion, map_mul, hr]
  simp

/-- The canonical normalized endpoint E_{g,p}, initially in h₀⁻¹, Eq.C.37. -/
def endpointAtH₀ (p : ℕ) : Series :=
  endpointZ*gammaRatioSeries (3/2)*endpointInsertion p*(1+C (4/5 : ℝ)*PowerSeries.X)⁻¹

@[simp] theorem endpointAtH₀_constant (p : ℕ) : constantCoeff (endpointAtH₀ p) = 1 := by
  simp [endpointAtH₀]

/-- Change h₀=h-p, preserving the finite complexity shift exactly. -/
def endpointSeries (p : ℕ) : Series := complexityShift p (endpointAtH₀ p)

@[simp] theorem endpointSeries_constant (p : ℕ) : constantCoeff (endpointSeries p) = 1 := by
  simp [endpointSeries]

/-- Finite coefficient formula for the formal logarithm when the input has
constant term 1. Only powers 1,...,n then enter coefficient n. Outside that
domain this operation is not asserted to be a formal logarithm. -/
def finiteLog (f : Series) : Series := PowerSeries.mk (fun n =>
  ∑ j ∈ Finset.Icc 1 n, (-1 : ℝ)^(j+1)*PowerSeries.coeff n ((f-1)^j)/j)

@[simp] theorem finiteLog_constant (f : Series) : constantCoeff (finiteLog f) = 0 := by
  simp [finiteLog, ← coeff_zero_eq_constantCoeff]

/-- The a*_{p,j} of Appendix C.9, generated from the fixed canonical endpoint series. -/
def endpointLogCoefficient (p j : ℕ) : ℝ := PowerSeries.coeff j (finiteLog (endpointSeries p))

@[simp] theorem endpointLogCoefficient_zero (p : ℕ) : endpointLogCoefficient p 0 = 0 := by
  simp [endpointLogCoefficient, finiteLog]

end WP.HigherOrder
