import WPFormalization.HigherOrder.Triangular
import WPFormalization.Statements.Volumes

/-! The explicit second degree coefficient and finite transport coefficient from
Appendix C.1--C.2. These are genuine formulas, not unspecified functions satisfying
an asymptotic bound. Path independence and the profile remainder are proved in
`Marked.SecondProfileCoherence` and exposed in `Statements.SecondProfile`. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries

/-- α_p in Eq.C.1. -/
def alpha (p : ℕ) (Y : ℝ) : ℝ :=
  A Y*((p-3 : ℝ)*Theta Y+2*moment₁ Y+2*p-3)

/-- Tail T_j; natural subtraction below implements max(0,j). -/
def tailWeight (Y : ℝ) (j : ℕ) : ℝ := ∑' l : ℕ, weight Y (l+j)

/- B_{p,i}(d) of Eq.C.2, written with the distinguished marking first. -/
@[blueprint "lem:second-profile"]
def secondIncrement (Y : ℝ) (i : ℕ) (d : List ℕ) : ℝ :=
  let p := d.length
  let t := d[i]!
  let tail := d.eraseIdx i
  let z := zeros tail
  A Y * (∑ j ∈ Finset.range tail.length, (2*(tail[j]! : ℝ)+1) *
    ∑' l : ℕ, if 1 ≤ t+tail[j]!+l then
      weight Y l*(1-transportBeta (p-1) Y-
        degreeCorrection ((t+tail[j]!+l-1) :: tail.eraseIdx j) Y) else 0) +
  2*A Y * (∑' l : ℕ, if 2 ≤ t+l then weight Y l *
    ∑ u ∈ Finset.range (t+l-1),
      (1-transportBeta (p+1) Y-alpha p Y-degreeCorrection (u :: (t+l-2-u) :: tail) Y)
    else 0) +
  (A Y)^2*((Nat.choose z 2+theta Y 1/2)*tailWeight Y (2-t)+tailWeight Y (3-t)/2)

/- e_p is defined along the fixed left-to-right coordinate path of Eq.C.3. -/
@[blueprint "lem:second-profile"]
def secondProfile (Y : ℝ) (d : List ℕ) : ℝ :=
  -(∑ i ∈ Finset.range d.length, ∑ t ∈ Finset.range d[i]!,
    secondIncrement Y i (beforeCoordinate d i t))

@[simp] theorem secondProfile_empty (Y : ℝ) : secondProfile Y [] = 0 := by
  simp [secondProfile]

/-- M_j=Σl l^j w_l. All orders used below are at most three. -/
def kernelMoment (j : ℕ) (Y : ℝ) : ℝ := ∑' l : ℕ, (l : ℝ)^j*weight Y l

@[simp] theorem kernelMoment_zero (Y : ℝ) : kernelMoment 0 Y = Theta Y := by
  simp [kernelMoment,Theta]

@[simp] theorem kernelMoment_one (Y : ℝ) : kernelMoment 1 Y = moment₁ Y := by
  simp [kernelMoment,moment₁]

/-- The cubic B_∞(t), obtained by expanding Eq.C.9 after removing its low cutoffs.
Moments replace powers of the kernel summation index exactly as in Eq.C.10. -/
def cubicIncrement (p : ℕ) (Y : ℝ) : Polynomial ℝ :=
  let a := A Y
  let m₀ := Theta Y
  let m₁ := moment₁ Y
  let m₂ := kernelMoment 2 Y
  let m₃ := kernelMoment 3 Y
  let q : ℝ := p
  let x : Polynomial ℝ := Polynomial.X
  let k := x-1
  let s := x-2
  let r₀ := 1-transportBeta (p-1) Y-a*(4-q)
  let r₁ := -a*((q-5)*m₀+2*m₁)
  let r₂ := -a*m₀
  let c := 1-transportBeta (p+1) Y-alpha p Y
  let s₀ := c+a
  let s₁ := c-a*((q-3)*m₀+2*m₁+5-2*q)
  let s₂ := -a*((q-2)*m₀+2*m₁)
  let s₃ := -a*m₀
  Polynomial.C (a*(q-1)) *
    (Polynomial.C (r₀*m₀) + Polynomial.C r₁*(Polynomial.C m₀*k+Polynomial.C m₁) +
      Polynomial.C r₂*(Polynomial.C m₀*k^2+Polynomial.C (2*m₁)*k+Polynomial.C m₂)) +
  Polynomial.C (2*a) *
    (Polynomial.C (s₀*m₀) + Polynomial.C s₁*(Polynomial.C m₀*s+Polynomial.C m₁) +
      Polynomial.C s₂*(Polynomial.C m₀*s^2+Polynomial.C (2*m₁)*s+Polynomial.C m₂) +
      Polynomial.C s₃*(Polynomial.C m₀*s^3+Polynomial.C (3*m₁)*s^2+
        Polynomial.C (3*m₂)*s+Polynomial.C m₃)) +
  Polynomial.C (a^2*((Nat.choose (p-1) 2 : ℝ)+theta Y 1/2+1/2)*m₀)

/-- The polynomial R_P after removing the k=0 correction. -/
def rInfinity (p : ℕ) (Y k : ℝ) : ℝ :=
  1-transportBeta (p-1) Y-A Y*(Theta Y*(k^2+(p-5 : ℝ)*k)+2*moment₁ Y*k+(4-p))

/-- The polynomial S_P after removing the s=0 correction. -/
def sInfinity (p : ℕ) (Y s : ℝ) : ℝ :=
  (s+1)*(1-transportBeta (p+1) Y-alpha p Y)-
    A Y*((s+1)*(Theta Y*(s^2+(p-3 : ℝ)*s)+2*moment₁ Y*s)+(5-2*(p : ℝ))*s-1)

/-- Δ_t=B_P(t)-B_∞(t), computed with only the omitted low coefficients.
This expression is identically zero for t≥3; no infinite kernel sum is used. -/
def exceptionalIncrement (p t : ℕ) (Y : ℝ) : ℝ :=
  A Y*(p-1 : ℝ)*
    (-(∑ l ∈ Finset.range (1-t), weight Y l*rInfinity p Y ((t : ℝ)+l-1)) +
      if t ≤ 1 then A Y*(4-p)*weight Y (1-t) else 0) +
  2*A Y*
    (-(∑ l ∈ Finset.range (2-t), weight Y l*sInfinity p Y ((t : ℝ)+l-2)) -
      if t ≤ 2 then A Y*weight Y (2-t) else 0) -
  (A Y)^2*(((Nat.choose (p-1) 2 : ℝ)+theta Y 1/2)*
    (∑ l ∈ Finset.range (2-t), weight Y l) + (∑ l ∈ Finset.range (3-t), weight Y l)/2)

theorem exceptionalIncrement_eq_zero (p t : ℕ) (Y : ℝ) (ht : 3 ≤ t) :
    exceptionalIncrement p t Y = 0 := by
  have h₁ : 1-t = 0 := Nat.sub_eq_zero_of_le (by omega)
  have h₂ : 2-t = 0 := Nat.sub_eq_zero_of_le (by omega)
  have h₃ : 3-t = 0 := Nat.sub_eq_zero_of_le ht
  have ht₁ : ¬ t ≤ 1 := by omega
  have ht₂ : ¬ t ≤ 2 := by omega
  simp [exceptionalIncrement,h₁,h₂,h₃,ht₁,ht₂]

/-- Euler-plus-one operator of the finite b_d moment formula in Appendix C.2. -/
def eulerPlusOne (f : ℂ → ℂ) (z : ℂ) : ℂ := z*deriv f z+f z

def bMoment (j : ℕ) (Y : ℝ) : ℝ := ((eulerPlusOne^[j]) (barH Y) 1).re/3

/-- Σ_b in Eq.C.11. Only four scalar moments and the cubic coefficients occur. -/
def sigmaB (p : ℕ) (Y : ℝ) : ℝ :=
  let a := fun j => (cubicIncrement p Y).coeff j
  a 3/4*(bMoment 4 Y-2*bMoment 3 Y+bMoment 2 Y) +
    a 2/6*(2*bMoment 3 Y-3*bMoment 2 Y+bMoment 1 Y) +
    a 1/2*(bMoment 2 Y-bMoment 1 Y)+a 0*bMoment 1 Y

/-- The finite, canonical transport coefficient γ_p of Eq.C.11. -/
def transportGamma (p : ℕ) (Y : ℝ) : ℝ :=
  transportBeta p Y^2-transportBeta p Y+
    (sigmaB (p+1) Y+exceptionalIncrement (p+1) 0 Y*A Y+
      exceptionalIncrement (p+1) 1 Y*(A Y-1/3)+
      exceptionalIncrement (p+1) 2 Y*(A Y-1/3+theta Y 1/5))/A Y

/- The endpoint first constant t_p, Eq.8.1 / Appendix C.9. -/
@[blueprint "eq:ST13"]
def firstEndpointConstant (p : ℕ) : ℝ := (-2*(p : ℝ)^2+12*p-11)/20

/- The first marked correction L_p of Eq.8.1, with the actual finite γ_p formula. -/
@[blueprint "eq:ST13"]
def firstMarkedCorrection (p : ℕ) (Y : ℝ) : ℝ :=
  firstEndpointConstant p - ∫ v in Y..y₀, transportGamma p v/(A v*r v)

@[simp] theorem firstMarkedCorrection_endpoint (p : ℕ) :
    firstMarkedCorrection p y₀ = firstEndpointConstant p := by
  simp [firstMarkedCorrection]

end WP.HigherOrder
