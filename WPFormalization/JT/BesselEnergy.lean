import WPFormalization.Analysis.BoundaryEndpoints

/-! The Bessel expressions in the JT energy variable, defined by entire power
series. In particular negative energies are not sent through `Real.sqrt`.
The identifications with the existing X and a are proved from their series. -/
noncomputable section
namespace WP.JT

def edgeEnergy (Y : ℝ) : ℝ := -Y/Real.pi^2

def besselI0EnergyC (E : ℂ) : ℂ :=
  ∑' n : ℕ, ((Real.pi : ℂ)^2*E)^n/(n.factorial : ℂ)^2

def besselI0Energy (E : ℝ) : ℝ := (besselI0EnergyC E).re

lemma besselI0EnergyC_eq_derivX (E : ℂ) :
    besselI0EnergyC E = deriv X (-(Real.pi : ℂ)^2*E) := by
  have hs := Complex.hasSum_taylorSeries_of_entire X_differentiable.deriv 0
    (-(Real.pi : ℂ)^2*E)
  unfold besselI0EnergyC
  rw [← hs.tsum_eq]
  apply tsum_congr
  intro n
  simp only [sub_zero, smul_eq_mul]
  rw [← iteratedDeriv_succ', iteratedDeriv_X_succ_zero]
  have hp : (-1:ℂ)^n * (-(Real.pi : ℂ)^2*E)^n = ((Real.pi : ℂ)^2*E)^n := by
    rw [← mul_pow]
    congr 1
    ring
  rw [← hp]
  simp only [div_eq_mul_inv]
  ring

lemma besselI0EnergyC_hasSum (E : ℂ) :
    HasSum (fun n : ℕ => ((Real.pi : ℂ)^2*E)^n/(n.factorial : ℂ)^2)
      (besselI0EnergyC E) := by
  rw [besselI0EnergyC_eq_derivX]
  convert Complex.hasSum_taylorSeries_of_entire X_differentiable.deriv 0
    (-(Real.pi : ℂ)^2*E) using 1
  ext n
  simp only [sub_zero, smul_eq_mul]
  rw [← iteratedDeriv_succ', iteratedDeriv_X_succ_zero]
  have hp : (-1:ℂ)^n * (-(Real.pi : ℂ)^2*E)^n = ((Real.pi : ℂ)^2*E)^n := by
    rw [← mul_pow]
    congr 1
    ring
  rw [← hp]
  simp only [div_eq_mul_inv]
  ring

lemma besselI0Energy_eq_a (E : ℝ) :
    besselI0Energy E = a (-Real.pi^2*E) := by
  rw [besselI0Energy, besselI0EnergyC_eq_derivX]
  simp only [a, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow]

lemma besselI0EnergyC_differentiable : Differentiable ℂ besselI0EnergyC := by
  have he : besselI0EnergyC = fun E : ℂ => deriv X (-(Real.pi : ℂ)^2*E) :=
    funext besselI0EnergyC_eq_derivX
  rw [he]
  exact X_differentiable.deriv.comp (by fun_prop)

lemma besselI0Energy_continuous : Continuous besselI0Energy := by
  exact Complex.continuous_re.comp
    (besselI0EnergyC_differentiable.continuous.comp Complex.continuous_ofReal)

lemma besselI0Energy_eq_I₀ (E : ℝ) (hE : 0 ≤ E) :
    besselI0Energy E = (I₀ ((2*Real.pi*Real.sqrt E : ℝ) : ℂ)).re := by
  rw [besselI0Energy, besselI0EnergyC_eq_derivX, Analysis.I₀_eq_derivX]
  congr 2
  have hs : (Real.sqrt E : ℂ)^2 = (E : ℂ) := by exact_mod_cast Real.sq_sqrt hE
  push_cast
  calc
    -(Real.pi : ℂ)^2*(E : ℂ) = -(Real.pi : ℂ)^2*(Real.sqrt E : ℂ)^2 := by rw [hs]
    _ = -(((2 : ℂ)*Real.pi*Real.sqrt E)/2)^2 := by ring

/-- Entire continuation of sqrt(E)/(2π) I₁(2π sqrt(E)). -/
def stringBesselEnergyC (E : ℂ) : ℂ :=
  ∑' n : ℕ, ((Real.pi : ℂ)^2)^n*E^(n+1) /
    (2*(n.factorial : ℂ)*(n+1).factorial)

def stringBesselEnergy (E : ℝ) : ℝ := (stringBesselEnergyC E).re

lemma stringBesselEnergyC_eq_X (E : ℂ) :
    stringBesselEnergyC E = -X (-(Real.pi : ℂ)^2*E)/(2*(Real.pi : ℂ)^2) := by
  unfold stringBesselEnergyC X
  rw [← tsum_neg, ← tsum_div_const]
  apply tsum_congr
  intro n
  have hp : (-1:ℂ)^n * (-(Real.pi : ℂ)^2*E)^(n+1) =
      -((Real.pi : ℂ)^2)^n*E^(n+1)*(Real.pi : ℂ)^2 := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]
    have hn : (-1:ℂ)*(-(Real.pi : ℂ)^2*E) = (Real.pi : ℂ)^2*E := by ring
    rw [hn, mul_pow, pow_succ]
    ring
  rw [hp]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

private lemma X_hasSum_complex (z : ℂ) :
    HasSum (fun n : ℕ => (-1:ℂ)^n*z^(n+1)/
      ((n.factorial:ℂ)*(n+1).factorial)) (X z) := by
  have hs := (hasSum_nat_add_iff' 1).mpr
    (Complex.hasSum_taylorSeries_of_entire X_differentiable 0 z)
  convert hs using 1
  · ext n
    rw [iteratedDeriv_X_succ_zero]
    simp only [sub_zero, smul_eq_mul]
    ring
  · simp [X]

lemma stringBesselEnergyC_hasSum (E : ℂ) :
    HasSum (fun n : ℕ => ((Real.pi : ℂ)^2)^n*E^(n+1) /
      (2*(n.factorial : ℂ)*(n+1).factorial)) (stringBesselEnergyC E) := by
  rw [stringBesselEnergyC_eq_X]
  convert (((X_hasSum_complex (-(Real.pi : ℂ)^2*E)).neg).div_const
    (2*(Real.pi : ℂ)^2)) using 1
  ext n
  have hp : (-1:ℂ)^n * (-(Real.pi : ℂ)^2*E)^(n+1) =
      -((Real.pi : ℂ)^2)^n*E^(n+1)*(Real.pi : ℂ)^2 := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]
    have hn : (-1:ℂ)*(-(Real.pi : ℂ)^2*E) = (Real.pi : ℂ)^2*E := by ring
    rw [hn, mul_pow, pow_succ]
    ring
  rw [hp]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

lemma stringBesselEnergy_eq_XR (E : ℝ) :
    stringBesselEnergy E = -XR (-Real.pi^2*E)/(2*Real.pi^2) := by
  rw [stringBesselEnergy, stringBesselEnergyC_eq_X]
  have he : -(Real.pi : ℂ)^2*(E : ℂ) = ((-Real.pi^2*E : ℝ) : ℂ) := by push_cast; rfl
  rw [he]
  rw [show (2:ℂ)*(Real.pi : ℂ)^2 = ((2*Real.pi^2 : ℝ) : ℂ) by push_cast; rfl]
  simp only [XR, Complex.div_ofReal_re, Complex.neg_re]

lemma stringBesselEnergyC_differentiable : Differentiable ℂ stringBesselEnergyC := by
  have he : stringBesselEnergyC = fun E : ℂ =>
      -X (-(Real.pi : ℂ)^2*E)/(2*(Real.pi : ℂ)^2) := funext stringBesselEnergyC_eq_X
  rw [he]
  exact ((X_differentiable.comp (by fun_prop)).neg).div_const _

/-- The usual modified Bessel function of order one, by its entire series. -/
def modifiedBessel1 (z : ℂ) : ℂ :=
  ∑' n : ℕ, (z/2)^(2*n+1)/((n.factorial : ℂ)*(n+1).factorial)

/-- The energy combination is independent of a choice of complex square root. -/
lemma stringBesselEnergyC_sq (w : ℂ) :
    stringBesselEnergyC (w^2) =
      w/(2*(Real.pi : ℂ))*modifiedBessel1 (2*(Real.pi : ℂ)*w) := by
  unfold stringBesselEnergyC modifiedBessel1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [show 2*(Real.pi : ℂ)*w/2 = (Real.pi : ℂ)*w by ring]
  simp only [mul_pow, pow_add, pow_one, pow_mul]
  field_simp

lemma stringBesselEnergy_eq_I₁ (E : ℝ) (hE : 0 ≤ E) :
    stringBesselEnergy E =
      Real.sqrt E/(2*Real.pi) *
        (modifiedBessel1 ((2*Real.pi*Real.sqrt E : ℝ) : ℂ)).re := by
  have he : (Real.sqrt E : ℂ)^2 = (E : ℂ) := by exact_mod_cast Real.sq_sqrt hE
  have hs := congrArg Complex.re (stringBesselEnergyC_sq (Real.sqrt E : ℂ))
  rw [he] at hs
  rw [show (Real.sqrt E : ℂ)/(2*(Real.pi : ℂ)) =
    ((Real.sqrt E/(2*Real.pi) : ℝ) : ℂ) by push_cast; rfl] at hs
  simpa only [stringBesselEnergy, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hs

end WP.JT
