import Mathlib
import VersoBlueprint.Attribute

/-! Numerical conventions used in the paper. No geometric moduli space is constructed here. -/
noncomputable section
namespace WP
open scoped BigOperators
open Filter Asymptotics

/- Blueprint def:stable, PDF p.3. Integer arithmetic avoids truncated natural subtraction. -/
/- Blueprint label(s): def:stable
Paper v3: unnumbered [PDF 3]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "def:stable"]
def Stable (g n : ℕ) : Prop := 2 < 2 * g + n

instance (g n : ℕ) : Decidable (Stable g n) := inferInstanceAs (Decidable (2 < 2*g+n))

/- Blueprint label(s): def:stable
Paper v3: unnumbered [PDF 3]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "def:stable"]
def complexity (g n : ℕ) : ℕ := 2 * g + n - 2
/- Blueprint label(s): def:stable
Paper v3: unnumbered [PDF 3]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "def:stable"]
def dimension (g n : ℕ) : ℕ := 3 * g + n - 3
/- Blueprint label(s): def:stable
Paper v3: unnumbered [PDF 3]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "def:stable"]
def totalDegree (d : List ℕ) : ℕ := d.sum
/- Blueprint label(s): def:stable
Paper v3: unnumbered [PDF 3]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "def:stable"]
def deficit (g : ℕ) (d : List ℕ) : ℕ := dimension g d.length - d.sum

def oddFactorial (n : ℕ) : ℕ := ∏ j ∈ Finset.range (n + 1), (2 * j + 1)

/-- Taylor coefficient of a scalar analytic function at zero. -/
def coeff (f : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n f 0 / n.factorial

def realCoeff (f : ℂ → ℂ) (n : ℕ) : ℝ := (coeff f n).re

/- The entire series in def:bessel; no unspecified value is chosen. -/
/- Blueprint label(s): def:bessel
Paper v3: unnumbered [PDF 4]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "def:bessel"]
def X (z : ℂ) : ℂ := ∑' j : ℕ, (-1 : ℂ)^j * z^(j+1) / (j.factorial * (j+1).factorial)
/- Blueprint label(s): def:bessel
Paper v3: unnumbered [PDF 4]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "def:bessel"]
def XR (y : ℝ) : ℝ := (X y).re
/- Blueprint label(s): def:bessel
Paper v3: unnumbered [PDF 4]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "def:bessel"]
def a (y : ℝ) : ℝ := (deriv X y).re
/- Infimum definition is total; nonemptiness and the root property are separate obligations. -/
/- Blueprint label(s): def:bessel
Paper v3: unnumbered [PDF 4]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "def:bessel"]
def y₀ : ℝ := sInf {y : ℝ | 0 < y ∧ deriv X y = 0}
/- Blueprint label(s): def:bessel
Paper v3: unnumbered [PDF 4]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "def:bessel"]
def xCritical : ℝ := XR y₀
/- Blueprint label(s): def:bessel
Paper v3: unnumbered [PDF 4]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "def:bessel"]
def inverseY (x : ℝ) : ℝ := sInf {y : ℝ | y ≤ y₀ ∧ XR y = x}

def I₀ (z : ℂ) : ℂ := ∑' j : ℕ, (z / 2)^(2*j) / (j.factorial : ℂ)^2

/- The following series lemmas prove entire analyticity and the exact origin jets directly
from the defining factorial series. They assume no kernel/positivity/root theorem. -/
private def xAuxCoeff (n : ℕ) : ℂ := (-1 : ℂ)^n / ((n.factorial : ℂ)*(n+1).factorial)
private lemma xAuxCoeff_ne (n : ℕ) : xAuxCoeff n ≠ 0 := by
  simp [xAuxCoeff, Nat.factorial_ne_zero]
private lemma xAuxCoeff_succ (n : ℕ) :
    xAuxCoeff (n+1) = -xAuxCoeff n / (((n+1 : ℕ) : ℂ)*(n+2)) := by
  unfold xAuxCoeff
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp
  ring
private lemma xAux_ratio (n : ℕ) :
    ‖xAuxCoeff (n+1)‖ / ‖xAuxCoeff n‖ = 1/(((n : ℝ)+1)*((n : ℝ)+2)) := by
  rw [xAuxCoeff_succ, norm_div, norm_neg, norm_mul]
  have hn : ‖xAuxCoeff n‖ ≠ 0 := norm_ne_zero_iff.mpr (xAuxCoeff_ne n)
  norm_cast
  field_simp
private lemma xAux_radius :
    (FormalMultilinearSeries.ofScalars ℂ xAuxCoeff).radius = ⊤ := by
  apply FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto
  · exact Filter.Eventually.of_forall xAuxCoeff_ne
  · simp_rw [Nat.succ_eq_add_one, xAux_ratio]
    have hg : Tendsto (fun n : ℕ => ((n : ℝ)+1)*((n : ℝ)+2)) atTop atTop :=
      tendsto_atTop_mono (fun n => by nlinarith [Nat.cast_nonneg (α := ℝ) n])
        (tendsto_natCast_atTop_atTop (R := ℝ))
    convert (tendsto_inv_atTop_zero.comp hg) using 1
    funext n
    simp [one_div, mul_inv_rev]
private lemma xAux_analytic (z : ℂ) : AnalyticAt ℂ (FormalMultilinearSeries.ofScalarsSum xAuxCoeff) z := by
  exact (FormalMultilinearSeries.analyticOnNhd
    (p := FormalMultilinearSeries.ofScalars ℂ xAuxCoeff)) z (by simp [xAux_radius])
private lemma X_eq_xAux : X = fun z : ℂ => z * FormalMultilinearSeries.ofScalarsSum xAuxCoeff z := by
  funext z
  rw [FormalMultilinearSeries.ofScalars_sum_eq, ← tsum_mul_left]
  unfold X
  apply tsum_congr
  intro n
  simp only [xAuxCoeff, smul_eq_mul, div_eq_mul_inv, pow_succ]
  ring
lemma X_differentiable : Differentiable ℂ X := by
  rw [X_eq_xAux]
  exact differentiable_id.mul (fun z => (xAux_analytic z).differentiableAt)
private lemma xAux_jets (n : ℕ) :
    iteratedDeriv n (FormalMultilinearSeries.ofScalarsSum xAuxCoeff) 0 =
      (n.factorial : ℂ)*xAuxCoeff n := by
  have h := (FormalMultilinearSeries.hasFPowerSeriesOnBall
    (FormalMultilinearSeries.ofScalars ℂ xAuxCoeff) (by simp [xAux_radius])).hasFPowerSeriesAt
  have heq := h.eq_formalMultilinearSeries (xAux_analytic 0).hasFPowerSeriesAt
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) heq
  simp only [FormalMultilinearSeries.coeff_ofScalars] at hc
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp at hc
  linear_combination -hc
lemma iteratedDeriv_X_succ_zero (n : ℕ) :
    iteratedDeriv (n+1) X 0 = (-1 : ℂ)^n/(n.factorial : ℂ) := by
  rw [X_eq_xAux]
  rw [iteratedDeriv_fun_mul (by fun_prop) (xAux_analytic 0).contDiffAt]
  simp only [iteratedDeriv_fun_id_zero]
  rw [Finset.sum_eq_single 1]
  · simp only [ite_true, mul_one, Nat.choose_one_right, Nat.add_sub_cancel]
    rw [xAux_jets]
    unfold xAuxCoeff
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  · intro b hb hne
    simp [hne]
  · simp

/-- The explicit real restriction of the Bessel series. -/
theorem X_ofReal (y : ℝ) : X (y : ℂ) =
    Complex.ofReal (∑' j : ℕ, (-1 : ℝ)^j*y^(j+1)/(j.factorial*(j+1).factorial)) := by
  rw [Complex.ofReal_tsum]
  unfold X
  apply tsum_congr
  intro j
  push_cast
  rfl

theorem X_im_ofReal (y : ℝ) : (X (y : ℂ)).im = 0 := by
  rw [X_ofReal]
  exact Complex.ofReal_im _

/-- Differentiation of a holomorphic function that is real on the real axis stays real there. -/
theorem deriv_im_eq_zero_of_real_axis (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hr : ∀ x : ℝ, (f x).im = 0) (y : ℝ) : (deriv f y).im = 0 := by
  have h₁ := (hf (y : ℂ)).hasDerivAt.comp_ofReal
  have h : HasDerivAt (fun x : ℝ => (f x).im) (deriv f y).im y :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt y h₁
  have heq : (fun x : ℝ => (f x).im) = fun _ => (0 : ℝ) := by
    funext x
    exact hr x
  have he := h.deriv
  rw [heq, deriv_const] at he
  exact he.symm

theorem iteratedDeriv_X_differentiable (n : ℕ) : Differentiable ℂ (iteratedDeriv n X) := by
  induction n with
  | zero => simpa using X_differentiable
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact fun z => ((ih.analyticAt z).deriv).differentiableAt

theorem iteratedDeriv_X_im_ofReal (n : ℕ) (y : ℝ) : (iteratedDeriv n X y).im = 0 := by
  induction n generalizing y with
  | zero => simpa using X_im_ofReal y
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact deriv_im_eq_zero_of_real_axis _ (iteratedDeriv_X_differentiable n) ih y

theorem iteratedDeriv_X_zero (k : ℕ) (hk : 1 ≤ k) :
    iteratedDeriv k X 0 = (-1 : ℂ)^(k-1)/((k-1).factorial : ℂ) := by
  cases k with
  | zero => omega
  | succ n => simpa using iteratedDeriv_X_succ_zero n

theorem iteratedDeriv_X_zero_re (k : ℕ) (hk : 1 ≤ k) :
    (iteratedDeriv k X 0).re = (-1 : ℝ)^(k-1)/((k-1).factorial : ℝ) := by
  rw [iteratedDeriv_X_zero k hk]
  norm_cast

theorem a_zero : a 0 = 1 := by
  unfold a
  have h := iteratedDeriv_X_zero_re 1 (by norm_num)
  simpa using h

/- Entire Bessel functions by their standard order-zero and order-one series. -/
/- Blueprint label(s): def:bessel
Paper v3: unnumbered [PDF 4]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "def:bessel"]
def besselJ₀ (z : ℂ) : ℂ := ∑' j : ℕ, (-1 : ℂ)^j*(z/2)^(2*j)/(j.factorial : ℂ)^2
/- Blueprint label(s): def:bessel
Paper v3: unnumbered [PDF 4]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "def:bessel"]
def besselJ₁ (z : ℂ) : ℂ := ∑' j : ℕ, (-1 : ℂ)^j*(z/2)^(2*j+1)/
  ((j.factorial : ℂ)*(j+1).factorial)
/- Blueprint label(s): def:bessel
Paper v3: unnumbered [PDF 4]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "def:bessel"]
def firstJ₀Zero : ℝ := sInf {t : ℝ | 0 < t ∧ besselJ₀ t = 0}

end WP
