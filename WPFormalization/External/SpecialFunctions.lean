import WPFormalization.Statements.Basic

/-! SF-GAMMA-RATIO: the fixed-shift Gamma ratio expansion, DLMF5.11.13,
https://dlmf.nist.gov/5.11.E13 (G0=1, G1 in5.11.15).
For fixed real alpha,beta, its positive-real specialization gives the quantified
O(1/x) relative error below. Constants may depend on both shifts. This does not
assume the paper's growing-order Gamma expansion or any endpoint WP asymptotic.
Mathlib's current Stirling module treats integer factorials and its Gamma
modules do not expose this shifted real-Gamma error estimate.
-/
noncomputable section
namespace WP.External

@[blueprint "ext:stirling"]
theorem gamma_ratio_error (alpha beta : ℝ) :
    ∃ C x₀ : ℝ, 0 < C ∧ 0 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      |Real.Gamma (x+alpha)/(Real.Gamma (x+beta)*Real.rpow x (alpha-beta))-1| ≤ C/x := by
  sorry

/- The ordinary positive-real Stirling leading term (DLMF5.11.3). -/
@[blueprint "ext:stirling"]
def gammaStirlingMain (x : ℝ) : ℝ :=
  Real.sqrt (2*Real.pi)*Real.rpow x (x-1/2)*Real.exp (-x)

/- SF-GAMMA-STIRLING: fixed-order remainder from DLMF5.11.3--5.11.4.
No order K or auxiliary geometric parameter occurs in this input. -/
@[blueprint "ext:stirling"]
theorem gamma_stirling_error :
    ∃ C x₀ : ℝ, 0 < C ∧ 0 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      |Real.Gamma x/gammaStirlingMain x-1| ≤ C/x := by
  sorry

/- Binet/Stirling logarithmic partial sum, with the exact next Bernoulli term. -/
@[blueprint "ext:stirling"]
def logStirlingPartial (K : ℕ) (x : ℝ) : ℝ :=
  (x-1/2)*Real.log x-x+Real.log (2*Real.pi)/2 +
    ∑ k ∈ Finset.Icc 1 (K-1), (bernoulli (2*k) : ℝ)/
      (((2*k : ℕ) : ℝ)*((2*k-1 : ℕ) : ℝ)*x^(2*k-1))

/- SF-BINET: DLMF5.11(ii), the paragraph immediately before5.11.10:
for positive real x the remainder is bounded by the first omitted term.
The bound is valid for every integer K≥1, and thus keeps its exact order
control. The target paper's subsequent re-expansion estimates are not assumed. -/
@[blueprint "ext:stirling"]
theorem log_gamma_stirling_remainder (K : ℕ) (hK : 1 ≤ K) (x : ℝ) (hx : 0 < x) :
    |Real.log (Real.Gamma x)-logStirlingPartial K x| ≤
      |(bernoulli (2*K) : ℝ)| /
        (((2*K : ℕ) : ℝ)*((2*K-1 : ℕ) : ℝ)*x^(2*K-1)) := by
  sorry

/- Exact Gamma products, already formalized recurrence reused from Mathlib. -/
@[blueprint "ext:stirling"]
theorem gamma_finite_product (x : ℝ) (hx : 0 < x) (n : ℕ) :
    Real.Gamma (x+n) = Real.Gamma x*∏ j ∈ Finset.range n, (x+j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc,
        Real.Gamma_add_one (by positivity : x+(n : ℝ) ≠ 0), ih,
        Finset.prod_range_succ]
      ring

/- Gaussian integration is directly reused, not an admitted input. -/
@[blueprint "ext:stirling"]
theorem gaussian_integral (b : ℝ) (hb : 0 < b) :
    (∫ x : ℝ, Real.exp (-b*x^2)) = Real.sqrt (Real.pi/b) := by
  exact integral_gaussian b

end WP.External
