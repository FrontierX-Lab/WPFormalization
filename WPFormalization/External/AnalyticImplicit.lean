import WPFormalization.HigherOrder.MajorantDefinitions

/-! Classical analytic implicit-function theorem for an already given formal solution.

Source: Guillemin--Campbell, MIT18.117 Lecture Notes (2005), PDF pp.15--16,
holomorphic inverse and implicit function theorems, together with the convergent
Taylor-series discussion on PDF pp.5--6:
https://ocw.mit.edu/courses/18-117-topics-in-several-complex-variables-spring-2005/3e8b0c3499d6226959485ace042cdaab_18117notes.pdf

The statement below is a classical CONSEQUENCE, not a verbatim theorem in those
notes. Complexify the absolutely convergent signed real series, apply the
holomorphic implicit-function theorem, and identify the Taylor coefficients
with the already supplied formal solution. The standard finite-substitution /
Taylor-coefficient bridge and general invertible-Jacobian formal uniqueness are
included in this deferred classical proof.

This interface does not construct a formal solution, prove triangular formal
uniqueness, prove nonnegative coefficients, give a geometric coefficient bound,
or compare any extended-valued subsolution. Those are proved separately in the
majorant implementation. No triangularity or positivity hypothesis occurs here.
-/
noncomputable section
namespace WP.External

/- A convergent implicit system with nonsingular v-Jacobian has no divergent
zero-constant formal branch. All coefficients may have either sign. -/
theorem convergent_formal_implicit_solution (m : ℕ)
    (Φ : Fin m → MvPowerSeries (Option (Fin m)) ℝ)
    (hzero : ∀ i, MvPowerSeries.coeff 0 (Φ i) = 0)
    (hconv : ∃ r : ℝ, 0 < r ∧ ∀ i,
      Summable (fun α : Option (Fin m) →₀ ℕ =>
        |MvPowerSeries.coeff α (Φ i)| * r^(multiDegree α)))
    (hjacobian : Matrix.det ((1 : Matrix (Fin m) (Fin m) ℝ) -
      Matrix.of (fun i l => MvPowerSeries.coeff (Finsupp.single (some l) 1) (Φ i))) ≠ 0)
    (U : Fin m → PowerSeries ℝ)
    (hUzero : ∀ i, PowerSeries.coeff 0 (U i) = 0)
    (hfixed : ∀ i j, PowerSeries.coeff j (U i) = substitutionCoeff (Φ i) U j) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i,
      Summable (fun j : ℕ => |PowerSeries.coeff j (U i)| * ρ^j) := by
  sorry

end WP.External
