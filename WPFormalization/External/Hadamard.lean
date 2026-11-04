import WPFormalization.Statements.Basic
/-! A genus-zero specialization of the classical Hadamard factorization theorem.
Source: C. McMullen, Advanced Complex Analysis, Harvard Math 213a notes
(2017 version), Thm3.7, printed p.43 / PDF p.44; convergence Thm3.11,
printed p.44; proof of the factorization through printed p.47:
https://people.math.harvard.edu/~ctm/home/text/class/harvard/213a/10/html/home/course/course.pdf
The explicit square-root growth bound gives order at most one half. Since
f(0) is nonzero, and every zero is simple and enumerated injectively, the
canonical factors have genus zero and the only exponential factor is a
constant, fixed by f(0). The zero sum is absolutely convergent, so the product
is unconditional in the enumeration. The input contains no kernel, parameter
family, root construction, positivity, common disk, or uniform coefficient
estimate. Each application must prove these paper-specific facts separately.
-/
noncomputable section
namespace WP.External

theorem hadamard_genus_zero_of_sqrt_growth
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hzero : f 0 ≠ 0)
    (A B : ℝ) (hA : 0<A) (hB : 0<B)
    (hgrowth : ∀ z : ℂ, ‖f z‖≤A*Real.exp (B*Real.sqrt ‖z‖))
    (roots : ℕ → ℂ) (hinj : Function.Injective roots)
    (hroots : ∀ z : ℂ, f z=0 ↔ ∃ n, z=roots n)
    (hsimple : ∀ n, deriv f (roots n)≠0) :
    ∀ z : ℂ, HasProd (fun n=>1-z/roots n) (f z/f 0) := by
  sorry

end WP.External
