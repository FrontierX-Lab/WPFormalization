import WPFormalization.Statements.Basic

/-! A generic consequence of classical Pringsheim theory.

Source: Flajolet--Sedgewick, Analytic Combinatorics, Theorem IV.6, printed p.240:
https://algo.inria.fr/flajolet/Publications/book.pdf
The authors' 2006 draft gives the same theorem on printed p.227:
https://algo.inria.fr/flajolet/Publications/book061023.pdf

Pringsheim says that a power series with real nonnegative coefficients and a
finite positive radius has a singularity at the positive real radius. For the
reciprocal of an entire nonzero function, the Taylor radius is the distance to
the nearest zero: such a zero is a pole of the reciprocal. A zero in the stated
closed disk would therefore force a zero on the positive real segment. The
formal Taylor/analytic-germ bridge and this standard pole/radius argument are
included in the deferred classical proof below. This is a consequence, not a
verbatim statement of the book's theorem.

The input applies to arbitrary entire scalar functions. It contains no kernel,
parameter family, root selection, common radius, or uniform bound. All such
applications and their hypotheses remain separate paper proofs.
-/
noncomputable section
namespace WP.External

theorem zero_free_disk_of_nonnegative_inverseCoefficients
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (R : ℝ) (hR : 0 ≤ R)
    (hcoeff : ∀ n : ℕ,
      (coeff (fun z => (f z)⁻¹) n).im = 0 ∧
        0 ≤ (coeff (fun z => (f z)⁻¹) n).re)
    (hreal : ∀ x : ℝ, x ∈ Set.Icc 0 R → f x ≠ 0) :
    ∀ z : ℂ, ‖z‖ ≤ R → f z ≠ 0 := by
  sorry

end WP.External
