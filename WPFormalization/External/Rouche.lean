import WPFormalization.Statements.Basic
/-! A finite prescribed-zero corollary of the classical Rouche theorem.
MIT 18.112 (2008), Lecture14, PDF pp.5--6 / printed pp.4--5, Corollary1:
https://ocw.mit.edu/courses/18-112-functions-of-a-complex-variable-fall-2008/59e058767d6256ca57d8e757bb257715_lecture14.pdf
Rouche equates numbers of zeros counted with multiplicity. If the comparison
function has exactly n simple zeros, n distinct zeros of the perturbed function
must exhaust its zero count and must also be simple. This generic corollary
includes only that classical counting implication. Any contour estimates,
construction of comparison or target zeros, and kernel-specific zero claims
are separate obligations. No particular analytic function occurs in it. -/
noncomputable section
namespace WP.External

def HasAllSimpleZerosInDisk {ι : Type*} [Fintype ι]
    (f : ℂ → ℂ) (R : ℝ) (roots : ι → ℂ) : Prop :=
  Function.Injective roots ∧
    (∀ i, ‖roots i‖ < R ∧ f (roots i) = 0 ∧ deriv f (roots i) ≠ 0) ∧
    (∀ z : ℂ, ‖z‖ < R → f z = 0 → ∃ i, z = roots i)

theorem rouche_exhausts_prescribed_zeros
    {ι : Type*} [Fintype ι] (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (R : ℝ) (hR : 0 < R)
    (hboundary : ∀ z : ℂ, ‖z‖ = R → ‖f z-g z‖ < ‖g z‖)
    (reference target : ι → ℂ)
    (hreference : HasAllSimpleZerosInDisk g R reference)
    (htarget : Function.Injective target)
    (hzeros : ∀ i, ‖target i‖ < R ∧ f (target i) = 0) :
    HasAllSimpleZerosInDisk f R target := by
  sorry

end WP.External
