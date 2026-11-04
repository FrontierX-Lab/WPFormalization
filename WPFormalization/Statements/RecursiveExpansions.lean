import WPFormalization.HigherOrder.FullRecursiveExpansionAssembly
import WPFormalization.HigherOrder.FiniteDataInduction

/-! Original Proposition C.3 for the actual canonical hierarchy.
The common-domain coefficient bounds, all-order actual remainders, arbitrary
coordinate compatibility and literal finite-kernel-data construction are all
supplied by proved producers. The only explicit interface is PsiTheory; its
classical external dependency closure is audited separately. -/
noncomputable section
namespace WP

@[blueprint "prop:hierarchy"]
theorem uniform_recursive_expansions (P : PsiTheory) :
    HigherOrder.UniformRecursiveExpansionsTarget P := by
  exact HigherOrder.full_recursive_expansion_assembly P
    (HigherOrder.KernelFiniteData.canonical_polynomial_dependence P)
    (HigherOrder.KernelFiniteData.canonical_profile_boundary_polynomial P)

end WP
