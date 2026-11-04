import WPFormalization.External.IntersectionTheory
/-! Classical nef projective intersection data, deferred for phase two.

INT-NEF sources: Arbarello--Cornalba alg-geom/9406008, Section 1,
Eq.(1.5)--(1.7), PDF pp.4--6 (the logarithmic kappa_1 is ample);
Keel math/9901149 Theorem 0.4, PDF p.3 (nefness holds in characteristic zero);
Boucksom--Favre--Jonsson math/0608260v2 Theorem 2.15, PDF p.15
(the classical nef Khovanskii--Teissier inequality).

The existence input also defers the classical DVV uniqueness and KMZ/Wolpert
transfer already exposed by IntersectionRealization. Passing from compact
DM orbifolds to projective schemes uses a finite level cover and a resolution,
nef pullback, and the same positive degree factor in all top intersections.
These transfer proofs remain explicit phase-two responsibilities. Only g>=2
is used, so the universal curve over unpointed genus g is stable.

No numerical mixedJ, coefficient ratio, or asymptotic estimate is a field.
No actual geometric instance is constructed here.
-/
set_option autoImplicit false
noncomputable section
universe u
namespace WP.External

/-- Classical nef mixed-intersection calculus, to be instantiated by projective orbifold classes. -/
structure NefIntersectionCalculus {g n:ℕ}(D:DMClasses.{u} g n) where
  Nef : D.Carrier → Prop
  teissier : ∀a b:D.Carrier,Nef a → Nef b →∀k:ℕ,1 ≤ k → k < dimension g n →
    D.integral (a^(dimension g n-(k-1))*b^(k-1))*
      D.integral (a^(dimension g n-(k+1))*b^(k+1)) ≤
        D.integral (a^(dimension g n-k)*b^k)^2

/-- Only the existing geometric realization and classical nefness; no numerical inequality is a field. -/
structure OnePointNefRealization (P:PsiTheory)(g:ℕ) where
  realization : IntersectionRealization.{u} P
  calculus : NefIntersectionCalculus (realization.classes g 1)
  psi_nef : calculus.Nef ((realization.classes g 1).psi 0)
  kappa_nef : calculus.Nef ((realization.classes g 1).kappa₁)

/- Classical geometric data existence, not the paper's numerical C7 conclusion. -/
@[blueprint "ext:nef-teissier"]
theorem classical_onepoint_nef_realization (P : PsiTheory) (g : ℕ) (hg : 2 ≤ g) :
    Nonempty (OnePointNefRealization.{0} P g) := by
  sorry

end WP.External
