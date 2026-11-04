import WPFormalization.Statements.IntersectionInterface

/-! Explicit classical intersection-theory inputs, with no global geometric instance.

Source INT-KMZ: Kaufmann--Manin--Zagier (1996), arXiv:alg-geom/9604001;
the mixed kappa/psi formula is restated precisely in Liu--Xu (2014), arXiv:1103.5136v2,
Eq.(24), p.6. INT-WOLPERT is [omega_WP]=2*pi^2*kappa_1 (Wolpert 1985;
Liu--Xu Eq.(1), p.1). These are pre-existing results, not this paper's asymptotics.

`DMClasses` is an abstract cohomological shadow: a ring, the actual distinguished
class roles, and pairing with the fundamental class. No DM stack or instance is
constructed or asserted. The interfaces below expose every imported equality.
-/
noncomputable section
universe u
namespace WP.External

/- Even tautological real cohomology, its distinguished degree-two classes, and the fundamental pairing.
The vanishing law states exactly which monomials have top complex degree. -/
@[blueprint "def:intersections"]
structure DMClasses (g n : ℕ) where
  Carrier : Type u
  [ring : CommRing Carrier]
  [algebra : Algebra ℝ Carrier]
  psi : Fin n → Carrier
  kappa₁ : Carrier
  wpClass : Carrier
  integral : Carrier →ₗ[ℝ] ℝ
  wolpert : wpClass = (2*Real.pi^2) • kappa₁
  dimension_vanish : ∀ (m : ℕ) (d : Fin n → ℕ),
    m + ∑ i, d i ≠ dimension g n →
    integral (kappa₁^m * ∏ i, psi i^(d i)) = 0

attribute [instance] DMClasses.ring DMClasses.algebra

@[blueprint "def:intersections"]
def mixedIntegral {g n : ℕ} (D : DMClasses.{u} g n) (m : ℕ) (d : Fin n → ℕ) : ℝ :=
  D.integral (D.kappa₁^m * ∏ i, D.psi i^(d i))

@[blueprint "def:intersections"]
def geometricBracket {g n : ℕ} (D : DMClasses.{u} g n) (d : Fin n → ℕ) : ℝ :=
  if Stable g n ∧ ∑ i, d i ≤ dimension g n then
    let m := dimension g n - ∑ i, d i
    (∏ i, (oddFactorial (d i) : ℝ)) * (4 : ℝ)^(∑ i, d i) *
      (2*Real.pi^2)^m * (mixedIntegral D m d / m.factorial)
  else 0

/- The finite background sum in the classical kappa/psi transformation, without any
new shifted-time or large-genus estimate. -/
def kappaPsiSum (P : PsiTheory) (g : ℕ) (d : List ℕ) : ℝ :=
  ∑ l ∈ backgrounds (deficit g d), pure P g (d ++ backgroundDegrees l) *
    ∏ i : Fin (deficit g d),
      (((-1 : ℝ)^(i.val+2)/(i.val+1).factorial)^(l i))/(l i).factorial

/- The geometric realization of the numerical psi theory is an explicit parameter.
The only additional transform is the classical KMZ identity. No new comparison,
profile, positivity, LLT, or uniform asymptotic claim occurs as a field. -/
@[blueprint "ext:mixed-transform"]
structure IntersectionRealization (P : PsiTheory) where
  classes : ∀ g n, DMClasses.{u} g n
  pure_identification : ∀ (g n : ℕ) (d : Fin n → ℕ), Stable g n →
    (∑ i, d i = dimension g n) →
    (classes g n).integral (∏ i, (classes g n).psi i^(d i)) = pure P g (List.ofFn d)
  kappa_psi_transform : ∀ (g n : ℕ) (d : Fin n → ℕ), Stable g n →
    (∑ i, d i ≤ dimension g n) →
    mixedIntegral (classes g n) (dimension g n - ∑ i, d i) d /
      (dimension g n - ∑ i, d i).factorial = kappaPsiSum P g (List.ofFn d)

end WP.External
