import WPFormalization.External.IntersectionTheory
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
/-! Generic classical higher-kappa intersection data (INT-HIGHER-KAPPA).

The classes are the logarithmic classes of the actual compact stable-curve
moduli stack: kappa_j=pi_*(K^(j+1)), K=c1(omega_pi(sum original sections)).
They share kappa_1 with the existing `IntersectionRealization`.

Direct primary sources:
* Manin--Zograf, Ann. Inst. Fourier 50(2) (2000), Theorem 4.1, printed p.525:
  arbitrary-times kappa/psi generating-function substitution. Taking x^0
  gives the finite unmarked polynomial identity below, with the standard
  multiplicity factorials and no extra dimension factorial.
* Kaufmann--Manin--Zagier, CMP 181 (1996), Theorem 2.2 (2.6)--(2.7), p.774,
  Corollary 2.3 (2.17), p.777: the equivalent arbitrary-genus transform.
* Arbarello--Cornalba, alg-geom/9406008, Section 1 p.5: logarithmic kappa
  definition and (1.6), ampleness of kappa_1; positive top degree follows.
* Keel, math/9901149, Theorem 0.4, p.255/PDF p.3: nefness of the universal
  logarithmic relative dualizing bundle, also in characteristic zero.
* Lazarsfeld, Positivity I (2004), Example 1.4.16, pp.57--58: nonnegativity
  of top mixed products of arbitrary nef divisor classes.

The mixed-kappa nonnegativity law is a DERIVED CLASSICAL COROLLARY, not
claimed as a direct positivity theorem of KMZ: on the r-fold Cartesian fiber
power of the original universal curve, flat base change and the projection
formula identify integral(prod kappa_{a_i}) with integral(prod pr_i^*K^(a_i+1)).
Its dimension is D+r and all divisors are nef. The fiber power permits
coincident added points; it is not Mbar_{g,n+r}, so no diagonal correction is
omitted. The nef mixed-intersection theorem gives nonnegativity in every
stable genus and every top degree. The usual finite projective cover and
positive degree transfer handle the DM-stack pairing.

Phase two must construct these classes and the pairing on genuine DM
moduli, the universal curve and its fiber powers, the finite-cover/stack
transfer, and prove the cited transform/nef/ample laws. No concrete geometry
or global instance is constructed or asserted here. No field contains Y,
planar inversion, tight volumes, coefficient positivity of a quotient, or
any new asymptotic conclusion of the paper.
-/
noncomputable section
universe u
namespace WP.External
abbrev KappaClassFamily (R : IntersectionRealization.{u} P) :=
  ∀ g n : ℕ, ℕ → (R.classes g n).Carrier

def kappaTopIntegral (R : IntersectionRealization.{u} P) (κ : KappaClassFamily R)
    (g n q : ℕ) (e : Fin q → ℕ) : ℝ :=
  (R.classes g n).integral (∏ i, (κ g n (i.val+1))^(e i))

def kappaTimesSeries (s : ℕ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun j=>if j=0 then 0 else s j)
def kappaSchurTime (s : ℕ → ℂ) (j : ℕ) : ℂ :=
  if j=0 then 0 else
    -PowerSeries.coeff j ((PowerSeries.exp ℂ).subst (-kappaTimesSeries s))

def descendantFreeEnergyPolynomial (P : PsiTheory) (g : ℕ) (t : ℕ → ℂ) : ℂ :=
  ∑ l ∈ backgrounds (dimension g 0),
    (pure P g (backgroundDegrees l):ℂ) *
      ∏ i : Fin (dimension g 0), t (i.val+1)^(l i)/(l i).factorial

def kappaFreeEnergyPolynomial (R : IntersectionRealization.{u} P) (κ : KappaClassFamily R)
    (g : ℕ) (s : ℕ → ℂ) : ℂ :=
  ∑ e ∈ backgrounds (dimension g 0),
    (kappaTopIntegral R κ g 0 (dimension g 0) e:ℂ) *
      ∏ i : Fin (dimension g 0), s (i.val+1)^(e i)/(e i).factorial

/-- Generic classical higher-kappa data only; no existence instance is asserted here.
The classes are the logarithmic kappa classes pi_*(K^(j+1)) of the actual
universal stable curve, K=c1(omega_pi(sum original marked sections)). -/
-- Classical generic kappa/psi transformation; this is the original external node.
@[blueprint "ext:mixed-transform"]
structure HigherKappaRealization (P : PsiTheory) where
  realization : IntersectionRealization.{u} P
  kappa : KappaClassFamily realization
  kappa_one : ∀ g n, kappa g n 1=(realization.classes g n).kappa₁
  top_nonnegative : ∀ (g n q : ℕ) (e : Fin q → ℕ), Stable g n →
    (∑ i : Fin q, (i.val+1)*e i)=dimension g n →
      0≤kappaTopIntegral realization kappa g n q e
  kappa_one_top_positive : ∀ g n, Stable g n →
    0<(realization.classes g n).integral
      ((realization.classes g n).kappa₁^(dimension g n))
  free_energy_transform : ∀ g, 2≤g → ∀ s : ℕ → ℂ,
    descendantFreeEnergyPolynomial P g (kappaSchurTime s)=
      kappaFreeEnergyPolynomial realization kappa g s
end WP.External
