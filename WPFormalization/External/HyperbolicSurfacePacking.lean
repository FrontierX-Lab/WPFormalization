import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import WPFormalization.External.HyperbolicCurveGeometry

/-! Explicit classical hyperbolic quotient, geodesic and local packing data.

The model uses Mathlib's actual hyperbolic upper half plane and invariant area.
The structures below are explicit stage-one classical inputs, not constructed
instances. They contain no primitive-count, net-cardinality, based-loop count,
or bounded-length finite-label injection statement.

Sources and exact field conditions are recorded in
`audit/primitive-count-classical-fields.md`; source registration is a separate
parent audit obligation and is not asserted complete by this module.

HP-M: Bruno Martelli, *Hyperbolic geometry, surfaces, and 3-manifolds*,
18 December 2013, Chapters 2--5 (quotients, geodesics, thick/thin, doubling, GB).
HP-P: Hugo Parlier, *Interrogating surface length spectra and quantifying
isospectrality*, author manuscript 2016-11-07, pp.4--6, Lemmas 2.1--2.4.
HP-H: Will Hide, IMRN 2023, DOI 10.1093/imrn/rnac293, proof of Lemma 4.7
(explicit noncompact adaptation using Buser Lemma 4.4.6). HP-P's count is only
closed; HP-H verifies the local cusp argument, without importing its final
asymptotic n=o(sqrt g) simplification.
-/
noncomputable section
universe u v w
namespace WP.External.HyperbolicPacking
open Set MeasureTheory
open scoped Classical

def IsometryOn {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    (f : α → β) (s : Set α) : Prop := ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y)=dist x y

abbrev DeckIsometry := UpperHalfPlane ≃ᵢ UpperHalfPlane

def primitiveElement (Γ : Subgroup DeckIsometry) (δ : Γ) : Prop :=
  ∀ η : Γ, ∀ m : ℕ, 2 ≤ m → η^m ≠ δ

/-- An actual primitive axial transformation of the fixed hyperbolic plane. -/
structure PrimitiveAxis (Γ : Subgroup DeckIsometry) (D : Set UpperHalfPlane) where
  deck : Γ
  axis : ℝ → UpperHalfPlane
  isometry : Isometry axis
  period : ℝ
  period_pos : 0 < period
  translates : ∀ t, deck.val (axis t) = axis (t+period)
  in_domain : ∀ t, axis t ∈ D
  primitive : primitiveElement Γ deck

def conjugateOrInverse {Γ : Subgroup DeckIsometry} (δ η : Γ) : Prop :=
  ∃ b : Γ, η=b*δ*b⁻¹ ∨ η=b*δ⁻¹*b⁻¹

/-- Quotient presentation of the actual intrinsic surface. A bordered surface
uses its convex lift domain; a complete boundaryless one has domain=univ. -/
structure QuotientSurface where
  Point : Type u
  [metric : MetricSpace Point]
  [measurable : MeasurableSpace Point]
  [borel : BorelSpace Point]
  area : Measure Point
  finite_area : area univ ≠ ⊤
  Γ : Subgroup DeckIsometry
  domain : Set UpperHalfPlane
  domain_nonempty : domain.Nonempty
  domain_closed : IsClosed domain
  domain_convex : ∀ a : ℝ → UpperHalfPlane, Isometry a → ∀ s t : ℝ,
    a s ∈ domain → a t ∈ domain → ∀ r ∈ Set.uIcc s t, a r ∈ domain
  domain_geodesic_boundary : ∀ z ∈ frontier domain, ∃ a : ℝ → UpperHalfPlane,
    Isometry a ∧ z ∈ Set.range a ∧ Set.range a ⊆ frontier domain
  invariant : ∀ δ : Γ, ∀ z ∈ domain, δ.val z ∈ domain
  free : ∀ δ : Γ, ∀ z : UpperHalfPlane, δ.val z=z → δ=1
  proper_orbit : ∀ z : UpperHalfPlane, ∀ r : ℝ,
    {δ : Γ | dist z (δ.val z) ≤ r}.Finite
  orientation_preserving : ∀ δ : Γ,
    ∃ m : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ z : UpperHalfPlane, δ.val z=m • z
  project : UpperHalfPlane → Point
  surjective_on_domain : ∀ p : Point, ∃ z ∈ domain, project z=p
  local_area : ∀ z ∈ interior domain, ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ domain ∧
    IsometryOn project (Metric.ball z r) ∧ ∀ A ⊆ Metric.ball z r, MeasurableSet A →
      area (project '' A)=volume A
  fibers : ∀ z ∈ domain, ∀ q ∈ domain,
    project z=project q ↔ ∃ δ : Γ, δ.val z=q
  quotient_distance : ∀ z ∈ domain, ∀ q ∈ domain,
    dist (project z) (project q) = sInf (Set.range (fun δ : Γ => dist z (δ.val q)))

attribute [instance] QuotientSurface.metric QuotientSurface.measurable QuotientSurface.borel

/-- Complete, unoriented primitive geodesic classes of the actual deck action.
The class map is complete for *all* primitive axial elements. Its equality,
length and trace laws enforce the actual geodesic quotient semantics. -/
structure PrimitiveGeometry (S : QuotientSurface.{u}) where
  Primitive : Type v
  representative : Primitive → PrimitiveAxis S.Γ S.domain
  classOf : PrimitiveAxis S.Γ S.domain → Primitive
  class_representative : ∀ γ, classOf (representative γ)=γ
  class_eq_iff : ∀ a b, classOf a=classOf b ↔ conjugateOrInverse a.deck b.deck
  period_class : ∀ a, (representative (classOf a)).period=a.period
  trace_class : ∀ a,
    S.project '' Set.range (representative (classOf a)).axis = S.project '' Set.range a.axis
  short : ℝ → Finset Primitive
  mem_short : ∀ L γ, γ ∈ short L ↔ (representative γ).period ≤ L

namespace PrimitiveGeometry
variable {S : QuotientSurface.{u}} (C : PrimitiveGeometry.{u,v} S)
def length (γ : C.Primitive) : ℝ := (C.representative γ).period
def trace (γ : C.Primitive) : Set S.Point := S.project '' Set.range (C.representative γ).axis
end PrimitiveGeometry

def epsilon : ℝ := 1/4
def diskArea (r : ℝ) : ℝ := 2*Real.pi*(Real.cosh r-1)
def Thick (S : QuotientSurface) (p : S.Point) : Prop :=
  ∀ z : UpperHalfPlane, S.project z=p → ∀ δ : S.Γ, δ ≠ 1 → 2*epsilon ≤ dist z (δ.val z)
def coreCollar {S : QuotientSurface} (C : PrimitiveGeometry S) (γ : C.Primitive) : Set S.Point :=
  {p | Metric.infDist p (C.trace γ) < Real.arsinh (1/Real.sinh (C.length γ/2))}
def thinCores {S : QuotientSurface} (C : PrimitiveGeometry S) : Finset C.Primitive :=
  (C.short (2*epsilon)).filter (fun γ => C.length γ < 2*epsilon)

/-- External classical inputs are all local geometry, never a primitive count.
The net and loop packing arithmetic will be proved from these fields. -/
structure PackingClassics (S : QuotientSurface.{u}) (C : PrimitiveGeometry.{u,v} S) where
  complete_domain : S.domain=univ
  /-- HP-M Chapter 2 §4.1: polar hyperbolic area; all radii r≥0. -/
  plane_disk_area : ∀ z : UpperHalfPlane, ∀ r : ℝ, 0 ≤ r →
    volume (Metric.ball z r)=ENNReal.ofReal (diskArea r)
  /-- HP-M Chapter 4 §1.1: injectivity radius and embedded metric disks. -/
  embedded_disk_area : ∀ p : S.Point, Thick S p → ∀ r : ℝ, 0 ≤ r → r ≤ epsilon →
    S.area (Metric.ball p r)=ENNReal.ofReal (diskArea r)
  /-- Buser Lemma 4.4.6 / HP-H Lemma 4.7 proof: cusp components have no
  closed geodesic; a primitive lying in a thin cylinder is its core. -/
  thin_classification : ∀ γ : C.Primitive, γ ∉ thinCores C → ∃ p ∈ C.trace γ, Thick S p
  /-- Standard collars are open metric tubes, hence Borel measurable. -/
  collars_measurable : ∀ γ ∈ thinCores C, MeasurableSet (coreCollar C γ)
  /-- HP-P Lemma 2.1, noncompact version Buser Lemma 4.4.6. -/
  collars_disjoint : ∀ γ ∈ thinCores C, ∀ δ ∈ thinCores C, γ ≠ δ →
    Disjoint (coreCollar C γ) (coreCollar C δ)
  /-- Collar metric dt²+cosh²(t)ds² integrated to the standard width.
  HP-P Lemmas 2.1--2.2 give that width and equidistant length formula. -/
  collar_area : ∀ γ ∈ thinCores C,
    S.area (coreCollar C γ)=ENNReal.ofReal (2*C.length γ/Real.sinh (C.length γ/2))

/-- The intrinsic topology and Gauss–Bonnet data of a finite-area bordered
surface. The actual quotient and primitive classes remain explicitly present. -/
structure BorderedGeometry where
  surface : QuotientSurface.{u}
  curves : PrimitiveGeometry.{u,v} surface
  genus : ℕ
  cusps : ℕ
  boundaries : ℕ
  euler_negative : 2 ≤ 2*genus+cusps+boundaries
  negativeEuler : ℕ
  euler_eq : negativeEuler+2=2*genus+cusps+boundaries
  /-- HP-M Chapter 5 §1.2; geodesic boundary has zero curvature contribution. -/
  gauss_bonnet : surface.area univ=ENNReal.ofReal (2*Real.pi*negativeEuler)

/-- Classical geodesic-boundary doubling and root-closed primitive inclusion.
This contains no cardinal bound. For empty boundary the complete model may
be S itself, so no disconnected double is treated as connected. -/
structure DoublingClassics (B : BorderedGeometry.{u,v}) where
  complete : QuotientSurface.{u}
  curves : PrimitiveGeometry.{u,v} complete
  packing : PackingClassics complete curves
  includePoint : B.surface.Point → complete.Point
  point_injective : Function.Injective includePoint
  local_isometry : ∀ p : B.surface.Point, ∃ r : ℝ, 0 < r ∧
    IsometryOn includePoint (Metric.ball p r)
  includePrimitive : B.curves.Primitive → curves.Primitive
  /-- Derived from the embedded geodesic-boundary inclusion: any root has
  the same geodesic axis/image and already closes inside the intrinsic piece. -/
  primitive_injective : Function.Injective includePrimitive
  length_preserved : ∀ γ, curves.length (includePrimitive γ)=B.curves.length γ
  trace_preserved : ∀ γ, curves.trace (includePrimitive γ)=includePoint '' B.curves.trace γ
  /-- HP-M Chapter 4 Proposition 2.20: geodesic-boundary double;
  area is twice the original (or unchanged for the empty-boundary identity). -/
  area_double : complete.area univ ≤ 2*B.surface.area univ

/-- Explicit bridge to the already existing, actual cusped ambient H. -/
structure AmbientRealization {P : WP.PsiTheory} {G : WP.External.WeilPeterssonGeometry.{u,v} P}
    (H : WP.External.HyperbolicCurveGeometry.{u,v,w} G) where
  model : ∀ g n, G.Moduli g n (fun _ => 0) → BorderedGeometry.{u,w}
  cusped : ∀ g n X, (model g n X).boundaries=0
  topology : ∀ g n X, (model g n X).genus=g ∧ (model g n X).cusps=n
  primitiveEquiv : ∀ g n X, H.Primitive g n X ≃ (model g n X).curves.Primitive
  length_eq : ∀ g n X γ, (model g n X).curves.length (primitiveEquiv g n X γ)=H.length γ

end WP.External.HyperbolicPacking
