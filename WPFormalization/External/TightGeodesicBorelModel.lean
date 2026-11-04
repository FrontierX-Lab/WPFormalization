import WPFormalization.External.TightGeodesicGeometry

/- Classical marked-class/Borel model, explicitly tied to the same G/T/H/Q.
Source: Wolpert, arXiv:math/0701556v4, printed p.14 (all nonperipheral free
homotopy classes, holonomy and lengths), pp.35--36 (real analytic FN coordinates);
Budd--Lions, arXiv:2506.02611v3, pp.14--16 (Teichmuller/MCG and capped classes).
Primitive/simple/capped-null/same-cap/disjoint label masks are static topological
data. Borel length and quotient measurable descent are classical consequences
of the marked analytic model and the actual moduli Borel quotient. Their
geometric realization remains a phase-two obligation. No concrete instance,
tight-predicate/count measurability, estimate, or probability limit is asserted;
those measurability deductions belong in local proved modules. -/
noncomputable section
universe u v w z
namespace WP.External
open Set
structure TightGeodesicBorelModel {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (T : TightRegions G) (H : HyperbolicCurveGeometry.{u,v,w} G)
    (Q : TightGeodesicGeometry G T H) (g n : ℕ) (_hg : 2 ≤ g) where
  Marked : Type z
  [markedMeasurable : MeasurableSpace Marked]
  forget : Marked → TightSurface G g 0 n (fun _ => 0) (fun _ => 0)
  forget_surjective : Function.Surjective forget
  forget_measurable : Measurable forget
  measurableSet_descend : ∀ S : Set (TightSurface G g 0 n (fun _ => 0) (fun _ => 0)),
    MeasurableSet (forget ⁻¹' S) → MeasurableSet S
  Label : Type w
  [labelCountable : Countable Label]
  labelEquiv : ∀ Y : Marked,
    Label ≃ Q.Geodesic g 0 n (fun _ => 0) (fun _ => 0) (forget Y)
  primitiveLabel : Label → Prop
  simpleLabel : Label → Prop
  nonnullLabel : Label → Prop
  sameCapLabel : Label → Label → Prop
  disjointLabel : Label → Label → Prop
  primitive_iff : ∀ Y a, Q.primitive (labelEquiv Y a) ↔ primitiveLabel a
  simple_iff : ∀ Y a, Q.simple (labelEquiv Y a) ↔ simpleLabel a
  nonnull_iff : ∀ Y a,
    Q.cap (labelEquiv Y a) ≠ T.cycles.nullClass g 0 n (fun _ => 0) (fun _ => 0) (forget Y) ↔
      nonnullLabel a
  sameCap_iff : ∀ Y a b,
    Q.cap (labelEquiv Y a) = Q.cap (labelEquiv Y b) ↔ sameCapLabel a b
  disjoint_iff : ∀ Y a b,
    Q.disjoint (labelEquiv Y a) (labelEquiv Y b) ↔ disjointLabel a b
  length_measurable : ∀ a, Measurable (fun Y => Q.length (labelEquiv Y a))

attribute [instance] TightGeodesicBorelModel.markedMeasurable
attribute [instance] TightGeodesicBorelModel.labelCountable

end WP.External
