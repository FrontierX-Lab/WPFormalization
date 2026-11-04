import VersoBlueprint.Attribute
import WPFormalization.External.HyperbolicSurfacePacking
import WPFormalization.External.MirzakhaniIntegration
noncomputable section
universe u v w z
namespace WP.External.ShortFillingGeometry
open Set
open HyperbolicPacking

def intrinsicInterior (B : BorderedGeometry.{u,v}) : Set B.surface.Point :=
  B.surface.project '' interior B.surface.domain

def intrinsicBoundary (B : BorderedGeometry.{u,v}) : Set B.surface.Point :=
  B.surface.project '' frontier B.surface.domain

def curveParam (B : BorderedGeometry.{u,v}) (γ : B.curves.Primitive) (t : ℝ) : B.surface.Point :=
  B.surface.project ((B.curves.representative γ).axis t)

def SimpleTrace (B : BorderedGeometry.{u,v}) (γ : B.curves.Primitive) : Prop :=
  Set.InjOn (curveParam B γ) (Ico 0 (B.curves.length γ))

def segmentScale (L : ℝ) : ℝ := Real.log (Real.cosh (L/4)/Real.sinh (L/4))

/- MP author PDF, Lemma 4.4 p.15 and Prop4.5 proof pp15--16.
The inequality is for two ACTUAL geodesic arcs with common endpoints and
transverse intersection. Distinct simple closed geodesics give the transverse
case by uniqueness; comparison at an upper length L uses monotonicity of coth.
No intersection count, graph size or recording is supplied. -/
structure SegmentClassics (B : BorderedGeometry.{u,v}) : Prop where
  endpoint_comparison : ∀ γ δ : B.curves.Primitive,
    SimpleTrace B γ → SimpleTrace B δ → γ≠δ → ∀ L : ℝ,
    0<L → B.curves.length γ≤L → B.curves.length δ≤L →
    ∀ s₁ s₂ t₁ t₂ : ℝ,
    s₁∈Ico 0 (B.curves.length γ) → s₂∈Ico 0 (B.curves.length γ) →
    t₁∈Ico 0 (B.curves.length δ) → t₂∈Ico 0 (B.curves.length δ) →
    s₁≠s₂ → t₁≠t₂ →
    curveParam B γ s₁=curveParam B δ t₁ →
    curveParam B γ s₂=curveParam B δ t₂ →
    2*segmentScale L≤|s₁-s₂|+|t₁-t₂|

/- Boundary circles are intrinsic, before their projection to an ambient
surface. These definitions impose actual frontier/trace semantics. -/
structure BoundaryRealization (B : BorderedGeometry.{u,v}) where
  curve : Fin B.boundaries→B.curves.Primitive
  injective : Function.Injective curve
  simple : ∀j,SimpleTrace B (curve j)
  disjoint : ∀i j,i≠j→Disjoint (B.curves.trace (curve i)) (B.curves.trace (curve j))
  cover : (⋃j,B.curves.trace (curve j))=intrinsicBoundary B

def boundaryLength {B : BorderedGeometry.{u,v}} (R : BoundaryRealization B) : ℝ :=
  ∑j,B.curves.length (R.curve j)

/- An intrinsic completion of an actual open geodesic subsurface. Its two
formal boundary circles may project to the same ambient geodesic. In particular
there is deliberately NO primitiveProjection_injective field. -/
structure IntrinsicPiece (ambient : BorderedGeometry.{u,v}) where
  model : BorderedGeometry.{u,v}
  boundary : BoundaryRealization model
  double : DoublingClassics model
  point : model.surface.Point→ambient.surface.Point
  local_isometry : ∀p,∃r:ℝ,0<r ∧ IsometryOn point (Metric.ball p r)
  interior_injective : Set.InjOn point (intrinsicInterior model)
  image_open : IsOpen (point '' intrinsicInterior model)
  image_connected : IsPreconnected (point '' intrinsicInterior model)
  primitiveProjection : model.curves.Primitive→ambient.curves.Primitive
  length_preserved : ∀γ,ambient.curves.length (primitiveProjection γ)=model.curves.length γ
  axis_map : ∀γ,∃phase:ℝ,∃reverse:Bool,∀t,
    point (curveParam model γ t)=curveParam ambient (primitiveProjection γ)
      (if reverse then phase-t else phase+t)
  boundary_simple : ∀j,SimpleTrace ambient (primitiveProjection (boundary.curve j))
  lift_interior : ∀γ:ambient.curves.Primitive,
    ambient.curves.trace γ⊆point '' intrinsicInterior model →
    ∃β:model.curves.Primitive,primitiveProjection β=γ

/- Exactly the geometric containment and quantitative consequences of Hide's
Def4.10 / Lem4.11 (author arXiv PDF p22). This does not package any G.3 graph
recording, graph marking, classification or multiplicity estimate. Canonical
filling/minimality must later be obtained from the actual neighborhood surgery;
it is not replaced by an arbitrary Predicate called 'filling'. -/
structure SingleCurvePieceData (B : BorderedGeometry.{u,v}) (γ : B.curves.Primitive) where
  piece : IntrinsicPiece B
  contains : B.curves.trace γ⊆piece.point '' intrinsicInterior piece.model
  boundary_length_le : boundaryLength piece.boundary≤2*B.curves.length γ
  area_le : (piece.model.surface.area univ).toReal≤4*B.curves.length γ

@[blueprint "ext:short-filling"]
structure SingleCurvePieceClassics {P : WP.PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} {H : HyperbolicCurveGeometry.{u,v,w} G}
    (A : AmbientRealization H) where
  piece : ∀g n,WP.Stable g n→∀(X:G.Moduli g n (fun _=>0)) (γ:H.Primitive g n X),
    ¬H.simple γ→SingleCurvePieceData (A.model g n X) (A.primitiveEquiv g n X γ)

/- Compatibility with the already existing ACTUAL moduli-family primitive
classes and multicurve disjointness; not a freely selected family of curves. -/
structure AmbientCurveCompatibility {P : WP.PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G}
    (A : AmbientRealization H) (T : MulticurveTopology.{u,v,w,z} G H) : Prop where
  complete_domain : ∀g n X,(A.model g n X).surface.domain=univ
  simple_iff : ∀g n X (γ:H.Primitive g n X),
    H.simple γ↔SimpleTrace (A.model g n X) (A.primitiveEquiv g n X γ)
  disjoint_iff : ∀g n X (γ δ:H.Primitive g n X),γ≠δ→
    (T.disjoint γ δ↔Disjoint
      ((A.model g n X).curves.trace (A.primitiveEquiv g n X γ))
      ((A.model g n X).curves.trace (A.primitiveEquiv g n X δ)))

/- The actual component semantics of an already-existing ambient cut. This
is a realization of the classical cut object T, not the construction of a G.3
recording or a theorem that a filled piece is one of these components. -/
def cutComplement {P : WP.PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (A : AmbientRealization H)
    {g n k : ℕ} {X : G.Moduli g n (fun _=>0)} (κ : Fin k→H.Primitive g n X) :
    Set (A.model g n X).surface.Point :=
  {p | ∀e,p∉(A.model g n X).curves.trace (A.primitiveEquiv g n X (κ e))}

structure CutComponentRealization {P : WP.PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} {H : HyperbolicCurveGeometry.{u,v,w} G}
    (A : AmbientRealization H) (T : MulticurveTopology.{u,v,w,z} G H)
    {g n k : ℕ} (o : T.Orbit g n k) (X : G.Moduli g n (fun _=>0))
    (κ : Fin k→H.Primitive g n X) (hκ : T.orbitMem o X κ) where
  piece : Fin (T.cut o).components→IntrinsicPiece (A.model g n X)
  componentEquiv : ConnectedComponents (cutComplement A κ)≃Fin (T.cut o).components
  image_eq : ∀c,(piece c).point '' intrinsicInterior (piece c).model =
    {p | ∃hp:p∈cutComplement A κ,componentEquiv (ConnectedComponents.mk ⟨p,hp⟩)=c}
  genus_eq : ∀c,(piece c).model.genus=(T.cut o).genus c
  cuspEquiv : ∀c,Fin (piece c).model.cusps≃{j:Fin n // (T.cut o).cuspVertex j=c}
  halfSideEquiv : ∀c,Fin (piece c).model.boundaries≃
    {e:Fin k×Fin 2 // (T.cut o).edgeVertex e=c}
  boundary_eq : ∀c j,(piece c).primitiveProjection ((piece c).boundary.curve j)=
    A.primitiveEquiv g n X (κ ((halfSideEquiv c j).val.1))

end WP.External.ShortFillingGeometry
