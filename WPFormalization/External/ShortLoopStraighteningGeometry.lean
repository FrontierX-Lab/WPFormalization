import WPFormalization.Critical.ShortConfigurationRecordingArcs
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
noncomputable section
set_option maxHeartbeats 0
universe u v
namespace WP.External.ShortLoopStraighteningGeometry
open Set WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.Critical.ShortConfiguration
open scoped ENNReal

structure ClosedLoop (X : Type u) [TopologicalSpace X] where
  map : C(unitInterval,X)
  closed : map 0=map 1

def ClosedLoop.trace {X : Type u} [TopologicalSpace X] (f : ClosedLoop X) : Set X :=
  Set.range f.map

def ClosedLoop.Simple {X : Type u} [TopologicalSpace X] (f : ClosedLoop X) : Prop :=
  Set.InjOn f.map (Ico (0:unitInterval) 1)

def ClosedLoop.reverse {X : Type u} [TopologicalSpace X] (f : ClosedLoop X) : ClosedLoop X where
  map := f.map.comp ⟨fun t => ⟨1-(t:ℝ),by constructor <;> linarith [t.property.1,t.property.2]⟩,
    Continuous.subtype_mk (by fun_prop) _⟩
  closed := by simpa using f.closed.symm

/- Literal free homotopy: endpoints may move, but remain equal throughout. -/
def ClosedLoop.FreelyHomotopic {X : Type u} [TopologicalSpace X]
    (f g : ClosedLoop X) : Prop :=
  Nonempty (ContinuousMap.HomotopyWith f.map g.map (fun h => h 0=h 1))

def ClosedLoop.UnorientedFreelyHomotopic {X : Type u} [TopologicalSpace X]
    (f g : ClosedLoop X) : Prop := f.FreelyHomotopic g ∨ f.FreelyHomotopic g.reverse

def ClosedLoop.length {X : Type u} [MetricSpace X] (f : ClosedLoop X) : ℝ≥0∞ :=
  eVariationOn f.map univ

/- Geometric nonperipheral/non-null condition without an arbitrary predicate or
chosen cusp function: the actual free homotopy class cannot be made arbitrarily
short. Complete finite-area hyperbolic classification identifies precisely the
null/peripheral classes with the omitted cases. -/
def ClosedLoop.PositiveHomotopyLength {X : Type u} [MetricSpace X] (f : ClosedLoop X) : Prop :=
  ∃ε:ℝ,0<ε ∧ ∀g:ClosedLoop X,f.UnorientedFreelyHomotopic g → ENNReal.ofReal ε≤g.length


def primitiveLoop (B : BorderedGeometry.{u,v}) (γ : B.curves.Primitive) : ClosedLoop B.surface.Point where
  map := ⟨fun t => curveParam B γ ((t:ℝ)*B.curves.length γ),
    (curveParam_lipschitz B γ).continuous.comp (by fun_prop)⟩
  closed := by
    simpa using ((curveParam_periodic B γ) 0).symm

/- The standard topological circle is the ACTUAL endpoint quotient of I. -/
def loopCircleEndpoint (s t : unitInterval) : Prop := s=0 ∧ t=1
def LoopCircle := Quot loopCircleEndpoint
instance : TopologicalSpace LoopCircle := inferInstanceAs (TopologicalSpace (Quot loopCircleEndpoint))
instance : CompactSpace LoopCircle := inferInstanceAs (CompactSpace (Quot loopCircleEndpoint))

def ClosedLoop.circleMap {X : Type u} [TopologicalSpace X] (f : ClosedLoop X) : C(LoopCircle,X) where
  toFun := Quot.lift f.map (fun s t h => by rcases h with ⟨rfl,rfl⟩;exact f.closed)
  continuous_toFun := continuous_quot_lift (fun s t h => by rcases h with ⟨rfl,rfl⟩;exact f.closed) f.map.continuous

/- Genuine embedded compact annulus, with its two actual boundary circles.
No absence of original network curves or marked classification is supplied. -/
structure AnnulusBetween {X : Type u} [TopologicalSpace X] (f g : ClosedLoop X) where
  map : C(LoopCircle × unitInterval,X)
  injective : Function.Injective map
  endReparam : LoopCircle ≃ₜ LoopCircle
  boundary_zero : ∀z,map (z,0)=f.circleMap z
  boundary_one : ∀z,map (z,1)=g.circleMap (endReparam z)

/- Classical old theorems on arbitrary actual closed-loop homotopy classes,
not G.3 regularization, filling, recording or expectation conclusions. -/
structure LoopStraighteningClassics (B : BorderedGeometry.{u,v})
    (hcomplete : B.surface.domain=univ) where
  representative : ∀f:ClosedLoop B.surface.Point,f.Simple → f.PositiveHomotopyLength →
    ∃γ:B.curves.Primitive,(primitiveLoop B γ).UnorientedFreelyHomotopic f
  class_eq : ∀γ δ:B.curves.Primitive,
    (primitiveLoop B γ).UnorientedFreelyHomotopic (primitiveLoop B δ) ↔ γ=δ
  length_minimal : ∀(γ:B.curves.Primitive) (f:ClosedLoop B.surface.Point),
    (primitiveLoop B γ).UnorientedFreelyHomotopic f →
      ENNReal.ofReal (B.curves.length γ)≤f.length
  simple_representative : ∀(γ:B.curves.Primitive) (f:ClosedLoop B.surface.Point),
    f.Simple → (primitiveLoop B γ).UnorientedFreelyHomotopic f → SimpleTrace B γ
  disjoint_representatives : ∀(γ δ:B.curves.Primitive) (f g:ClosedLoop B.surface.Point),
    f.Simple → g.Simple → (primitiveLoop B γ).UnorientedFreelyHomotopic f →
    (primitiveLoop B δ).UnorientedFreelyHomotopic g → Disjoint f.trace g.trace →
      γ=δ ∨ Disjoint (B.curves.trace γ) (B.curves.trace δ)

/- Classical annulus criterion only, for ACTUAL disjoint essential circles.
This does not collapse an annulus in a G.3 recording. -/
structure SimpleAnnulusClassics (B : BorderedGeometry.{u,v})
    (hcomplete : B.surface.domain=univ) where
  annulus : ∀f g:ClosedLoop B.surface.Point,f.Simple → g.Simple →
    f.PositiveHomotopyLength → f.UnorientedFreelyHomotopic g → Disjoint f.trace g.trace →
    Nonempty (AnnulusBetween f g)

end WP.External.ShortLoopStraighteningGeometry
