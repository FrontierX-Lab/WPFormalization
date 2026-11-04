import WPFormalization.Critical.ShortConfigurationDartCounts

/- General regular-neighborhood data for actual finite embedded networks.
Classical derived local disk-and-band construction; no geometric instance is
asserted. Primary source: Lazarus--de Mesmay, Surfaces and embedded graphs
(2017), printed pp8--9, Fig9; actual noncompact ambient use is the finite-chart
local corollary around the compact graph. This is not a literal theorem in
that compact-surface manuscript. No filling, recording or G.3 bound is a field.
Full field/source conditions: audit/short-regular-neighborhood-classical-fields.md. -/
noncomputable section


namespace WP.External.ShortRegularNeighborhoodGeometry
open Set WP.External.HyperbolicPacking WP.Critical.ShortConfiguration
universe x y z

def setInclusion {X : Type x} [TopologicalSpace X] {s t : Set X}
    (h : s⊆t) : C(s,t) where
  toFun p := ⟨p.val,h p.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def walkInSupport {X : Type x} [MetricSpace X] (N : EmbeddedNetwork.{x,y} X)
    (R : NetworkRotation N) : C(BoundaryWalkSpace N R,N.support) where
  toFun p := ⟨boundaryWalk N R p,boundaryWalk_mem_support N R p⟩
  continuous_toFun := (boundaryWalk N R).continuous.subtype_mk _

/- Proposed classical regular-neighborhood DATA only. No filled subsurface,
ambient cut, graph bound, topology budget or classification is returned. -/
structure NeighborhoodData {X : Type x} [MetricSpace X] (N : EmbeddedNetwork.{x,y} X) where
  rotation : NetworkRotation N
  region : Set X
  compact : IsCompact region
  regular_closed : closure (interior region)=region
  support_interior : N.support⊆interior region
  boundaryHomeo : BoundaryWalkSpace N rotation ≃ₜ {p:region // p.val∈frontier region}
  retract : C(region,N.support)
  deformation : Nonempty (ContinuousMap.HomotopyRel (ContinuousMap.id region)
    ((setInclusion (support_interior.trans interior_subset)).comp retract)
    {p:region | p.val∈N.support})
  boundary_retract : ∀p,retract (boundaryHomeo p).val=walkInSupport N rotation p

/- The ambient quotient is the fixed actual orientation-preserving hyperbolic
surface, not a freely selected metric space or genus metadata. This field is
the ordinary finite embedded graph regular-neighborhood theorem only. -/
structure RegularNeighborhoodClassics (B : BorderedGeometry.{x,y})
    (hcomplete : B.surface.domain=univ) where
  realize : ∀N:EmbeddedNetwork.{x,z} B.surface.Point,NeighborhoodData N

end WP.External.ShortRegularNeighborhoodGeometry
