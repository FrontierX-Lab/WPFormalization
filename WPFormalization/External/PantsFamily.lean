import WPFormalization.External.ShortFillingGeometry

/-! Stage-one classical interfaces HYP-PANTS-FAMILY/HYP-PANTS-DEFORMATION,
approved by the root source audit on 2026-11-01. The objects below are actual
convex hyperbolic quotients and the complete
primitive axial conjugacy/inverse catalogs already used by Lemma G.2.
No cluster measure, support property, continuity of a cluster, or stochastic
conclusion is an input. -/
noncomputable section
universe u v
namespace WP.External.PantsCluster
open HyperbolicPacking ShortFillingGeometry Set Filter
open scoped Topology

abbrev Waist := {s : ℝ // 0 < s}

def referenceWaist : Waist := ⟨1, zero_lt_one⟩

/-- The actual topological pants: one closed disk boundary and two punctures.
This prevents genus/cusp numerical labels alone from defining the family. -/
abbrev TwicePuncturedDisk :=
  {z : ℂ // ‖z‖ ≤ 1 ∧ z ≠ (1/2 : ℂ) ∧ z ≠ -(1/2 : ℂ)}

/- The marked Fenchel--Nielsen family with boundary lengths (s,0,0).
Martelli Ch5 Proposition1.6, pp84--87, includes cusp cuffs explicitly.
The deck marking and its class compatibility retain actual free homotopy
classes and unoriented multiplicities, rather than arbitrary labels. -/
structure Family where
  model : Waist → BorderedGeometry.{u,v}
  topology : ∀ s, (model s).surface.Point ≃ₜ TwicePuncturedDisk
  topological_boundary : ∀ s p,
    p ∈ intrinsicBoundary (model s) ↔ ‖((topology s) p).val‖ = 1
  genus : ∀ s, (model s).genus = 0
  cusps : ∀ s, (model s).cusps = 2
  boundaries : ∀ s, (model s).boundaries = 1
  boundary : ∀ s, BoundaryRealization (model s)
  waist : ∀ s, Fin (model s).boundaries
  waist_length : ∀ s, (model s).curves.length ((boundary s).curve (waist s)) = s.val
  double : ∀ s, DoublingClassics (model s)
  marking : ∀ s, (model referenceWaist).curves.Primitive ≃ (model s).curves.Primitive
  deckMarking : ∀ s, (model referenceWaist).surface.Γ ≃* (model s).surface.Γ
  marking_class : ∀ s γ,
    conjugateOrInverse
      (deckMarking s (((model referenceWaist).curves.representative γ).deck))
      (((model s).curves.representative (marking s γ)).deck)
  marking_waist : ∀ s,
    marking s ((boundary referenceWaist).curve (waist referenceWaist)) =
      (boundary s).curve (waist s)

namespace Family
variable (F : Family.{u,v})
abbrev Primitive := (F.model referenceWaist).curves.Primitive

def length (s : Waist) (γ : F.Primitive) : ℝ :=
  (F.model s).curves.length (F.marking s γ)

lemma length_pos (s : Waist) (γ : F.Primitive) : 0 < F.length s γ :=
  ((F.model s).curves.representative (F.marking s γ)).period_pos

def waistClass : F.Primitive :=
  (F.boundary referenceWaist).curve (F.waist referenceWaist)

lemma length_waist (s : Waist) : F.length s F.waistClass = s.val := by
  unfold length waistClass
  rw [F.marking_waist, F.waist_length]

def short (s : Waist) (L : ℝ) : Finset F.Primitive :=
  ((F.model s).curves.short L).preimage (F.marking s) (F.marking s).injective.injOn

lemma mem_short (s : Waist) (L : ℝ) (γ : F.Primitive) :
    γ ∈ F.short s L ↔ F.length s γ ≤ L := by
  simp only [short, Finset.mem_preimage, (F.model s).curves.mem_short]
  rfl
end Family

/- Classical local metric comparison, not a bound on clusters.
Bishop, RevMatIberoam18(2002), Lemma6.2 p651 / Thm1.1 p628, explicitly
allows both unchanged cuffs to be punctures. Its qc constant is at most
1+C(B)|log(s/t)|. Bers, ActaMath141(1978), Lemma1 pp81--82, reproduces
Wolpert's annular-cover proof for every closed geodesic, without simplicity.
Apply it to the doubled marked pants (boundary reflection preserves K).
The *same marked primitive class* is required in this inequality.
Both marked length continuity and all cluster consequences are local proofs.
-/
structure DeformationClassics (F : Family.{u,v}) : Prop where
  length_comparison : ∀ B : ℝ, 0 < B → ∃ C : ℝ, 0 < C ∧
    ∀ s t : Waist, s.val ≤ B → t.val ≤ B → |Real.log (s.val / t.val)| ≤ 2 →
    ∀ γ : F.Primitive,
      F.length s γ ≤ (1 + C * |Real.log (s.val / t.val)|) * F.length t γ

end WP.External.PantsCluster
