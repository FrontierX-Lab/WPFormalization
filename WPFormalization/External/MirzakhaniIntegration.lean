import WPFormalization.External.HyperbolicCurveGeometry
import WPFormalization.External.MulticurveCutData

/-! Classical ordered-multicurve integration, with its cut incidence explicit.

The exact source is Shen--Wu, arXiv:2203.15681v4, §2.2 Theorem 6 and Remark
(PDF p.7), restating Mirzakhani's integration theorem. The coefficient is the
reciprocal of 2^M times the orientation-stabilizer index. The two exceptional
topologies (1,1),(2,0) are excluded from this coefficient convention.

No pants moment, volume-ratio estimate, limit, or Poisson approximation is a
field. All geometric families remain explicit parameters, without an instance.
-/
noncomputable section
universe u v w z
namespace WP.External
open MeasureTheory
open scoped ENNReal

namespace MulticurveCutData
variable {n r : ℕ} (D : MulticurveCutData n r)

def volumeProduct {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (x : Fin r → ℝ) : ℝ :=
  ∏ c : Fin D.components,
    wpVolume G (D.genus c) (D.boundaryCount c) (D.boundaryLengths x c)
end MulticurveCutData

/-- A classical topological realization of all ordered disjoint simple
multicurve orbits. `orbitMem` is tied to the same geometric primitive curves H;
its partition axiom covers every injective simple/disjoint tuple, rather than
an arbitrary incomplete list of selected orbits.

`cut` denotes the actual connected components, genera, original cusp labels
and edge-side incidences of that orbit. Constructing this object from a
hyperbolic surface and mapping-class group is deferred to phase two. -/
structure MulticurveTopology {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (H : HyperbolicCurveGeometry.{u,v,w} G) where
  disjoint : ∀ {g n : ℕ} {X : G.Moduli g n (fun _ => 0)},
    H.Primitive g n X → H.Primitive g n X → Prop
  Orbit : ℕ → ℕ → ℕ → Type z
  [orbitFinite : ∀ g n r, Fintype (Orbit g n r)]
  orbitMem : ∀ {g n r : ℕ}, Orbit g n r → (X : G.Moduli g n (fun _ => 0)) →
    (Fin r → H.Primitive g n X) → Prop
  orbit_injective : ∀ {g n r : ℕ} (o : Orbit g n r) (X) (γ),
    orbitMem o X γ → Function.Injective γ
  orbit_simple : ∀ {g n r : ℕ} (o : Orbit g n r) (X) (γ),
    orbitMem o X γ → ∀ i, H.simple (γ i)
  orbit_disjoint : ∀ {g n r : ℕ} (o : Orbit g n r) (X) (γ),
    orbitMem o X γ → ∀ i j, i ≠ j → disjoint (γ i) (γ j)
  orbit_partition : ∀ {g n r : ℕ} (X : G.Moduli g n (fun _ => 0))
    (γ : Fin r → H.Primitive g n X), Function.Injective γ →
    (∀ i, H.simple (γ i)) → (∀ i j, i ≠ j → disjoint (γ i) (γ j)) →
    ∃! o : Orbit g n r, orbitMem o X γ
  cut : ∀ {g n r : ℕ}, Orbit g n r → MulticurveCutData n r
  cut_stable : ∀ {g n r : ℕ} (o : Orbit g n r) (c : Fin (cut o).components),
    Stable ((cut o).genus c) ((cut o).boundaryCount c)
  cut_euler : ∀ {g n r : ℕ} (o : Orbit g n r),
    (∑ c : Fin (cut o).components, (cut o).genus c) + r + 1 = g + (cut o).components
  cut_connected : ∀ {g n r : ℕ} (o : Orbit g n r),
    (cut o).ConnectedWithin Finset.univ
  planarSide_iff : ∀ {g n r : ℕ} (o : Orbit g n r)
    (X : G.Moduli g n (fun _ => 0)) (γ : Fin r → H.Primitive g n X),
    orbitMem o X γ → 1 ≤ g → ∀ e S,
      H.planarSide (γ e) = some S ↔ (cut o).PlanarSide e S
  cut_classifies : ∀ {g n r : ℕ} (o p : Orbit g n r),
    Nonempty (MulticurveCutData.Isomorphism (cut o) (cut p)) → o = p
  cut_realizes : ∀ {g n r : ℕ} (D : MulticurveCutData n r),
    (∀ c, Stable (D.genus c) (D.boundaryCount c)) → D.ConnectedWithin Finset.univ →
    (∑ c : Fin D.components, D.genus c) + r + 1 = g + D.components →
    ∃ o : Orbit g n r, Nonempty (MulticurveCutData.Isomorphism D (cut o))

attribute [instance] MulticurveTopology.orbitFinite

namespace MulticurveTopology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G}
    (T : MulticurveTopology.{u,v,w,z} G H)

def coefficient {g n r : ℕ} (o : T.Orbit g n r) : ℝ≥0∞ :=
  (2^((T.cut o).oneHandleCount) * ((T.cut o).orientationStabilizerIndex : ℝ≥0∞))⁻¹

/-- The actual orbit sum of a nonnegative length test function. -/
def orbitSum {g n r : ℕ} (o : T.Orbit g n r) (F : (Fin r → ℝ) → ℝ≥0∞)
    (X : G.Moduli g n (fun _ => 0)) : ℝ≥0∞ :=
  ∑' γ : {γ : Fin r → H.Primitive g n X // T.orbitMem o X γ},
    F (fun i => H.length (γ.val i))

end MulticurveTopology

/- Only the generic exact integration law is deferred. Its integrand uses
the fixed G and the actual component-incidence data of T. -/
@[blueprint "ext:mir-integration"]
structure MirzakhaniIntegration {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H) : Prop where
  orbitSum_measurable : ∀ {g n r : ℕ} (o : T.Orbit g n r)
    (F : (Fin r → ℝ) → ℝ≥0∞), Measurable F →
    Measurable (T.orbitSum o F)
  orbit_integral : ∀ {g n r : ℕ} (o : T.Orbit g n r) (hst : Stable g n),
    (g, n) ≠ (1, 1) → (g, n) ≠ (2, 0) →
    ∀ (F : (Fin r → ℝ) → ℝ≥0∞), Measurable F →
    (∫⁻ X, T.orbitSum o F X ∂G.wpMeasure g n (fun _ => 0)) =
      T.coefficient o *
        ∫⁻ x : Fin r → ℝ in {x | ∀ i, 0 ≤ x i},
          F x * ENNReal.ofReal ((T.cut o).volumeProduct G x) *
            ∏ i, ENNReal.ofReal (x i)

end WP.External
