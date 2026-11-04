import WPFormalization.External.TightGeodesicGeometry
import WPFormalization.External.MulticurveCutData

/- Finite topological MCG orbit/cut classification underlying Budd--Lions
Proposition 3.2, arXiv:2506.02611v3, pp.13--17. Cuts retain original protected
labels and ordered unoriented edge labels. Free boundaries are assigned
individually only in tightCutKernel, so there is no unrecorded multinomial.
Geometric realization/classification and stability remain explicit classical
phase-two obligations; no separating-contribution estimate is a field. -/
noncomputable section
universe u v w z
namespace WP.External
open Set MeasureTheory
open scoped ENNReal

/- Finite ordered base-surface MCG orbit types; the free boundary labels have
not yet been assigned to vertices. The cap relation above determines which
actual tight geodesic tuples occupy an orbit. -/
structure TightMulticurveTopology {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (T : TightRegions G) (H : HyperbolicCurveGeometry.{u,v,w} G)
    (Q : TightGeodesicGeometry G T H) where
  Orbit : ℕ → ℕ → ℕ → Type z
  [orbitFinite : ∀ g p r, Fintype (Orbit g p r)]
  cut : ∀ {g p r}, Orbit g p r → MulticurveCutData p r
  orbitMem : ∀ {g p r} (o : Orbit g p r) {k L K}
    (X : TightSurface G g p k L K), (Fin r → Q.Geodesic g p k L K X) → Prop
  orbit_good : ∀ {g p r} (o : Orbit g p r) {k L K X γ},
    orbitMem o (k:=k) (L:=L) (K:=K) X γ → Q.GoodTuple γ
  orbit_partition : ∀ {g p r k L K} (X : TightSurface G g p k L K)
    (γ : Fin r → Q.Geodesic g p k L K X), Stable g p →
    Q.GoodTuple γ → ∃! o : Orbit g p r, orbitMem o X γ
  cut_stable : ∀ {g p r} (o : Orbit g p r) (c : Fin (cut o).components),
    Stable ((cut o).genus c) ((cut o).boundaryCount c)
  cut_euler : ∀ {g p r} (o : Orbit g p r),
    (∑ c, (cut o).genus c) + r + 1 = g + (cut o).components
  cut_connected : ∀ {g p r} (o : Orbit g p r), (cut o).ConnectedWithin Finset.univ
  cut_classifies : ∀ {g p r} (o q : Orbit g p r),
    Nonempty (MulticurveCutData.Isomorphism (cut o) (cut q)) → o = q


  /- Classical realization of a stable connected labelled cut graph;
  BL Proposition 3.2 and ordinary classification of compact bordered surfaces.
  No integration identity, estimate or asymptotic conclusion is included. -/
  cut_realizes : ∀ {g p r : ℕ}, Stable g p → ∀ D : MulticurveCutData p r,
    (∀ c, Stable (D.genus c) (D.boundaryCount c)) →
    D.ConnectedWithin Finset.univ →
    (∑ c : Fin D.components, D.genus c) + r + 1 = g + D.components →
    ∃ o : Orbit g p r, Nonempty (MulticurveCutData.Isomorphism D (cut o))

attribute [instance] TightMulticurveTopology.orbitFinite

namespace MulticurveCutData
variable {p r : ℕ} (D : MulticurveCutData p r)

def tightProtectedLengths (L : Fin p → ℝ) (x : Fin r → ℝ)
    (c : Fin D.components) : Fin (D.boundaryCount c) → ℝ := fun i =>
  match (Fintype.equivFin (D.Boundary c)).symm i with
  | Sum.inl j => L j.val
  | Sum.inr e => x e.val.1

def assignedCount {k : ℕ} (a : Fin k → Fin D.components) (c : Fin D.components) : ℕ :=
  Fintype.card {j : Fin k // a j = c}

def assignedLengths {k : ℕ} (a : Fin k → Fin D.components) (K : Fin k → ℝ)
    (c : Fin D.components) : Fin (D.assignedCount a c) → ℝ :=
  fun i => K (((Fintype.equivFin {j : Fin k // a j = c}).symm i).val)

def tightCutKernel {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (T : TightRegions G) {k : ℕ} (L : Fin p → ℝ) (K : Fin k → ℝ) (x : Fin r → ℝ) : ℝ :=
  ∑ a : Fin k → Fin D.components, ∏ c : Fin D.components,
    tightVolume T (D.genus c) (D.boundaryCount c) (D.assignedCount a c)
      (D.tightProtectedLengths L x c) (D.assignedLengths a K c)

end MulticurveCutData

namespace TightMulticurveTopology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P} {T : TightRegions G}
  {H : HyperbolicCurveGeometry.{u,v,w} G} {Q : TightGeodesicGeometry G T H}
  (A : TightMulticurveTopology G T H Q)

def orbitSum {g p r k L K} (o : A.Orbit g p r) (F : (Fin r → ℝ) → ℝ≥0∞)
    (X : TightSurface G g p k L K) : ℝ≥0∞ := by
  classical
  exact ∑' γ : Fin r → Q.Geodesic g p k L K X,
    if A.orbitMem o X γ then F (fun i => Q.length (γ i)) else 0

def Separating {g p r k L K X} (γ : Fin r → Q.Geodesic g p k L K X) : Prop :=
  ∃ o : A.Orbit g p r, A.orbitMem o X γ ∧ 2 ≤ (A.cut o).components

end TightMulticurveTopology

end WP.External
