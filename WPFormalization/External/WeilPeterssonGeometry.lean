import WPFormalization.External.IntersectionTheory
import WPFormalization.Statements.Boundary

/-! Mature geometric inputs, isolated from the paper's new estimates.

WP-POLY: Mirzakhani, JAMS 20 (2007), 1--23, volume/intersection theorem;
normalization is also explicitly recorded in Liu--Xu, arXiv:1103.5136v2, §1 Eq.(1)
and the following boundary-volume formula (p.1). Physical lengths are L, not 2L.
The only field involving volumes is this fixed-genus exact finite polynomial.
There is no assumption about large genus, cusp density, ratios, or error bounds.

The actual hyperbolic moduli, orbifold measure, cohomology classes and their
simultaneous realization remain phase-two constructions. In particular this
structure does not assert existence of any concrete WP model.
-/
noncomputable section
universe u v
namespace WP.External
open MeasureTheory

/- An abstract geometric family with its known cohomological volume polynomial.
`wpMeasure` denotes the orbifold symplectic measure omega_WP^N/N! on the indicated
space of labeled geodesic boundaries; length zero denotes a cusp. -/
@[blueprint "def:wp-volume"]
structure WeilPeterssonGeometry (P : PsiTheory) extends IntersectionRealization.{u} P where
  Moduli : (g n : ℕ) → (Fin n → ℝ) → Type v
  [measurable : ∀ g n L, MeasurableSpace (Moduli g n L)]
  wpMeasure : ∀ g n L, Measure (Moduli g n L)
  finite_volume : ∀ (g n : ℕ) (L : Fin n → ℝ), Stable g n →
    (∀ i, 0 ≤ L i) → wpMeasure g n L Set.univ ≠ ⊤
  volume_polynomial : ∀ (g n : ℕ) (L : Fin n → ℝ), Stable g n → (∀ i, 0 ≤ L i) →
    (wpMeasure g n L Set.univ).toReal =
      ∑ d ∈ degreeTuples g n, geometricBracket (classes g n) d *
        ∏ i, L i^(2*d i)/((4 : ℝ)^(d i)*(2*d i+1).factorial)

attribute [instance] WeilPeterssonGeometry.measurable

/- Geometric volume is the total orbifold symplectic measure, with all realization
conditions retained in G; it is not defined as a solution to a scalar recursion. -/
@[blueprint "def:wp-volume"]
def wpVolume {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (g n : ℕ) (L : Fin n → ℝ) : ℝ := (G.wpMeasure g n L Set.univ).toReal

def cuspVolume {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P) (g n : ℕ) : ℝ :=
  wpVolume G g n (fun _ => 0)

end WP.External
