import WPFormalization.External.SpectralGeometry

/-! The already published Shen--Wu second-moment lower bound, separated
from the paper's new volume-ratio estimate.  Exact source:
arXiv:2203.15681v4, Proposition 35, PDF p.34, proof pp.34--35.
Its only growth assumption is n/sqrt(g) -> infinity.  The finite positive
eigenvalue theorem and the new ratio limit are NOT fields of this structure.
The ratio below is made from the given G's geometric cusp volumes.
-/
noncomputable section
universe u v w
namespace WP.External
open Filter
open scoped Topology

def shenWuLength (n : ℕ → ℕ) (g : ℕ) : ℝ := Real.sqrt (Real.sqrt g / n g)

@[blueprint "ext:shen-wu"]
structure ShenWuPantsBound {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) where
  probability_liminf : ∀ n : ℕ → ℕ,
    Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop atTop →
    Filter.liminf (fun g =>
      cuspVolume G g (n g - 1) ^ 2 /
        (cuspVolume G g (n g) * cuspVolume G g (n g - 2))) atTop ≤
    Filter.liminf (fun g => (wpProbability G g (n g)).real
      {X | 1 ≤ H.pantsCount X (shenWuLength n g)}) atTop

end WP.External
