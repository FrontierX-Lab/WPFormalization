import WPFormalization.Critical.ShortConfigurationRecordingClusterNetworks
import WPFormalization.Critical.PrimitiveCount
import WPFormalization.Critical.CutUniformBoundedFamilyRate

/- A genuine measurable finite-cut-catalog majorant with the fixed recording
constants. Pointwise domination of the actual intersecting tuple count is a
separate local recording theorem, not a field or an assumption here. -/
noncomputable section
universe u v w z
namespace WP.Critical.ShortConfiguration
open WP.External WP.Critical.PrimitivePacking MeasureTheory Filter
open scoped ENNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
  {g n : ℕ}

def intersectingRecordingEdgeCap (r : ℕ) (L : ℝ) : ℕ :=
  2*recordingEdgeCap r L+r

def intersectingRecordingTupleCap (r : ℕ) (L : ℝ) : ℕ :=
  (intersectingRecordingEdgeCap r L+
    r*primitiveCountBound (4*Real.pi*recordingEdgeCap r L) L)^r

def intersectingRecordingMultiplicity (r : ℕ) (L : ℝ) : ℕ :=
  intersectingRecordingTupleCap r L*2^(2*intersectingRecordingEdgeCap r L)+1

lemma intersectingRecordingMultiplicity_pos (r : ℕ) (L : ℝ) :
    0 < intersectingRecordingMultiplicity r L := by
  unfold intersectingRecordingMultiplicity
  omega

def intersectingCutMajorant (X : G.Moduli g n (fun _ => 0)) (r : ℕ) (L : ℝ) : ℝ≥0∞ :=
  (intersectingRecordingMultiplicity r L : ℝ≥0∞)*
    boundedComplexCutFamilyCount T (intersectingRecordingEdgeCap r L) (3*(r:ℝ)*L) X

lemma intersectingCutMajorant_measurable (MI : MirzakhaniIntegration G H T)
    (r : ℕ) (L : ℝ) :
    Measurable (fun X : G.Moduli g n (fun _ => 0) => intersectingCutMajorant T X r L) :=
  measurable_const.mul (boundedComplexCutFamilyCount_measurable T MI _ _)

lemma critical_intersectingCutMajorant_half_uniform_sequences
    (MI : MirzakhaniIntegration G H T) (r : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (c : ℝ) (hc : 0 < c) :
    ∃C : ℝ,0 < C ∧ ∀n : ℕ→ℕ,
      Tendsto (fun g : ℕ => (n g:ℝ)/Real.sqrt g) atTop (𝓝 c) →
      ∀ᶠg in atTop,(∫⁻X,intersectingCutMajorant T X r L ∂wpProbability G g (n g)) ≤
        ENNReal.ofReal (C*(g:ℝ)^(-1/2:ℝ)) := by
  have hD : 0 < (intersectingRecordingMultiplicity r L:ℝ) :=
    Nat.cast_pos.mpr (intersectingRecordingMultiplicity_pos r L)
  simpa only [intersectingCutMajorant,ENNReal.ofReal_natCast] using
    critical_boundedComplexCutFamilyCount_weighted_half_uniform_sequences T MI
      (intersectingRecordingMultiplicity r L) hD (intersectingRecordingEdgeCap r L)
      (3*(r:ℝ)*L) (by positivity) c hc

lemma critical_intersectingCutMajorant_tendsto_zero
    (MI : MirzakhaniIntegration G H T) (r : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (n : ℕ→ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g:ℝ)/Real.sqrt g) atTop (𝓝 c)) :
    Tendsto (fun g : ℕ => ∫⁻X,intersectingCutMajorant T X r L
      ∂wpProbability G g (n g)) atTop (𝓝 0) := by
  have hD : 0 < (intersectingRecordingMultiplicity r L:ℝ) :=
    Nat.cast_pos.mpr (intersectingRecordingMultiplicity_pos r L)
  simpa only [intersectingCutMajorant,ENNReal.ofReal_natCast] using
    critical_boundedComplexCutFamilyCount_weighted_tendsto_zero T MI
      (intersectingRecordingMultiplicity r L) hD (intersectingRecordingEdgeCap r L)
      (3*(r:ℝ)*L) (by positivity) n c hc hn

end WP.Critical.ShortConfiguration
