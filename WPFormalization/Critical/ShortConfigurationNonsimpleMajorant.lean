import WPFormalization.Critical.ShortConfigurationRecordingSingleNonPants
import WPFormalization.Critical.CutUniformBoundedFamilyRate
noncomputable section
universe u v w z
namespace WP.Critical.ShortConfiguration
open WP.External WP.Critical.PrimitivePacking MeasureTheory Filter
open scoped ENNReal Topology
variable {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {H:HyperbolicCurveGeometry.{u,v,w} G} (T:MulticurveTopology.{u,v,w,z} G H)
  {g n:ℕ}

def singleRecordingMultiplicity (L:ℝ) : ℕ :=
  2*singleRecordingEdgeCap L*primitiveCountBound (4*Real.pi*singleRecordingEulerCap L) L*
    2^(2*singleRecordingEdgeCap L)+1

lemma singleRecordingMultiplicity_pos (L:ℝ) : 0 < singleRecordingMultiplicity L := by
  unfold singleRecordingMultiplicity
  omega

/- This is the explicit genuine measurable cut-catalog majorant. Its
pointwise domination of the canonical Hide badcurve count is a separate
LOCAL recording proof, not assumed in this definition or analytic lemma. -/
def nonsimpleCutMajorant (X:G.Moduli g n (fun _=>0)) (L:ℝ) : ℝ≥0∞ :=
  (singleRecordingMultiplicity L:ℝ≥0∞)*
    boundedComplexCutFamilyCount T (singleRecordingEdgeCap L) (2*L) X

lemma nonsimpleCutMajorant_measurable (MI:MirzakhaniIntegration G H T) (L:ℝ) :
    Measurable (fun X:G.Moduli g n (fun _=>0)=>nonsimpleCutMajorant T X L) :=
  measurable_const.mul (boundedComplexCutFamilyCount_measurable T MI _ _)

lemma critical_nonsimpleCutMajorant_half_uniform_sequences
    (MI:MirzakhaniIntegration G H T) (L:ℝ) (hL:0 ≤ L) (c:ℝ) (hc:0 < c) :
    ∃C:ℝ,0 < C ∧ ∀n:ℕ→ℕ,
      Tendsto (fun g:ℕ=>(n g:ℝ)/Real.sqrt g) atTop (𝓝 c)→
      ∀ᶠg in atTop,(∫⁻X,nonsimpleCutMajorant T X L ∂wpProbability G g (n g)) ≤
        ENNReal.ofReal (C*(g:ℝ)^(-1/2:ℝ)) := by
  have hD:0 < (singleRecordingMultiplicity L:ℝ):=Nat.cast_pos.mpr (singleRecordingMultiplicity_pos L)
  simpa only [nonsimpleCutMajorant,ENNReal.ofReal_natCast] using
    critical_boundedComplexCutFamilyCount_weighted_half_uniform_sequences T MI
      (singleRecordingMultiplicity L) hD (singleRecordingEdgeCap L) (2*L) (by linarith) c hc

lemma critical_nonsimpleCutMajorant_tendsto_zero
    (MI:MirzakhaniIntegration G H T) (L:ℝ) (hL:0 ≤ L) (n:ℕ→ℕ) (c:ℝ) (hc:0 < c)
    (hn:Tendsto (fun g:ℕ=>(n g:ℝ)/Real.sqrt g) atTop (𝓝 c)) :
    Tendsto (fun g:ℕ=>∫⁻X,nonsimpleCutMajorant T X L ∂wpProbability G g (n g)) atTop (𝓝 0) := by
  have hD:0 < (singleRecordingMultiplicity L:ℝ):=Nat.cast_pos.mpr (singleRecordingMultiplicity_pos L)
  simpa only [nonsimpleCutMajorant,ENNReal.ofReal_natCast] using
    critical_boundedComplexCutFamilyCount_weighted_tendsto_zero T MI
      (singleRecordingMultiplicity L) hD (singleRecordingEdgeCap L) (2*L) (by linarith) n c hc hn
end WP.Critical.ShortConfiguration
