import WPFormalization.Tight.SpectrumTupleExtensionsActualProcess
import WPFormalization.Probability.PointMeasureDilation
import WPFormalization.RandomGeometry.BoltzmannWpMixtureScale
noncomputable section
universe u v w
namespace WP.BoltzmannWp
open External Set MeasureTheory Filter WP.Probability
open scoped ENNReal NNReal Topology
variable {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  (H:HyperbolicCurveGeometry.{u,v,w} G) {g n:ℕ}

lemma curveLengthPointMeasure_dilation
    (X:G.Moduli g n (fun _=>0)) (s:ℝ) (hs:0<s)
    (p:H.Primitive g n X→Prop) (a:PositiveScale) :
    pointMeasureDilation a (RandomGeometry.curveLengthPointMeasure H X s hs p)=
      RandomGeometry.curveLengthPointMeasure H X ((a.val:ℝ)*s)
        (mul_pos (by exact_mod_cast a.property) hs) p := by
  apply pointMeasure_ext_toMeasure
  change (RandomGeometry.curveNNLengthMeasure H X s p).map (fun x:ℝ≥0=>a.val*x)=
    RandomGeometry.curveNNLengthMeasure H X ((a.val:ℝ)*s) p
  unfold RandomGeometry.curveNNLengthMeasure
  rw [Measure.map_sum (by fun_prop)]
  congr 1
  funext γ
  rw [Measure.map_dirac' (by fun_prop)]
  congr 1
  apply NNReal.eq
  rw [NNReal.coe_mul,
    Real.coe_toNNReal _ (mul_pos hs (H.length_pos γ.val)).le,
    Real.coe_toNNReal _ (mul_pos (mul_pos (by exact_mod_cast a.property) hs)
      (H.length_pos γ.val)).le]
  ring
end WP.BoltzmannWp

namespace WP.BoltzmannWp
open External Set MeasureTheory Filter WP.Probability
open scoped ENNReal NNReal Topology
variable {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
  {T:TightRegions G} {H:HyperbolicCurveGeometry.{u,v,w} G}
  (Q:TightGeodesicGeometry G T H)

/-- The complete primitive tight catalogue on the actual WP disjoint union,
with lengths multiplied by a deterministic positive physical scale. -/
def actualLengthPointMeasure (g:ℕ) (s:ℝ) (hs:0<s) (X:Surface G g) :
    PointMeasure ℝ≥0 :=
  Tight.tightLengthPointMeasure Q ((tightCuspMeasurableEquiv G g X.fst).symm X.snd) s hs

def physicalPointMeasure (g:ℕ) (μ:ℝ) (hμ:μ∈Ico (0:ℝ) muCritical) :
    Surface G g→PointMeasure ℝ≥0 :=
  actualLengthPointMeasure Q g (physicalScale μ) (physicalScale_pos μ hμ)

lemma physicalPointMeasure_dilation (g:ℕ) (μ:ℝ) (hμ:μ∈Ico (0:ℝ) muCritical)
    (X:Surface G g) :
    pointMeasureDilation (scaleRatio g μ hμ X.fst)
      (Tight.actualScaledTightPointMeasure Q g X.fst X.snd)=
      physicalPointMeasure Q g μ hμ X := by
  have hα:=TightConnected.tightScale_pos ((X.fst:ℝ)/(g:ℝ)) (by positivity)
  have he:=curveLengthPointMeasure_dilation H
    (tightCuspSurface G ((tightCuspMeasurableEquiv G g X.fst).symm X.snd))
    (tightScale ((X.fst:ℝ)/(g:ℝ))) hα
    (Q.cuspTight ((tightCuspMeasurableEquiv G g X.fst).symm X.snd))
    (scaleRatio g μ hμ X.fst)
  have hr : (((scaleRatio g μ hμ X.fst).val):ℝ)*tightScale ((X.fst:ℝ)/(g:ℝ))=
      physicalScale μ := by rw [scaleRatio_coe,div_mul_cancel₀ _ hα.ne']
  simpa only [Tight.actualScaledTightPointMeasure,Tight.scaledTightPointMeasure,
    Tight.tightLengthPointMeasure,physicalPointMeasure,actualLengthPointMeasure,hr] using he

lemma aemeasurable_actualLengthPointMeasure (g:ℕ) (hg:2≤g)
    (BM:∀n,TightGeodesicBorelModel G T H Q g n hg) (s:ℝ) (hs:0<s) (x:ℝ) :
    AEMeasurable (actualLengthPointMeasure Q g s hs) (wpMixture G g x) := by
  apply wpMixture_aemeasurable
  intro n
  apply WP.External.pointMeasure_nnreal_aemeasurable_of_prefix_counts
  intro b
  exact ((Tight.measurable_tightLengthPointMeasure_prefix_count Q (BM n) s hs b).comp
    (tightCuspMeasurableEquiv G g n).symm.measurable).aemeasurable

lemma physicalPointMeasure_zero (g:ℕ) (hμ:0∈Ico (0:ℝ) muCritical) :
    physicalPointMeasure Q g 0 hμ=actualLengthPointMeasure Q g 1 (by norm_num) := by
  funext X
  apply pointMeasure_ext_toMeasure
  change RandomGeometry.curveNNLengthMeasure H _ (physicalScale 0) _ =
    RandomGeometry.curveNNLengthMeasure H _ 1 _
  rw [physicalScale_zero]

end WP.BoltzmannWp
