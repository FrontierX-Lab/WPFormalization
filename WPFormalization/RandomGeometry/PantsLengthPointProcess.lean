import WPFormalization.RandomGeometry.CurveWindowPointCounts
import WPFormalization.Spectral.PantsScaleGrowth

/-! Actual rescaled length point measures. A transparent positive extension of
the square-root scale handles the irrelevant finite initial range q_g=0. Under
the original fast-cusp hypothesis it is eventually exactly sqrt(q_g). -/
noncomputable section
universe u v w
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

/- This total scale agrees with the original physical scale whenever q>0. -/
def pantsLengthScale (g n : ℕ) : ℝ :=
  if 0<pantsScale g n then Real.sqrt (pantsScale g n) else 1

lemma pantsLengthScale_pos (g n : ℕ) : 0<pantsLengthScale g n := by
  unfold pantsLengthScale
  split_ifs with h
  · exact Real.sqrt_pos.mpr h
  · norm_num

lemma pantsLengthScale_eventually_eq_sqrt (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop atTop) :
    ∀ᶠg in atTop, pantsLengthScale g (n g)=Real.sqrt (pantsScale g (n g)) := by
  filter_upwards [(WP.Spectral.pantsScale_tendsto_atTop n hnfast).eventually_gt_atTop 0]
    with g hg
  exact if_pos hg

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

def pantsLengthPointProcess (X : G.Moduli g n (fun _ => 0)) : PointMeasure ℝ≥0 :=
  planarLengthPointMeasure H X (pantsLengthScale g n) (pantsLengthScale_pos g n) 2

def primitiveLengthPointProcess (X : G.Moduli g n (fun _ => 0)) : PointMeasure ℝ≥0 :=
  primitiveLengthPointMeasure H X (pantsLengthScale g n) (pantsLengthScale_pos g n)

lemma pantsLengthPointProcess_prefix_measurable (B : ℝ≥0) :
    Measurable (fun X : G.Moduli g n (fun _ => 0) =>
      (pantsLengthPointProcess H X).toMeasure (Iic B)) :=
  planarLengthPointMeasure_prefix_measurable H _ (pantsLengthScale_pos g n) 2 B

lemma primitiveLengthPointProcess_prefix_measurable (B : ℝ≥0) :
    Measurable (fun X : G.Moduli g n (fun _ => 0) =>
      (primitiveLengthPointProcess H X).toMeasure (Iic B)) :=
  primitiveLengthPointMeasure_prefix_measurable H _ (pantsLengthScale_pos g n) B

lemma pantsLengthPointProcess_actual_eventually (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop atTop) :
    ∀ᶠg in atTop, ∀X : G.Moduli g (n g) (fun _ => 0),
      (pantsLengthPointProcess H X).toMeasure =
        Measure.sum (fun γ : {γ : H.Primitive g (n g) X //
          ∃S : Finset (Fin (n g)), H.planarSide γ=some S ∧ S.card=2} =>
          Measure.dirac (Real.toNNReal (Real.sqrt (pantsScale g (n g))*H.length γ.val))) := by
  filter_upwards [pantsLengthScale_eventually_eq_sqrt n hnfast] with g hg
  intro X
  change curveNNLengthMeasure H X _ _ = _
  rw [hg]
  rfl

lemma primitiveLengthPointProcess_actual_eventually (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop atTop) :
    ∀ᶠg in atTop, ∀X : G.Moduli g (n g) (fun _ => 0),
      (primitiveLengthPointProcess H X).toMeasure =
        Measure.sum (fun γ : {γ : H.Primitive g (n g) X // True} =>
          Measure.dirac (Real.toNNReal (Real.sqrt (pantsScale g (n g))*H.length γ.val))) := by
  filter_upwards [pantsLengthScale_eventually_eq_sqrt n hnfast] with g hg
  intro X
  change curveNNLengthMeasure H X _ _ = _
  rw [hg]
  rfl

end WP.RandomGeometry
