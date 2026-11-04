import WPFormalization.Tight.SpectrumTupleExtensionsMeasurability
import WPFormalization.RandomGeometry.CurveLengthPointMeasures
import WPFormalization.Probability.NNRealPoissonConvergence
noncomputable section
universe u v w z
namespace WP.Tight
open External Set MeasureTheory
open scoped ENNReal NNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  (Q : TightGeodesicGeometry G T H) {g n : ℕ}

/- The actual scaled full primitive tight spectrum, including nonsimple curves,
as a genuine locally finite Radon point measure; all finite-catalog/Radon work
is supplied by the already proved arbitrary-subset curve-length construction. -/
def tightLengthPointMeasure (X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0))
    (s : ℝ) (hs : 0 < s) : WP.Probability.PointMeasure ℝ≥0 :=
  RandomGeometry.curveLengthPointMeasure H (tightCuspSurface G X) s hs (Q.cuspTight X)

lemma tightLengthPointMeasure_prefix_count
    (X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0))
    (s : ℝ) (hs : 0 < s) (b : ℝ≥0) :
    (tightLengthPointMeasure Q X s hs).count ℝ≥0 (WP.Probability.nnrealPrefixWindow b) =
      Q.cuspTightCount X (Iic ((b:ℝ)/s)) := by
  have hm := RandomGeometry.curveNNLengthMeasure_Iic H (tightCuspSurface G X)
    s hs (Q.cuspTight X) b
  have hc : Nat.card {γ : H.Primitive g n (tightCuspSurface G X) //
      H.length γ ≤ (b:ℝ)/s ∧ Q.cuspTight X γ} = Q.cuspTightCount X (Iic ((b:ℝ)/s)) := by
    apply Nat.card_congr
    exact {
      toFun := fun γ => ⟨γ.val, γ.property.2, γ.property.1⟩
      invFun := fun γ => ⟨γ.val, γ.property.2, γ.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [hc] at hm
  have hspec := (tightLengthPointMeasure Q X s hs).count_spec ℝ≥0
    (WP.Probability.nnrealPrefixWindow b)
  change RandomGeometry.curveNNLengthMeasure H (tightCuspSurface G X) s (Q.cuspTight X) (Iic b) =
    ((tightLengthPointMeasure Q X s hs).count ℝ≥0 (WP.Probability.nnrealPrefixWindow b):ℝ≥0∞) at hspec
  exact_mod_cast hspec.symm.trans hm


lemma tightLengthPointMeasure_window_count
    (X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0))
    (s : ℝ) (hs : 0 < s) (W : WP.Probability.RelCompactBorelWindow ℝ≥0) :
    (tightLengthPointMeasure Q X s hs).count ℝ≥0 W =
      Q.cuspTightCount X ((fun l : ℝ => Real.toNNReal (s*l)) ⁻¹' W.carrier) := by
  letI := RandomGeometry.curveNNLengthMeasure_finite_window H (tightCuspSurface G X)
    s hs (Q.cuspTight X) W.carrier (W.compactClosure.bddAbove.mono subset_closure)
  have hm : (tightLengthPointMeasure Q X s hs).toMeasure W.carrier =
      (Nat.card {γ : {γ : H.Primitive g n (tightCuspSurface G X) // Q.cuspTight X γ} //
        Real.toNNReal (s*H.length γ.val) ∈ W.carrier} : ℝ≥0∞) := by
    change RandomGeometry.curveNNLengthMeasure H (tightCuspSurface G X) s (Q.cuspTight X) W.carrier = _
    rw [RandomGeometry.curveNNLengthMeasure]
    exact RandomGeometry.sum_dirac_apply_eq_natCard _ W.carrier W.measurableSet
  have hc : Nat.card {γ : {γ : H.Primitive g n (tightCuspSurface G X) // Q.cuspTight X γ} //
        Real.toNNReal (s*H.length γ.val) ∈ W.carrier} =
      Q.cuspTightCount X ((fun l : ℝ => Real.toNNReal (s*l)) ⁻¹' W.carrier) := by
    apply Nat.card_congr
    exact {
      toFun := fun γ => ⟨γ.val.val, γ.val.property, γ.property⟩
      invFun := fun γ => ⟨⟨γ.val, γ.property.1⟩, γ.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [hc] at hm
  exact_mod_cast ((tightLengthPointMeasure Q X s hs).count_spec ℝ≥0 W).symm.trans hm

variable {hg : 2 ≤ g} (B : TightGeodesicBorelModel G T H Q g n hg)
include B

theorem measurable_tightLengthPointMeasure_prefix_count (s : ℝ) (hs : 0 < s) (b : ℝ≥0) :
    Measurable (fun X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0) =>
      (tightLengthPointMeasure Q X s hs).count ℝ≥0 (WP.Probability.nnrealPrefixWindow b)) := by
  simpa only [tightLengthPointMeasure_prefix_count] using
    measurable_actual_tight_count B (Iic ((b:ℝ)/s)) measurableSet_Iic

theorem aemeasurable_tightLengthPointMeasure
    (μ : Measure (TightSurface G g 0 n (fun _ => 0) (fun _ => 0)))
    (s : ℝ) (hs : 0 < s) :
    AEMeasurable (fun X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0) =>
      tightLengthPointMeasure Q X s hs) μ := by
  apply WP.External.pointMeasure_nnreal_aemeasurable_of_prefix_counts
  intro b
  exact (measurable_tightLengthPointMeasure_prefix_count Q B s hs b).aemeasurable



theorem measurable_tightLengthPointMeasure_window_count (s : ℝ) (hs : 0 < s)
    (W : WP.Probability.RelCompactBorelWindow ℝ≥0) :
    Measurable (fun X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0) =>
      (tightLengthPointMeasure Q X s hs).count ℝ≥0 W) := by
  have hcont : Continuous (fun l : ℝ => Real.toNNReal (s*l)) := by fun_prop
  simpa only [tightLengthPointMeasure_window_count] using
    measurable_actual_tight_count B _ (hcont.measurable W.measurableSet)

end WP.Tight
