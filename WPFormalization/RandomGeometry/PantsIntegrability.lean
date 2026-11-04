import WPFormalization.RandomGeometry.PantsCutTopology

/-! Actual short-pants random variables have every finite moment. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory
open scoped ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) {g n : ℕ}

include T C in
lemma short_pants_memLp (hg : 1 ≤ g) (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (μ : Measure (G.Moduli g n (fun _ => 0))) [IsFiniteMeasure μ] (p : ℝ≥0∞) :
    MemLp (fun X => (H.pantsCount X L : ℝ)) p μ := by
  have hm : Measurable (fun X : G.Moduli g n (fun _ => 0) => (H.pantsCount X L : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (H.measurable_pantsCount L)
  apply MemLp.of_bound hm.aestronglyMeasurable (n : ℝ)
  filter_upwards [] with X
  have hb := short_pants_count_bound T C hg L hL X
  have hn : H.pantsCount X L ≤ n := by omega
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ (H.pantsCount X L : ℝ) by positivity)]
  exact Nat.cast_le.mpr hn

end WP.RandomGeometry
