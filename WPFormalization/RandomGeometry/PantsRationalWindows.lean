import WPFormalization.Probability.NNRealWindowBasis
import WPFormalization.RandomGeometry.PantsLengthPointProcess
import WPFormalization.RandomGeometry.QuadraticLengthIntensity

/-! Rational continuity windows reduce to nonnegative half-open windows after
removing the origin, which carries no actual scaled-geodesic atom. -/
noncomputable section
universe u v w
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

lemma nnreal_rational_window_sdiff_zero (a b : ℚ) :
    (nnrealRationalWindow a b).carrier \ {0} =
      Ioc (min (Real.toNNReal a) (Real.toNNReal b)) (Real.toNNReal b) := by
  ext x
  have hp (hx : x ≠ (0:ℝ≥0)) : 0<(x : ℝ) := by
    exact_mod_cast (show 0<x from bot_lt_iff_ne_bot.mpr hx)
  have hl (hx : x ≠ (0:ℝ≥0)) : Real.toNNReal (a : ℝ)<x ↔ (a : ℝ)<x := by
    simpa only [Real.toNNReal_coe] using
      (Real.toNNReal_lt_toNNReal_iff (hp hx) :
        Real.toNNReal (a : ℝ)<Real.toNNReal (x : ℝ) ↔ (a : ℝ)<x)
  have hu (hx : x ≠ (0:ℝ≥0)) : x≤Real.toNNReal (b : ℝ) ↔ (x : ℝ)≤b := by
    simpa only [Real.toNNReal_coe] using
      (Real.toNNReal_le_toNNReal_iff_of_pos (hp hx) :
        Real.toNNReal (x : ℝ)≤Real.toNNReal (b : ℝ) ↔ (x : ℝ)≤b)
  simp only [Set.mem_sdiff,mem_nnrealRationalWindow,mem_singleton_iff,mem_Ioc]
  constructor
  · rintro ⟨⟨hax,hxb⟩,hx⟩
    exact ⟨(min_le_left _ _).trans_lt ((hl hx).mpr hax),(hu hx).mpr hxb⟩
  · rintro ⟨hmin,hxb⟩
    have hmin0 : (0 : ℝ≥0) ≤ min (Real.toNNReal a) (Real.toNNReal b) := bot_le
    have hx : x ≠ (0 : ℝ≥0) := ne_of_gt (hmin0.trans_lt hmin)
    have hax : Real.toNNReal (a : ℝ)<x := by
      rcases min_lt_iff.mp hmin with h | h
      · exact h
      · exact False.elim ((not_lt_of_ge hxb) h)
    exact ⟨⟨(hl hx).mp hax,(hu hx).mp hxb⟩,hx⟩

lemma measure_rational_window_eq_canonical_Ioc (μ : Measure ℝ≥0) (hzero : μ {0}=0)
    (a b : ℚ) :
    μ (nnrealRationalWindow a b).carrier =
      μ (Ioc (min (Real.toNNReal a) (Real.toNNReal b)) (Real.toNNReal b)) := by
  rw [←nnreal_rational_window_sdiff_zero,measure_sdiff_null hzero]

lemma pointMeasure_count_rational_window_eq_canonical_Ioc (ξ : PointMeasure ℝ≥0)
    (hzero : ξ.toMeasure {0}=0) (a b : ℚ) :
    ξ.count ℝ≥0 (nnrealRationalWindow a b) =
      ξ.count ℝ≥0 (lengthIocWindow (min (Real.toNNReal a) (Real.toNNReal b))
        (Real.toNNReal b)) := by
  apply Nat.cast_injective (R:=ℝ≥0∞)
  rw [←ξ.count_spec ℝ≥0 _,←ξ.count_spec ℝ≥0 _]
  exact measure_rational_window_eq_canonical_Ioc ξ.toMeasure hzero a b

lemma rational_windows_canonical_Ioc_disjoint {ι : Type*}
    (a b : ι → ℚ)
    (hdis : Pairwise (fun j k => Disjoint (nnrealRationalWindow (a j) (b j)).carrier
      (nnrealRationalWindow (a k) (b k)).carrier)) :
    Pairwise (fun j k => Disjoint
      (Ioc (min (Real.toNNReal (a j)) (Real.toNNReal (b j))) (Real.toNNReal (b j)))
      (Ioc (min (Real.toNNReal (a k)) (Real.toNNReal (b k))) (Real.toNNReal (b k)))) := by
  intro j k hjk
  rw [←nnreal_rational_window_sdiff_zero,←nnreal_rational_window_sdiff_zero]
  exact (hdis hjk).mono sdiff_subset sdiff_subset

lemma quadraticLengthIntensity_rational_window (a b : ℚ) :
    quadraticLengthIntensity (nnrealRationalWindow a b).carrier =
      ENNReal.ofReal ((Real.toNNReal b : ℝ)^2-
        (min (Real.toNNReal a) (Real.toNNReal b) : ℝ≥0)^2) := by
  rw [measure_rational_window_eq_canonical_Ioc _ (measure_singleton _) a b,
    quadraticLengthIntensity_Ioc]

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

lemma pantsLengthPointProcess_singleton_zero (X : G.Moduli g n (fun _ => 0)) :
    (pantsLengthPointProcess H X).toMeasure {0}=0 :=
  curveNNLengthMeasure_singleton_zero H X _ (pantsLengthScale_pos g n) _

lemma primitiveLengthPointProcess_singleton_zero (X : G.Moduli g n (fun _ => 0)) :
    (primitiveLengthPointProcess H X).toMeasure {0}=0 :=
  curveNNLengthMeasure_singleton_zero H X _ (pantsLengthScale_pos g n) _

end WP.RandomGeometry
