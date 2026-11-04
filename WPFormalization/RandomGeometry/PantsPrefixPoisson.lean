import WPFormalization.RandomGeometry.PantsPoissonProcess

/-! Genuine prefix counts converge to the one-dimensional Poisson law. This
uses the actual nonnegative factorial moments directly. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

lemma pointMeasure_prefix_count_eq_Ioc_zero (ξ : PointMeasure ℝ≥0)
    (hzero : ξ.toMeasure {0}=0) (t : ℝ≥0) :
    ξ.count ℝ≥0 (nnrealPrefixWindow t)=ξ.count ℝ≥0 (lengthIocWindow 0 t) := by
  apply Nat.cast_injective (R:=ℝ≥0∞)
  rw [←ξ.count_spec ℝ≥0 _,←ξ.count_spec ℝ≥0 _]
  change ξ.toMeasure (Iic t)=ξ.toMeasure (Ioc 0 t)
  rw [←measure_sdiff_null (s:=Iic t) hzero]
  congr 1
  ext x
  simp only [Set.mem_sdiff,mem_Iic,mem_singleton_iff,mem_Ioc]
  exact ⟨fun h => ⟨bot_lt_iff_ne_bot.mpr h.2,h.1⟩,
    fun h => ⟨h.2,ne_of_gt h.1⟩⟩

variable {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

include C MI in
lemma pants_prefix_mixedFactorialMomentLimit (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop atTop) (t : ℝ≥0) :
    MixedFactorialMomentLimit (fun g => wpProbability G g (n g))
      (fun g X (_ : Fin 1) => (pantsLengthPointProcess H X).count ℝ≥0 (nnrealPrefixWindow t))
      (fun _ : Fin 1 => Real.toNNReal ((t : ℝ)^2)) := by
  intro a
  have hh := pants_point_process_Ioc_mixed_moments G H T C MI a n hnfast
    (fun _ : Fin 1 => 0) (fun _ => t) (fun _ => bot_le)
    (fun i j hij => False.elim (hij (Subsingleton.elim _ _)))
  simpa only [pointMeasure_prefix_count_eq_Ioc_zero _
      (pantsLengthPointProcess_singleton_zero H _),NNReal.coe_zero,zero_pow two_ne_zero,
      sub_zero,ENNReal.ofReal,ENNReal.coe_toNNReal] using hh

include C MI in
lemma pants_prefix_counts_poisson (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop atTop) (t : ℝ≥0) :
    LawConverges (fun g => wpProbability G g (n g))
      (fun g X (_ : Fin 1) => (pantsLengthPointProcess H X).count ℝ≥0 (nnrealPrefixWindow t))
      (productPoissonMeasure (fun _ : Fin 1 => Real.toNNReal ((t : ℝ)^2))) (fun z => z) := by
  apply WP.External.factorial_moments_poisson_nonneg
    (fun g => wpProbability G g (n g))
    (fun g X (_ : Fin 1) => (pantsLengthPointProcess H X).count ℝ≥0 (nnrealPrefixWindow t))
    (WP.Spectral.wpProbability_eventually_probability P G n
      ((pants_fast_cusps_tendsto_atTop n hnfast).eventually_ge_atTop 1)) ?_
    (fun _ : Fin 1 => Real.toNNReal ((t : ℝ)^2))
    (pants_prefix_mixedFactorialMomentLimit G H T C MI n hnfast t)
  filter_upwards [] with g
  exact (measurable_pi_lambda (fun _ : Fin 1 =>
    pantsLengthPointProcess_prefix_count_measurable G H t)).aemeasurable

end WP.RandomGeometry
