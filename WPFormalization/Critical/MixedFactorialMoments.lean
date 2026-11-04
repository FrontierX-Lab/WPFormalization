import WPFormalization.Critical.MixedWindowMoments
import WPFormalization.Critical.MixedColoredFactorials
import WPFormalization.Probability.TwoColorPointMeasuresIntensities
noncomputable section
set_option maxHeartbeats 0
universe aa bb cc dd
namespace WP.Critical
open WP.External WP.RandomGeometry WP.Probability MeasureTheory Filter Set
open scoped Classical ENNReal NNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
    (MI : MirzakhaniIntegration G H T) (RG : MulticurveRestrictionGeometry G H T)

include MI RG in
lemma critical_colored_factorial_moments_of_intersecting
    (n : ℕ→ℕ) (c : ℝ) (hc : 0<c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (𝓝 c))
    (d : ℕ) (color : Fin d→Bool) (B : Fin d→RelCompactBorelWindow ℝ≥0)
    (L : ℝ≥0) (hBL : ∀i,(B i).carrier⊆Iic L)
    (hB : ∀i j,i≠j → color i=color j → Disjoint (B i).carrier (B j).carrier)
    (hinter : ∀a : Fin d→ℕ,Tendsto (fun g => ∫⁻ X,mixedIntersectingWindowTupleCount T X
      (fun j => NNReal.toReal '' (B ((coloredSlotsEquiv a color).symm j).1).carrier)
      ∂wpProbability G g (n g)) atTop (𝓝 0)) :
    MixedFactorialMomentLimit (fun g => wpProbability G g (n g))
      (fun g X i => (coloredLengthPointMeasure T X (color i)).count ℝ≥0 (B i))
      (fun i => (if color i then criticalPantsLengthIntensity c (B i).carrier else
        nonseparatingLengthIntensity (B i).carrier).toNNReal) := by
  intro a
  let I := fun j : Fin (pantsSlotsCount a color+nonsepSlotsCount a color) =>
    NNReal.toReal '' (B ((coloredSlotsEquiv a color).symm j).1).carrier
  have hI j : MeasurableSet (I j) :=
    nonnegativeIntensity_window_image_measurable _ (B _).measurableSet
  have hIL j : I j⊆Icc 0 (L:ℝ) := nonnegativeIntensity_window_image_bound _ L (hBL _)
  have hm := critical_mixed_window_tendsto_of_intersecting T MI RG n c hc hn
    (pantsSlotsCount a color) (nonsepSlotsCount a color) I hI L L.2 hIL (hinter a)
  have hlim : ENNReal.ofReal
      ((∏j : Fin (pantsSlotsCount a color),∫s in I (j.castAdd (nonsepSlotsCount a color)),criticalIntensityDensity c s)*
       ∏i : Fin (nonsepSlotsCount a color),∫t in I (Fin.natAdd (pantsSlotsCount a color) i),tightIntensityDensity t)=
      ∏i : Fin d,((if color i then criticalPantsLengthIntensity c (B i).carrier else
        nonseparatingLengthIntensity (B i).carrier).toNNReal : ℝ≥0∞)^(a i) := by
    change ENNReal.ofReal
      ((∏j : Fin (pantsSlotsCount a color),∫s in NNReal.toReal '' (B ((coloredSlotsEquiv a color).symm
          (j.castAdd (nonsepSlotsCount a color))).1).carrier,criticalIntensityDensity c s)*
       ∏i : Fin (nonsepSlotsCount a color),∫t in NNReal.toReal '' (B ((coloredSlotsEquiv a color).symm
          (Fin.natAdd (pantsSlotsCount a color) i)).1).carrier,tightIntensityDensity t)=_
    simp_rw [←criticalPantsLengthIntensity_toReal c _ (B _).measurableSet L (hBL _),
      ←nonseparatingLengthIntensity_toReal _ (B _).measurableSet L (hBL _)]
    rw [coloredSlots_intensity_product a color
      (fun i => (criticalPantsLengthIntensity c (B i).carrier).toReal)
      (fun i => (nonseparatingLengthIntensity (B i).carrier).toReal)]
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => pow_nonneg (by split_ifs <;> exact ENNReal.toReal_nonneg) _)]
    apply Finset.prod_congr rfl
    intro i hi
    rw [ENNReal.ofReal_pow (by split_ifs <;> exact ENNReal.toReal_nonneg)]
    congr 1
    split_ifs <;> simp only [ENNReal.ofReal,ENNReal.toNNReal_toReal_eq]
  rw [hlim] at hm
  apply hm.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
  apply lintegral_congr
  intro X
  exact (colored_factorial_eq_actual_mixed_tuple_count T hg X L color B a
    (fun i b hb => by exact_mod_cast hBL i hb) hB).symm
end WP.Critical
