import WPFormalization.RandomGeometry.PantsMomentAsymptoticsIntegrals
import WPFormalization.Geometry.Bridge

noncomputable section
universe u v
namespace WP.RandomGeometry
open Set Filter MeasureTheory
open scoped ENNReal Classical

/-- Cutting the nonnegative orthant by the upper length condition gives the
actual Lebesgue cube, without a scaling or normalization factor. -/
lemma pants_lintegral_orthant_upper (r : ℕ) (L : ℝ)
    (f : (Fin r → ℝ) → ℝ≥0∞) :
    (∫⁻ x : Fin r → ℝ in {x | ∀ i, 0 ≤ x i},
      (if ∀ i, x i ≤ L then (1 : ℝ≥0∞) else 0) * f x) =
      ∫⁻ x : Fin r → ℝ, f x ∂pantsBoxMeasure r L := by
  have hind : (fun x : Fin r → ℝ =>
      (if ∀ i, x i ≤ L then (1 : ℝ≥0∞) else 0) * f x) =
      (Iic (fun _ : Fin r => L)).indicator f := by
    funext x
    by_cases hx : ∀ i, x i ≤ L <;> simp [Set.indicator, Pi.le_def, hx]
  rw [hind, lintegral_indicator measurableSet_Iic, pantsBoxMeasure_eq_restrict,
    Measure.restrict_restrict measurableSet_Iic]
  have hs : (Iic (fun _ : Fin r => L)) ∩ {x | ∀ i, 0 ≤ x i} =
      Icc (0 : Fin r → ℝ) (fun _ => L) := by
    ext x
    change ((∀ i, x i ≤ L) ∧ (∀ i, 0 ≤ x i)) ↔
      ((∀ i, 0 ≤ x i) ∧ (∀ i, x i ≤ L))
    exact and_comm
  rw [hs]

lemma pants_box_integrand_nonneg (P : PsiTheory)
    (G : WP.External.WeilPeterssonGeometry.{u,v} P)
    (g m r : ℕ) (hr : r ≤ m) (hs : Stable g m) (L : ℝ) :
    0 ≤ᵐ[pantsBoxMeasure r L] (fun x : Fin r → ℝ =>
      boundaryVolumeModel P g m (activeBoundaryLengths hr x) * ∏ i, x i) := by
  filter_upwards [pantsBoxMeasure_ae_mem r L] with x hx
  have hx0 : ∀ i, 0 ≤ x i := fun i => (hx i).1
  have hvb : 0 ≤ boundaryVolumeModel P g m (activeBoundaryLengths hr x) := by
    rw [← WP.Geometry.wpVolume_eq_boundaryVolumeModel P G _ _ _ hs
      (activeBoundaryLengths_nonneg hr x hx0)]
    exact ENNReal.toReal_nonneg
  exact mul_nonneg hvb (Finset.prod_nonneg (fun i _ => hx0 i))

/-- The exact nonnegative integral appearing in multicurve integration is the
ofReal of the actual finite-dimensional weighted boundary-volume integral. -/
theorem pantsBox_lintegral_eq (P : PsiTheory)
    (G : WP.External.WeilPeterssonGeometry.{u,v} P)
    (g m r : ℕ) (hr : r ≤ m) (hs : Stable g m) (L : ℝ) :
    (∫⁻ x : Fin r → ℝ in {x | ∀ i, 0 ≤ x i},
      (if ∀ i, x i ≤ L then (1 : ℝ≥0∞) else 0) *
        ENNReal.ofReal (boundaryVolumeModel P g m (activeBoundaryLengths hr x)) *
          ∏ i, ENNReal.ofReal (x i)) =
      ENNReal.ofReal (weightedBoxIntegral P g m r hr L) := by
  have hbox := pants_lintegral_orthant_upper r L
    (fun x => ENNReal.ofReal (boundaryVolumeModel P g m (activeBoundaryLengths hr x)) *
      ∏ i, ENNReal.ofReal (x i))
  simp only [← mul_assoc] at hbox
  rw [hbox]
  unfold weightedBoxIntegral
  rw [ofReal_integral_eq_lintegral_ofReal
    (weightedBoxIntegral_integrable P g m r hr L)
    (pants_box_integrand_nonneg P G g m r hr hs L)]
  apply lintegral_congr_ae
  filter_upwards [pantsBoxMeasure_ae_mem r L] with x hx
  have hw : 0 ≤ ∏ i, x i := Finset.prod_nonneg (fun i _ => (hx i).1)
  rw [mul_comm (boundaryVolumeModel P g m (activeBoundaryLengths hr x)),
    ENNReal.ofReal_mul hw, ENNReal.ofReal_prod_of_nonneg (fun i _ => (hx i).1), mul_comm]

end WP.RandomGeometry
