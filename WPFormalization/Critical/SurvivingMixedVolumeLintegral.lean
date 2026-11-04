import WPFormalization.Critical.SurvivingMixedVolumeIntegrals

/-! Exact nonnegative-integral conversion for the actual surviving mixed
physical window contribution. No moment or orbit estimate is used. -/
noncomputable section
universe u v
namespace WP.Critical
open Set MeasureTheory
open scoped ENNReal Classical

lemma surviving_mixed_window_lintegral_eq (P : PsiTheory)
    (G : External.WeilPeterssonGeometry.{u,v} P) (g n r k : ℕ)
    (hg : k+1 ≤ g) (hn : 2*r+1 ≤ n)
    (I : Fin (r+k) → Set ℝ) (hI : ∀ i,MeasurableSet (I i))
    (L : ℝ) (hL : 0 ≤ L) (hIL : ∀ i,I i ⊆ Icc 0 L) :
    (∫⁻ x : Fin (r+k) → ℝ in {x | ∀ i,0 ≤ x i},
      (if ∀ i,x i ∈ I i then (1:ℝ≥0∞) else 0) *
        ENNReal.ofReal (boundaryVolumeModel P (g-k) (n-r+2*k)
          (survivingBoundaryLengths r k n x)) * ∏ i,ENNReal.ofReal (x i)) =
      ENNReal.ofReal (survivingMixedVolumeIntegral P g n r k I) := by
  let W : Set (Fin (r+k) → ℝ) := {x | ∀ i,x i ∈ I i}
  have hW : MeasurableSet W := RandomGeometry.pants_numeric_window_set_measurable _ I hI
  have hsub : W ⊆ {x | ∀ i,0 ≤ x i} := fun x hx i => (hIL i (hx i)).1
  have hrestrict : volume.restrict W =
      (volume.restrict {x : Fin (r+k) → ℝ | ∀ i,0 ≤ x i}).restrict W := by
    rw [Measure.restrict_restrict hW,inter_eq_left.mpr hsub]
  have hind : (fun x : Fin (r+k) → ℝ =>
      (if ∀ i,x i ∈ I i then (1:ℝ≥0∞) else 0) *
        ENNReal.ofReal (boundaryVolumeModel P (g-k) (n-r+2*k)
          (survivingBoundaryLengths r k n x)) * ∏ i,ENNReal.ofReal (x i)) =
      W.indicator (fun x => ENNReal.ofReal (boundaryVolumeModel P (g-k) (n-r+2*k)
        (survivingBoundaryLengths r k n x))*∏ i,ENNReal.ofReal (x i)) := by
    funext x
    by_cases hx : ∀ i,x i ∈ I i <;> simp [W,Set.indicator,hx]
  rw [hind,lintegral_indicator hW,←hrestrict]
  have hnonneg : 0 ≤ᵐ[volume.restrict W] (fun x : Fin (r+k) → ℝ =>
      boundaryVolumeModel P (g-k) (n-r+2*k) (survivingBoundaryLengths r k n x)*∏ i,x i) := by
    filter_upwards [ae_restrict_mem hW] with x hx
    have hs := survivingZeroPad_mem (r+(k+k)) (n-r+2*k) _ L hL
      (survivingBoundaryCore_mem r k x L (fun i => hIL i (hx i)))
    have he := Geometry.wpVolume_eq_boundaryVolumeModel P G (g-k) (n-r+2*k)
      (survivingBoundaryLengths r k n x) (by unfold Stable;omega) (fun i => (hs i).1)
    have hv : 0 ≤ boundaryVolumeModel P (g-k) (n-r+2*k) (survivingBoundaryLengths r k n x) :=
      he ▸ ENNReal.toReal_nonneg
    exact mul_nonneg hv (Finset.prod_nonneg (fun i _ => hsub hx i))
  unfold survivingMixedVolumeIntegral
  rw [ofReal_integral_eq_lintegral_ofReal
    (survivingMixedVolumeIntegral_integrable P g n r k I L hIL) hnonneg]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hW] with x hx
  have hw : 0 ≤ ∏ i,x i := Finset.prod_nonneg (fun i _ => hsub hx i)
  rw [mul_comm (boundaryVolumeModel P (g-k) (n-r+2*k) (survivingBoundaryLengths r k n x)),
    ENNReal.ofReal_mul hw, ENNReal.ofReal_prod_of_nonneg (fun i _ => hsub hx i),mul_comm]

end WP.Critical
