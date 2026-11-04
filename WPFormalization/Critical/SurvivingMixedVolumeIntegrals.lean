import WPFormalization.Critical.SurvivingMixedVolumeBoundary
import WPFormalization.Critical.CutBoundaryEnvelope
import WPFormalization.RandomGeometry.PantsFixedOrderAsymptoticsWindows
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Actual bounded physical-window integrals in the surviving mixed cut.
The dominating function is the canonical b_0 integrand, proved from the
already established all-stable boundary envelope. Empty windows are allowed. -/
noncomputable section
namespace WP.Critical
open Filter Set MeasureTheory
open scoped Topology

/-- The actual surviving root volume with the physical edge Jacobian. -/
def survivingMixedVolumeIntegral (P : PsiTheory) (g n r k : ℕ)
    (I : Fin (r+k) → Set ℝ) : ℝ :=
  ∫ x : Fin (r+k) → ℝ in {x | ∀ i, x i ∈ I i},
    boundaryVolumeModel P (g-k) (n-r+2*k) (survivingBoundaryLengths r k n x) * ∏ i, x i

/-- The canonical limiting physical integrand, before label and flip factors. -/
def survivingMixedLimitIntegrand (r k : ℕ) (x : Fin (r+k) → ℝ) : ℝ :=
  survivingBoundaryFactor r k 0 x * ∏ i, x i

set_option backward.isDefEq.respectTransparency false in
lemma survivingBoundaryFactor_continuous_lengths (r k : ℕ) (Y : Icc (0:ℝ) y₀) :
    Continuous (survivingBoundaryFactor r k Y) := by
  have hf (i : Fin (r+k)) : Continuous (fun x : Fin (r+k) → ℝ => boundaryFactor (Y:ℝ) (x i)) := by
    have hh : Continuous (fun x : Fin (r+k) → ℝ => ((Y,x i) : (Icc (0:ℝ) y₀) × ℝ)) :=
      continuous_const.prodMk (continuous_apply i)
    have hh' := boundaryFactor_joint_continuous.comp hh
    change Continuous (fun x : Fin (r+k) → ℝ => boundaryFactor (Y:ℝ) (x i)) at hh'
    exact hh'
  unfold survivingBoundaryFactor
  exact (continuous_finsetProd _ (fun j _ => hf (Fin.castAdd k j))).mul
    (continuous_finsetProd _ (fun i _ => (hf (Fin.natAdd r i)).pow 2))

lemma survivingMixedLimitIntegrand_continuous (r k : ℕ) :
    Continuous (survivingMixedLimitIntegrand r k) := by
  unfold survivingMixedLimitIntegrand
  exact (survivingBoundaryFactor_continuous_lengths r k ⟨0,le_rfl,y₀_pos.le⟩).mul (by fun_prop)

lemma survivingMixedVolumeIntegrand_continuous (P : PsiTheory) (g n r k : ℕ) :
    Continuous (fun x : Fin (r+k) → ℝ =>
      boundaryVolumeModel P (g-k) (n-r+2*k) (survivingBoundaryLengths r k n x)*∏ i,x i) := by
  have hb : Continuous (boundaryVolumeModel P (g-k) (n-r+2*k)) := by
    unfold boundaryVolumeModel
    fun_prop
  exact (hb.comp (survivingBoundaryLengths_continuous r k n)).mul (by fun_prop)

lemma survivingMixedVolumeIntegral_integrable (P : PsiTheory) (g n r k : ℕ)
    (I : Fin (r+k) → Set ℝ) (L : ℝ) (hIL : ∀ i,I i ⊆ Icc 0 L) :
    IntegrableOn (fun x : Fin (r+k) → ℝ =>
      boundaryVolumeModel P (g-k) (n-r+2*k) (survivingBoundaryLengths r k n x)*∏ i,x i)
      {x | ∀ i,x i ∈ I i} :=
  RandomGeometry.pants_window_integrable_continuous _ I L hIL _
    (survivingMixedVolumeIntegrand_continuous P g n r k)

/-- The actual physical-window integral divided by its cusp volume converges
on every bounded Borel product window, including the zero-dimensional window. -/
lemma surviving_mixed_volume_integral_normalized (P : PsiTheory) (n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop)
    (hd : Tendsto (fun g => (n g:ℝ)/g) atTop (𝓝 0)) (r k : ℕ)
    (I : Fin (r+k) → Set ℝ) (hI : ∀ i,MeasurableSet (I i))
    (L : ℝ) (hL : 0 ≤ L) (hIL : ∀ i,I i ⊆ Icc 0 L) :
    Tendsto (fun g => survivingMixedVolumeIntegral P g (n g) r k I /
      volumeModel P (g-k) (n g-r+2*k)) atTop
      (𝓝 (∫ x : Fin (r+k) → ℝ in {x | ∀ i,x i ∈ I i}, survivingMixedLimitIntegrand r k x)) := by
  let W : Set (Fin (r+k) → ℝ) := {x | ∀ i,x i ∈ I i}
  let F : ℕ → (Fin (r+k) → ℝ) → ℝ := fun g x =>
    boundaryVolumeModel P (g-k) (n g-r+2*k) (survivingBoundaryLengths r k (n g) x) /
      volumeModel P (g-k) (n g-r+2*k) * ∏ i,x i
  have hW : MeasurableSet W := RandomGeometry.pants_numeric_window_set_measurable _ I hI
  have hcont (g : ℕ) : Continuous (F g) := by
    have hh := (survivingMixedVolumeIntegrand_continuous P g (n g) r k).div_const
      (volumeModel P (g-k) (n g-r+2*k))
    convert hh using 1
    funext x
    dsimp [F]
    ring
  have hmeas : ∀ᶠ g in atTop,AEStronglyMeasurable (F g) (volume.restrict W) :=
    Eventually.of_forall (fun g => (hcont g).aestronglyMeasurable)
  have hb : Integrable (survivingMixedLimitIntegrand r k) (volume.restrict W) :=
    RandomGeometry.pants_window_integrable_continuous _ I L hIL _
      (survivingMixedLimitIntegrand_continuous r k)
  have hbound : ∀ᶠ g in atTop,∀ᵐ x ∂volume.restrict W,
      ‖F g x‖ ≤ survivingMixedLimitIntegrand r k x := by
    filter_upwards [hn.eventually_ge_atTop (2*r+1),eventually_ge_atTop (k+1)] with g hng hg
    filter_upwards [ae_restrict_mem hW] with x hx
    have hxL : ∀ i,x i ∈ Icc 0 L := fun i => hIL i (hx i)
    have hslot := survivingZeroPad_mem (r+(k+k)) (n g-r+2*k) _ L hL
      (survivingBoundaryCore_mem r k x L hxL)
    have hv : 0 < volumeModel P (g-k) (n g-r+2*k) :=
      diagonal_volume_pos_nonempty P _ _ (by omega) (by unfold Stable;omega)
    have hlo := (RandomGeometry.pants_boundary_volume_bounds P (g-k) (n g-r+2*k)
      (by omega) (by omega) _ (fun i => (hslot i).1)).1
    change 1 ≤ boundaryVolumeModel P (g-k) (n g-r+2*k)
      (survivingBoundaryLengths r k (n g) x)/volumeModel P (g-k) (n g-r+2*k) at hlo
    have hup := cut_boundaryVolumeModel_envelope P (g-k) (n g-r+2*k)
      (by omega) (by unfold Stable;omega) (survivingBoundaryLengths r k (n g) x)
    rw [survivingBoundaryLengths_prod r k (n g) (by omega)] at hup
    have hratio : boundaryVolumeModel P (g-k) (n g-r+2*k)
        (survivingBoundaryLengths r k (n g) x) / volumeModel P (g-k) (n g-r+2*k) ≤
        survivingBoundaryFactor r k 0 x := (div_le_iff₀ hv).mpr (by simpa only [mul_comm] using hup)
    have hw : 0 ≤ ∏ i,x i := Finset.prod_nonneg (fun i _ => (hxL i).1)
    dsimp [F,survivingMixedLimitIntegrand]
    rw [abs_of_nonneg (mul_nonneg (le_trans zero_le_one hlo) hw)]
    exact mul_le_mul_of_nonneg_right hratio hw
  have hpoint : ∀ᵐ x ∂volume.restrict W,
      Tendsto (fun g => F g x) atTop (𝓝 (survivingMixedLimitIntegrand r k x)) := by
    filter_upwards [ae_restrict_mem hW] with x hx
    exact (surviving_mixed_boundary_ratio P n hn hd r k L hL x (fun i => hIL i (hx i))).mul_const _
  have ht := tendsto_integral_filter_of_dominated_convergence
    (survivingMixedLimitIntegrand r k) hmeas hbound hb hpoint
  convert ht using 1
  funext g
  simp only [F,survivingMixedVolumeIntegral,W]
  rw [←integral_div]
  congr 1
  funext x
  ring

end WP.Critical
