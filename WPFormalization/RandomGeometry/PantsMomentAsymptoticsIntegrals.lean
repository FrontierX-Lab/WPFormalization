import WPFormalization.RandomGeometry.PantsMomentAsymptotics
import WPFormalization.RandomGeometry.PantsMomentAsymptoticsBoundary
import Mathlib.MeasureTheory.Integral.Pi

/-! Actual finite-dimensional short-boundary integrals. The measure is the
product of Lebesgue measure on the physical intervals [0,L]. The active lengths
occupy precisely the first r boundary slots of the actual volume polynomial. -/
noncomputable section
namespace WP.RandomGeometry
open Set Filter MeasureTheory
open scoped Topology

/-- Embed r labelled physical lengths into m boundary slots, filling the
remaining slots with zero. -/
def activeBoundaryLengths {r m : ℕ} (hr : r ≤ m) (x : Fin r → ℝ) : Fin m → ℝ :=
  fun i => ∑ j : Fin r, if Fin.castLE hr j=i then x j else 0

@[simp] lemma activeBoundaryLengths_apply {r m : ℕ} (hr : r ≤ m)
    (x : Fin r → ℝ) (j : Fin r) : activeBoundaryLengths hr x (Fin.castLE hr j) = x j := by
  classical
  simp [activeBoundaryLengths]

lemma activeBoundaryLengths_sum {r m : ℕ} (hr : r ≤ m) (x : Fin r → ℝ) :
    (∑ i, activeBoundaryLengths hr x i) = ∑ j, x j := by
  classical
  unfold activeBoundaryLengths
  rw [Finset.sum_comm]
  simp

lemma activeBoundaryLengths_nonneg {r m : ℕ} (hr : r ≤ m) (x : Fin r → ℝ)
    (hx : ∀ j, 0 ≤ x j) : ∀ i, 0 ≤ activeBoundaryLengths hr x i := by
  classical
  intro i
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact hx j
  · exact le_rfl

lemma activeBoundaryLengths_continuous {r m : ℕ} (hr : r ≤ m) :
    Continuous (activeBoundaryLengths hr) := by
  classical
  unfold activeBoundaryLengths
  apply continuous_pi
  intro i
  apply continuous_finset_sum
  intro j _
  split_ifs <;> fun_prop

/-- The physical r-dimensional cube measure; no scaled or limiting process. -/
def pantsBoxMeasure (r : ℕ) (L : ℝ) : Measure (Fin r → ℝ) :=
  Measure.pi (fun _ : Fin r => volume.restrict (Icc 0 L))

lemma pantsBoxMeasure_eq_restrict (r : ℕ) (L : ℝ) :
    pantsBoxMeasure r L = volume.restrict (Icc (0 : Fin r → ℝ) (fun _ => L)) := by
  rw [pantsBoxMeasure,←Measure.restrict_pi_pi,←volume_pi,pi_univ_Icc]
  rfl

lemma pantsBoxMeasure_ae_mem (r : ℕ) (L : ℝ) :
    ∀ᵐ x ∂pantsBoxMeasure r L, ∀ i, 0 ≤ x i ∧ x i ≤ L := by
  rw [pantsBoxMeasure_eq_restrict]
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx i
  exact ⟨hx.1 i,hx.2 i⟩

lemma pantsBoxMeasure_integrable_continuous (r : ℕ) (L : ℝ)
    (f : (Fin r → ℝ) → ℝ) (hf : Continuous f) : Integrable f (pantsBoxMeasure r L) := by
  rw [pantsBoxMeasure_eq_restrict]
  exact hf.integrableOn_Icc

lemma pantsBoxMeasure_integral_weight (r : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    (∫ x : Fin r → ℝ, ∏ i, x i ∂pantsBoxMeasure r L) = (L^2/2)^r := by
  rw [pantsBoxMeasure,integral_fintype_prod_eq_pow (fun x : ℝ => x)]
  simp only [Fintype.card_fin]
  congr 1
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hL]
  simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0),sub_zero] using integral_id (a := (0:ℝ)) (b := L)

/-- The actual boundary-volume integral which occurs after cutting r distinct
short pants curves, before its explicit cusp-label coefficient is applied. -/
def weightedBoxIntegral (P : PsiTheory) (g m r : ℕ) (hr : r ≤ m) (L : ℝ) : ℝ :=
  ∫ x : Fin r → ℝ,
    boundaryVolumeModel P g m (activeBoundaryLengths hr x) * ∏ i, x i
      ∂pantsBoxMeasure r L

lemma weightedBoxIntegral_integrable (P : PsiTheory) (g m r : ℕ) (hr : r ≤ m) (L : ℝ) :
    Integrable (fun x : Fin r → ℝ =>
      boundaryVolumeModel P g m (activeBoundaryLengths hr x) * ∏ i, x i)
      (pantsBoxMeasure r L) := by
  apply pantsBoxMeasure_integrable_continuous
  have hc : Continuous (boundaryVolumeModel P g m) := by
    unfold boundaryVolumeModel
    fun_prop
  exact (hc.comp (activeBoundaryLengths_continuous hr)).mul (by fun_prop)

/-- A uniform integral comparison for every number r of active short boundaries.
It includes exactly the (L²/2)^r physical Jacobian, with no factorial correction. -/
lemma weightedBoxIntegral_bounds (P : PsiTheory) (g m r : ℕ) (hr : r ≤ m)
    (hg : 1 ≤ g) (hm : 1 ≤ m) (L : ℝ) (hL : 0 ≤ L) :
    volumeModel P g m*(L^2/2)^r ≤ weightedBoxIntegral P g m r hr L ∧
      weightedBoxIntegral P g m r hr L ≤
        Real.exp (r*L/2)*(volumeModel P g m*(L^2/2)^r) := by
  have hv : 0 < volumeModel P g m :=
    diagonal_volume_pos_nonempty P g m hm (by unfold Stable;omega)
  have hb : Integrable (fun x : Fin r → ℝ => volumeModel P g m*∏ i, x i)
      (pantsBoxMeasure r L) :=
    (pantsBoxMeasure_integrable_continuous r L _ (by fun_prop))
  have hu : Integrable (fun x : Fin r → ℝ =>
      Real.exp (r*L/2)*volumeModel P g m*∏ i, x i) (pantsBoxMeasure r L) :=
    pantsBoxMeasure_integrable_continuous r L _ (by fun_prop)
  have hi := weightedBoxIntegral_integrable P g m r hr L
  have hpoint : ∀ᵐ x ∂pantsBoxMeasure r L,
      volumeModel P g m*∏ i, x i ≤
        boundaryVolumeModel P g m (activeBoundaryLengths hr x)*∏ i, x i ∧
      boundaryVolumeModel P g m (activeBoundaryLengths hr x)*∏ i, x i ≤
        Real.exp (r*L/2)*volumeModel P g m*∏ i, x i := by
    filter_upwards [pantsBoxMeasure_ae_mem r L] with x hx
    have hx0 : ∀ i, 0 ≤ x i := fun i => (hx i).1
    have hw : 0 ≤ ∏ i, x i := Finset.prod_nonneg (fun i _ => hx0 i)
    have hbounds := pants_boundary_volume_bounds P g m hg hm
      (activeBoundaryLengths hr x) (activeBoundaryLengths_nonneg hr x hx0)
    have hsum : (∑ i, activeBoundaryLengths hr x i) ≤ (r:ℝ)*L := by
      rw [activeBoundaryLengths_sum]
      exact (Finset.sum_le_sum (fun i _ => (hx i).2)).trans_eq (by simp)
    have he : Real.exp ((∑ i, activeBoundaryLengths hr x i)/2) ≤ Real.exp (r*L/2) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hsum (by norm_num))
    constructor
    · exact mul_le_mul_of_nonneg_right (by simpa using (le_div_iff₀ hv).mp hbounds.1) hw
    · exact mul_le_mul_of_nonneg_right
        (((div_le_iff₀ hv).mp hbounds.2).trans (mul_le_mul_of_nonneg_right he hv.le)) hw
  constructor
  · have h := integral_mono_ae hb hi (hpoint.mono fun _ hx => hx.1)
    simpa only [weightedBoxIntegral,integral_const_mul,pantsBoxMeasure_integral_weight r L hL] using h
  · have h := integral_mono_ae hi hu (hpoint.mono fun _ hx => hx.2)
    simpa only [weightedBoxIntegral,integral_const_mul,pantsBoxMeasure_integral_weight r L hL,mul_assoc] using h

end WP.RandomGeometry
