import WPFormalization.RandomGeometry.PrimitiveSeparatingOrbitSums
import WPFormalization.RandomGeometry.GeneralPlanarCutIntegralBound
import WPFormalization.RandomGeometry.GeneralPlanarRemainderIntegration

/-! Actual Mirzakhani integration for every positive-genus separating orbit.
The ordered allocation sum gives an upper bound, with no assumed symmetry
factor or omitted genus-one or zero-cusp components. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory Set Filter Finset
open scoped Topology ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    (MI : MirzakhaniIntegration G H T) {g n : ℕ}

def IsPositiveGenusSeparating {X : G.Moduli g n (fun _=>0)} (γ : H.Primitive g n X) : Prop :=
  ∃o : PrimitiveSeparatingOrbit T g n,T.orbitMem o.val X (fun _=>γ)

def primitiveSeparatingWindowSum (X : G.Moduli g n (fun _=>0)) (L : ℝ) : ℝ≥0∞ :=
  ∑o : PrimitiveSeparatingOrbit T g n,T.orbitSum o.val (pantsWindowTest (fun _=>Icc 0 L)) X

def primitiveSeparatingOrbitWeight (o : PrimitiveSeparatingOrbit T g n) : ℝ :=
  volumeModel P (primitiveSeparatingOrbitGenus T o) (primitiveSeparatingOrbitCuspCount T o+1)*
    volumeModel P (g-primitiveSeparatingOrbitGenus T o) (n-primitiveSeparatingOrbitCuspCount T o+1)

lemma primitiveSeparatingOrbitWeight_nonneg (o : PrimitiveSeparatingOrbit T g n) :
    0≤primitiveSeparatingOrbitWeight T o := by
  rw [primitiveSeparatingOrbitWeight,←primitiveSeparatingAllocationWeight_of_orbit T]
  exact primitiveSeparatingAllocationWeight_nonneg P g n _

include MI in
lemma primitiveSeparatingWindowSum_measurable (L : ℝ) :
    Measurable (fun X : G.Moduli g n (fun _=>0)=>primitiveSeparatingWindowSum T X L) := by
  exact Finset.measurable_sum _ (fun o _=>MI.orbitSum_measurable o.val _
    (pantsWindowTest_measurable _ (fun _=>measurableSet_Icc)))

include MI in
lemma primitiveSeparating_orbit_wp_lintegral_upper (hg : 3≤g)
    (o : PrimitiveSeparatingOrbit T g n) (L : ℝ) (hL : 0≤L) :
    (∫⁻X,T.orbitSum o.val (pantsWindowTest (fun _ : Fin 1=>Icc 0 L)) X
      ∂G.wpMeasure g n (fun _=>0))≤
      ENNReal.ofReal (Real.exp L*primitiveSeparatingOrbitWeight T o*(L^2/2)) := by
  have hw := primitiveSeparatingOrbitWeight_nonneg T o
  have hi := physical_window_lintegral_le_const ((T.cut o.val).volumeProduct G)
    (fun _ : Fin 1=>Icc 0 L) L (Real.exp L*primitiveSeparatingOrbitWeight T o) hL
    (mul_nonneg (Real.exp_pos _).le hw) (fun _=>Subset.rfl) (fun x hx=>
      (primitiveSeparatingOrbit_volume_upper T o x (fun i=>(hx i).1)).trans
        (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hx 0).2) hw))
  simp only [pow_one] at hi
  rw [MI.orbit_integral o.val (by unfold Stable;omega)
    (by intro he;cases Prod.mk.inj he;omega) (by intro he;cases Prod.mk.inj he;omega)
    _ (pantsWindowTest_measurable _ (fun _=>measurableSet_Icc))]
  exact (mul_le_mul' (multicurve_coefficient_le_one T o.val) hi).trans_eq (one_mul _)

include MI in
lemma primitiveSeparating_wp_lintegral_upper (hg : 3≤g) (L : ℝ) (hL : 0≤L) :
    (∫⁻X : G.Moduli g n (fun _=>0),primitiveSeparatingWindowSum T X L
      ∂G.wpMeasure g n (fun _=>0))≤
      ENNReal.ofReal (Real.exp L*(L^2/2)*∑o : PrimitiveSeparatingOrbit T g n,
        primitiveSeparatingOrbitWeight T o) := by
  simp only [primitiveSeparatingWindowSum]
  rw [lintegral_finsetSum _ (fun o _=>
    MI.orbitSum_measurable o.val _ (pantsWindowTest_measurable _ (fun _=>measurableSet_Icc)))]
  apply (Finset.sum_le_sum (fun o _=>primitiveSeparating_orbit_wp_lintegral_upper T MI hg o L hL)).trans_eq
  rw [←ENNReal.ofReal_sum_of_nonneg (fun o _=>
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (primitiveSeparatingOrbitWeight_nonneg T o)) (by positivity))]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  ring

include MI in
lemma primitiveSeparating_probability_lintegral_upper (hg : 3≤g) (L : ℝ) (hL : 0≤L)
    (hV : 0<volumeModel P g n) :
    (∫⁻X : G.Moduli g n (fun _=>0),primitiveSeparatingWindowSum T X L ∂wpProbability G g n)≤
      ENNReal.ofReal (primitiveSeparatingWindowEnvelope P g n L) := by
  have hs : Stable g n := by unfold Stable;omega
  have hmass : G.wpMeasure g n (fun _=>0) univ=ENNReal.ofReal (volumeModel P g n) := by
    rw [←WP.Geometry.cuspVolume_eq_volumeModel P G g n hs]
    exact (ENNReal.ofReal_toReal (G.finite_volume g n _ hs (fun _=>le_rfl))).symm
  rw [wpProbability,lintegral_smul_measure,smul_eq_mul]
  have hi := mul_le_mul' (le_refl ((G.wpMeasure g n (fun _=>0) univ)⁻¹))
    (primitiveSeparating_wp_lintegral_upper T MI (g:=g) (n:=n) hg L hL)
  apply hi.trans
  rw [hmass,←ENNReal.ofReal_inv_of_pos hV,←ENNReal.ofReal_mul (inv_nonneg.mpr hV.le)]
  apply ENNReal.ofReal_le_ofReal
  have hsum := primitiveSeparatingOrbit_weight_ratio_sum_le T (g:=g) (n:=n) hV
  have hh := mul_le_mul_of_nonneg_left hsum (show 0≤Real.exp L*(L^2/2) by positivity)
  change _≤Real.exp L*(L^2/2)*primitiveSeparatingVolumeSum P g n
  convert hh using 1 <;> simp only [primitiveSeparatingOrbitWeight] <;> ring

end WP.RandomGeometry
