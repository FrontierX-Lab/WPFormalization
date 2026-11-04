import WPFormalization.RandomGeometry.PrimitiveNonseparatingCuts
import WPFormalization.RandomGeometry.PrimitiveNonseparatingVolumeRatio
import WPFormalization.RandomGeometry.GeneralPlanarCutIntegralBound
import WPFormalization.RandomGeometry.GeneralPlanarRemainderIntegration
import WPFormalization.Critical.NonseparatingPointCounts

/-! Actual one-curve integration for nonseparating primitive geodesics,
with no cusp-density restriction and no additional expectation hypothesis. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory Set Filter
open scoped Topology ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    (MI : MirzakhaniIntegration G H T) {g n : ℕ}

def primitiveNonseparatingWindowSum (X : G.Moduli g n (fun _=>0)) (L : ℝ) : ℝ≥0∞ :=
  ∑o : PrimitiveNonseparatingOrbit T g n,T.orbitSum o.val (pantsWindowTest (fun _=>Icc 0 L)) X

lemma primitiveNonseparatingWindowSum_eq_actual (X : G.Moduli g n (fun _=>0))
    (L : ℝ) (hL : 0≤L) : primitiveNonseparatingWindowSum T X L=
      (WP.Critical.nonseparatingLengthPointMeasure T X).toMeasure (Iic (Real.toNNReal L)) := by
  rw [WP.Critical.nonseparatingLengthPointMeasure_eq_orbitSum T X _ measurableSet_Iic]
  unfold primitiveNonseparatingWindowSum
  apply Finset.sum_congr rfl
  intro o _
  apply tsum_congr
  intro γ
  have hpos := H.length_pos (γ.val 0)
  have he : (∀i : Fin 1,H.length (γ.val i)∈Icc 0 L) ↔H.length (γ.val 0)≤L := by
    constructor
    · intro hh
      exact (hh 0).2
    · intro hh i
      rw [Fin.eq_zero i]
      exact ⟨hpos.le,hh⟩
  simp only [WP.Critical.nonseparatingWindowTest,pantsWindowTest,he,mem_Iic,
    Real.toNNReal_le_iff_le_coe,Real.coe_toNNReal L hL]

include MI in
lemma primitiveNonseparatingWindowSum_measurable (L : ℝ) :
    Measurable (fun X : G.Moduli g n (fun _=>0)=>primitiveNonseparatingWindowSum T X L) := by
  exact Finset.measurable_sum _ (fun o _=>MI.orbitSum_measurable o.val _
    (pantsWindowTest_measurable _ (fun _=>measurableSet_Icc)))

include MI in
lemma primitiveNonseparating_orbit_wp_lintegral_upper (hg : 3≤g)
    (o : PrimitiveNonseparatingOrbit T g n) (L : ℝ) (hL : 0≤L) :
    (∫⁻X,T.orbitSum o.val (pantsWindowTest (fun _ : Fin 1=>Icc 0 L)) X
      ∂G.wpMeasure g n (fun _=>0))≤
      ENNReal.ofReal (Real.exp L*volumeModel P (g-1) (n+2)*(L^2/2)) := by
  have hchild := (diagonal_volume_pos_nonempty P (g-1) (n+2) (by omega) (by unfold Stable;omega)).le
  have hB : 0≤Real.exp L*volumeModel P (g-1) (n+2) := mul_nonneg (Real.exp_pos _).le hchild
  have hi := physical_window_lintegral_le_const ((T.cut o.val).volumeProduct G)
    (fun _ : Fin 1=>Icc 0 L) L (Real.exp L*volumeModel P (g-1) (n+2)) hL hB
    (fun _=>Subset.rfl) (fun x hx=>
      (OneEdgeCut.nonseparating_volume_upper (T.cut o.val) G (by omega) o.property
        (T.cut_euler o.val) x (fun i=>(hx i).1)).trans
          (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hx 0).2) hchild))
  simp only [pow_one] at hi
  rw [MI.orbit_integral o.val (by unfold Stable;omega)
    (by intro he;cases Prod.mk.inj he;omega) (by intro he;cases Prod.mk.inj he;omega)
    _ (pantsWindowTest_measurable _ (fun _=>measurableSet_Icc))]
  exact (mul_le_mul' (multicurve_coefficient_le_one T o.val) hi).trans_eq (one_mul _)

include MI in
lemma primitiveNonseparating_wp_lintegral_upper (hg : 3≤g) (L : ℝ) (hL : 0≤L) :
    (∫⁻X : G.Moduli g n (fun _=>0),primitiveNonseparatingWindowSum T X L
      ∂G.wpMeasure g n (fun _=>0))≤
      ENNReal.ofReal (Real.exp L*volumeModel P (g-1) (n+2)*(L^2/2)) := by
  simp only [primitiveNonseparatingWindowSum]
  rw [lintegral_finsetSum _ (fun o _=>
    (MI.orbitSum_measurable o.val _ (pantsWindowTest_measurable _ (fun _=>measurableSet_Icc))))]
  calc
    _≤∑_o : PrimitiveNonseparatingOrbit T g n,
        ENNReal.ofReal (Real.exp L*volumeModel P (g-1) (n+2)*(L^2/2)) :=
      Finset.sum_le_sum (fun o _=>primitiveNonseparating_orbit_wp_lintegral_upper T MI hg o L hL)
    _=(Fintype.card (PrimitiveNonseparatingOrbit T g n):ℝ≥0∞)*
        ENNReal.ofReal (Real.exp L*volumeModel P (g-1) (n+2)*(L^2/2)) := by simp
    _≤1*ENNReal.ofReal (Real.exp L*volumeModel P (g-1) (n+2)*(L^2/2)) :=
      mul_le_mul' (by exact_mod_cast primitiveNonseparatingOrbit_card_le_one T g n) le_rfl
    _=_ := one_mul _

include MI in
lemma primitiveNonseparating_probability_lintegral_upper (hg : 3≤g) (L : ℝ) (hL : 0≤L)
    (hV : 0<volumeModel P g n) :
    (∫⁻X : G.Moduli g n (fun _=>0),primitiveNonseparatingWindowSum T X L ∂wpProbability G g n)≤
      ENNReal.ofReal (Real.exp L*(volumeModel P (g-1) (n+2)/volumeModel P g n)*(L^2/2)) := by
  have hs : Stable g n := by unfold Stable;omega
  have hmass : G.wpMeasure g n (fun _=>0) univ=ENNReal.ofReal (volumeModel P g n) := by
    rw [←WP.Geometry.cuspVolume_eq_volumeModel P G g n hs]
    exact (ENNReal.ofReal_toReal (G.finite_volume g n _ hs (fun _=>le_rfl))).symm
  rw [wpProbability,lintegral_smul_measure,smul_eq_mul]
  have hi := mul_le_mul' (le_refl ((G.wpMeasure g n (fun _=>0) univ)⁻¹))
    (primitiveNonseparating_wp_lintegral_upper T MI (g:=g) (n:=n) hg L hL)
  apply hi.trans_eq
  rw [hmass,←ENNReal.ofReal_inv_of_pos hV,←ENNReal.ofReal_mul (inv_nonneg.mpr hV.le)]
  congr 1
  ring

end WP.RandomGeometry
