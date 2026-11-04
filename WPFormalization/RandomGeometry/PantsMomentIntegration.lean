import WPFormalization.RandomGeometry.PantsOrbitPartition
import WPFormalization.RandomGeometry.PantsMomentAsymptoticsStarVolume
import WPFormalization.RandomGeometry.CutVolumeTransport

/-! Actual factorial-moment integration, derived from the generic classical
orbit theorem and the locally proved complete pants-orbit classification. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory
open scoped ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T) {g n r : ℕ}

lemma pantsLengthTest_measurable (L : ℝ) : Measurable (pantsLengthTest (r:=r) L) := by
  classical
  apply Measurable.ite _ measurable_const measurable_const
  have h := MeasurableSet.iInter (fun i : Fin r =>
    measurableSet_le (measurable_pi_apply i : Measurable (fun x : Fin r → ℝ => x i))
      (measurable_const : Measurable (fun _ : Fin r → ℝ => L)))
  simpa only [Set.setOf_forall] using h

lemma pants_orthant_measurable (r : ℕ) : MeasurableSet {x : Fin r → ℝ | ∀i, 0 ≤ x i} := by
  have h := MeasurableSet.iInter (fun i : Fin r =>
    measurableSet_le (measurable_const : Measurable (fun _ : Fin r → ℝ => (0:ℝ)))
      (measurable_pi_apply i : Measurable (fun x : Fin r → ℝ => x i)))
  simpa only [Set.setOf_forall] using h

def pantsOrthantCutIntegral (P : PsiTheory) (g n r : ℕ) (hn : 2*r ≤ n) (L : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : Fin r → ℝ in {x | ∀i, 0 ≤ x i},
    pantsLengthTest L x * ENNReal.ofReal
      (boundaryVolumeModel P g (n-r) (activeBoundaryLengths (show r ≤ n-r by omega) x)) *
      ∏i, ENNReal.ofReal (x i)

lemma pantsStarOrbit_volumeProduct {g n r : ℕ} (hg : 2 ≤ g) (hn : 2*r ≤ n)
    (o : PantsStarOrbit T g n r) (x : Fin r → ℝ) (hx : ∀i, 0 ≤ x i) :
    (T.cut o.val).volumeProduct G x =
      boundaryVolumeModel P g (n-r) (activeBoundaryLengths (show r ≤ n-r by omega) x) := by
  exact ((pantsOrbitLabelIso T o).volumeProduct_eq G x hx
    (pantsStar_stable g n r _ hg)).symm.trans
      (pantsStar_volumeProduct P G g n r (pantsOrbitLabel T o) hg hn x hx)

include MI in
lemma pantsStarOrbit_lintegral (hg : 2 ≤ g) (hn : 2*r ≤ n)
    (o : PantsStarOrbit T g n r) (hgn : (g,n) ≠ (2,0)) (L : ℝ) :
    (∫⁻ X, T.orbitSum o.val (pantsLengthTest L) X ∂G.wpMeasure g n (fun _ => 0)) =
      pantsOrthantCutIntegral P g n r hn L := by
  rw [MI.orbit_integral o.val (by unfold Stable; omega) (by intro h; cases Prod.mk.inj h; omega)
    hgn (pantsLengthTest L) (pantsLengthTest_measurable L),pantsStarOrbit_coefficient T hg,one_mul]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (pants_orthant_measurable r)] with x hx
  rw [pantsStarOrbit_volumeProduct T hg hn o x hx]

include C MI in
lemma pants_factorial_wp_lintegral (hg : 2 ≤ g) (hr : 0 < r) (hn : 2*r ≤ n)
    (L : ℝ) (hL : L < 2*Real.arsinh 1) :
    (∫⁻ X : G.Moduli g n (fun _ => 0),
      ((H.pantsCount X L).descFactorial r : ℝ≥0∞) ∂G.wpMeasure g n (fun _ => 0)) =
      (Fintype.card (PantsStarOrbit T g n r) : ℝ≥0∞) * pantsOrthantCutIntegral P g n r hn L := by
  have hgn : (g,n) ≠ (2,0) := by
    intro h
    have h0 := congrArg Prod.snd h
    simp only [Prod.snd] at h0
    omega
  calc
    _ = ∫⁻ X, ∑' o : PantsStarOrbit T g n r,
        T.orbitSum o.val (pantsLengthTest L) X ∂G.wpMeasure g n (fun _ => 0) := by
      apply lintegral_congr
      intro X
      exact (pants_factorial_orbit_sum T C (by omega) hr X L hL).symm
    _ = ∑' o : PantsStarOrbit T g n r,
        ∫⁻ X, T.orbitSum o.val (pantsLengthTest L) X ∂G.wpMeasure g n (fun _ => 0) :=
      lintegral_tsum (fun o => (MI.orbitSum_measurable o.val _ (pantsLengthTest_measurable L)).aemeasurable)
    _ = ∑' _ : PantsStarOrbit T g n r, pantsOrthantCutIntegral P g n r hn L := by
      apply tsum_congr
      intro o
      exact pantsStarOrbit_lintegral T MI hg hn o hgn L
    _ = _ := by rw [tsum_fintype]; simp

include C MI in
lemma pants_factorial_probability_lintegral (hg : 2 ≤ g) (hr : 0 < r) (hn : 2*r ≤ n)
    (L : ℝ) (hL : L < 2*Real.arsinh 1) :
    (∫⁻ X : G.Moduli g n (fun _ => 0),
      ((H.pantsCount X L).descFactorial r : ℝ≥0∞) ∂wpProbability G g n) =
      (G.wpMeasure g n (fun _ => 0) Set.univ)⁻¹ *
        (Fintype.card (PantsStarOrbit T g n r) : ℝ≥0∞) * pantsOrthantCutIntegral P g n r hn L := by
  rw [wpProbability,lintegral_smul_measure,pants_factorial_wp_lintegral T C MI hg hr hn L hL]
  simp only [smul_eq_mul,mul_assoc]

end WP.RandomGeometry
