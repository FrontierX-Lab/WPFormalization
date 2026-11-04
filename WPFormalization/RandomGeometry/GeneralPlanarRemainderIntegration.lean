import WPFormalization.RandomGeometry.GeneralPlanarMomentDecomposition

/-! Exact integration of the actual nonstar configurations, before bounding the
finite patterns. Every component volume and symmetry factor remains visible. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory
open scoped ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    (MI : MirzakhaniIntegration G H T) {g n r : ℕ}

lemma multicurve_coefficient_le_one (o : T.Orbit g n r) : T.coefficient o≤1 := by
  unfold MulticurveTopology.coefficient
  apply ENNReal.inv_le_one.mpr
  have hi : (1:ℝ≥0∞)≤((T.cut o).orientationStabilizerIndex:ℝ≥0∞) := by
    exact_mod_cast (T.cut o).orientationStabilizerIndex_pos
  have hp : (1:ℝ≥0∞)≤(2:ℝ≥0∞)^((T.cut o).oneHandleCount) := one_le_pow₀ (by norm_num)
  calc
    1 = 1*1 := by simp
    _ ≤ _ := mul_le_mul' hp hi

include MI in
lemma generalPlanarRemainder_wp_lintegral (hg : 2≤g) (hgn : (g,n)≠(2,0))
    (k : Fin r → ℕ) (F : (Fin r → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻X,generalPlanarRemainderWindowSum T g n r k F X ∂G.wpMeasure g n (fun _ => 0)) =
      ∑'o : GeneralPlanarRemainderOrbit T g n r k,T.coefficient o.val.val *
        ∫⁻x : Fin r → ℝ in {x |∀i,0≤x i},
          F x*ENNReal.ofReal ((T.cut o.val.val).volumeProduct G x)*∏i,ENNReal.ofReal (x i) := by
  calc
    _ = ∑'o : GeneralPlanarRemainderOrbit T g n r k,
      ∫⁻X,T.orbitSum o.val.val F X ∂G.wpMeasure g n (fun _ => 0) :=
      lintegral_tsum (fun o => (MI.orbitSum_measurable o.val.val F hF).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro o
      exact MI.orbit_integral o.val.val (by unfold Stable;omega)
        (by intro h;cases Prod.mk.inj h;omega) hgn F hF

include MI in
lemma generalPlanarRemainder_probability_lintegral (hg : 2≤g) (hgn : (g,n)≠(2,0))
    (k : Fin r → ℕ) (F : (Fin r → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻X,generalPlanarRemainderWindowSum T g n r k F X ∂wpProbability G g n) =
      (G.wpMeasure g n (fun _ => 0) Set.univ)⁻¹ *
      ∑'o : GeneralPlanarRemainderOrbit T g n r k,T.coefficient o.val.val *
        ∫⁻x : Fin r → ℝ in {x |∀i,0≤x i},
          F x*ENNReal.ofReal ((T.cut o.val.val).volumeProduct G x)*∏i,ENNReal.ofReal (x i) := by
  rw [wpProbability,lintegral_smul_measure,generalPlanarRemainder_wp_lintegral T MI hg hgn k F hF]
  rfl
end WP.RandomGeometry
