import WPFormalization.RandomGeometry.GeneralPlanarStarIntegration
import WPFormalization.RandomGeometry.PantsWindowIntegration
import WPFormalization.RandomGeometry.GeneralPlanarStarIntegralBoundary

/-! Exact normalization of the actual general-star window integral. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory
open scoped ENNReal
variable {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (MI : MirzakhaniIntegration G H T) {g n r : ℕ}

include G in
lemma generalPlanarStarVolumeIntegrand_nonneg (k : Fin r → ℕ)
    (hg : 2≤g) (hk : ∀i,2≤k i) (x : Fin r → ℝ) (hx : ∀i,0≤x i) :
    0≤generalPlanarStarVolumeIntegrand P g n r k x := by
  unfold generalPlanarStarVolumeIntegrand
  apply mul_nonneg
  · rw [←WP.Geometry.wpVolume_eq_boundaryVolumeModel P G g _ _ (by unfold Stable;omega)
      (generalPlanarStarRootLengths_nonneg n r k x hx)]
    exact ENNReal.toReal_nonneg
  · apply Finset.prod_nonneg
    intro i _
    have hki := hk i
    rw [←WP.Geometry.wpVolume_eq_boundaryVolumeModel P G 0 (k i+1) _ (by unfold Stable;omega)
      (generalPlanarStarLeafLengths_nonneg (k i) (x i) (hx i))]
    exact ENNReal.toReal_nonneg

lemma generalPlanarStar_window_orthant_lintegral (g n r : ℕ) (k : Fin r → ℕ)
    (I : Fin r → Set ℝ) (hI : ∀i,MeasurableSet (I i))
    (hpos : ∀i x,x∈I i →0≤x) :
    generalPlanarStarOrthantIntegral P g n r k (pantsWindowTest I) =
      ∫⁻x : Fin r → ℝ in {x | ∀i,x i∈I i},
        ENNReal.ofReal (generalPlanarStarVolumeIntegrand P g n r k x)*∏i,ENNReal.ofReal (x i) := by
  classical
  let B : Set (Fin r → ℝ) := {x | ∀i,x i∈I i}
  let f := fun x : Fin r → ℝ => ENNReal.ofReal (generalPlanarStarVolumeIntegrand P g n r k x)*
    ∏i,ENNReal.ofReal (x i)
  have hfun : (fun x => pantsWindowTest I x*f x)=B.indicator f := by
    funext x
    by_cases hx : ∀i,x i∈I i <;> simp [pantsWindowTest,Set.indicator,B,hx]
  have hB : MeasurableSet B := pants_window_set_measurable I hI
  have hinter : B∩{x | ∀i,0≤x i}=B := by
    apply Set.inter_eq_left.mpr
    intro x hx i
    exact hpos i (x i) (hx i)
  unfold generalPlanarStarOrthantIntegral
  simp only [mul_assoc]
  change (∫⁻x in {x | ∀i,0≤x i},pantsWindowTest I x*f x)=_
  rw [hfun,lintegral_indicator hB,Measure.restrict_restrict hB,hinter]

include G in
lemma generalPlanarStar_window_lintegral_toReal (k : Fin r → ℕ)
    (hg : 2≤g) (hk : ∀i,2≤k i) (I : Fin r → Set ℝ)
    (hI : ∀i,MeasurableSet (I i)) (hpos : ∀i x,x∈I i →0≤x) :
    (generalPlanarStarOrthantIntegral P g n r k (pantsWindowTest I)).toReal =
      generalPlanarStarWindowIntegral P g n r k I := by
  rw [generalPlanarStar_window_orthant_lintegral g n r k I hI hpos]
  have hm := (generalPlanarStarVolumeIntegrand_continuous P g n r k).mul
    (show Continuous (fun x : Fin r → ℝ => ∏i,x i) by fun_prop)
  have hn : 0≤ᵐ[volume.restrict {x : Fin r → ℝ | ∀i,x i∈I i}]
      (fun x => generalPlanarStarVolumeIntegrand P g n r k x*∏i,x i) := by
    filter_upwards [ae_restrict_mem (pants_window_set_measurable I hI)] with x hx
    have hx0 : ∀i,0≤x i := fun i => hpos i (x i) (hx i)
    exact mul_nonneg (generalPlanarStarVolumeIntegrand_nonneg G k hg hk x hx0)
      (Finset.prod_nonneg (fun i _ => hx0 i))
  rw [generalPlanarStarWindowIntegral,integral_eq_lintegral_of_nonneg_ae hn hm.aestronglyMeasurable]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (pants_window_set_measurable I hI)] with x hx
  have hx0 : ∀i,0≤x i := fun i => hpos i (x i) (hx i)
  have hw : 0≤∏i,x i := Finset.prod_nonneg (fun i _ => hx0 i)
  rw [mul_comm (generalPlanarStarVolumeIntegrand P g n r k x),ENNReal.ofReal_mul hw,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => hx0 i),mul_comm]

include MI in
lemma generalPlanarStar_windows_moment_toReal (k : Fin r → ℕ)
    (hg : 2≤g) (hk : ∀i,2≤k i) (hgn : (g,n)≠(2,0))
    (I : Fin r → Set ℝ) (hI : ∀i,MeasurableSet (I i)) (hpos : ∀i x,x∈I i →0≤x) :
    (∫⁻X,generalPlanarStarWindowSum T g n r k (pantsWindowTest I) X ∂wpProbability G g n).toReal =
      generalPlanarStarWindowCut P g n r k I := by
  have hmass : (G.wpMeasure g n (fun _ => 0) Set.univ).toReal=volumeModel P g n :=
    WP.Geometry.cuspVolume_eq_volumeModel P G g n (by unfold Stable;omega)
  rw [generalPlanarStar_probability_lintegral T MI hg hk hgn _ (pantsWindowTest_measurable I hI),
    ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    hmass,
    generalPlanarStar_window_lintegral_toReal G k hg hk I hI hpos,
    generalPlanarStarOrbit_card_real T g n r k hg hk]
  unfold generalPlanarStarWindowCut
  ring
end WP.RandomGeometry
