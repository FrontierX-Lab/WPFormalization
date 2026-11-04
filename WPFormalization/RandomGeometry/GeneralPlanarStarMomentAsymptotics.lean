import WPFormalization.RandomGeometry.GeneralPlanarStarWindowMoments
import WPFormalization.RandomGeometry.GeneralPlanarStarIntegralAsymptotics

/-! The actual star contribution in (14.12), before imposing a density limit.
The limiting comparison retains the moving saddle weights, including zero limits. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory Filter Set
open scoped Topology ENNReal
variable {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (MI : MirzakhaniIntegration G H T)

include MI in
theorem generalPlanarStar_actual_window_asymptotic (r : ℕ) (k : Fin r → ℕ)
    (hk : ∀i,2≤k i) (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin r → ℝ) (hlo : ∀i,0≤lo i) (hab : ∀i,lo i≤hi i) :
    Tendsto (fun g =>
      (∫⁻X,generalPlanarStarWindowSum T g (n g) r k
        (pantsWindowTest (generalPlanarStarScaledWindows r (primitivePlanarEffectiveScale g (n g)) lo hi)) X
        ∂wpProbability G g (n g)).toReal -
        generalPlanarStarWeight P r k lo hi (primitiveSaddleX g (n g))) atTop (𝓝 0) := by
  have hq := primitive_planar_scale_tendsto_atTop n hnfast
  apply (general_planar_star_scaled_window_asymptotic P r k hk n hnfast lo hi hlo hab).congr'
  filter_upwards [eventually_ge_atTop (3:ℕ),hq.eventually_gt_atTop 0] with g hg hqg
  have hp : ∀i x,x∈generalPlanarStarScaledWindows r (primitivePlanarEffectiveScale g (n g)) lo hi i →0≤x := by
    intro i x hx
    exact (div_nonneg (hlo i) (Real.sqrt_nonneg _)).trans hx.1.le
  have hm := generalPlanarStar_windows_moment_toReal G H T MI (g:=g) (n:=n g) k (by omega) hk
    (by intro h;cases Prod.mk.inj h;omega)
    (generalPlanarStarScaledWindows r (primitivePlanarEffectiveScale g (n g)) lo hi)
    (fun i => measurableSet_Ioc) hp
  exact (congrArg (fun z => z-generalPlanarStarWeight P r k lo hi (primitiveSaddleX g (n g))) hm).symm
end WP.RandomGeometry
