import WPFormalization.RandomGeometry.GeneralPlanarRemainderAsymptotics
import WPFormalization.RandomGeometry.GeneralPlanarStarMomentAsymptotics

/-! All actual fixed ordered planar cusp types, including nested cuts. Their
moments have the moving star weights with an absolute error tending to zero. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory Set Filter
open scoped Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

def generalPlanarFixedWindowCap (g n r : ℕ) (hi : Fin r→ℝ) : ℝ :=
  (1+∑i,hi i)/Real.sqrt (primitivePlanarEffectiveScale g n)

lemma generalPlanar_scaled_windows_subset_cap (g n r : ℕ) (lo hi : Fin r→ℝ)
    (hlo : ∀i,0≤lo i) (hab : ∀i,lo i≤hi i) :
    ∀i,generalPlanarStarScaledWindows r (primitivePlanarEffectiveScale g n) lo hi i⊆
      Icc 0 (generalPlanarFixedWindowCap g n r hi) := by
  intro i x hx
  have hhi : ∀j,0≤hi j := fun j=>(hlo j).trans (hab j)
  have hsum : hi i≤∑j,hi j := Finset.single_le_sum (fun j _=>hhi j) (Finset.mem_univ i)
  refine ⟨(div_nonneg (hlo i) (Real.sqrt_nonneg _)).trans hx.1.le,?_⟩
  exact hx.2.trans (div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))

include C MI in
theorem generalPlanar_fixed_windows_moving_moments (r : ℕ) (k : Fin r→ℕ)
    (hk : ∀i,2≤k i) (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin r→ℝ) (hlo : ∀i,0≤lo i) (hab : ∀i,lo i≤hi i) :
    Tendsto (fun g=>(∫X : G.Moduli g (n g) (fun _=>0),
      (generalPlanarWindowCount H X k (generalPlanarFixedWindowCap g (n g) r hi)
        (generalPlanarStarScaledWindows r (primitivePlanarEffectiveScale g (n g)) lo hi):ℝ)
      ∂wpProbability G g (n g))-
        generalPlanarStarWeight P r k lo hi (primitiveSaddleX g (n g))) atTop (𝓝 0) := by
  let I := fun g=>generalPlanarStarScaledWindows r (primitivePlanarEffectiveScale g (n g)) lo hi
  let t : ℝ := 1+∑i,hi i
  have ht : 0≤t := by
    have hs : 0≤∑i,hi i := Finset.sum_nonneg (fun i _=>(hlo i).trans (hab i))
    dsimp [t]
    linarith
  have hrem := generalPlanarRemainder_moment_tendsto_zero T C MI r k n hn t ht I
    (fun g i=>measurableSet_Ioc) (Eventually.of_forall (fun g=>
      generalPlanar_scaled_windows_subset_cap g (n g) r lo hi hlo hab))
  have hstar := general_planar_star_scaled_window_asymptotic P r k hk n hn lo hi hlo hab
  have htend := hstar.add hrem
  simp only [add_zero] at htend
  apply htend.congr'
  have hL := primitive_planar_rescaled_length_tendsto_zero n hn t
  have hcollar : 0<2*Real.arsinh 1 :=
    mul_pos (by norm_num) (Real.arsinh_pos_iff.mpr (by norm_num))
  filter_upwards [eventually_ge_atTop (3:ℕ),hL.eventually (gt_mem_nhds hcollar)] with g hg hLg
  have hdecomp := generalPlanar_actual_moment_decomposition H T C MI (g:=g) (n:=n g)
    (by omega) k hk (by intro h;cases Prod.mk.inj h;omega)
    (generalPlanarFixedWindowCap g (n g) r hi) hLg (I g) (fun i=>measurableSet_Ioc)
    (generalPlanar_scaled_windows_subset_cap g (n g) r lo hi hlo hab)
  change generalPlanarStarWindowCut P g (n g) r k (I g)-
      generalPlanarStarWeight P r k lo hi (primitiveSaddleX g (n g))+
      (∫X,(generalPlanarRemainderWindowSum T g (n g) r k (pantsWindowTest (I g)) X).toReal
        ∂wpProbability G g (n g))=_
  rw [hdecomp]
  ring

end WP.RandomGeometry
