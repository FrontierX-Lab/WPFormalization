import WPFormalization.RandomGeometry.GeneralPlanarRemainderFiberSums
import WPFormalization.RandomGeometry.GeneralPlanarRemainderNumericalBound
import WPFormalization.RandomGeometry.PantsMomentAsymptoticsConcentration

/-! The actual nested configurations vanish: uniform finite cut-pattern
counts and physical integration are combined with the true volume-ratio decay. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory Set Filter
open scoped Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)
    {g n r : ℕ} {k : Fin r→ℕ}

include C MI in
lemma generalPlanarRemainder_mean_upper (hg : 2≤g) (hn : (∑i,k i)<n)
    (I : Fin r→Set ℝ) (hI : ∀i,MeasurableSet (I i)) (L : ℝ)
    (hL0 : 0≤L) (hL : L<2*Real.arsinh 1) (hsub : ∀i,I i⊆Icc 0 L) :
    (∫X : G.Moduli g n (fun _=>0),
      (generalPlanarRemainderWindowSum T g n r k (pantsWindowTest I) X).toReal
        ∂wpProbability G g n)≤generalPlanarRemainderNumericalBound P g n r (∑i,k i) L := by
  rw [generalPlanarRemainder_real_moment_eq_sum T C MI hg hn I hI L hL0 hL hsub,
    generalPlanarRemainder_sum_by_budget T (by omega)]
  unfold generalPlanarRemainderNumericalBound
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  exact generalPlanarRemainder_fiber_term_upper T hg hn a d
    (Nat.le_of_lt_succ (Finset.mem_range.mp ha)) I L hL0 hsub

include C MI in
theorem generalPlanarRemainder_moment_tendsto_zero (r : ℕ) (k : Fin r→ℕ)
    (n : ℕ→ℕ) (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (t : ℝ) (ht : 0≤t) (I : ℕ→Fin r→Set ℝ) (hI : ∀g i,MeasurableSet (I g i))
    (hsub : ∀ᶠg : ℕ in atTop,∀i,I g i⊆Icc 0
      (t/Real.sqrt (primitivePlanarEffectiveScale g (n g)))) :
    Tendsto (fun g=>∫X : G.Moduli g (n g) (fun _=>0),
      (generalPlanarRemainderWindowSum T g (n g) r k (pantsWindowTest (I g)) X).toReal
        ∂wpProbability G g (n g)) atTop (𝓝 0) := by
  have hL := primitive_planar_rescaled_length_tendsto_zero n hn t
  have hninf := pants_fast_cusps_tendsto_atTop n hn
  have hcollar : 0<2*Real.arsinh 1 :=
    mul_pos (by norm_num) (Real.arsinh_pos_iff.mpr (by norm_num))
  apply squeeze_zero' (Eventually.of_forall (fun g=>integral_nonneg (fun X=>ENNReal.toReal_nonneg))) _
    (generalPlanarRemainderNumericalBound_tendsto_zero P r (∑i,k i) n hn t)
  filter_upwards [eventually_ge_atTop (2:ℕ),hninf.eventually_gt_atTop (∑i,k i),
    hL.eventually (gt_mem_nhds hcollar),hsub] with g hg hng hLg hsg
  exact generalPlanarRemainder_mean_upper T C MI hg hng (I g) (hI g) _
    (div_nonneg ht (Real.sqrt_nonneg _)) hLg hsg

end WP.RandomGeometry
