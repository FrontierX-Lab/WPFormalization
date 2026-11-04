import WPFormalization.RandomGeometry.GeneralPlanarMixedWindowMoments
import WPFormalization.External.PointProcessProbability
import WPFormalization.Spectral.VanishingGap
import Mathlib.MeasureTheory.Function.Floor

/-! Genuine factorial-moment limits of the actual fixed planar type/window
family, conditional only on convergence of the actual saddle parameter. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

def generalPlanarFamilyRate (P : PsiTheory) (k : ℕ) (lo hi x : ℝ) : ℝ :=
  2*volumeModel P 0 (k+1)/(k.factorial:ℝ)*(x/(2*Real.pi^2))^(k-2)*(hi^2-lo^2)

def generalPlanarFamilyRates {ι : Type*} (P : PsiTheory) (k : ι→ℕ)
    (lo hi : ι→ℝ) (x : ℝ) : ι→ℝ≥0 :=
  fun j=>Real.toNNReal (generalPlanarFamilyRate P (k j) (lo j) (hi j) x)

def generalPlanarFamilyCounts {ι : Type*} [Fintype ι] (g n : ℕ)
    (k : ι→ℕ) (lo hi : ι→ℝ) (X : G.Moduli g n (fun _=>0)) : ι→ℕ :=
  fun j=>generalPlanarWindowCount H X (fun _ : Fin 1=>k j)
    (generalPlanarFamilyWindowCap g n hi) (fun _=>generalPlanarFamilyWindows g n lo hi j)

lemma generalPlanar_family_rate_nonneg (P : PsiTheory) (k : ℕ) (hk : 2≤k)
    (lo hi x : ℝ) (hlo : 0≤lo) (hab : lo≤hi) (hx : 0≤x) :
    0≤generalPlanarFamilyRate P k lo hi x := by
  have hV := (diagonal_volume_pos_nonempty P 0 (k+1) (by omega) (by unfold Stable;omega)).le
  have hd : 0≤hi^2-lo^2 := by nlinarith
  unfold generalPlanarFamilyRate
  exact mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hV) (by positivity))
    (pow_nonneg (div_nonneg hx (by positivity)) _)) hd

lemma generalPlanar_family_moving_weight_continuous {ι : Type*} [Fintype ι]
    (P : PsiTheory) (k : ι→ℕ) (lo hi : ι→ℝ) (a : ι→ℕ) :
    Continuous (generalPlanarFamilyMovingWeight P k lo hi a) := by
  unfold generalPlanarFamilyMovingWeight
  fun_prop

lemma generalPlanar_family_window_cap_tendsto_zero {ι : Type*} [Fintype ι]
    (n : ℕ→ℕ) (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (hi : ι→ℝ) : Tendsto (fun g=>generalPlanarFamilyWindowCap g (n g) hi) atTop (𝓝 0) :=
  primitive_planar_rescaled_length_tendsto_zero n hn (1+∑j,hi j)

include C MI in
lemma generalPlanar_family_counts_measurable {ι : Type*} [Fintype ι]
    (n : ℕ→ℕ) (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (k : ι→ℕ) (lo hi : ι→ℝ) (hlo : ∀j,0≤lo j) (hab : ∀j,lo j≤hi j) :
    ∀ᶠg in atTop,Measurable (generalPlanarFamilyCounts H g (n g) k lo hi) := by
  have hp : 0<2*Real.arsinh 1 := mul_pos (by norm_num) (Real.arsinh_pos_iff.mpr (by norm_num))
  filter_upwards [eventually_ge_atTop (1:ℕ),
    (generalPlanar_family_window_cap_tendsto_zero n hn hi).eventually (gt_mem_nhds hp)] with g hg hsmall
  apply Measurable.of_eval
  intro j
  have hm := generalPlanarWindowCount_measurable H T C MI (g:=g) (n:=n g) hg (fun _ : Fin 1=>k j) _ hsmall
    (fun _=>generalPlanarFamilyWindows g (n g) lo hi j) (fun _=>measurableSet_Ioc)
    (fun _=>generalPlanar_family_window_subset_cap g (n g) lo hi hlo hab j)
  simpa [generalPlanarFamilyCounts] using hm.nat_floor

include C MI in
theorem generalPlanar_fixed_mixed_windows_lintegral_moments {ι : Type*} [Fintype ι]
    (k : ι→ℕ) (hk : ∀j,2≤k j) (a : ι→ℕ) (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : ι→ℝ) (hlo : ∀j,0≤lo j) (hab : ∀j,lo j≤hi j)
    (hdis : Pairwise (fun j l=>k j≠k l ∨ Disjoint (Ioc (lo j) (hi j)) (Ioc (lo l) (hi l))))
    (x : ℝ) (hx : 0≤x)
    (hxs : Tendsto (fun g=>primitiveSaddleX g (n g)) atTop (𝓝 x)) :
    Tendsto (fun g=>∫⁻X : G.Moduli g (n g) (fun _=>0),
      ∏j,(((generalPlanarFamilyCounts H g (n g) k lo hi X j).descFactorial (a j):ℕ):ℝ≥0∞)
        ∂wpProbability G g (n g))
      atTop (𝓝 (∏j,((generalPlanarFamilyRates P k lo hi x j:ℝ≥0∞)^(a j)))) := by
  have herr := generalPlanar_fixed_mixed_windows_moving_moments H T C MI k hk a n hn lo hi hlo hab hdis
  have hw := (generalPlanar_family_moving_weight_continuous P k lo hi a).tendsto x |>.comp hxs
  have hr := herr.add hw
  simp only [Function.comp_def,zero_add,sub_add_cancel] at hr
  have hrate := fun j=>generalPlanar_family_rate_nonneg P (k j) (hk j) (lo j) (hi j) x (hlo j) (hab j) hx
  have hh := (ENNReal.continuous_ofReal.tendsto _).comp hr
  change Tendsto _ atTop (𝓝 (ENNReal.ofReal (∏j,(generalPlanarFamilyRate P (k j) (lo j) (hi j) x)^(a j)))) at hh
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _=>pow_nonneg (hrate j) _)] at hh
  simp_rw [ENNReal.ofReal_pow (hrate _)] at hh
  have hp : 0<2*Real.arsinh 1 := mul_pos (by norm_num) (Real.arsinh_pos_iff.mpr (by norm_num))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ),
    (primitive_planar_scale_tendsto_atTop n hn).eventually_gt_atTop (0:ℝ),
    (generalPlanar_family_window_cap_tendsto_zero n hn hi).eventually (gt_mem_nhds hp)] with g hg hq hsmall
  have hdisg := generalPlanar_scaled_type_windows_disjoint g (n g) hq k lo hi hdis
  change ENNReal.ofReal (∫X,∏j,((generalPlanarWindowCount H X (fun _ : Fin 1=>k j)
    (generalPlanarFamilyWindowCap g (n g) hi) (fun _=>generalPlanarFamilyWindows g (n g) lo hi j)).descFactorial (a j):ℝ)
      ∂wpProbability G g (n g))=_
  simp_rw [generalPlanar_mixed_factorial_eq_expandedWindowCount_real H _ k _ _ a hdisg]
  simp only [generalPlanarFamilyCounts]
  simp_rw [generalPlanar_mixed_factorial_eq_expandedWindowCount_ennreal H _ k _ _ a hdisg]
  exact (generalPlanarWindowCount_lintegral_eq_ofReal_integral H T C MI hg _ _ hsmall _
    (fun _=>measurableSet_Ioc) (fun i=>generalPlanar_family_window_subset_cap g (n g) lo hi hlo hab _)).symm

include C MI in
theorem generalPlanar_fixed_type_window_counts_poisson {d : ℕ}
    (k : Fin d→ℕ) (hk : ∀j,2≤k j) (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin d→ℝ) (hlo : ∀j,0≤lo j) (hab : ∀j,lo j≤hi j)
    (hdis : Pairwise (fun j l=>k j≠k l ∨ Disjoint (Ioc (lo j) (hi j)) (Ioc (lo l) (hi l))))
    (x : ℝ) (hx : 0≤x)
    (hxs : Tendsto (fun g=>primitiveSaddleX g (n g)) atTop (𝓝 x)) :
    LawConverges (fun g=>wpProbability G g (n g))
      (fun g=>generalPlanarFamilyCounts H g (n g) k lo hi)
      (productPoissonMeasure (generalPlanarFamilyRates P k lo hi x)) id := by
  apply factorial_moments_poisson_nonneg
  · exact WP.Spectral.wpProbability_eventually_probability P G n
      ((pants_fast_cusps_tendsto_atTop n hn).eventually_ge_atTop 1)
  · exact (generalPlanar_family_counts_measurable H T C MI n hn k lo hi hlo hab).mono
      (fun _ h=>h.aemeasurable)
  · intro a
    exact generalPlanar_fixed_mixed_windows_lintegral_moments H T C MI k hk a n hn lo hi hlo hab hdis x hx hxs

end WP.RandomGeometry
