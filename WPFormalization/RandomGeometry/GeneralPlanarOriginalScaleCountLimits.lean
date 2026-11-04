import WPFormalization.RandomGeometry.GeneralPlanarOriginalScaleOrderedMoments
import WPFormalization.RandomGeometry.GeneralPlanarDensityCountLimits

/-! Actual fixed type/window Poisson laws at the original paper scale q.
No change-of-scale probability premise is assumed. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

def generalPlanarOriginalFamilyWindows {ι : Type*} (g n : ℕ) (lo hi : ι→ℝ) : ι→Set ℝ :=
  fun j=>Ioc (lo j/Real.sqrt (pantsScale g n)) (hi j/Real.sqrt (pantsScale g n))

def generalPlanarOriginalFamilyCounts {ι : Type*} [Fintype ι] (g n : ℕ)
    (k : ι→ℕ) (lo hi : ι→ℝ) (X : G.Moduli g n (fun _=>0)) : ι→ℕ :=
  fun j=>generalPlanarWindowCount H X (fun _ : Fin 1=>k j)
    (pantsScaledWindowCap (pantsScale g n) hi) (fun _=>generalPlanarOriginalFamilyWindows g n lo hi j)

lemma generalPlanar_original_scaled_type_windows_disjoint {ι : Type*}
    (g n : ℕ) (hq : 0<pantsScale g n) (k : ι→ℕ) (lo hi : ι→ℝ)
    (hdis : Pairwise (fun j l=>k j≠k l ∨ Disjoint (Ioc (lo j) (hi j)) (Ioc (lo l) (hi l)))) :
    Pairwise (fun j l=>k j≠k l ∨ Disjoint
      (generalPlanarOriginalFamilyWindows g n lo hi j) (generalPlanarOriginalFamilyWindows g n lo hi l)) := by
  intro j l hjl
  rcases hdis hjl with hne|hset
  · exact Or.inl hne
  · right
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hs := Real.sqrt_pos.mpr hq
    apply Set.disjoint_left.mp hset
      (show x*Real.sqrt (pantsScale g n)∈Ioc (lo j) (hi j) from
        ⟨(div_lt_iff₀ hs).mp hx.1,(le_div_iff₀ hs).mp hx.2⟩)
      (show x*Real.sqrt (pantsScale g n)∈Ioc (lo l) (hi l) from
        ⟨(div_lt_iff₀ hs).mp hy.1,(le_div_iff₀ hs).mp hy.2⟩)

include C MI in
lemma generalPlanar_original_fixed_mixed_moment_limit {ι : Type*} [Fintype ι]
    (k : ι→ℕ) (hk : ∀j,2≤k j) (a : ι→ℕ) (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : ι→ℝ) (hlo : ∀j,0≤lo j) (hab : ∀j,lo j≤hi j)
    (hdis : Pairwise (fun j l=>k j≠k l ∨ Disjoint (Ioc (lo j) (hi j)) (Ioc (lo l) (hi l))))
    (x : ℝ) (hxs : Tendsto (fun g=>primitiveSaddleX g (n g)) atTop (𝓝 x)) :
    Tendsto (fun g=>∫X : G.Moduli g (n g) (fun _=>0),
      ∏j,((generalPlanarOriginalFamilyCounts H g (n g) k lo hi X j).descFactorial (a j):ℝ)
        ∂wpProbability G g (n g)) atTop (𝓝 (generalPlanarFamilyMovingWeight P k lo hi a x)) := by
  let R := ∑j,a j
  let lo' : Fin R→ℝ := fun i=>lo ((mixedSlotsEquiv a).symm i).1
  let hi' : Fin R→ℝ := fun i=>hi ((mixedSlotsEquiv a).symm i).1
  have hprod : generalPlanarStarWeight P R (expandedTypes a k) lo' hi' x=
      generalPlanarFamilyMovingWeight P k lo hi a x := by
    unfold generalPlanarStarWeight generalPlanarFamilyMovingWeight
    simpa only [expandedTypes,lo',hi',generalPlanarFamilyRate] using mixedSlots_prod (M:=ℝ) a R (mixedSlotsEquiv a)
      (fun j=>generalPlanarFamilyRate P (k j) (lo j) (hi j) x)
  have hm := generalPlanar_original_scaled_ordered_moment_limit H T C MI R (expandedTypes a k)
    (fun i=>hk _) n hn lo' hi' (fun i=>hlo _) (fun i=>hab _) x hxs
  rw [hprod] at hm
  apply hm.congr'
  filter_upwards [(WP.Spectral.pantsScale_tendsto_atTop n hn).eventually_gt_atTop (0:ℝ)] with g hq
  have hdisg := generalPlanar_original_scaled_type_windows_disjoint g (n g) hq k lo hi hdis
  have he : ∀X : G.Moduli g (n g) (fun _=>0),
      (∏j,((generalPlanarOriginalFamilyCounts H g (n g) k lo hi X j).descFactorial (a j):ℝ))=
      (generalPlanarWindowCount H X (expandedTypes a k)
        (pantsScaledWindowCap (pantsScale g (n g)) hi')
        (generalPlanarStarScaledWindows R (pantsScale g (n g)) lo' hi'):ℝ) := by
    intro X
    unfold generalPlanarOriginalFamilyCounts
    rw [generalPlanar_mixed_factorial_eq_expandedWindowCount_real H X k _ _ a hdisg]
    congr 1
    exact generalPlanarWindowCount_cutoff_eq H X (expandedTypes a k) _ _ _
      (fun i=>pants_scaled_window_subset_cap _ lo hi hlo hab _)
      (pants_scaled_window_subset_cap _ lo' hi' (fun i=>hlo _) (fun i=>hab _))
  simp_rw [he]

include C MI in
lemma generalPlanar_original_family_counts_measurable {ι : Type*} [Fintype ι]
    (n : ℕ→ℕ) (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (k : ι→ℕ) (lo hi : ι→ℝ) (hlo : ∀j,0≤lo j) (hab : ∀j,lo j≤hi j) :
    ∀ᶠg in atTop,Measurable (generalPlanarOriginalFamilyCounts H g (n g) k lo hi) := by
  have hp : 0<2*Real.arsinh 1 := mul_pos (by norm_num) (Real.arsinh_pos_iff.mpr (by norm_num))
  filter_upwards [eventually_ge_atTop (1:ℕ),
    (pants_scaled_window_cap_tendsto_zero _ (WP.Spectral.pantsScale_tendsto_atTop n hn) hi).eventually
      (gt_mem_nhds hp)] with g hg hsmall
  apply Measurable.of_eval
  intro j
  have hm := generalPlanarWindowCount_measurable H T C MI (g:=g) (n:=n g) hg (fun _ : Fin 1=>k j) _ hsmall
    (fun _=>generalPlanarOriginalFamilyWindows g (n g) lo hi j) (fun _=>measurableSet_Ioc)
    (fun _=>pants_scaled_window_subset_cap _ lo hi hlo hab j)
  simpa [generalPlanarOriginalFamilyCounts] using hm.nat_floor

include C MI in
theorem generalPlanar_original_fixed_mixed_lintegral_moments {ι : Type*} [Fintype ι]
    (k : ι→ℕ) (hk : ∀j,2≤k j) (a : ι→ℕ) (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : ι→ℝ) (hlo : ∀j,0≤lo j) (hab : ∀j,lo j≤hi j)
    (hdis : Pairwise (fun j l=>k j≠k l ∨ Disjoint (Ioc (lo j) (hi j)) (Ioc (lo l) (hi l))))
    (x : ℝ) (hx : 0≤x)
    (hxs : Tendsto (fun g=>primitiveSaddleX g (n g)) atTop (𝓝 x)) :
    Tendsto (fun g=>∫⁻X : G.Moduli g (n g) (fun _=>0),
      ∏j,(((generalPlanarOriginalFamilyCounts H g (n g) k lo hi X j).descFactorial (a j):ℕ):ℝ≥0∞)
        ∂wpProbability G g (n g))
      atTop (𝓝 (∏j,((generalPlanarFamilyRates P k lo hi x j:ℝ≥0∞)^(a j)))) := by
  have hr := generalPlanar_original_fixed_mixed_moment_limit H T C MI k hk a n hn lo hi hlo hab hdis x hxs
  have hrate := fun j=>generalPlanar_family_rate_nonneg P (k j) (hk j) (lo j) (hi j) x (hlo j) (hab j) hx
  have hh := (ENNReal.continuous_ofReal.tendsto _).comp hr
  change Tendsto _ atTop (𝓝 (ENNReal.ofReal (∏j,(generalPlanarFamilyRate P (k j) (lo j) (hi j) x)^(a j)))) at hh
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _=>pow_nonneg (hrate j) _)] at hh
  simp_rw [ENNReal.ofReal_pow (hrate _)] at hh
  have hp : 0<2*Real.arsinh 1 := mul_pos (by norm_num) (Real.arsinh_pos_iff.mpr (by norm_num))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ),
    (WP.Spectral.pantsScale_tendsto_atTop n hn).eventually_gt_atTop (0:ℝ),
    (pants_scaled_window_cap_tendsto_zero _ (WP.Spectral.pantsScale_tendsto_atTop n hn) hi).eventually
      (gt_mem_nhds hp)] with g hg hq hsmall
  have hdisg := generalPlanar_original_scaled_type_windows_disjoint g (n g) hq k lo hi hdis
  change ENNReal.ofReal (∫X,∏j,((generalPlanarWindowCount H X (fun _ : Fin 1=>k j)
    (pantsScaledWindowCap (pantsScale g (n g)) hi)
    (fun _=>generalPlanarOriginalFamilyWindows g (n g) lo hi j)).descFactorial (a j):ℝ)
      ∂wpProbability G g (n g))=_
  simp_rw [generalPlanar_mixed_factorial_eq_expandedWindowCount_real H _ k _ _ a hdisg]
  simp only [generalPlanarOriginalFamilyCounts]
  simp_rw [generalPlanar_mixed_factorial_eq_expandedWindowCount_ennreal H _ k _ _ a hdisg]
  exact (generalPlanarWindowCount_lintegral_eq_ofReal_integral H T C MI hg _ _ hsmall _
    (fun _=>measurableSet_Ioc) (fun i=>pants_scaled_window_subset_cap _ lo hi hlo hab _)).symm

include C MI in
theorem generalPlanar_original_density_mixed_factorial_limits {d : ℕ}
    (k : Fin d→ℕ) (hk : ∀j,2≤k j) (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin d→ℝ) (hlo : ∀j,0≤lo j) (hab : ∀j,lo j≤hi j)
    (hdis : Pairwise (fun j m=>k j≠k m ∨ Disjoint (Ioc (lo j) (hi j)) (Ioc (lo m) (hi m))))
    (l : ℝ≥0∞) (hl : Tendsto (fun g : ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) :
    MixedFactorialMomentLimit (fun g=>wpProbability G g (n g))
      (fun g=>generalPlanarOriginalFamilyCounts H g (n g) k lo hi)
      (generalPlanarDensityWindowRates P k lo hi l) := by
  rw [generalPlanar_density_window_rates_eq P k hk]
  intro a
  exact generalPlanar_original_fixed_mixed_lintegral_moments H T C MI k hk a n hn lo hi hlo hab hdis
    _ (planar_density_saddle_mem l).1 (primitive_saddle_tendsto_density_fast n hn l hl)

include C MI in
theorem generalPlanar_original_density_type_window_counts_poisson {d : ℕ}
    (k : Fin d→ℕ) (hk : ∀j,2≤k j) (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin d→ℝ) (hlo : ∀j,0≤lo j) (hab : ∀j,lo j≤hi j)
    (hdis : Pairwise (fun j m=>k j≠k m ∨ Disjoint (Ioc (lo j) (hi j)) (Ioc (lo m) (hi m))))
    (l : ℝ≥0∞) (hl : Tendsto (fun g : ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) :
    LawConverges (fun g=>wpProbability G g (n g))
      (fun g=>generalPlanarOriginalFamilyCounts H g (n g) k lo hi)
      (productPoissonMeasure (generalPlanarDensityWindowRates P k lo hi l)) id := by
  apply factorial_moments_poisson_nonneg
  · exact WP.Spectral.wpProbability_eventually_probability P G n
      ((pants_fast_cusps_tendsto_atTop n hn).eventually_ge_atTop 1)
  · exact (generalPlanar_original_family_counts_measurable H T C MI n hn k lo hi hlo hab).mono
      (fun _ h=>h.aemeasurable)
  · exact generalPlanar_original_density_mixed_factorial_limits H T C MI k hk n hn lo hi hlo hab hdis l hl

end WP.RandomGeometry
