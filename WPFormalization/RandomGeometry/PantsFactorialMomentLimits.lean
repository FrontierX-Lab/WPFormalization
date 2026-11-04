import WPFormalization.RandomGeometry.PantsFixedOrderAsymptoticsMoments
import WPFormalization.RandomGeometry.PantsWindowIntegrability

/-! Genuine nonnegative factorial-moment limits for the actual WP pants
counts. The proved finite real moments justify the change of integral type. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
variable {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

include C MI in
lemma pants_fixed_mixed_Ioc_lintegral_moments_of_fast_cusps {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : ι → ℝ) (hlo : ∀j, 0≤lo j) (horder : ∀j, lo j≤hi j)
    (hdis : Pairwise (fun j k => Disjoint (Ioc (lo j) (hi j)) (Ioc (lo k) (hi k)))) :
    Tendsto (fun g => ∫⁻ X : G.Moduli g (n g) (fun _ => 0),
      ∏j, ((pantsWindowCount H X
        (pantsMixedScaledWindowCap a (pantsScale g (n g)) hi)
        (fun _ : Fin 1 => Ioc (lo j/Real.sqrt (pantsScale g (n g)))
          (hi j/Real.sqrt (pantsScale g (n g))))).descFactorial (a j) : ℝ≥0∞)
      ∂wpProbability G g (n g))
      atTop (𝓝 (∏j, (ENNReal.ofReal ((hi j)^2-(lo j)^2))^(a j))) := by
  have hd : ∀j, 0≤(hi j)^2-(lo j)^2 := by
    intro j
    have := hlo j
    have := horder j
    nlinarith
  have hh := (ENNReal.continuous_ofReal.tendsto _).comp
    (pants_fixed_mixed_Ioc_moments_of_fast_cusps G H T C MI a n hnfast lo hi hlo horder hdis)
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => pow_nonneg (hd j) _)] at hh
  simp_rw [ENNReal.ofReal_pow (hd _)] at hh
  have hq := WP.Spectral.pantsScale_tendsto_atTop n hnfast
  have hcap := pants_scaled_window_cap_tendsto_zero _ hq
    (fun i : Fin (∑j, a j) => hi ((mixedSlotsEquiv a).symm i).1)
  have hp : 0<2*Real.arsinh 1 := by
    have : 0<Real.arsinh 1 := Real.arsinh_pos_iff.mpr (by norm_num)
    positivity
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ),hq.eventually_gt_atTop 0,
    hcap.eventually (gt_mem_nhds hp)] with g hg hqg hsmall
  letI := wpProbability_isFinite G g (n g)
  let I : ι → Set ℝ := fun j => Ioc (lo j/Real.sqrt (pantsScale g (n g)))
      (hi j/Real.sqrt (pantsScale g (n g)))
  have hdisg : Pairwise (fun j k => Disjoint (I j) (I k)) :=
    pants_scaled_Ioc_pairwise_disjoint _ hqg lo hi hdis
  have hsupport : ∀i, expandedWindows a I i ⊆
      Icc 0 (pantsMixedScaledWindowCap a (pantsScale g (n g)) hi) :=
    pants_scaled_window_subset_cap _
      (fun i : Fin (∑j, a j) => lo ((mixedSlotsEquiv a).symm i).1)
      (fun i : Fin (∑j, a j) => hi ((mixedSlotsEquiv a).symm i).1)
      (fun i => hlo _) (fun i => horder _)
  change ENNReal.ofReal (∫X, ∏j,
      ((pantsWindowCount H X _ (fun _ : Fin 1 => I j)).descFactorial (a j) : ℝ)
      ∂wpProbability G g (n g)) =
    ∫⁻X, ∏j,
      ((pantsWindowCount H X _ (fun _ : Fin 1 => I j)).descFactorial (a j) : ℝ≥0∞)
      ∂wpProbability G g (n g)
  simp_rw [pants_mixed_factorial_eq_expandedWindowCount_real H _ _ I a hdisg,
    pants_mixed_factorial_eq_expandedWindowCount_ennreal H _ _ I a hdisg]
  exact (pantsWindowCount_lintegral_eq_ofReal_integral H T C MI hg _ hsmall
    (expandedWindows a I) (fun _ => measurableSet_Ioc) hsupport _).symm

end WP.RandomGeometry
