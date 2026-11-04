import WPFormalization.RandomGeometry.PantsFixedOrderAsymptoticsMoments
import WPFormalization.RandomGeometry.PantsOrderedMoments
import WPFormalization.RandomGeometry.PantsMomentAsymptoticsConcentration

/-! Actual fixed-window moments obtained from the proved geometric PS3
identity and the numerical fixed-order window limits. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External Set Filter MeasureTheory
open scoped Topology

lemma pants_scaled_closed_window_subset_cap {ι : Type*} [Fintype ι] (q : ℝ)
    (lo hi : ι → ℝ) (hlo : ∀j,0≤lo j) (horder : ∀j,lo j≤hi j) :
    ∀j, Icc (lo j/Real.sqrt q) (hi j/Real.sqrt q) ⊆
      Icc 0 (pantsScaledWindowCap q hi) := by
  intro j x hx
  have hb : ∀k,0≤hi k := fun k => (hlo k).trans (horder k)
  have hsum : hi j≤1+∑k,hi k := by
    have hh := Finset.single_le_sum (fun k _ => hb k) (Finset.mem_univ j)
    linarith
  exact ⟨(div_nonneg (hlo j) (Real.sqrt_nonneg q)).trans hx.1,
    hx.2.trans (div_le_div_of_nonneg_right hsum (Real.sqrt_nonneg q))⟩

variable {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

include C MI in
/-- The actual ordered pants window moments at the original scale, including
r=0 and all zero-intensity windows. No exact-moment premise is added. -/
lemma pants_fixed_scaled_Icc_moments_of_fast_cusps (r : ℕ) (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin r → ℝ) (hlo : ∀ j, 0 ≤ lo j) (horder : ∀ j, lo j ≤ hi j) :
    Tendsto (fun g => ∫ X : G.Moduli g (n g) (fun _ => 0),
      (pantsWindowCount H X (pantsScaledWindowCap (pantsScale g (n g)) hi)
        (fun j => Icc (lo j/Real.sqrt (pantsScale g (n g)))
          (hi j/Real.sqrt (pantsScale g (n g)))) : ℝ) ∂wpProbability G g (n g))
      atTop (𝓝 (∏ j, ((hi j)^2-(lo j)^2))) := by
  have hn := pants_fast_cusps_tendsto_atTop n hnfast
  have hq := WP.Spectral.pantsScale_tendsto_atTop n hnfast
  have hcap := pants_scaled_window_cap_tendsto_zero _ hq hi
  have hpos : 0 < 2*Real.arsinh 1 := by
    have : 0 < Real.arsinh 1 := Real.arsinh_pos_iff.mpr (by norm_num)
    positivity
  apply (pants_fixed_scaled_windows_of_fast_cusps P r n hnfast lo hi hlo horder).congr'
  filter_upwards [eventually_ge_atTop (2:ℕ),hn.eventually_ge_atTop (2*r),
    hcap.eventually (gt_mem_nhds hpos)] with g hg hng hsmall
  rw [pants_ordered_window_moments_model G H T C MI hg hng _ hsmall _
    (fun _ => measurableSet_Icc) (pants_scaled_closed_window_subset_cap _ lo hi hlo horder)]
  exact dif_pos hng

/-- Positive rescaling preserves pairwise disjoint half-open windows. -/
lemma pants_scaled_Icc_pairwise_disjoint {ι : Type*} (q : ℝ) (hq : 0 < q)
    (lo hi : ι → ℝ) (hdis : Pairwise (fun j k => Disjoint (Icc (lo j) (hi j))
      (Icc (lo k) (hi k)))) :
    Pairwise (fun j k => Disjoint (Icc (lo j/Real.sqrt q) (hi j/Real.sqrt q))
      (Icc (lo k/Real.sqrt q) (hi k/Real.sqrt q))) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro x hxj hxk
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  exact Set.disjoint_left.mp (hdis hjk)
    ⟨(div_le_iff₀ hs).mp hxj.1,(le_div_iff₀ hs).mp hxj.2⟩
    ⟨(div_le_iff₀ hs).mp hxk.1,(le_div_iff₀ hs).mp hxk.2⟩

include C MI in
/-- Genuine mixed factorial moments of the actual pants window counts. Every
finite multiindex is allowed, and zero-width windows retain zero intensity. -/
lemma pants_fixed_mixed_Icc_moments_of_fast_cusps {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : ι → ℝ) (hlo : ∀ j, 0 ≤ lo j) (horder : ∀ j, lo j ≤ hi j)
    (hdis : Pairwise (fun j k => Disjoint (Icc (lo j) (hi j)) (Icc (lo k) (hi k)))) :
    Tendsto (fun g => ∫ X : G.Moduli g (n g) (fun _ => 0),
      (∏ j, ((pantsWindowCount H X
        (pantsMixedScaledWindowCap a (pantsScale g (n g)) hi)
        (fun _ : Fin 1 => Icc (lo j/Real.sqrt (pantsScale g (n g)))
          (hi j/Real.sqrt (pantsScale g (n g))))).descFactorial (a j) : ℝ))
      ∂wpProbability G g (n g)) atTop (𝓝 (∏ j, ((hi j)^2-(lo j)^2)^(a j))) := by
  have hh := pants_fixed_scaled_Icc_moments_of_fast_cusps G H T C MI (∑ j, a j) n hnfast
    (fun i => lo ((mixedSlotsEquiv a).symm i).1)
    (fun i => hi ((mixedSlotsEquiv a).symm i).1)
    (fun i => hlo ((mixedSlotsEquiv a).symm i).1)
    (fun i => horder ((mixedSlotsEquiv a).symm i).1)
  rw [mixedSlots_prod a _ (mixedSlotsEquiv a) (fun j => (hi j)^2-(lo j)^2)] at hh
  apply hh.congr'
  filter_upwards [(WP.Spectral.pantsScale_tendsto_atTop n hnfast).eventually_gt_atTop 0]
    with g hqg
  apply integral_congr_ae
  apply Eventually.of_forall
  intro X
  exact (pants_mixed_factorial_eq_expandedWindowCount_real H X
    (pantsMixedScaledWindowCap a (pantsScale g (n g)) hi)
    (fun j => Icc (lo j/Real.sqrt (pantsScale g (n g)))
      (hi j/Real.sqrt (pantsScale g (n g)))) a
    (pants_scaled_Icc_pairwise_disjoint _ hqg lo hi hdis)).symm

end WP.RandomGeometry
