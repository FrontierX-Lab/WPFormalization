import WPFormalization.RandomGeometry.GeneralPlanarFactorialMomentLimits
import WPFormalization.RandomGeometry.PantsFixedOrderAsymptoticsMoments

/-! Full ordered planar moments at the paper's original q scale. The change
from the coefficient saddle scale q* is proved locally on the exact physical
window integrals, including empty orders and zero-width windows. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory Set Filter
open scoped Topology

lemma generalPlanar_scaled_window_base_scale (P : PsiTheory) (g n r : ℕ)
    (k : Fin r→ℕ) (lo hi : Fin r→ℝ) (hab : ∀i,lo i≤hi i)
    (q q' : ℝ) (hq : 0<q) (hq' : 0<q') :
    generalPlanarStarWindowBase P g n r k (generalPlanarStarScaledWindows r q lo hi)=
      (q'/q)^r*generalPlanarStarWindowBase P g n r k
        (generalPlanarStarScaledWindows r q' lo hi) := by
  unfold generalPlanarStarWindowBase
  rw [general_planar_star_scaled_window_weight r q hq lo hi hab,
    general_planar_star_scaled_window_weight r q' hq' lo hi hab]
  simp only [Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [div_pow]
  field_simp
  ring

lemma generalPlanar_original_windows_subset_effective_cap (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (r : ℕ) (lo hi : Fin r→ℝ) (hlo : ∀i,0≤lo i) (hab : ∀i,lo i≤hi i) :
    ∀ᶠg in atTop,∀i,generalPlanarStarScaledWindows r (pantsScale g (n g)) lo hi i⊆
      Icc 0 ((2*(1+∑i,hi i))/Real.sqrt (primitivePlanarEffectiveScale g (n g))) := by
  have hratio := primitive_planar_scale_ratio_tendsto_one n
    ((pants_fast_cusps_tendsto_atTop n hn).eventually_ge_atTop 2)
  have hq := WP.Spectral.pantsScale_tendsto_atTop n hn
  have hq' := primitive_planar_scale_tendsto_atTop n hn
  filter_upwards [hq.eventually_gt_atTop (0:ℝ),hq'.eventually_gt_atTop (0:ℝ),
    hratio.eventually (gt_mem_nhds (by norm_num : (1:ℝ)<4))] with g hqg hq'g hrat
  have hmul : primitivePlanarEffectiveScale g (n g)≤4*pantsScale g (n g) :=
    ((div_lt_iff₀ hqg).mp hrat).le
  have hs : Real.sqrt (primitivePlanarEffectiveScale g (n g))≤2*Real.sqrt (pantsScale g (n g)) := by
    have h1 := Real.sqrt_nonneg (primitivePlanarEffectiveScale g (n g))
    have h2 := Real.sqrt_nonneg (pantsScale g (n g))
    have hsq1 := Real.sq_sqrt hq'g.le
    have hsq2 := Real.sq_sqrt hqg.le
    nlinarith
  have hB : 0≤1+∑i,hi i := by
    have := Finset.sum_nonneg (fun i (_:i∈(Finset.univ : Finset (Fin r)))=>(hlo i).trans (hab i))
    linarith
  intro i x hx
  have hc := pants_scaled_window_subset_cap (pantsScale g (n g)) lo hi hlo hab i hx
  refine ⟨hc.1,hc.2.trans ?_⟩
  change (1+∑i,hi i)/Real.sqrt (pantsScale g (n g))≤_
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hqg) (Real.sqrt_pos.mpr hq'g)).mpr
  nlinarith

lemma generalPlanar_original_scaled_window_base_limit (P : PsiTheory) (r : ℕ)
    (k : Fin r→ℕ) (hk : ∀i,2≤k i) (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin r→ℝ) (hab : ∀i,lo i≤hi i) (x : ℝ)
    (hxs : Tendsto (fun g=>primitiveSaddleX g (n g)) atTop (𝓝 x)) :
    Tendsto (fun g=>generalPlanarStarWindowBase P g (n g) r k
      (generalPlanarStarScaledWindows r (pantsScale g (n g)) lo hi))
      atTop (𝓝 (generalPlanarStarWeight P r k lo hi x)) := by
  have hninf := pants_fast_cusps_tendsto_atTop n hn
  have hbase := (general_planar_star_base_asymptotic_fast P r k lo hi hk n hn).add
    ((general_planar_star_weight_continuous P r k lo hi).tendsto x |>.comp hxs)
  simp only [Function.comp_def,sub_add_cancel,zero_add] at hbase
  have hratio := (primitive_planar_scale_ratio_tendsto_one n (hninf.eventually_ge_atTop 2)).pow r
  have ht := hratio.mul hbase
  simp only [one_pow,one_mul] at ht
  apply ht.congr'
  filter_upwards [(WP.Spectral.pantsScale_tendsto_atTop n hn).eventually_gt_atTop (0:ℝ),
    (primitive_planar_scale_tendsto_atTop n hn).eventually_gt_atTop (0:ℝ),
    hninf.eventually_ge_atTop (∑i,k i)] with g hq hq' hng
  rw [generalPlanar_scaled_window_base_scale P g (n g) r k lo hi hab _ _ hq hq',
    general_planar_star_scaled_window_base_identity P g (n g) r k hk hng lo hi hab hq']

lemma generalPlanar_original_scaled_window_cut_limit (P : PsiTheory) (r : ℕ)
    (k : Fin r→ℕ) (hk : ∀i,2≤k i) (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin r→ℝ) (hlo : ∀i,0≤lo i) (hab : ∀i,lo i≤hi i) (x : ℝ)
    (hxs : Tendsto (fun g=>primitiveSaddleX g (n g)) atTop (𝓝 x)) :
    Tendsto (fun g=>generalPlanarStarWindowCut P g (n g) r k
      (generalPlanarStarScaledWindows r (pantsScale g (n g)) lo hi))
      atTop (𝓝 (generalPlanarStarWeight P r k lo hi x)) := by
  have hb := generalPlanar_original_scaled_window_base_limit P r k hk n hn lo hi hab x hxs
  have hdiff := general_planar_star_window_cut_difference P r k hk n
    (pants_fast_cusps_tendsto_atTop n hn)
    (fun g=>generalPlanarStarScaledWindows r (pantsScale g (n g)) lo hi)
    (fun g=>pantsScaledWindowCap (pantsScale g (n g)) hi)
    (pants_scaled_window_cap_tendsto_zero _ (WP.Spectral.pantsScale_tendsto_atTop n hn) hi)
    (Eventually.of_forall (fun _ _=>measurableSet_Ioc))
    (Eventually.of_forall (fun g=>pants_scaled_window_subset_cap _ lo hi hlo hab))
    hb.norm.isBoundedUnder_le
  have hh := hdiff.add hb
  simpa only [zero_add,sub_add_cancel] using hh

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

include C MI in
theorem generalPlanar_original_scaled_ordered_moment_limit (r : ℕ)
    (k : Fin r→ℕ) (hk : ∀i,2≤k i) (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin r→ℝ) (hlo : ∀i,0≤lo i) (hab : ∀i,lo i≤hi i) (x : ℝ)
    (hxs : Tendsto (fun g=>primitiveSaddleX g (n g)) atTop (𝓝 x)) :
    Tendsto (fun g=>∫X : G.Moduli g (n g) (fun _=>0),
      (generalPlanarWindowCount H X k (pantsScaledWindowCap (pantsScale g (n g)) hi)
        (generalPlanarStarScaledWindows r (pantsScale g (n g)) lo hi):ℝ)∂wpProbability G g (n g))
      atTop (𝓝 (generalPlanarStarWeight P r k lo hi x)) := by
  let I := fun g=>generalPlanarStarScaledWindows r (pantsScale g (n g)) lo hi
  have hB : 0≤2*(1+∑i,hi i) := by
    have := Finset.sum_nonneg (fun i (_:i∈(Finset.univ : Finset (Fin r)))=>(hlo i).trans (hab i))
    linarith
  have hrem := generalPlanarRemainder_moment_tendsto_zero T C MI r k n hn _ hB I
    (fun _ _=>measurableSet_Ioc) (generalPlanar_original_windows_subset_effective_cap n hn r lo hi hlo hab)
  have hstar := generalPlanar_original_scaled_window_cut_limit P r k hk n hn lo hi hlo hab x hxs
  have hh := hstar.add hrem
  simp only [add_zero] at hh
  apply hh.congr'
  have hcollar : 0<2*Real.arsinh 1 := mul_pos (by norm_num) (Real.arsinh_pos_iff.mpr (by norm_num))
  filter_upwards [eventually_ge_atTop (3:ℕ),
    (pants_scaled_window_cap_tendsto_zero _ (WP.Spectral.pantsScale_tendsto_atTop n hn) hi).eventually
      (gt_mem_nhds hcollar)] with g hg hsmall
  exact (generalPlanar_actual_moment_decomposition H T C MI (g:=g) (n:=n g) (by omega) k hk
    (by intro he;cases Prod.mk.inj he;omega) _ hsmall (I g) (fun _=>measurableSet_Ioc)
    (pants_scaled_window_subset_cap _ lo hi hlo hab)).symm

end WP.RandomGeometry
