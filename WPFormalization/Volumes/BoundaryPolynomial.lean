import WPFormalization.Statements.BoundaryDefinitions
import WPFormalization.Analysis.BoundaryFactorBasic
import WPFormalization.Volumes.OriginSaddleMatching
import WPFormalization.Marked.SingleMarkingProfile
import WPFormalization.Marked.UnmarkedReduction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
noncomputable section
namespace WP
open Set Filter
open scoped Topology
lemma mem_degreeTuples_iff (g n : ℕ) (d : Fin n → ℕ) :
    d ∈ degreeTuples g n ↔ ∑ i, d i ≤ dimension g n := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨fun i => ⟨d i, ?_⟩, Finset.mem_univ _, rfl⟩, h⟩
    exact Nat.lt_succ_of_le ((Finset.single_le_sum (fun i _ => Nat.zero_le (d i)) (Finset.mem_univ _)).trans h)

lemma mixedBracket_eq_scaled_normalized_zero (P : PsiTheory) (g : ℕ) (d : List ℕ) :
    mixedBracket P g d = (4 : ℝ)^(dimension g d.length) * normalized P g d 0 := by
  by_cases hd : d.sum ≤ dimension g d.length
  · simp only [mixedBracket, normalized, ne_of_lt y₀_pos, ite_false, a_zero,
      one_pow, one_mul, r_zero_parameter]
    have he : (2*Real.pi^2:ℝ)^(deficit g d) =
        (4:ℝ)^(deficit g d)*(Real.pi^2/2:ℝ)^(deficit g d) := by
      rw [← mul_pow]
      congr 1
      ring
    rw [he]
    have hn : dimension g d.length = d.sum + deficit g d := by
      unfold deficit
      omega
    rw [hn,pow_add]
    ring
  · have hz : shifted P g d 0 = 0 := by simp [shifted, hd]
    simp [mixedBracket, normalized, ne_of_lt y₀_pos, hz]

lemma mixedBracket_div_volumeModel_eq_profile (P : PsiTheory) (g : ℕ) (d : List ℕ) :
    mixedBracket P g d / volumeModel P g d.length = profile P g d 0 := by
  rw [mixedBracket_eq_scaled_normalized_zero]
  have hv : volumeModel P g d.length =
      (4:ℝ)^(dimension g d.length)*normalized P g (List.replicate d.length 0) 0 := by
    simpa only [volumeModel,List.length_replicate] using
      mixedBracket_eq_scaled_normalized_zero P g (List.replicate d.length 0)
  rw [hv,mul_div_mul_left _ _ (by positivity : (4:ℝ)^(dimension g d.length) ≠ 0)]
  rfl

def boundaryDegreeWeight (n : ℕ) (L : Fin n → ℝ) (d : Fin n → ℕ) : ℝ :=
    ∏ i, L i^(2*d i)/((4:ℝ)^(d i)*(2*d i+1).factorial)

lemma boundaryVolumeModel_div_eq_profile_sum (P : PsiTheory) (g n : ℕ) (L : Fin n → ℝ) :
    boundaryVolumeModel P g n L / volumeModel P g n =
      ∑ d ∈ degreeTuples g n, profile P g (List.ofFn d) 0 * boundaryDegreeWeight n L d := by
  unfold boundaryVolumeModel
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have he := mixedBracket_div_volumeModel_eq_profile P g (List.ofFn d)
  simp only [List.length_ofFn] at he
  change mixedBracket P g (List.ofFn d) * boundaryDegreeWeight n L d / volumeModel P g n = _
  rw [show mixedBracket P g (List.ofFn d) * boundaryDegreeWeight n L d / volumeModel P g n =
    (mixedBracket P g (List.ofFn d) / volumeModel P g n)*boundaryDegreeWeight n L d by ring,he]

lemma profile_ofFn_zero_of_not_mem_degreeTuples (P : PsiTheory) (g n : ℕ)
    (d : Fin n → ℕ) (hd : d ∉ degreeTuples g n) : profile P g (List.ofFn d) 0 = 0 := by
  have he : dimension g n < ∑ i, d i := lt_of_not_ge (mt (mem_degreeTuples_iff g n d).mpr hd)
  unfold profile
  rw [normalized_excess P g (List.ofFn d) 0 (by simpa only [List.length_ofFn,List.sum_ofFn] using he),zero_div]

lemma boundaryVolumeModel_div_eq_profile_tsum (P : PsiTheory) (g n : ℕ) (L : Fin n → ℝ) :
    boundaryVolumeModel P g n L / volumeModel P g n =
      ∑' d : Fin n → ℕ, profile P g (List.ofFn d) 0 * boundaryDegreeWeight n L d := by
  classical
  rw [boundaryVolumeModel_div_eq_profile_sum]
  symm
  apply tsum_eq_sum
  intro d hd
  rw [profile_ofFn_zero_of_not_mem_degreeTuples P g n d hd,zero_mul]
end WP
namespace WP
open Set Filter
open scoped Topology
lemma summable_fin_tuple_product (n : ℕ) (f : Fin n → ℕ → ℝ)
    (hf : ∀ i, Summable (f i)) (hpos : ∀ i k, 0 ≤ f i k) :
    Summable (fun d : Fin n → ℕ => ∏ i, f i (d i)) := by
  induction n with
  | zero => exact (hasSum_fintype _).summable
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n+1) => ℕ)
    have ht := ih (fun i => f i.succ) (fun i => hf i.succ) (fun i => hpos i.succ)
    have hs := (hf 0).mul_of_nonneg ht (hpos 0) (fun d => Finset.prod_nonneg (fun i _ => hpos i.succ (d i)))
    rw [← e.summable_iff]
    convert hs using 1
    ext d
    simp [e,Fin.prod_univ_succ]

lemma tsum_fin_tuple_product (n : ℕ) (f : Fin n → ℕ → ℝ)
    (hf : ∀ i, Summable (f i)) (hpos : ∀ i k, 0 ≤ f i k) :
    (∑' d : Fin n → ℕ, ∏ i, f i (d i)) = ∏ i, ∑' k, f i k := by
  induction n with
  | zero => simp
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n+1) => ℕ)
    rw [← e.tsum_eq]
    have ht := summable_fin_tuple_product n (fun i => f i.succ) (fun i => hf i.succ) (fun i => hpos i.succ)
    have hs := (hf 0).mul_of_nonneg ht (hpos 0) (fun d => Finset.prod_nonneg (fun i _ => hpos i.succ (d i)))
    have he : (fun d : ℕ × (Fin n → ℕ) => ∏ i, f i (e d i)) =
        fun d => f 0 d.1 * ∏ i, f i.succ (d.2 i) := by
      funext d
      simp [e,Fin.prod_univ_succ]
    rw [he,← (hf 0).tsum_mul_tsum ht hs, ih _ (fun i => hf i.succ) (fun i => hpos i.succ),Fin.prod_univ_succ]
end WP
namespace WP
open Set Filter
open scoped Topology

def boundaryLengthCoefficient (L : ℝ) (k : ℕ) : ℝ := L^(2*k)/((4:ℝ)^k*(2*k+1).factorial)
lemma boundaryLengthCoefficient_nonneg (L : ℝ) (k : ℕ) : 0 ≤ boundaryLengthCoefficient L k := by
  unfold boundaryLengthCoefficient
  apply div_nonneg
  · simpa only [← pow_mul] using pow_nonneg (sq_nonneg L) k
  · positivity
lemma boundaryLengthCoefficient_zero (k : ℕ) : boundaryLengthCoefficient 0 k = if k=0 then 1 else 0 := by
  by_cases hk : k=0
  · simp [boundaryLengthCoefficient,hk]
  · simp [boundaryLengthCoefficient,hk]
lemma boundaryLengthCoefficient_eq (L : ℝ) (k : ℕ) :
    boundaryLengthCoefficient L k = (L/2)^(2*k)/(2*k+1).factorial := by
  unfold boundaryLengthCoefficient
  rw [div_pow]
  have he : (2:ℝ)^(2*k) = 4^k := by rw [pow_mul];norm_num
  rw [he]
  ring
lemma boundaryLengthCoefficient_hasSum (L : ℝ) :
    HasSum (boundaryLengthCoefficient L) (boundaryFactor 0 L) := by
  rw [(boundary_factor_endpoints L).1]
  by_cases hL : L=0
  · subst L
    rw [if_pos rfl]
    convert (hasSum_ite_eq 0 (1:ℝ)) using 1
    ext k
    exact boundaryLengthCoefficient_zero k
  · rw [if_neg hL]
    have hs := (Real.hasSum_sinh (L/2)).div_const (L/2)
    convert hs using 1
    ext k
    rw [boundaryLengthCoefficient_eq,pow_succ]
    have hn : L/2 ≠ 0 := div_ne_zero hL (by norm_num)
    field_simp

lemma boundaryDegreeWeight_nonneg (n : ℕ) (L : Fin n → ℝ) (d : Fin n → ℕ) :
    0 ≤ boundaryDegreeWeight n L d := by
  apply Finset.prod_nonneg
  intro i _
  exact boundaryLengthCoefficient_nonneg (L i) (d i)

lemma boundaryDegreeWeight_summable (n : ℕ) (L : Fin n → ℝ) : Summable (boundaryDegreeWeight n L) := by
  exact summable_fin_tuple_product n (fun i => boundaryLengthCoefficient (L i))
    (fun i => (boundaryLengthCoefficient_hasSum (L i)).summable)
    (fun i => boundaryLengthCoefficient_nonneg (L i))

lemma boundaryDegreeWeight_tsum (n : ℕ) (L : Fin n → ℝ) :
    (∑' d, boundaryDegreeWeight n L d) = ∏ i, boundaryFactor 0 (L i) := by
  have he := tsum_fin_tuple_product n (fun i => boundaryLengthCoefficient (L i))
    (fun i => (boundaryLengthCoefficient_hasSum (L i)).summable)
    (fun i => boundaryLengthCoefficient_nonneg (L i))
  change (∑' d, boundaryDegreeWeight n L d) = ∏ i, ∑' k, boundaryLengthCoefficient (L i) k at he
  rw [he]
  apply Finset.prod_congr rfl
  intro i _
  exact (boundaryLengthCoefficient_hasSum (L i)).tsum_eq
end WP
namespace WP
open Set Filter
open scoped Topology
lemma boundaryDegreeWeight_mono (n : ℕ) (L U : Fin n → ℝ)
    (hL : ∀ i, 0 ≤ L i) (hLU : ∀ i, L i ≤ U i) (d : Fin n → ℕ) :
    boundaryDegreeWeight n L d ≤ boundaryDegreeWeight n U d := by
  apply Finset.prod_le_prod₀
  · intro i _
    exact boundaryLengthCoefficient_nonneg _ _
  · intro i _
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ (hL i) (hLU i) _

lemma profile_zero_loss_tendsto (P : PsiTheory) (d : List ℕ) (hn : 1 ≤ d.length) :
    Tendsto (fun g : ℕ => 1-profile P g d 0) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := quadratic_profile_all_markings_proof P d.length hn
  have hlim := tendsto_const_div_atTop_nhds_zero_nat (C*(d.sum:ℝ)*(d.sum+1))
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
    exact (hbound g hg d rfl 0 ⟨le_rfl,y₀_pos.le⟩).1
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
    exact (hbound g hg d rfl 0 ⟨le_rfl,y₀_pos.le⟩).2

lemma profile_zero_bounds (P : PsiTheory) (g n : ℕ) (hg : 1 ≤ g) (hn : 1 ≤ n) (d : Fin n → ℕ) :
    0 ≤ profile P g (List.ofFn d) 0 ∧ profile P g (List.ofFn d) 0 ≤ 1 := by
  have hs : Stable g (List.ofFn d).length := by simp only [List.length_ofFn]; unfold Stable;omega
  have hn' : 0 < (List.ofFn d).length := by simpa only [List.length_ofFn] using (show 0 < n by omega)
  exact (profile_monotone P g (List.ofFn d) hs 0 hn' 0 ⟨le_rfl,y₀_pos.le⟩).2

def boundaryProfileLoss (P : PsiTheory) (g n : ℕ) (L : Fin n → ℝ) (d : Fin n → ℕ) : ℝ :=
    (1-profile P g (List.ofFn d) 0)*boundaryDegreeWeight n L d

lemma boundaryProfileLoss_tsum_tendsto (P : PsiTheory) (n : ℕ) (hn : 1 ≤ n) (L : Fin n → ℝ) :
    Tendsto (fun g => ∑' d, boundaryProfileLoss P g n L d) atTop (𝓝 0) := by
  have hlim (d : Fin n → ℕ) : Tendsto (fun g => boundaryProfileLoss P g n L d) atTop (𝓝 0) := by
    simpa only [zero_mul,boundaryProfileLoss] using
      (profile_zero_loss_tendsto P (List.ofFn d) (by simpa using hn)).mul_const (boundaryDegreeWeight n L d)
  have h := tendsto_tsum_of_dominated_convergence (boundaryDegreeWeight_summable n L) hlim ?_
  · simpa only [tsum_zero] using h
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg d
    have hp := profile_zero_bounds P g n hg hn d
    have hw := boundaryDegreeWeight_nonneg n L d
    rw [boundaryProfileLoss,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by linarith) hw)]
    exact mul_le_of_le_one_left hw (by linarith)
end WP
namespace WP
open Set Filter
open scoped Topology
lemma boundaryProfileLoss_summable (P : PsiTheory) (g n : ℕ) (hg : 1 ≤ g) (hn : 1 ≤ n)
    (L : Fin n → ℝ) : Summable (boundaryProfileLoss P g n L) := by
  apply (boundaryDegreeWeight_summable n L).of_nonneg_of_le
  · intro d
    have hp := profile_zero_bounds P g n hg hn d
    exact mul_nonneg (by linarith) (boundaryDegreeWeight_nonneg n L d)
  · intro d
    have hp := profile_zero_bounds P g n hg hn d
    exact mul_le_of_le_one_left (boundaryDegreeWeight_nonneg n L d) (by linarith)
lemma boundaryProfileLoss_tsum_eq (P : PsiTheory) (g n : ℕ) (hg : 1 ≤ g) (hn : 1 ≤ n)
    (L : Fin n → ℝ) :
    (∑' d, boundaryProfileLoss P g n L d) =
      (∏ i, boundaryFactor 0 (L i))-boundaryVolumeModel P g n L/volumeModel P g n := by
  have hp : Summable (fun d : Fin n → ℕ => profile P g (List.ofFn d) 0 * boundaryDegreeWeight n L d) := by
    apply (boundaryDegreeWeight_summable n L).of_nonneg_of_le
    · intro d
      exact mul_nonneg (profile_zero_bounds P g n hg hn d).1 (boundaryDegreeWeight_nonneg n L d)
    · intro d
      exact mul_le_of_le_one_left (boundaryDegreeWeight_nonneg n L d) (profile_zero_bounds P g n hg hn d).2
  rw [boundaryVolumeModel_div_eq_profile_tsum,← boundaryDegreeWeight_tsum,← (boundaryDegreeWeight_summable n L).tsum_sub hp]
  apply tsum_congr
  intro d
  unfold boundaryProfileLoss
  ring

lemma boundaryVolumeModel_profile_error_bound (P : PsiTheory) (g n : ℕ) (hg : 1 ≤ g) (hn : 1 ≤ n)
    (L U : Fin n → ℝ) (hL : ∀ i, 0 ≤ L i) (hLU : ∀ i, L i ≤ U i) :
    |boundaryVolumeModel P g n L/volumeModel P g n-∏ i, boundaryFactor 0 (L i)| ≤
      ∑' d, boundaryProfileLoss P g n U d := by
  have he := boundaryProfileLoss_tsum_eq P g n hg hn L
  have hpos : 0 ≤ ∑' d, boundaryProfileLoss P g n L d := by
    apply tsum_nonneg
    intro d
    have hp := profile_zero_bounds P g n hg hn d
    exact mul_nonneg (by linarith) (boundaryDegreeWeight_nonneg n L d)
  rw [abs_sub_comm,← he,abs_of_nonneg hpos]
  apply (boundaryProfileLoss_summable P g n hg hn L).tsum_le_tsum _ (boundaryProfileLoss_summable P g n hg hn U)
  intro d
  have hp := profile_zero_bounds P g n hg hn d
  exact mul_le_mul_of_nonneg_left (boundaryDegreeWeight_mono n L U hL hLU d) (by linarith)

lemma fixed_cusp_boundary_zero_parameter (P : PsiTheory) (n : ℕ) (hn : 1 ≤ n) (L0 : ℝ) (hL0 : 0 ≤ L0) :
    ∀ ε : ℝ, 0 < ε → ∃ G : ℕ, ∀ g ≥ G, ∀ L : Fin n → ℝ,
      (∀ i, 0 ≤ L i) → (∀ i, L i ≤ L0) →
      |boundaryVolumeModel P g n L /
        (volumeModel P g n * ∏ i, boundaryFactor 0 (L i))-1| ≤ ε := by
  intro ε hε
  have ht := boundaryProfileLoss_tsum_tendsto P n hn (fun _ => L0)
  obtain ⟨G,hG⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  refine ⟨max G 1,?_⟩
  intro g hg L hL hLU
  have hg1 : 1 ≤ g := (le_max_right _ _).trans hg
  have he := boundaryVolumeModel_profile_error_bound P g n hg1 hn L (fun _ => L0) hL hLU
  have hsmall := hG g ((le_max_left _ _).trans hg)
  have hB : 1 ≤ ∏ i, boundaryFactor 0 (L i) := by
    exact Finset.one_le_prod₀ (fun i _ => one_le_boundaryFactor 0 (L i))
  have hBp : 0 < ∏ i, boundaryFactor 0 (L i) := zero_lt_one.trans_le hB
  rw [div_mul_eq_div_div,div_sub_one hBp.ne',abs_div,abs_of_pos hBp]
  exact (div_le_self (abs_nonneg _) hB).trans (he.trans hsmall.le)
end WP
namespace WP
open Set Filter
open scoped Topology
set_option maxHeartbeats 100000 in
lemma boundaryFactor_product_fixed_cusp_uniform (n : ℕ) (L0 : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ G : ℕ, ∀ g ≥ G, ∀ L : Fin n → ℝ,
      (∀ i, 0 ≤ L i) → (∀ i, L i ≤ L0) →
      |(∏ i, boundaryFactor (densityY ((n:ℝ)/(g:ℝ))) (L i))-
        (∏ i, boundaryFactor 0 (L i))| < ε := by
  let F : Icc (0:ℝ) y₀ → (Fin n → Icc (0:ℝ) L0) → ℝ := fun Y L =>
    ∏ i, boundaryFactor Y (L i)
  have hF : Continuous (Function.uncurry F) := by
    change Continuous (fun q : Icc (0:ℝ) y₀ × (Fin n → Icc (0:ℝ) L0) =>
      ∏ i, boundaryFactor (q.1:ℝ) (q.2 i:ℝ))
    apply continuous_finsetProd
    intro i _
    have hi : Continuous (fun q : Icc (0:ℝ) y₀ × (Fin n → Icc (0:ℝ) L0) => (q.2 i:ℝ)) :=
      continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)
    exact Continuous.comp
      (g := fun r : (Icc (0:ℝ) y₀) × ℝ => boundaryFactor (r.1:ℝ) r.2)
      (f := fun q : (Icc (0:ℝ) y₀) × (Fin n → Icc (0:ℝ) L0) => (q.1,(q.2 i:ℝ)))
      boundaryFactor_joint_continuous (continuous_fst.prodMk hi)
  let Y0 : Icc (0:ℝ) y₀ := ⟨0,le_rfl,y₀_pos.le⟩
  have hu := Continuous.tendstoUniformly F hF Y0
  have hy : Tendsto (fun g : ℕ => densityY ((n:ℝ)/(g:ℝ))) atTop (𝓝 0) := by
    apply Analysis.densityY_tendsto_zero_right.comp
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_const_div_atTop_nhds_zero_nat (n:ℝ),Filter.Eventually.of_forall (by intro g; change 0 ≤ (n:ℝ)/(g:ℝ); positivity)⟩
  have hs : ∀ g : ℕ, densityY ((n:ℝ)/(g:ℝ)) ∈ Icc (0:ℝ) y₀ := by
    intro g
    exact ⟨(Analysis.densityY_spec _ (by positivity)).1.1,(Analysis.densityY_spec _ (by positivity)).1.2.le⟩
  have ht : Tendsto (fun g : ℕ => (⟨densityY ((n:ℝ)/(g:ℝ)),hs g⟩ : Icc (0:ℝ) y₀)) atTop (𝓝 Y0) :=
    tendsto_subtype_rng.mpr hy
  intro ε hε
  obtain ⟨G,hG⟩ := eventually_atTop.mp (ht.eventually ((Metric.tendstoUniformly_iff.mp hu) ε hε))
  refine ⟨G,?_⟩
  intro g hg L hL hLU
  have he := hG g hg (fun i => (⟨L i,hL i,hLU i⟩ : Icc (0:ℝ) L0))
  simpa only [F,Y0,dist_eq_norm,Real.norm_eq_abs,abs_sub_comm] using he

lemma fixed_cusp_boundary_estimate (P : PsiTheory) (n : ℕ) (hn : 1 ≤ n) (L0 : ℝ) (hL0 : 0 ≤ L0) :
    ∀ ε : ℝ, 0 < ε → ∃ G : ℕ, ∀ g ≥ G, ∀ L : Fin n → ℝ,
      (∀ i, 0 ≤ L i) → (∀ i, L i ≤ L0) →
      |boundaryVolumeModel P g n L /
        (volumeModel P g n * ∏ i, boundaryFactor (densityY ((n:ℝ)/(g:ℝ))) (L i))-1| ≤ ε := by
  intro ε hε
  have ht := boundaryProfileLoss_tsum_tendsto P n hn (fun _ => L0)
  obtain ⟨G1,hG1⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (half_pos hε)))
  obtain ⟨G2,hG2⟩ := boundaryFactor_product_fixed_cusp_uniform n L0 (ε/2) (half_pos hε)
  refine ⟨max 1 (max G1 G2),?_⟩
  intro g hg L hL hLU
  have hg1 : 1 ≤ g := (le_max_left _ _).trans hg
  have hgG1 : G1 ≤ g := (le_max_left _ _).trans ((le_max_right _ _).trans hg)
  have hgG2 : G2 ≤ g := (le_max_right _ _).trans ((le_max_right _ _).trans hg)
  have he1 := boundaryVolumeModel_profile_error_bound P g n hg1 hn L (fun _ => L0) hL hLU
  have he2 := hG2 g hgG2 L hL hLU
  have he3 := hG1 g hgG1
  have hB : 1 ≤ ∏ i, boundaryFactor (densityY ((n:ℝ)/(g:ℝ))) (L i) :=
    Finset.one_le_prod₀ (fun i _ => one_le_boundaryFactor _ _)
  have hBp := zero_lt_one.trans_le hB
  rw [div_mul_eq_div_div,div_sub_one hBp.ne',abs_div,abs_of_pos hBp]
  apply (div_le_self (abs_nonneg _) hB).trans
  have htri := abs_sub_le (boundaryVolumeModel P g n L/volumeModel P g n)
    (∏ i, boundaryFactor 0 (L i)) (∏ i, boundaryFactor (densityY ((n:ℝ)/(g:ℝ))) (L i))
  rw [abs_sub_comm (∏ i, boundaryFactor 0 (L i))] at htri
  linarith
end WP
namespace WP
open Set Filter
open scoped Topology
lemma bounded_cusp_count_boundary_estimate (P : PsiTheory) (N : ℕ) (L0 : ℝ) (hL0 : 0 ≤ L0) :
    ∀ ε : ℝ, 0 < ε → ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ, 1 ≤ n → n ≤ N →
      ∀ L : Fin n → ℝ, (∀ i, 0 ≤ L i) → (∀ i, L i ≤ L0) →
      |boundaryVolumeModel P g n L /
        (volumeModel P g n * ∏ i, boundaryFactor (densityY ((n:ℝ)/(g:ℝ))) (L i))-1| ≤ ε := by
  classical
  intro ε hε
  have hs (n : ℕ) : ∃ G : ℕ, ∀ g ≥ G, 1 ≤ n →
      ∀ L : Fin n → ℝ, (∀ i, 0 ≤ L i) → (∀ i, L i ≤ L0) →
      |boundaryVolumeModel P g n L /
        (volumeModel P g n * ∏ i, boundaryFactor (densityY ((n:ℝ)/(g:ℝ))) (L i))-1| ≤ ε := by
    by_cases hn : 1 ≤ n
    · obtain ⟨G,hG⟩ := fixed_cusp_boundary_estimate P n hn L0 hL0 ε hε
      exact ⟨G,fun g hg _ => hG g hg⟩
    · exact ⟨0,fun g hg hng => (hn hng).elim⟩
  choose G hG using hs
  refine ⟨(Finset.range (N+1)).sup G,?_⟩
  intro g hg n hn hnN L hL hLU
  apply hG n g _ hn L hL hLU
  exact (Finset.le_sup (f:=G) (Finset.mem_range.mpr (by omega))).trans hg
end WP
