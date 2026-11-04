import WPFormalization.Tight.SeparatingCoefficientRates
import WPFormalization.Tight.SeparatingPhysicalKernel
import WPFormalization.Tight.SeparatingGenusSum
import WPFormalization.RandomGeometry.PrimitiveCoefficientRatio
import WPFormalization.Spectral.PantsScaleGrowth

/-! The actual positive-genus separating sum in (14.15).
The coefficient identity retains both endpoint cusp allocations and genus one.
The proved F.3 genus-family and coefficient-transfer estimates give a uniform
O(1/g) bound; the bounded-cusp branch uses the genuine Poisson denominator.
A diagonal argument combines the two branches without a density restriction.
The final scalar envelope vanishes on the original primitive short window. -/
noncomputable section
namespace WP.RandomGeometry
open Set Filter
open scoped Topology BigOperators

/-- The exact ordered positive-genus sum in (14.15), with every cusp allocation. -/
def primitiveSeparatingVolumeSum (P : PsiTheory) (g n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (g-1), ∑ k ∈ Finset.range (n+1),
    (n.choose k : ℝ)*volumeModel P (i+1) (k+1)*
      volumeModel P (g-(i+1)) (n-k+1)/volumeModel P g n

def primitiveSeparatingTerm (P : PsiTheory) (g i : ℕ) (z : ℂ) : ℂ :=
  iteratedDeriv 1 (Phi P (i+1)) z * iteratedDeriv 1 (Phi P (g-(i+1))) z

def primitiveSeparatingSeries (P : PsiTheory) (g : ℕ) (z : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (g-1), primitiveSeparatingTerm P g i z

lemma primitive_separating_term_coefficient (P : PsiTheory) (g i n : ℕ) :
    realCoeff (primitiveSeparatingTerm P g i) n =
      ∑ k ∈ Finset.range (n+1),
        realCoeff (iteratedDeriv 1 (Phi P (i+1))) k *
          realCoeff (iteratedDeriv 1 (Phi P (g-(i+1)))) (n-k) := by
  have hz : ‖(0 : ℂ)‖ < xCritical := by simpa using Analysis.xCritical_pos_parameter
  have ha (j : ℕ) : AnalyticAt ℂ (iteratedDeriv 1 (Phi P j)) 0 := by
    simpa only [iteratedDeriv_eq_iterate] using (Phi_analyticAt_open_disk P j 0 hz).iterated_deriv 1
  have hr (j : ℕ) : Analysis.RealCoefficients (iteratedDeriv 1 (Phi P j)) := by
    intro n
    unfold coeff
    rw [Analysis.iteratedDeriv_iteratedDeriv_eq,PositiveConvolution.Phi_iteratedDeriv_zero]
    norm_cast
  unfold primitiveSeparatingTerm
  rw [←Analysis.realTaylor_coeff,Analysis.realTaylor_mul (ha _) (ha _) (hr _) (hr _),
    PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Analysis.realTaylor_coeff]

lemma primitive_separating_term_volume_identity (P : PsiTheory) (g i n : ℕ)
    (hg : 2 ≤ g) (hi : i < g-1) :
    (∑ k ∈ Finset.range (n+1), (n.choose k : ℝ)*volumeModel P (i+1) (k+1)*
      volumeModel P (g-(i+1)) (n-k+1)/volumeModel P g n) =
      (1/(2*Real.pi^2)) *
        (realCoeff (primitiveSeparatingTerm P g i) n/realCoeff (Phi P g) n) := by
  rw [primitive_separating_term_coefficient,Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  have hdim : dimension (i+1) (k+1)+dimension (g-(i+1)) (n-k+1)+1 = dimension g n := by
    unfold dimension
    omega
  have hpow : (2*Real.pi^2)^(dimension g n) =
      (2*Real.pi^2)^(dimension (i+1) (k+1))*
        (2*Real.pi^2)^(dimension (g-(i+1)) (n-k+1))*(2*Real.pi^2) := by
    rw [←hdim,pow_add,pow_add,pow_one]
  rw [marked_one_realCoeff_volume,marked_one_realCoeff_volume,
    TightSeparating.unmarked_realCoeff_volume,Nat.cast_choose ℝ hkn,hpow]
  have hP : 2*Real.pi^2 ≠ 0 := by positivity
  have hf (m : ℕ) : (m.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hP,hf]


lemma primitive_separating_volume_coefficient_identity (P : PsiTheory) (g n : ℕ)
    (hg : 2 ≤ g) :
    primitiveSeparatingVolumeSum P g n =
      (1/(2*Real.pi^2)) *
        (∑ i ∈ Finset.range (g-1),
          realCoeff (primitiveSeparatingTerm P g i) n/realCoeff (Phi P g) n) := by
  unfold primitiveSeparatingVolumeSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i hi =>
    primitive_separating_term_volume_identity P g i n hg (Finset.mem_range.mp hi))

lemma primitive_tight_zero_lengths (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p)
    (hs : Stable g p) (Y : ℝ) (hY : Y ∈ Ico (0:ℝ) y₀) :
    tightShiftedPolynomial P g p Y (fun _ => 0) = shifted P g (List.replicate p 0) Y := by
  have hf : 0 < shifted P g (List.replicate p 0) Y :=
    shifted_zero_pos_nonempty P g p hp hs Y hY
  have hb := tightShiftedPolynomial_bounds P g p hp hs Y hY (fun _ => 0)
  simp only [mul_zero,boundaryFactor_zero_length,Finset.prod_const_one] at hb
  have hquot : tightShiftedPolynomial P g p Y (fun _ => 0)/
      shifted P g (List.replicate p 0) Y = 1 := le_antisymm hb.2 hb.1
  exact (div_eq_one_iff_eq hf.ne').mp hquot

lemma primitive_moment_zero_lengths (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p)
    (hs : Stable g p) (z : ℂ) (hz : ‖z‖ < xCritical) :
    TightMoments.momentTightG P g p (fun _ => 0) z = iteratedDeriv p (Phi P g) z := by
  have hf : AnalyticOnNhd ℂ (TightMoments.momentTightG P g p (fun _ => 0))
      (Metric.ball 0 xCritical) := by
    intro w hw
    exact TightMoments.momentTightG_analyticAt P g p _ w
      (by simpa only [Metric.mem_ball,dist_zero_right] using hw)
  have hd : AnalyticOnNhd ℂ (iteratedDeriv p (Phi P g)) (Metric.ball 0 xCritical) := by
    intro w hw
    simpa only [iteratedDeriv_eq_iterate] using
      (Phi_analyticAt_open_disk P g w
        (by simpa only [Metric.mem_ball,dist_zero_right] using hw)).iterated_deriv p
  have hc : xCritical/2 ∈ Ioo (0:ℝ) xCritical :=
    ⟨half_pos Analysis.xCritical_pos_parameter,half_lt_self Analysis.xCritical_pos_parameter⟩
  have hmem : ((xCritical/2:ℝ):ℂ) ∈ Metric.ball 0 xCritical := by
    simpa only [Metric.mem_ball,dist_zero_right,Complex.norm_of_nonneg hc.1.le] using hc.2
  have he : EqOn (TightMoments.momentTightG P g p (fun _ => 0))
      (iteratedDeriv p (Phi P g)) (Metric.ball 0 xCritical) := by
    apply Analysis.complex_identity_of_real_germ _ _ _ (xCritical/2) hf hd
      (convex_ball (0:ℂ) xCritical).isPreconnected hmem
    filter_upwards [isOpen_Ioo.mem_nhds hc] with x hx
    rw [TightMoments.momentTightG_ofReal P g p _ x ⟨hx.1.le,hx.2⟩,
      primitive_tight_zero_lengths P g p hp hs _ (inverseY_branch x ⟨hx.1.le,hx.2⟩).1,
      PositiveConvolution.Phi_iteratedDeriv_ofReal P g p hs x ⟨hx.1.le,hx.2⟩]
  exact he (by simpa only [Metric.mem_ball,dist_zero_right] using hz)

def primitiveSeparatingGenera (g i : ℕ) : Fin 2 → ℕ := ![i+1,g-(i+1)]

lemma primitive_separating_genera_budget (g i : ℕ) (hg : 2 ≤ g) (hi : i < g-1) :
    (∀ c, Stable (primitiveSeparatingGenera g i c) 1) ∧
      (∑ c, complexity (primitiveSeparatingGenera g i c) 1) = complexity g 0 ∧
      (∑ c, primitiveSeparatingGenera g i c)+1 = g+(2-1) := by
  constructor
  · intro c
    fin_cases c <;> simp [primitiveSeparatingGenera,Stable] <;> omega
  · simp only [primitiveSeparatingGenera,Fin.sum_univ_two,Matrix.cons_val_zero,
      Matrix.cons_val_one]
    unfold complexity
    omega

lemma primitive_separating_term_eq_cut (P : PsiTheory) (g i : ℕ)
    (hg : 2 ≤ g) (hi : i < g-1) (z : ℂ) (hz : ‖z‖ < xCritical) :
    primitiveSeparatingTerm P g i z =
      TightSeparating.cutProductG P (primitiveSeparatingGenera g i)
        (fun _ => 1) (fun _ _ => 0) z := by
  have hs := (primitive_separating_genera_budget g i hg hi).1
  unfold TightSeparating.cutProductG
  simp_rw [primitive_moment_zero_lengths P _ 1 (by omega) (hs _) z hz]
  simp only [primitiveSeparatingTerm,primitiveSeparatingGenera,Fin.prod_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one]

lemma primitive_separating_term_cut_coefficient (P : PsiTheory) (g i : ℕ)
    (hg : 2 ≤ g) (hi : i < g-1) (n : ℕ) :
    realCoeff (primitiveSeparatingTerm P g i) n =
      realCoeff (TightSeparating.cutProductG P (primitiveSeparatingGenera g i)
        (fun _ => 1) (fun _ _ => 0)) n := by
  have he : primitiveSeparatingTerm P g i =ᶠ[𝓝 (0:ℂ)]
      TightSeparating.cutProductG P (primitiveSeparatingGenera g i)
        (fun _ => 1) (fun _ _ => 0) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) Analysis.xCritical_pos_parameter] with z hz
    exact primitive_separating_term_eq_cut P g i hg hi z
      (by simpa only [Metric.mem_ball,dist_zero_right] using hz)
  simp only [realCoeff,coeff,he.iteratedDeriv_eq n]


def primitiveSeparatingFamily (g : ℕ) : Finset (Fin 2 → ℕ) :=
  (Finset.range (g-1)).image (primitiveSeparatingGenera g)

lemma primitive_separating_genera_injective (g : ℕ) :
    Function.Injective (primitiveSeparatingGenera g) := by
  intro i j h
  have he := congrFun h (0 : Fin 2)
  simp only [primitiveSeparatingGenera,Matrix.cons_val_zero] at he
  omega

lemma primitive_separating_amplitude_sum (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ x ∈ Ico (0:ℝ) xCritical,
      (∑ i ∈ Finset.range (g-1),
        markedF P (i+1) 1 x*markedF P (g-(i+1)) 1 x)/markedF P g 0 x ≤ C/(g:ℝ) := by
  classical
  obtain ⟨C,hC,G,hbound⟩ := TightSeparating.separating_amplitude_genus_sum P 1
  refine ⟨C*(Real.pi^2/2),by positivity,max 2 G,?_⟩
  intro g hg x hx
  have hg2 : 2 ≤ g := by omega
  let Y := inverseY x
  have hY : Y ∈ Ico (0:ℝ) y₀ := (inverseY_branch x hx).1
  have hxy : XR Y = x := (inverseY_branch x hx).2
  have hs : ∀ a ∈ primitiveSeparatingFamily g,
      (∀ c, Stable (a c) 1) ∧
        (∑ c, complexity (a c) 1) = complexity g 0 ∧
        (∑ c, a c)+1=g+(2-1) := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact primitive_separating_genera_budget g i hg2 (Finset.mem_range.mp hi)
  have hb := hbound g (by omega) 2 (by omega) (by omega) (fun _ => 1)
    (by intro c;omega) (by simp : ∑ _c : Fin 2, (1:ℕ) = 2*1)
    (primitiveSeparatingFamily g) hs Y hY
  have hsum : (∑ a ∈ primitiveSeparatingFamily g,
      ∏ c, markedF P (a c) 1 (XR Y)) =
      ∑ i ∈ Finset.range (g-1), markedF P (i+1) 1 x*markedF P (g-(i+1)) 1 x := by
    unfold primitiveSeparatingFamily
    rw [Finset.sum_image (primitive_separating_genera_injective g).injOn]
    simp only [Fin.prod_univ_two,primitiveSeparatingGenera,Matrix.cons_val_zero,
      Matrix.cons_val_one,hxy]
  rw [hsum,hxy,pow_one,show (2:ℕ)-1=1 from rfl,pow_one] at hb
  have hr : r Y ≤ Real.pi^2/2 := by
    have hh := Analysis.r_le_pi Y hY
    nlinarith [hY.1]
  exact hb.trans (by gcongr)


lemma primitive_separating_cut_ofReal (P : PsiTheory) (g i : ℕ)
    (hg : 2 ≤ g) (hi : i < g-1) (x : ℝ) (hx : x ∈ Ico (0:ℝ) xCritical) :
    (TightSeparating.cutProductG P (primitiveSeparatingGenera g i)
      (fun _ => 1) (fun _ _ => 0) (x:ℂ)).re =
      markedF P (i+1) 1 x*markedF P (g-(i+1)) 1 x := by
  have hnorm : ‖(x:ℂ)‖ < xCritical := by
    simpa only [Complex.norm_of_nonneg hx.1] using hx.2
  rw [←primitive_separating_term_eq_cut P g i hg hi _ hnorm]
  have hreal (j : ℕ) : (iteratedDeriv 1 (Phi P j) (x:ℂ)).im = 0 :=
    PositiveConvolution.Phi_iteratedDeriv_real P j 1 x (by simpa only [abs_of_nonneg hx.1] using hx.2)
  simp only [primitiveSeparatingTerm,Complex.mul_re,hreal,mul_zero,sub_zero,markedF]

lemma primitive_separating_from_transfer (P : PsiTheory) (g n : ℕ) (hg : 2 ≤ g)
    (x : ℝ) (hx : x ∈ Ico (0:ℝ) xCritical) (K C : ℝ) (hK : 0 ≤ K)
    (htransfer : ∀ Q : ℕ, ∀ gs ps : Fin Q → ℕ,
      (∀ i, 1 ≤ ps i) → (∀ i, Stable (gs i) (ps i)) →
      (∑ i, complexity (gs i) (ps i)) = complexity g 0 →
      ∀ L : (i : Fin Q) → Fin (ps i) → ℝ,
      realCoeff (TightSeparating.cutProductG P gs ps L) n/realCoeff (Phi P g) n ≤
        K*((TightSeparating.cutProductG P gs ps L (x:ℂ)).re/markedF P g 0 x))
    (hamp : (∑ i ∈ Finset.range (g-1),
      markedF P (i+1) 1 x*markedF P (g-(i+1)) 1 x)/markedF P g 0 x ≤ C/(g:ℝ)) :
    primitiveSeparatingVolumeSum P g n ≤ (K*C/(2*Real.pi^2))/(g:ℝ) := by
  rw [primitive_separating_volume_coefficient_identity P g n hg]
  have hsum : (∑ i ∈ Finset.range (g-1),
      realCoeff (primitiveSeparatingTerm P g i) n/realCoeff (Phi P g) n) ≤
      K*((∑ i ∈ Finset.range (g-1),
        markedF P (i+1) 1 x*markedF P (g-(i+1)) 1 x)/markedF P g 0 x) := by
    rw [Finset.sum_div,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hb := primitive_separating_genera_budget g i hg hi'
    rw [primitive_separating_term_cut_coefficient P g i hg hi' n]
    have ht := htransfer 2 (primitiveSeparatingGenera g i) (fun _ => 1)
      (by intro c;omega) hb.1 hb.2.1 (fun _ _ => 0)
    rwa [primitive_separating_cut_ofReal P g i hg hi' x hx] at ht
  calc
    _ ≤ (1/(2*Real.pi^2))*(K*(C/(g:ℝ))) :=
      mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_left hamp hK))
        (by positivity)
    _ = _ := by ring

lemma primitive_separating_volume_sum_unbounded (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∀ gg nn : ℕ → ℕ,
      Tendsto gg atTop atTop → Tendsto nn atTop atTop →
      (∀ j, 2 ≤ gg j) → (∀ j, 2 ≤ nn j) →
      ∀ᶠ j : ℕ in atTop,
        primitiveSeparatingVolumeSum P (gg j) (nn j) ≤ C/(gg j:ℝ) := by
  obtain ⟨K,hK,htransfer⟩ := TightSeparating.separating_coefficient_transfer_unbounded P
  obtain ⟨C,hC,G,hamp⟩ := primitive_separating_amplitude_sum P
  refine ⟨K*C/(2*Real.pi^2),by positivity,?_⟩
  intro gg nn hg hn hg2 hn2
  filter_upwards [htransfer gg nn hg hn hg2 hn2,hg.eventually_ge_atTop G]
    with j hj hjG
  let x := TightConnected.connectedSaddle (gg j) (nn j)
  have hx : x ∈ Ioo (0:ℝ) xCritical :=
    (TightConnected.connectedSaddle_spec _ _ (hg2 j) (hn2 j)).1
  exact primitive_separating_from_transfer P (gg j) (nn j) (hg2 j) x
    ⟨hx.1.le,hx.2⟩ K C hK.le hj (hamp (gg j) hjG x ⟨hx.1.le,hx.2⟩)

lemma primitive_separating_volume_sum_fixed (P : PsiTheory) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ gg : ℕ → ℕ, Tendsto gg atTop atTop →
      ∀ᶠ j : ℕ in atTop,
        primitiveSeparatingVolumeSum P (gg j) n ≤ C/(gg j:ℝ) := by
  obtain ⟨K,hK,htransfer⟩ := TightSeparating.separating_coefficient_transfer_bounded P n 1 (by norm_num)
  obtain ⟨C,hC,G,hamp⟩ := primitive_separating_amplitude_sum P
  refine ⟨K*C/(2*Real.pi^2),by positivity,?_⟩
  intro gg hg
  have hh := (Analysis.complexity_real_tendsto_atTop 0).comp hg
  filter_upwards [htransfer gg hg,hg.eventually_ge_atTop (max 2 G),
    TightConnected.connected_small_weight_eventually (fun j => (complexity (gg j) 0:ℝ))
      hh 1 (by norm_num)] with j hj hjG hx
  have hg2 : 2 ≤ gg j := by omega
  have ht : ∀ Q : ℕ, ∀ gs ps : Fin Q → ℕ,
      (∀ i, 1 ≤ ps i) → (∀ i, Stable (gs i) (ps i)) →
      (∑ i, complexity (gs i) (ps i)) = complexity (gg j) 0 →
      ∀ L : (i : Fin Q) → Fin (ps i) → ℝ,
      realCoeff (TightSeparating.cutProductG P gs ps L) n/realCoeff (Phi P (gg j)) n ≤
        K*((TightSeparating.cutProductG P gs ps L ((1/(complexity (gg j) 0:ℝ):ℝ):ℂ)).re/
          markedF P (gg j) 0 (1/(complexity (gg j) 0:ℝ))) := by
    intro Q gs ps hp hs hsum L
    exact hj Q gs ps hp hs L
  exact primitive_separating_from_transfer P (gg j) n hg2 _ hx K C hK.le ht
    (hamp (gg j) (by omega) _ hx)


lemma primitive_separating_volume_sum_uniform (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ,
      primitiveSeparatingVolumeSum P g n ≤ C/(g:ℝ) := by
  classical
  obtain ⟨K,hK,hunbounded⟩ := primitive_separating_volume_sum_unbounded P
  have hlarge : ∃ N : ℕ, ∀ g ≥ N, ∀ n ≥ N,
      primitiveSeparatingVolumeSum P g n ≤ (K+1)/(g:ℝ) := by
    by_contra h
    push Not at h
    choose gg hgg nn hnn hbad using fun j => h (j+2)
    have hgg2 : ∀ j, 2 ≤ gg j := by intro j; have := hgg j; omega
    have hnn2 : ∀ j, 2 ≤ nn j := by intro j; have := hnn j; omega
    have hg : Tendsto gg atTop atTop :=
      tendsto_atTop_mono (fun j => by change j ≤ gg j;have := hgg j;omega) tendsto_id
    have hn : Tendsto nn atTop atTop :=
      tendsto_atTop_mono (fun j => by change j ≤ nn j;have := hnn j;omega) tendsto_id
    have hgood := hunbounded gg nn hg hn hgg2 hnn2
    obtain ⟨j,hj⟩ := hgood.exists
    have hgp : 0 < (gg j:ℝ) := by exact_mod_cast (show 0 < gg j by have := hgg2 j;omega)
    have hh : K/(gg j:ℝ) < (K+1)/(gg j:ℝ) := by gcongr; linarith
    exact (not_lt_of_ge (hj.trans hh.le)) (hbad j)
  obtain ⟨N,hN⟩ := hlarge
  have hfixed : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G,
      primitiveSeparatingVolumeSum P g n ≤ C/(g:ℝ) := by
    intro n
    obtain ⟨C,hC,hbound⟩ := primitive_separating_volume_sum_fixed P n
    obtain ⟨G,hG⟩ := Filter.eventually_atTop.mp (hbound id tendsto_id)
    exact ⟨C,hC,G,hG⟩
  choose C hC G hG using hfixed
  let Ctot : ℝ := K+1+∑ n ∈ Finset.range N,C n
  have hsum0 : 0 ≤ ∑ n ∈ Finset.range N,C n :=
    Finset.sum_nonneg (fun n _ => (hC n).le)
  have hCtot : 0 < Ctot := by dsimp [Ctot]; linarith
  refine ⟨Ctot,hCtot,max 2 (N+∑ n ∈ Finset.range N,G n),?_⟩
  intro g hg n
  have hgp : 0 < (g:ℝ) := by exact_mod_cast (show 0 < g by omega)
  have hgN : N ≤ g := by have := (le_max_right 2 (N+∑ n ∈ Finset.range N,G n)).trans hg;omega
  by_cases hn : N ≤ n
  · exact (hN g hgN n hn).trans (by apply div_le_div_of_nonneg_right _ hgp.le;dsimp[Ctot];linarith)
  · have hnmem : n ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have hGn : G n ≤ ∑ j ∈ Finset.range N,G j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (G j)) hnmem
    have hgG : G n ≤ g := by have := (le_max_right 2 (N+∑ n ∈ Finset.range N,G n)).trans hg;omega
    have hCn : C n ≤ ∑ j ∈ Finset.range N,C j :=
      Finset.single_le_sum (fun j _ => (hC j).le) hnmem
    exact (hG n g hgG).trans (by
      apply div_le_div_of_nonneg_right _ hgp.le
      dsimp [Ctot]
      linarith)


lemma primitive_separating_volume_sum_nonneg (P : PsiTheory) (g n : ℕ)
    (hg : 2 ≤ g) (hn : 1 ≤ n) : 0 ≤ primitiveSeparatingVolumeSum P g n := by
  apply Finset.sum_nonneg
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hb := (primitive_separating_genera_budget g i hg hi').1
  apply Finset.sum_nonneg
  intro k hk
  have hleft : 0 < volumeModel P (i+1) (k+1) :=
    diagonal_volume_pos_nonempty P _ _ (by omega) (by unfold Stable;omega)
  have hright : 0 < volumeModel P (g-(i+1)) (n-k+1) :=
    diagonal_volume_pos_nonempty P _ _ (by omega) (by unfold Stable;omega)
  have hparent : 0 < volumeModel P g n :=
    diagonal_volume_pos_nonempty P _ _ hn (by unfold Stable;omega)
  exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hleft.le) hright.le) hparent.le

lemma primitive_separating_volume_sum_tendsto_zero (P : PsiTheory) (n : ℕ → ℕ)
    (hn : ∀ᶠ g in atTop, 1 ≤ n g) :
    Tendsto (fun g => primitiveSeparatingVolumeSum P g (n g)) atTop (𝓝 0) := by
  obtain ⟨C,hC,G,hbound⟩ := primitive_separating_volume_sum_uniform P
  apply squeeze_zero' ?_ ?_ (tendsto_const_div_atTop_nhds_zero_nat C)
  · filter_upwards [hn,eventually_ge_atTop (2:ℕ)] with g hng hg
    exact primitive_separating_volume_sum_nonneg P g (n g) hg hng
  · filter_upwards [eventually_ge_atTop G] with g hg
    exact hbound g hg (n g)

/-- The actual numerical envelope supplied to the classical one-edge integral. -/
def primitiveSeparatingWindowEnvelope (P : PsiTheory) (g n : ℕ) (L : ℝ) : ℝ :=
  Real.exp L*(L^2/2)*primitiveSeparatingVolumeSum P g n

lemma primitive_separating_window_envelope_tendsto_zero (P : PsiTheory)
    (n : ℕ → ℕ)
    (hn : Tendsto (fun g:ℕ => (n g:ℝ)/Real.sqrt g) atTop atTop) (T : ℝ) :
    Tendsto (fun g => primitiveSeparatingWindowEnvelope P g (n g)
      (T/Real.sqrt (pantsScale g (n g)))) atTop (𝓝 0) := by
  have hn2 := Spectral.fast_cusps_eventually_two n hn
  have hA := primitive_separating_volume_sum_tendsto_zero P n (by
    filter_upwards [hn2] with g hg;omega)
  have hL : Tendsto (fun g => T/Real.sqrt (pantsScale g (n g))) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp (Spectral.pantsScale_tendsto_atTop n hn)).const_div_atTop T
  have ht := ((Real.continuous_exp.continuousAt.tendsto.comp hL).mul
    ((hL.pow 2).div_const 2)).mul hA
  simpa only [Function.comp_def,primitiveSeparatingWindowEnvelope,Real.exp_zero,
    zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_div,mul_zero] using ht


lemma primitive_separating_series_coefficient (P : PsiTheory) (g n : ℕ) :
    realCoeff (primitiveSeparatingSeries P g) n =
      ∑ i ∈ Finset.range (g-1), realCoeff (primitiveSeparatingTerm P g i) n := by
  have hz : ‖(0:ℂ)‖ < xCritical := by simpa using Analysis.xCritical_pos_parameter
  have ha (i : ℕ) : AnalyticAt ℂ (primitiveSeparatingTerm P g i) 0 := by
    apply AnalyticAt.mul
    · simpa only [iteratedDeriv_eq_iterate] using
        (Phi_analyticAt_open_disk P (i+1) 0 hz).iterated_deriv 1
    · simpa only [iteratedDeriv_eq_iterate] using
        (Phi_analyticAt_open_disk P (g-(i+1)) 0 hz).iterated_deriv 1
  unfold realCoeff coeff primitiveSeparatingSeries
  rw [iteratedDeriv_fun_sum (fun i _ => (ha i).contDiffAt),Finset.sum_div]
  exact map_sum Complex.reAddGroupHom _ _

lemma primitive_separating_series_volume_identity (P : PsiTheory) (g n : ℕ)
    (hg : 2 ≤ g) :
    primitiveSeparatingVolumeSum P g n =
      (1/(2*Real.pi^2)) *
        (realCoeff (primitiveSeparatingSeries P g) n/realCoeff (Phi P g) n) := by
  rw [primitive_separating_volume_coefficient_identity P g n hg,
    primitive_separating_series_coefficient,Finset.sum_div]

end WP.RandomGeometry
