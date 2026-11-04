import WPFormalization.RandomGeometry.PantsFixedOrderAsymptoticsWindows
import WPFormalization.Spectral.PantsScaleGrowth

/-! Fixed arbitrary physical windows at the original q_g^(-1/2) scale.
The limits are absolute, including all degenerate zero-intensity windows. -/
noncomputable section
namespace WP.RandomGeometry
open Set Filter MeasureTheory
open scoped Topology

/-- Closed physical windows obtained from fixed nonnegative rescaled windows. -/
def pantsScaledWindows (r : ℕ) (q : ℝ) (a b : Fin r → ℝ) : Fin r → Set ℝ :=
  fun i => Icc (a i/Real.sqrt q) (b i/Real.sqrt q)

lemma pants_scaled_window_weight (r : ℕ) (q : ℝ) (hq : 0 < q)
    (a b : Fin r → ℝ) (hab : ∀ i, a i ≤ b i) :
    pantsWindowWeight r (pantsScaledWindows r q a b) =
      (∏ i, ((b i)^2-(a i)^2))/(2*q)^r := by
  have hi (i : Fin r) : (∫ t in pantsScaledWindows r q a b i, t) =
      ((b i)^2-(a i)^2)/(2*q) := by
    unfold pantsScaledWindows
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le
      (div_le_div_of_nonneg_right (hab i) (Real.sqrt_nonneg q)),integral_id]
    simp only [div_pow,Real.sq_sqrt hq.le]
    field_simp
  rw [pants_window_weight_eq_product]
  simp_rw [hi]
  rw [Finset.prod_div_distrib]
  simp

lemma pants_fixed_scaled_window_base_identity (P : PsiTheory) (g n r : ℕ)
    (hq : 0 < pantsScale g n) (a b : Fin r → ℝ) (hab : ∀ i, a i ≤ b i) :
    pantsFixedOrderWindowBase P g n r (pantsScaledWindows r (pantsScale g n) a b) =
      (pantsFixedOrderBase P g n r 1/(pantsScale g n)^r)*
        ∏ i, ((b i)^2-(a i)^2) := by
  rw [pantsFixedOrderWindowBase,pants_scaled_window_weight r _ hq a b hab]
  unfold pantsFixedOrderBase
  simp only [one_pow,mul_pow,div_pow]
  field_simp

lemma pants_fixed_scaled_window_base_tendsto (P : PsiTheory) (r : ℕ)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hq : Tendsto (fun g => pantsScale g (n g)) atTop atTop)
    (a b : Fin r → ℝ) (hab : ∀ i, a i ≤ b i) :
    Tendsto (fun g => pantsFixedOrderWindowBase P g (n g) r
      (pantsScaledWindows r (pantsScale g (n g)) a b)) atTop
        (𝓝 (∏ i, ((b i)^2-(a i)^2))) := by
  have hc := pants_fixed_order_base_asymptotic P r n (fun _ => 1) hn
    (Eventually.of_forall (fun _ => one_ne_zero))
  simp only [one_pow,mul_one] at hc
  have ht := hc.mul_const (∏ i, ((b i)^2-(a i)^2))
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [hq.eventually_gt_atTop 0] with g hqg
  exact (pants_fixed_scaled_window_base_identity P g (n g) r hqg a b hab).symm

/-- Absolute limit of every fixed physical-window cut integral. No window
is required to have positive width or positive limiting intensity. -/
lemma pants_fixed_scaled_window_cut_tendsto (P : PsiTheory) (r : ℕ)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hq : Tendsto (fun g => pantsScale g (n g)) atTop atTop)
    (a b : Fin r → ℝ) (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i) :
    Tendsto (fun g => pantsFixedOrderWindowCut P g (n g) r
      (pantsScaledWindows r (pantsScale g (n g)) a b)) atTop
        (𝓝 (∏ i, ((b i)^2-(a i)^2))) := by
  let B : ℝ := 1+∑ i, b i
  have hb0 : ∀ i, 0 ≤ b i := fun i => (ha i).trans (hab i)
  have hB (i : Fin r) : b i ≤ B := by
    have hi := Finset.single_le_sum (fun j _ => hb0 j) (Finset.mem_univ i)
    dsimp [B]
    linarith
  let cap : ℕ → ℝ := fun g => B/Real.sqrt (pantsScale g (n g))
  have hcap : Tendsto cap atTop (𝓝 0) := by
    have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hq)
    simpa only [cap,div_eq_mul_inv,mul_zero,Function.comp_def] using hi.const_mul B
  apply pants_fixed_window_cut_tendsto P r n
    (fun g => pantsScaledWindows r (pantsScale g (n g)) a b) cap hn hcap
  · exact Eventually.of_forall (fun _ _ => measurableSet_Icc)
  · apply Eventually.of_forall
    intro g i t ht
    constructor
    · exact (div_nonneg (ha i) (Real.sqrt_nonneg _)).trans ht.1
    · exact ht.2.trans (div_le_div_of_nonneg_right (hB i) (Real.sqrt_nonneg _))
  · exact pants_fixed_scaled_window_base_tendsto P r n hn hq a b hab

/-- The original fast-cusp hypothesis alone supplies the two divergence
conditions used in the numerical fixed-window limit. -/
lemma pants_fixed_scaled_windows_of_fast_cusps (P : PsiTheory) (r : ℕ)
    (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g:ℝ)/Real.sqrt g) atTop atTop)
    (a b : Fin r → ℝ) (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i) :
    Tendsto (fun g => pantsFixedOrderWindowCut P g (n g) r
      (pantsScaledWindows r (pantsScale g (n g)) a b)) atTop
        (𝓝 (∏ i, ((b i)^2-(a i)^2))) := by
  have hnreal : Tendsto (fun g => (n g:ℝ)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hnfast
    filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
    have hgR : (1:ℝ) ≤ g := by exact_mod_cast hg
    have hs : 1 ≤ Real.sqrt (g:ℝ) :=
      (Real.le_sqrt (by norm_num) (by positivity)).2 (by nlinarith)
    exact div_le_self (by positivity) hs
  exact pants_fixed_scaled_window_cut_tendsto P r n (tendsto_natCast_atTop_iff.mp hnreal)
    (WP.Spectral.pantsScale_tendsto_atTop n hnfast) a b ha hab

/-- The same exact limit for disjoint-style half-open rescaled windows. -/
lemma pants_fixed_scaled_Ioc_windows_of_fast_cusps (P : PsiTheory) (r : ℕ)
    (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g:ℝ)/Real.sqrt g) atTop atTop)
    (a b : Fin r → ℝ) (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i) :
    Tendsto (fun g => pantsFixedOrderWindowCut P g (n g) r
      (fun i => Ioc (a i/Real.sqrt (pantsScale g (n g)))
        (b i/Real.sqrt (pantsScale g (n g))))) atTop
        (𝓝 (∏ i, ((b i)^2-(a i)^2))) := by
  apply (pants_fixed_scaled_windows_of_fast_cusps P r n hnfast a b ha hab).congr
  intro g
  exact (pants_fixed_window_cut_Ioc_eq_Icc P g (n g) r
    (fun i => a i/Real.sqrt (pantsScale g (n g)))
    (fun i => b i/Real.sqrt (pantsScale g (n g)))).symm

end WP.RandomGeometry
