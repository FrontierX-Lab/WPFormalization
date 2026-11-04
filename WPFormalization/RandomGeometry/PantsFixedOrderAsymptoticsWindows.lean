import WPFormalization.RandomGeometry.PantsFixedOrderAsymptotics
import WPFormalization.RandomGeometry.PantsWindowIntegralDefinitions

/-! Actual physical window integrals and their absolute, rather than relative,
short-boundary comparisons. Empty and zero-width windows remain allowed. -/
noncomputable section
namespace WP.RandomGeometry
open Set Filter MeasureTheory
open scoped Topology

/-- The exact physical Jacobian integral on the specified windows. -/
def pantsWindowWeight (r : ℕ) (I : Fin r → Set ℝ) : ℝ :=
  ∫ x : Fin r → ℝ in {x | ∀ i, x i ∈ I i}, ∏ i, x i

lemma pants_numeric_window_set_measurable (r : ℕ) (I : Fin r → Set ℝ)
    (hI : ∀ i, MeasurableSet (I i)) : MeasurableSet {x : Fin r → ℝ | ∀ i, x i ∈ I i} := by
  have he : {x : Fin r → ℝ | ∀ i, x i ∈ I i}=Set.univ.pi I := by ext x; simp
  rw [he]
  exact MeasurableSet.univ_pi hI

lemma pants_window_weight_eq_product (r : ℕ) (I : Fin r → Set ℝ) :
    pantsWindowWeight r I = ∏ i, ∫ t in I i, t := by
  have he : {x : Fin r → ℝ | ∀ i, x i ∈ I i}=Set.univ.pi I := by ext x; simp
  unfold pantsWindowWeight
  rw [he,volume_pi,Measure.restrict_pi_pi,integral_fintype_prod_eq_prod (fun (_ : Fin r) (t : ℝ) => t)]

lemma pants_window_integrable_continuous (r : ℕ) (I : Fin r → Set ℝ) (L : ℝ)
    (hI : ∀ i, I i ⊆ Icc 0 L) (f : (Fin r → ℝ) → ℝ) (hf : Continuous f) :
    IntegrableOn f {x : Fin r → ℝ | ∀ i, x i ∈ I i} := by
  have hi : IntegrableOn f (Icc (0 : Fin r → ℝ) (fun _ => L)) := hf.integrableOn_Icc
  apply hi.mono_set
  intro x hx
  exact ⟨fun i => (hI i (hx i)).1,fun i => (hI i (hx i)).2⟩

lemma pants_window_weight_nonneg (r : ℕ) (I : Fin r → Set ℝ)
    (hI : ∀ i, MeasurableSet (I i)) (L : ℝ) (hIL : ∀ i, I i ⊆ Icc 0 L) :
    0 ≤ pantsWindowWeight r I := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (pants_numeric_window_set_measurable r I hI)] with x hx
  exact Finset.prod_nonneg (fun i _ => (hIL i (hx i)).1)

lemma pants_window_volume_integrable (P : PsiTheory) (g m r : ℕ) (hr : r ≤ m)
    (I : Fin r → Set ℝ) (L : ℝ) (hIL : ∀ i, I i ⊆ Icc 0 L) :
    IntegrableOn (fun x : Fin r → ℝ =>
      boundaryVolumeModel P g m (activeBoundaryLengths hr x)*∏ i, x i)
      {x | ∀ i, x i ∈ I i} := by
  apply pants_window_integrable_continuous r I L hIL
  have hc : Continuous (boundaryVolumeModel P g m) := by
    unfold boundaryVolumeModel
    fun_prop
  exact (hc.comp (activeBoundaryLengths_continuous hr)).mul (by fun_prop)

/-- Full uniform physical-window bounds, allowing arbitrary Borel subsets of
[0,L] and vanishing bare Jacobian integral. -/
lemma pants_window_volume_bounds (P : PsiTheory) (g m r : ℕ) (hr : r ≤ m)
    (hg : 1 ≤ g) (hm : 1 ≤ m) (I : Fin r → Set ℝ)
    (hI : ∀ i, MeasurableSet (I i)) (L : ℝ) (hIL : ∀ i, I i ⊆ Icc 0 L) :
    volumeModel P g m*pantsWindowWeight r I ≤ pantsWindowVolumeIntegral P g m r hr I ∧
      pantsWindowVolumeIntegral P g m r hr I ≤
        Real.exp (r*L/2)*(volumeModel P g m*pantsWindowWeight r I) := by
  have hv : 0 < volumeModel P g m :=
    diagonal_volume_pos_nonempty P g m hm (by unfold Stable;omega)
  have hb : IntegrableOn (fun x : Fin r → ℝ => volumeModel P g m*∏ i, x i)
      {x | ∀ i, x i ∈ I i} := pants_window_integrable_continuous r I L hIL _ (by fun_prop)
  have hu : IntegrableOn (fun x : Fin r → ℝ => Real.exp (r*L/2)*volumeModel P g m*∏ i, x i)
      {x | ∀ i, x i ∈ I i} := pants_window_integrable_continuous r I L hIL _ (by fun_prop)
  have hi := pants_window_volume_integrable P g m r hr I L hIL
  have hpoint : ∀ᵐ x ∂volume.restrict {x : Fin r → ℝ | ∀ i, x i ∈ I i},
      volumeModel P g m*∏ i, x i ≤
        boundaryVolumeModel P g m (activeBoundaryLengths hr x)*∏ i, x i ∧
      boundaryVolumeModel P g m (activeBoundaryLengths hr x)*∏ i, x i ≤
        Real.exp (r*L/2)*volumeModel P g m*∏ i, x i := by
    filter_upwards [ae_restrict_mem (pants_numeric_window_set_measurable r I hI)] with x hx
    have hx0 : ∀ i, 0 ≤ x i := fun i => (hIL i (hx i)).1
    have hw : 0 ≤ ∏ i, x i := Finset.prod_nonneg (fun i _ => hx0 i)
    have hbounds := pants_boundary_volume_bounds P g m hg hm
      (activeBoundaryLengths hr x) (activeBoundaryLengths_nonneg hr x hx0)
    have hsum : (∑ i, activeBoundaryLengths hr x i) ≤ (r:ℝ)*L := by
      rw [activeBoundaryLengths_sum]
      exact (Finset.sum_le_sum (fun i _ => (hIL i (hx i)).2)).trans_eq (by simp)
    have he : Real.exp ((∑ i, activeBoundaryLengths hr x i)/2) ≤ Real.exp (r*L/2) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hsum (by norm_num))
    constructor
    · exact mul_le_mul_of_nonneg_right (by simpa using (le_div_iff₀ hv).mp hbounds.1) hw
    · exact mul_le_mul_of_nonneg_right
        (((div_le_iff₀ hv).mp hbounds.2).trans (mul_le_mul_of_nonneg_right he hv.le)) hw
  constructor
  · have h := integral_mono_ae hb hi (hpoint.mono fun _ hx => hx.1)
    simpa only [pantsWindowVolumeIntegral,pantsWindowWeight,integral_const_mul] using h
  · have h := integral_mono_ae hi hu (hpoint.mono fun _ hx => hx.2)
    simpa only [pantsWindowVolumeIntegral,pantsWindowWeight,integral_const_mul,mul_assoc] using h

/-- Exact zero-boundary window base, including all ordered cusp labels. -/
def pantsFixedOrderWindowBase (P : PsiTheory) (g n r : ℕ) (I : Fin r → Set ℝ) : ℝ :=
  ((n.descFactorial (2*r) : ℝ)/((2:ℝ)^r*volumeModel P g n))*
    volumeModel P g (n-r)*pantsWindowWeight r I

/-- The actual polynomial cut integral on the windows. Impossible cusp label
counts are zero, in agreement with their falling factorial. -/
def pantsFixedOrderWindowCut (P : PsiTheory) (g n r : ℕ) (I : Fin r → Set ℝ) : ℝ :=
  if hn : 2*r ≤ n then
    ((n.descFactorial (2*r) : ℝ)/((2:ℝ)^r*volumeModel P g n))*
      pantsWindowVolumeIntegral P g (n-r) r (by omega) I
  else 0

lemma pants_fixed_window_cut_bounds (P : PsiTheory) (g n r : ℕ)
    (hg : 1 ≤ g) (hn : 2*r ≤ n) (hnm : r+1 ≤ n) (I : Fin r → Set ℝ)
    (hI : ∀ i, MeasurableSet (I i)) (L : ℝ) (hIL : ∀ i, I i ⊆ Icc 0 L) :
    pantsFixedOrderWindowBase P g n r I ≤ pantsFixedOrderWindowCut P g n r I ∧
      pantsFixedOrderWindowCut P g n r I ≤
        Real.exp (r*L/2)*pantsFixedOrderWindowBase P g n r I := by
  have hv : 0 < volumeModel P g n :=
    diagonal_volume_pos_nonempty P g n (by omega) (by unfold Stable;omega)
  have ha : 0 ≤ (n.descFactorial (2*r) : ℝ)/((2:ℝ)^r*volumeModel P g n) := by positivity
  have hb := pants_window_volume_bounds P g (n-r) r (by omega) hg (by omega) I hI L hIL
  unfold pantsFixedOrderWindowBase pantsFixedOrderWindowCut
  rw [dif_pos hn]
  constructor
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb.1 ha
  · have h := mul_le_mul_of_nonneg_left hb.2 ha
    convert h using 1 <;> ring

/-- Absolute convergence transfer, including all zero-intensity windows. -/
lemma pants_fixed_window_cut_tendsto (P : PsiTheory) (r : ℕ)
    (n : ℕ → ℕ) (I : ℕ → Fin r → Set ℝ) (L : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hL : Tendsto L atTop (𝓝 0))
    (hI : ∀ᶠ g in atTop, ∀ i, MeasurableSet (I g i))
    (hIL : ∀ᶠ g in atTop, ∀ i, I g i ⊆ Icc 0 (L g)) (b : ℝ)
    (hbase : Tendsto (fun g => pantsFixedOrderWindowBase P g (n g) r (I g)) atTop (𝓝 b)) :
    Tendsto (fun g => pantsFixedOrderWindowCut P g (n g) r (I g)) atTop (𝓝 b) := by
  have he : Tendsto (fun g => Real.exp (r*L g/2)) atTop (𝓝 1) := by
    have ht := (hL.const_mul (r:ℝ)).div_const 2
    simp only [mul_zero,zero_div] at ht
    simpa only [Function.comp_def,Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp ht
  have hu := he.mul hbase
  simp only [one_mul] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hbase hu
  · filter_upwards [hn.eventually_ge_atTop (max (2*r) (r+1)),hI,hIL,eventually_ge_atTop (1:ℕ)] with g hng hIg hILg hg
    exact (pants_fixed_window_cut_bounds P g (n g) r hg (by omega) (by omega) (I g) hIg (L g) hILg).1
  · filter_upwards [hn.eventually_ge_atTop (max (2*r) (r+1)),hI,hIL,eventually_ge_atTop (1:ℕ)] with g hng hIg hILg hg
    exact (pants_fixed_window_cut_bounds P g (n g) r hg (by omega) (by omega) (I g) hIg (L g) hILg).2

/-- Choosing open or closed left endpoints does not change the actual physical
Lebesgue window measure, including a=b. -/
lemma pants_window_measure_Ioc_eq_Icc (r : ℕ) (a b : Fin r → ℝ) :
    volume.restrict {x : Fin r → ℝ | ∀ i, x i ∈ Ioc (a i) (b i)} =
      volume.restrict {x : Fin r → ℝ | ∀ i, x i ∈ Icc (a i) (b i)} := by
  have ho : {x : Fin r → ℝ | ∀ i, x i ∈ Ioc (a i) (b i)}=
      Set.univ.pi (fun i => Ioc (a i) (b i)) := by
      ext x
      simp only [Set.mem_setOf_eq,Set.mem_pi,Set.mem_univ,forall_const]
  have hc : {x : Fin r → ℝ | ∀ i, x i ∈ Icc (a i) (b i)}=
      Set.univ.pi (fun i => Icc (a i) (b i)) := by
      ext x
      simp only [Set.mem_setOf_eq,Set.mem_pi,Set.mem_univ,forall_const]
  rw [ho,hc,volume_pi,Measure.restrict_pi_pi,Measure.restrict_pi_pi]
  congr 1
  funext i
  exact restrict_Ioc_eq_restrict_Icc

lemma pants_window_integral_Ioc_eq_Icc (P : PsiTheory) (g m r : ℕ) (hr : r ≤ m)
    (a b : Fin r → ℝ) :
    pantsWindowVolumeIntegral P g m r hr (fun i => Ioc (a i) (b i)) =
      pantsWindowVolumeIntegral P g m r hr (fun i => Icc (a i) (b i)) := by
  unfold pantsWindowVolumeIntegral
  rw [pants_window_measure_Ioc_eq_Icc]

lemma pants_fixed_window_cut_Ioc_eq_Icc (P : PsiTheory) (g n r : ℕ)
    (a b : Fin r → ℝ) :
    pantsFixedOrderWindowCut P g n r (fun i => Ioc (a i) (b i)) =
      pantsFixedOrderWindowCut P g n r (fun i => Icc (a i) (b i)) := by
  unfold pantsFixedOrderWindowCut
  split_ifs
  · rw [pants_window_integral_Ioc_eq_Icc]
  · rfl

/-- Zeroth factorial order is exactly probability one, with no geometric or
positive-window assumption. -/
lemma pants_zero_factorial_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : Ω → ℕ) :
    (∫ x, ((N x).descFactorial 0 : ℝ) ∂μ)=1 := by
  simp

end WP.RandomGeometry
