import WPFormalization.Critical.PantsClusterBounds

/-! Uniform bounds and a Borel zero extension for actual cluster test pairings.
The estimate comes from G.2, including as the waist approaches zero.  It
contains no waist support cutoff or filling assumption. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster MeasureTheory Set Filter
open scoped Topology ENNReal NNReal CompactlySupported

variable (F : Family.{u,v})

lemma test_integral_norm_le (s : Waist) (f : C_c(ℝ≥0,ℝ)) (L : ℝ≥0)
    (hf : tsupport f ⊆ Iic L) :
    ‖∫ x, f x ∂measure F s‖ ≤
      ‖f.toBoundedContinuousFunction‖ * (measure F s (Iic L)).toReal := by
  have hi : (∫ x in Iic L, f x ∂measure F s) = ∫ x, f x ∂measure F s := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    exact fun h => hx (hf h)
  rw [←hi]
  apply norm_setIntegral_le_of_norm_le_const_ae
  · rw [measure_Iic]
    exact ENNReal.natCast_lt_top _
  · exact Filter.Eventually.of_forall (fun x =>
      f.toBoundedContinuousFunction.norm_coe_le_norm x)

lemma test_integral_uniform_bound (f : C_c(ℝ≥0,ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Waist, ‖∫ x, f x ∂measure F s‖ ≤ C := by
  obtain ⟨L,hL⟩ := (show IsCompact (tsupport f) from f.hasCompactSupport).bddAbove
  obtain ⟨A,hA,hbound⟩ := cluster_prefix_uniform_bound F L
  refine ⟨‖f.toBoundedContinuousFunction‖ * A + 1, by positivity, ?_⟩
  intro s
  exact (test_integral_norm_le F s f L hL).trans
    ((mul_le_mul_of_nonneg_left (hbound s) (norm_nonneg _)).trans (by linarith))

lemma test_integral_nonneg (s : Waist) (f : C_c(ℝ≥0,ℝ)) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ ∫ x, f x ∂measure F s := integral_nonneg hf

/-- The zero-waist extension is used only for Borel integration. The family
itself remains defined precisely at positive physical waist length. -/
def testPairingNN (f : C_c(ℝ≥0,ℝ)) (s : ℝ≥0) : ℝ :=
  if hs : s ∈ Ioi (0 : ℝ≥0) then
    ∫ x, f x ∂measure F ⟨(s:ℝ), by exact_mod_cast hs⟩ else 0

lemma testPairingNN_zero (f : C_c(ℝ≥0,ℝ)) : testPairingNN F f 0 = 0 := by
  simp [testPairingNN]

lemma testPairingNN_pos (f : C_c(ℝ≥0,ℝ)) (s : ℝ≥0) (hs : 0 < s) :
    testPairingNN F f s = ∫ x, f x ∂measure F ⟨(s:ℝ), by exact_mod_cast hs⟩ := by
  simp only [testPairingNN,mem_Ioi,dite_eq_left hs]

lemma testPairingNN_measurable (D : DeformationClassics F) (f : C_c(ℝ≥0,ℝ)) :
    Measurable (testPairingNN F f) := by
  let e : Ioi (0:ℝ≥0) → Waist := fun s => ⟨(s.val:ℝ), by exact_mod_cast s.property⟩
  have he : Continuous e := by
    apply Continuous.subtype_mk
    exact NNReal.continuous_coe.comp continuous_subtype_val
  exact Measurable.dite
    ((test_integral_continuous F D f).comp he).measurable
    measurable_const measurableSet_Ioi

lemma testPairingNN_nonneg (f : C_c(ℝ≥0,ℝ)) (hf : ∀ x, 0 ≤ f x) (s : ℝ≥0) :
    0 ≤ testPairingNN F f s := by
  unfold testPairingNN
  split_ifs
  · exact test_integral_nonneg F _ f hf
  · exact le_rfl

lemma testPairingNN_uniform_bound (f : C_c(ℝ≥0,ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ≥0, ‖testPairingNN F f s‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := test_integral_uniform_bound F f
  refine ⟨C,hC,fun s => ?_⟩
  unfold testPairingNN
  split_ifs
  · exact hbound _
  · simpa using hC.le

lemma testPairingNN_integrable (D : DeformationClassics F) (f : C_c(ℝ≥0,ℝ))
    (μ : Measure ℝ≥0) [IsFiniteMeasure μ] : Integrable (testPairingNN F f) μ := by
  obtain ⟨C,hC,hbound⟩ := testPairingNN_uniform_bound F f
  exact Integrable.mono' (integrable_const C)
    (testPairingNN_measurable F D f).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- The bounded nonnegative integrand in the pants Poisson Laplace exponent. -/
def laplaceCostNN (f : C_c(ℝ≥0,ℝ)) (s : ℝ≥0) : ℝ :=
  1 - Real.exp (-testPairingNN F f s)

lemma laplaceCostNN_measurable (D : DeformationClassics F) (f : C_c(ℝ≥0,ℝ)) :
    Measurable (laplaceCostNN F f) :=
  measurable_const.sub ((testPairingNN_measurable F D f).neg.exp)

lemma laplaceCostNN_nonneg_le_one (f : C_c(ℝ≥0,ℝ)) (hf : ∀ x, 0 ≤ f x)
    (s : ℝ≥0) : 0 ≤ laplaceCostNN F f s ∧ laplaceCostNN F f s ≤ 1 := by
  have hpos := testPairingNN_nonneg F f hf s
  constructor
  · dsimp [laplaceCostNN]
    have := (Real.exp_le_one_iff).mpr (neg_nonpos.mpr hpos)
    linarith
  · dsimp [laplaceCostNN]
    linarith [Real.exp_pos (-testPairingNN F f s)]

lemma laplaceCostNN_le_testPairingNN (f : C_c(ℝ≥0,ℝ)) (s : ℝ≥0) :
    laplaceCostNN F f s ≤ testPairingNN F f s := by
  dsimp [laplaceCostNN]
  linarith [Real.add_one_le_exp (-testPairingNN F f s)]

lemma laplaceCostNN_integrable (D : DeformationClassics F) (f : C_c(ℝ≥0,ℝ))
    (hf : ∀ x, 0 ≤ f x) (μ : Measure ℝ≥0) [IsFiniteMeasure μ] :
    Integrable (laplaceCostNN F f) μ := by
  refine Integrable.mono' (integrable_const (1:ℝ))
    (laplaceCostNN_measurable F D f).aestronglyMeasurable ?_
  apply Filter.Eventually.of_forall
  intro s
  rw [Real.norm_eq_abs,abs_of_nonneg (laplaceCostNN_nonneg_le_one F f hf s).1]
  exact (laplaceCostNN_nonneg_le_one F f hf s).2

end WP.Critical.PantsCluster
