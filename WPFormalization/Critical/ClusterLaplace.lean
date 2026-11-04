import WPFormalization.Critical.PantsClusterTestBounds
import WPFormalization.Probability.PoissonClusterLaplace

/- Local interface between the actual full primitive pants spectra and the
generic Poisson Laplace formula. A deterministic proper-support hypothesis
is explicit in this generic wrapper. It is not an external probability
field or the paper's ambient-spectrum convergence theorem. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster MeasureTheory Set Filter WP.Probability
open scoped ENNReal NNReal Topology CompactlySupported
variable (F : Family.{u,v})

lemma testPairingNN_compact_support_of_prefix_cutoff
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    (f : C_c(ℝ≥0,ℝ)) :
    ∃K : Set ℝ≥0,IsCompact K ∧ Function.support (testPairingNN F f)⊆K := by
  obtain ⟨L,hLf⟩:=(show IsCompact (tsupport f) from f.hasCompactSupport).bddAbove
  have hcompact : IsCompact (Iic (2*L) : Set ℝ≥0) := by
    have he : (Iic (2*L) : Set ℝ≥0)=Icc (0:ℝ≥0) (2*L) := by ext x;simp
    rw [he]
    exact isCompact_Icc
  refine ⟨Iic (2*L),hcompact,?_⟩
  intro s hs
  by_contra hnot
  have hlarge : 2*L<s := lt_of_not_ge hnot
  have hspos : 0<s := lt_of_le_of_lt (by positivity : 0≤2*L) hlarge
  have hval : 2*(L:ℝ)<(s:ℝ) := by exact_mod_cast hlarge
  let t : Waist:=⟨(s:ℝ),by exact_mod_cast hspos⟩
  have hnorm:=test_integral_norm_le F t f L hLf
  rw [hproper t L hval,ENNReal.toReal_zero,mul_zero] at hnorm
  have hz : testPairingNN F f s=0 := by
    rw [testPairingNN_pos F f s hspos]
    exact norm_le_zero_iff.mp hnorm
  exact hs hz

lemma testPairingNN_bounded_above (f : C_c(ℝ≥0,ℝ)) :
    ∃C : ℝ,∀s,testPairingNN F f s≤C := by
  obtain ⟨C,_,hC⟩:=testPairingNN_uniform_bound F f
  refine ⟨C,fun s=>?_⟩
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC s)

lemma testPairingNN_integrable_of_prefix_cutoff
    (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    (f : C_c(ℝ≥0,ℝ)) (hf : ∀x,0≤f x) (μ : Measure ℝ≥0) [IsLocallyFiniteMeasure μ] :
    Integrable (testPairingNN F f) μ := by
  exact PoissonCluster.integrable_of_bounded_nonneg_compact_support μ _
    (testPairingNN_measurable F D f) (testPairingNN_nonneg F f hf)
    (testPairingNN_bounded_above F f) (testPairingNN_compact_support_of_prefix_cutoff F hproper f)

theorem pants_pairing_poisson_laplace_of_prefix_cutoff
    (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    (μ : Measure ℝ≥0) [IsLocallyFiniteMeasure μ] [Measure.Regular μ]
    (QP : ProbabilityMeasure (PointMeasure ℝ≥0))
    (hP : IsPoissonPointProcessLaw ℝ≥0 μ QP)
    (f : C_c(ℝ≥0,ℝ)) (hf : ∀x,0≤f x) :
    Measurable (PoissonCluster.laplaceObservable (testPairingNN F f)) ∧
    (∫ξ,PoissonCluster.laplaceObservable (testPairingNN F f) ξ ∂QP)=
      Real.exp (-(∫s,laplaceCostNN F f s ∂μ)) := by
  exact WP.External.poisson_laplace_functional ℝ≥0 μ QP hP _
    (testPairingNN_measurable F D f) (testPairingNN_nonneg F f hf)
    (testPairingNN_bounded_above F f) (testPairingNN_compact_support_of_prefix_cutoff F hproper f)

theorem independent_pants_pairing_laplace_of_prefix_cutoff
    (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    (ν μ : Measure ℝ≥0) [IsLocallyFiniteMeasure ν] [Measure.Regular ν]
    [IsLocallyFiniteMeasure μ] [Measure.Regular μ]
    (QN QP : ProbabilityMeasure (PointMeasure ℝ≥0))
    (hN : IsPoissonPointProcessLaw ℝ≥0 ν QN) (hP : IsPoissonPointProcessLaw ℝ≥0 μ QP)
    (f : C_c(ℝ≥0,ℝ)) (hf : ∀x,0≤f x) :
    (∫ξ,PoissonCluster.jointLaplaceObservable (fun x=>f x) (testPairingNN F f) ξ
      ∂(QN : Measure (PointMeasure ℝ≥0)).prod QP)=
      Real.exp (-(∫x,1-Real.exp (-f x) ∂ν)-(∫s,laplaceCostNN F f s ∂μ)) := by
  apply PoissonCluster.independent_poisson_laplace_formula ℝ≥0 ν μ QN QP hN hP
    (fun x=>f x) (testPairingNN F f) f.continuous.measurable
    (testPairingNN_measurable F D f) hf (testPairingNN_nonneg F f hf)
    ?_ (testPairingNN_bounded_above F f) ?_
    (testPairingNN_compact_support_of_prefix_cutoff F hproper f)
  · exact ⟨‖f.toBoundedContinuousFunction‖,fun x=>f.toBoundedContinuousFunction.apply_le_norm x⟩
  · exact ⟨tsupport f,f.hasCompactSupport,subset_tsupport f⟩

end WP.Critical.PantsCluster
