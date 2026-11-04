import WPFormalization.Critical.ClusterFiniteWaistMapping
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster MeasureTheory Set Filter WP.Probability TopologicalSpace
open scoped ENNReal NNReal Topology CompactlySupported
variable (F : Family.{u,v})

lemma testPairingNN_ae_continuousAt_of_no_atom_zero (D : DeformationClassics F)
    (f : C_c(ℝ≥0,ℝ)) (ξ : Measure ℝ≥0) (hzero : ξ {0}=0) :
    ∀ᵐs ∂ξ,ContinuousAt (testPairingNN F f) s := by
  have ha : ∀ᵐs ∂ξ,s≠0 := by
    apply ae_iff.mpr
    have he : {s : ℝ≥0 | ¬s≠0}={0} := by ext s;simp
    rwa [he]
  filter_upwards [ha] with s hs
  exact testPairingNN_continuousAt_pos F D f s (pos_iff_ne_zero.mpr hs)

lemma clusterPointMeasure_continuousAt_of_no_atom_zero
    (B : WP.External.CompactBorelVaguePairing) (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    (ξ : PointMeasure ℝ≥0) (hzero : ξ.toMeasure {0}=0) :
    ContinuousAt (clusterPointMeasure F D hproper) ξ := by
  apply pointMeasure_continuousAt_of_test_pairings
  intro f
  obtain ⟨C,_,hC⟩ := testPairingNN_uniform_bound F f
  have hc := (B (testPairingNN F f) (testPairingNN_measurable F D f)
    ⟨C,hC⟩ (testPairingNN_compact_support_of_prefix_cutoff F hproper f)).2 ξ
      (testPairingNN_ae_continuousAt_of_no_atom_zero F D f ξ.toMeasure hzero)
  simpa only [clusterPointMeasure_integral] using hc

lemma clusterSuperposition_continuousAt_of_no_atom_zero
    (B : WP.External.CompactBorelVaguePairing) (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    (p : PointMeasure ℝ≥0 × PointMeasure ℝ≥0) (hzero : p.2.toMeasure {0}=0) :
    ContinuousAt (clusterSuperposition F D hproper) p :=
  pointMeasureAdd_continuous.continuousAt.comp
    (continuousAt_fst.prodMk
      ((clusterPointMeasure_continuousAt_of_no_atom_zero F B D hproper p.2 hzero).comp continuousAt_snd))

theorem lawConverges_clusterSuperposition
    (B : WP.External.CompactBorelVaguePairing)
    (C : WP.External.AlmostSureContinuousMapping.{0,0,w,z}) (D : DeformationClassics F)
    (hproper : ∀(s : Waist)(L : ℝ≥0),2*(L:ℝ)<s.val→measure F s (Iic L)=0)
    {Ω : ℕ → Type w} [∀j,MeasurableSpace (Ω j)]
    {Ωlimit : Type z} [MeasurableSpace Ωlimit]
    (μ : (j : ℕ) → Measure (Ω j))
    (X : (j : ℕ) → Ω j → PointMeasure ℝ≥0 × PointMeasure ℝ≥0)
    (Q : Measure Ωlimit) [IsProbabilityMeasure Q]
    (Z : Ωlimit → PointMeasure ℝ≥0 × PointMeasure ℝ≥0)
    (hprob : ∀ᶠj in atTop,IsProbabilityMeasure (μ j))
    (hX : ∀ᶠj in atTop,AEMeasurable (X j) (μ j))
    (hZ : AEMeasurable Z Q) (hLaw : LawConverges μ X Q Z)
    (hzero : ∀ᵐω ∂Q,(Z ω).2.toMeasure {0}=0) :
    LawConverges μ (fun j ω => clusterSuperposition F D hproper (X j ω))
      Q (fun ω => clusterSuperposition F D hproper (Z ω)) := by
  letI : MetrizableSpace (PointMeasure ℝ≥0) :=
    WP.External.pointMeasure_nnreal_vague_metrizable_secondCountable.1
  letI : SecondCountableTopology (PointMeasure ℝ≥0) :=
    WP.External.pointMeasure_nnreal_vague_metrizable_secondCountable.2
  apply C (PointMeasure ℝ≥0 × PointMeasure ℝ≥0) (PointMeasure ℝ≥0) Ω Ωlimit μ X Q Z
    (clusterSuperposition F D hproper) hprob hX hZ (clusterSuperposition_measurable F D hproper) _ hLaw
  filter_upwards [hzero] with ω hω
  exact clusterSuperposition_continuousAt_of_no_atom_zero F B D hproper (Z ω) hω

end WP.Critical.PantsCluster
