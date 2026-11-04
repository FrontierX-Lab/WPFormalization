import WPFormalization.Probability.TwoColorPointMeasuresLaws
import WPFormalization.Probability.PoissonClusterLaplace
/- Local calculation for a genuine PPP on a disjoint union. The two test
functions are arbitrary nonnegative bounded compactly supported Borel tests.
The only deferred result is the already registered generic Laplace formula;
no independence or paper convergence is added as an assumption. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace WP.Probability
open MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

lemma twoColorMeasure_integral_sumElim (ν μ : Measure ℝ≥0)
    (h k : ℝ≥0→ℝ) (hh : Measurable h) (hk : Measurable k)
    (hi : Integrable h ν) (ki : Integrable k μ) :
    (∫z,Sum.elim h k z ∂twoColorMeasure ν μ)=(∫x,h x ∂ν)+∫x,k x ∂μ := by
  have hm : Measurable (Sum.elim h k) := hh.sumElim hk
  have hl : Integrable (Sum.elim h k) (Measure.map Sum.inl ν) :=
    (integrable_map_measure hm.aestronglyMeasurable measurable_inl.aemeasurable).mpr hi
  have hr : Integrable (Sum.elim h k) (Measure.map Sum.inr μ) :=
    (integrable_map_measure hm.aestronglyMeasurable measurable_inr.aemeasurable).mpr ki
  rw [twoColorMeasure,integral_add_measure hl hr,
    integral_map measurable_inl.aemeasurable hm.aestronglyMeasurable,
    integral_map measurable_inr.aemeasurable hm.aestronglyMeasurable]
  rfl

lemma twoColor_sumElim_compact_support
    (h k : ℝ≥0→ℝ)
    (hs : ∃K : Set ℝ≥0,IsCompact K ∧ Function.support h⊆K)
    (ks : ∃K : Set ℝ≥0,IsCompact K ∧ Function.support k⊆K) :
    ∃K : Set TwoColorSpace,IsCompact K ∧ Function.support (Sum.elim h k)⊆K := by
  obtain ⟨H,hH,hHs⟩:=hs
  obtain ⟨K,hK,hKs⟩:=ks
  refine ⟨Sum.inl '' H ∪ Sum.inr '' K,(hH.image continuous_inl).union (hK.image continuous_inr),?_⟩
  intro z hz
  cases z with
  | inl x => exact Or.inl ⟨x,hHs hz,rfl⟩
  | inr x => exact Or.inr ⟨x,hKs hz,rfl⟩

lemma twoColorDecode_integral_sumElim (ξ : PointMeasure TwoColorSpace)
    (h k : ℝ≥0→ℝ) (hh : Measurable h) (hk : Measurable k)
    (hi : Integrable h (twoColorDecode ξ).1.toMeasure)
    (ki : Integrable k (twoColorDecode ξ).2.toMeasure) :
    (∫z,Sum.elim h k z ∂ξ.toMeasure)=
      (∫x,h x ∂(twoColorDecode ξ).1.toMeasure)+∫x,k x ∂(twoColorDecode ξ).2.toMeasure := by
  have he : ξ.toMeasure=twoColorMeasure (twoColorDecode ξ).1.toMeasure (twoColorDecode ξ).2.toMeasure := by
    exact congrArg PointMeasure.toMeasure (twoColorEncode_decode ξ).symm
  rw [he]
  exact twoColorMeasure_integral_sumElim _ _ h k hh hk hi ki

theorem twoColor_poisson_joint_laplace
    (ν μ : Measure ℝ≥0) [IsLocallyFiniteMeasure ν] [IsLocallyFiniteMeasure μ]
    (Q : ProbabilityMeasure (PointMeasure TwoColorSpace))
    (hQ : IsPoissonPointProcessLaw TwoColorSpace (twoColorMeasure ν μ) Q)
    (h k : ℝ≥0→ℝ) (hh : Measurable h) (hk : Measurable k)
    (hn : ∀x,0≤h x) (kn : ∀x,0≤k x)
    (hb : ∃C : ℝ,∀x,h x≤C) (kb : ∃C : ℝ,∀x,k x≤C)
    (hs : ∃K : Set ℝ≥0,IsCompact K ∧ Function.support h⊆K)
    (ks : ∃K : Set ℝ≥0,IsCompact K ∧ Function.support k⊆K) :
    (∫ξ,PoissonCluster.jointLaplaceObservable h k (twoColorDecode ξ) ∂Q)=
      Real.exp (-(∫x,1-Real.exp (-h x) ∂ν)-(∫x,1-Real.exp (-k x) ∂μ)) := by
  have hem : Measurable (Sum.elim h k) := hh.sumElim hk
  have hen : ∀z,0≤Sum.elim h k z := by intro z;cases z <;> simp [hn,kn]
  have heb : ∃C : ℝ,∀z,Sum.elim h k z≤C := by
    obtain ⟨A,hA⟩:=hb
    obtain ⟨B,hB⟩:=kb
    exact ⟨max A B,fun z=>by cases z with
      | inl x => exact (hA x).trans (le_max_left _ _)
      | inr x => exact (hB x).trans (le_max_right _ _)⟩
  have hes := twoColor_sumElim_compact_support h k hs ks
  have hp := (WP.External.poisson_laplace_functional TwoColorSpace
    (twoColorMeasure ν μ) Q hQ (Sum.elim h k) hem hen heb hes).2
  have hi : ∀ξ : PointMeasure ℝ≥0,Integrable h ξ.toMeasure := fun ξ=>
    PoissonCluster.integrable_of_bounded_nonneg_compact_support ξ.toMeasure h hh hn hb hs
  have ki : ∀ξ : PointMeasure ℝ≥0,Integrable k ξ.toMeasure := fun ξ=>
    PoissonCluster.integrable_of_bounded_nonneg_compact_support ξ.toMeasure k hk kn kb ks
  have hc : ∀ξ : PointMeasure TwoColorSpace,
      PoissonCluster.jointLaplaceObservable h k (twoColorDecode ξ)=
      Real.exp (-(∫z,Sum.elim h k z ∂ξ.toMeasure)) := by
    intro ξ
    rw [twoColorDecode_integral_sumElim ξ h k hh hk (hi _) (ki _)]
    simp only [PoissonCluster.jointLaplaceObservable]
    congr 1
    ring
  simp_rw [hc]
  rw [hp]
  let ch : ℝ≥0→ℝ:=fun x=>1-Real.exp (-h x)
  let ck : ℝ≥0→ℝ:=fun x=>1-Real.exp (-k x)
  have chm : Measurable ch := measurable_const.sub (hh.neg.exp)
  have ckm : Measurable ck := measurable_const.sub (hk.neg.exp)
  have chn : ∀x,0≤ch x := fun x=>sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hn x)))
  have ckn : ∀x,0≤ck x := fun x=>sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (kn x)))
  have chb : ∃C : ℝ,∀x,ch x≤C := ⟨1,fun x=>sub_le_self _ (Real.exp_nonneg _)⟩
  have ckb : ∃C : ℝ,∀x,ck x≤C := ⟨1,fun x=>sub_le_self _ (Real.exp_nonneg _)⟩
  have chs : ∃K : Set ℝ≥0,IsCompact K ∧ Function.support ch⊆K := by
    obtain ⟨K,hK,hKs⟩:=hs
    refine ⟨K,hK,fun x hx=>hKs ?_⟩
    contrapose! hx
    simp [ch,Function.notMem_support.mp hx]
  have cks : ∃K : Set ℝ≥0,IsCompact K ∧ Function.support ck⊆K := by
    obtain ⟨K,hK,hKs⟩:=ks
    refine ⟨K,hK,fun x hx=>hKs ?_⟩
    contrapose! hx
    simp [ck,Function.notMem_support.mp hx]
  have hci := PoissonCluster.integrable_of_bounded_nonneg_compact_support ν ch chm chn chb chs
  have kci := PoissonCluster.integrable_of_bounded_nonneg_compact_support μ ck ckm ckn ckb cks
  have he : (fun z : TwoColorSpace=>1-Real.exp (-Sum.elim h k z))=Sum.elim ch ck := by
    funext z;cases z <;> rfl
  rw [he,twoColorMeasure_integral_sumElim ν μ ch ck chm ckm hci kci]
  congr 1
  ring

end WP.Probability
