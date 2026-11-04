import WPFormalization.Probability.PoissonClusterDefinitions
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
noncomputable section
set_option maxHeartbeats 0
universe u
namespace WP.Probability.PoissonCluster
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Classical
variable {J : Type u}

def indexedKernelMeasure (length : J→ℝ≥0→ℝ≥0) (s : ℝ≥0) : Measure ℝ≥0 :=
  Measure.sum (fun γ : J=>Measure.dirac (length γ s))

lemma indexedKernelMeasure_lintegral (length : J→ℝ≥0→ℝ≥0) (s : ℝ≥0)
    (f : ℝ≥0→ℝ≥0∞) :
    (∫⁻x,f x ∂indexedKernelMeasure length s)=∑'γ,f (length γ s) := by
  simp only [indexedKernelMeasure,lintegral_sum_measure,lintegral_dirac]

lemma indexedClusterMeasure_lintegral [Countable J] (length : J→ℝ≥0→ℝ≥0)
    (hlength : ∀γ,Measurable (length γ)) (ξ : Measure ℝ≥0)
    (f : ℝ≥0→ℝ≥0∞) (hf : Measurable f) :
    (∫⁻x,f x ∂indexedClusterMeasure length ξ)=
      ∫⁻s,(∫⁻x,f x ∂indexedKernelMeasure length s) ∂ξ.restrict (Ioi (0:ℝ≥0)) := by
  rw [indexedClusterMeasure,lintegral_sum_measure]
  simp_rw [lintegral_map hf (hlength _),indexedKernelMeasure_lintegral]
  exact (lintegral_tsum (fun γ=>(hf.comp (hlength γ)).aemeasurable)).symm

lemma indexedClusterMeasure_apply [Countable J] (length : J→ℝ≥0→ℝ≥0)
    (hlength : ∀γ,Measurable (length γ)) (ξ : Measure ℝ≥0)
    (B : Set ℝ≥0) (hB : MeasurableSet B) :
    indexedClusterMeasure length ξ B=
      ∫⁻s,indexedKernelMeasure length s B ∂ξ.restrict (Ioi (0:ℝ≥0)) := by
  have h:=indexedClusterMeasure_lintegral length hlength ξ (B.indicator (fun _=>1))
    (measurable_const.indicator hB)
  simpa only [lintegral_indicator_fun_one hB] using h

lemma indexedKernelMeasure_eq_zero_iff (length : J→ℝ≥0→ℝ≥0) (s : ℝ≥0)
    (B : Set ℝ≥0) (hB : MeasurableSet B) :
    indexedKernelMeasure length s B=0 ↔ ∀γ,length γ s∉B := by
  rw [indexedKernelMeasure,Measure.sum_apply _ hB,ENNReal.tsum_eq_zero]
  constructor
  · intro h γ hγ
    simpa [Measure.dirac_apply' _ hB,hγ] using h γ
  · intro h γ
    simp [Measure.dirac_apply' _ hB,h γ]

lemma finite_ennreal_sum_integer {a : J→ℝ≥0∞} (ha : (∑'j,a j)≠∞)
    (hi : ∀j,∃n : ℕ,a j=n) : ∃n : ℕ,(∑'j,a j)=n := by
  classical
  choose n hn using hi
  have hs : (Function.support a).Finite :=
    (ENNReal.finite_const_le_of_tsum_ne_top ha (by norm_num : (1:ℝ≥0∞)≠0)).subset (by
      intro j hj
      change a j≠0 at hj
      change 1≤a j
      have hj' : (n j:ℝ≥0∞)≠0 := by simpa only [←hn j] using hj
      have hn' : n j≠0 := by exact_mod_cast hj'
      rw [hn j]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn')
  refine ⟨∑j ∈ hs.toFinset,n j,?_⟩
  rw [tsum_eq_sum (s:=hs.toFinset) (fun j hj=>by
    simpa only [Set.Finite.mem_toFinset,Function.mem_support,not_not] using hj)]
  simp only [hn,Nat.cast_sum]

lemma isCompact_nnreal_prefix (L : ℝ≥0) : IsCompact (Iic L : Set ℝ≥0) := by
  have he : (Iic L : Set ℝ≥0)=Icc (0:ℝ≥0) L := by ext x;simp
  rw [he]
  exact isCompact_Icc

lemma indexedClusterMeasure_prefix_le [Countable J] (length : J→ℝ≥0→ℝ≥0)
    (hlength : ∀γ,Measurable (length γ)) (ξ : PointMeasure ℝ≥0) (L : ℝ≥0)
    (C : ℝ≥0∞) (hC : ∀s : ℝ≥0,0<s→indexedKernelMeasure length s (Iic L)≤C)
    (hproper : ∀s : ℝ≥0,2*L<s→indexedKernelMeasure length s (Iic L)=0) :
    indexedClusterMeasure length ξ.toMeasure (Iic L)≤C*ξ.toMeasure (Iic (2*L)) := by
  rw [indexedClusterMeasure_apply length hlength ξ.toMeasure _ measurableSet_Iic]
  calc
    _≤∫⁻s,(Iic (2*L)).indicator (fun _=>C) s ∂ξ.toMeasure.restrict (Ioi (0:ℝ≥0)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      by_cases hb : s≤2*L
      · simpa [Set.indicator,Set.mem_Iic,hb] using hC s hs
      · simp [hproper s (lt_of_not_ge hb),Set.indicator,Set.mem_Iic,hb]
    _=C*(ξ.toMeasure.restrict (Ioi (0:ℝ≥0))) (Iic (2*L)) :=
      lintegral_indicator_const measurableSet_Iic C
    _≤C*ξ.toMeasure (Iic (2*L)) := mul_le_mul le_rfl (Measure.restrict_apply_le _ _) (by positivity) (by positivity)

lemma indexedClusterMeasure_locallyFinite [Countable J] (length : J→ℝ≥0→ℝ≥0)
    (hlength : ∀γ,Measurable (length γ)) (ξ : PointMeasure ℝ≥0)
    (hbound : ∀L : ℝ≥0,∃C : ℝ≥0∞,C<∞ ∧
      ∀s : ℝ≥0,0<s→indexedKernelMeasure length s (Iic L)≤C)
    (hproper : ∀(L s : ℝ≥0),2*L<s→indexedKernelMeasure length s (Iic L)=0) :
    IsLocallyFiniteMeasure (indexedClusterMeasure length ξ.toMeasure) := by
  constructor
  intro x
  obtain ⟨C,hC,hbound⟩:=hbound (x+1)
  refine ⟨Iic (x+1),Iic_mem_nhds (by simp),?_⟩
  exact (indexedClusterMeasure_prefix_le length hlength ξ (x+1) C hbound (hproper _)).trans_lt
    (ENNReal.mul_lt_top hC (isCompact_nnreal_prefix _).measure_lt_top)


lemma indexedClusterMeasure_integerOnRelCompact [Countable J] (length : J→ℝ≥0→ℝ≥0)
    (hlength : ∀γ,Measurable (length γ)) (ξ : PointMeasure ℝ≥0)
    (hbound : ∀L : ℝ≥0,∃C : ℝ≥0∞,C<∞ ∧
      ∀s : ℝ≥0,0<s→indexedKernelMeasure length s (Iic L)≤C)
    (hproper : ∀(L s : ℝ≥0),2*L<s→indexedKernelMeasure length s (Iic L)=0)
    (B : Set ℝ≥0) (hB : MeasurableSet B) (hcompact : IsCompact (closure B)) :
    ∃n : ℕ,indexedClusterMeasure length ξ.toMeasure B=n := by
  letI:=indexedClusterMeasure_locallyFinite length hlength ξ hbound hproper
  have hfinite : indexedClusterMeasure length ξ.toMeasure B<∞ :=
    (measure_mono subset_closure).trans_lt hcompact.measure_lt_top
  obtain ⟨L,hL⟩:=hcompact.bddAbove
  have hsum : (∑'γ : J,((ξ.toMeasure.restrict (Ioi (0:ℝ≥0))).map (length γ)) B)≠∞ := by
    simpa only [indexedClusterMeasure,Measure.sum_apply _ hB] using hfinite.ne
  have hint (γ : J) : ∃n : ℕ,((ξ.toMeasure.restrict (Ioi (0:ℝ≥0))).map (length γ)) B=n := by
    let S : Set ℝ≥0:=(length γ) ⁻¹' B ∩ Ioi (0:ℝ≥0)
    have hS : MeasurableSet S:=(hB.preimage (hlength γ)).inter measurableSet_Ioi
    have hSsub : S⊆Iic (2*L) := by
      intro s hs
      by_contra hnot
      have hz:=hproper L s (lt_of_not_ge hnot)
      have hno:=(indexedKernelMeasure_eq_zero_iff length s _ measurableSet_Iic).mp hz γ
      exact hno (hL (subset_closure hs.1))
    have hSc : IsCompact (closure S) := (isCompact_nnreal_prefix (2*L)).of_isClosed_subset
      isClosed_closure (closure_minimal hSsub isClosed_Iic)
    obtain ⟨n,hn⟩:=ξ.integerOnRelCompact S hS hSc
    refine ⟨n,?_⟩
    rw [Measure.map_apply (hlength γ) hB,Measure.restrict_apply (hB.preimage (hlength γ))]
    exact hn
  simpa only [indexedClusterMeasure,Measure.sum_apply _ hB] using finite_ennreal_sum_integer hsum hint

def indexedClusterPointMeasure [Countable J] (length : J→ℝ≥0→ℝ≥0)
    (hlength : ∀γ,Measurable (length γ)) (ξ : PointMeasure ℝ≥0)
    (hbound : ∀L : ℝ≥0,∃C : ℝ≥0∞,C<∞ ∧
      ∀s : ℝ≥0,0<s→indexedKernelMeasure length s (Iic L)≤C)
    (hproper : ∀(L s : ℝ≥0),2*L<s→indexedKernelMeasure length s (Iic L)=0) :
    PointMeasure ℝ≥0 where
  toMeasure:=indexedClusterMeasure length ξ.toMeasure
  locallyFinite:=indexedClusterMeasure_locallyFinite length hlength ξ hbound hproper
  regular:=by
    letI:=indexedClusterMeasure_locallyFinite length hlength ξ hbound hproper
    infer_instance
  integerOnRelCompact:=indexedClusterMeasure_integerOnRelCompact length hlength ξ hbound hproper

end WP.Probability.PoissonCluster
