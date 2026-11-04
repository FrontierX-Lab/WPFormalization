import WPFormalization.HigherOrder.UnmarkedCuspSequence
import WPFormalization.Analysis.GevreyTwoSequenceShift
import WPFormalization.HigherOrder.EndpointInsertionMatching
import WPFormalization.HigherOrder.MarkedRelativeGevrey
import WPFormalization.Volumes.UnmarkedVolumeIdentity
/-! The actual unmarked-volume branch of Theorem 1.1. The exact reduction
is combined with the proved p=0 cusp expansion, the prescribed complexity
shift, the actual first marked model and the analytic square-root factor.
The resulting coefficients are canonicalUnmarkedSeries, with common
Gevrey-two bounds and optimal truncation; no coefficient family is replaced. -/
noncomputable section
namespace WP.HigherOrder
open Filter PowerSeries
open scoped Topology

lemma marked_volume_one_gevrey_two_sequence (P:PsiTheory):
    Analysis.GevreyTwoSequence (fun g=>(complexity g 1:ℝ))
      (fun g=>volumeModel P g 1/leadingVolume g 1)
      (PowerSeries.mk (fun j=>markedCoefficient P 1 j 0)):=by
  obtain ⟨C,B,c,H,hC,hB,hc,hH,herr⟩:=actual_marked_relative_uniform_gevrey_two P 1 (by norm_num)
  obtain ⟨N,hN⟩:=eventually_atTop.1 ((Analysis.complexity_real_tendsto_atTop 1).eventually (eventually_ge_atTop H))
  refine ⟨C,B,c,max N 2,hC,hB,hc,?_⟩
  intro g hg
  have hh:H≤(complexity g 1:ℝ):=hN g ((le_max_left _ _).trans hg)
  refine ⟨hH.trans_le hh,?_⟩
  intro K hK
  dsimp only at hK ⊢
  rw[volume_one_over_leading P g ((le_max_right _ _).trans hg)]
  simpa only[Analysis.inversePowerTruncation,PowerSeries.coeff_mk,XR_zero] using
    herr g K hh hK 0 ⟨le_rfl,y₀_pos⟩

lemma unmarked_sqrt_gevrey_two_sequence:
    Analysis.GevreyTwoSequence (fun g=>(complexity g 1:ℝ))
      (fun g=>Real.sqrt (1+1/(complexity g 1:ℝ))) (binomial (1/2)):=by
  have hs:=Analysis.complexity_real_tendsto_atTop 1
  have hG1:=Analysis.GevreyOneSequence.of_real _ hs _ _ (endpointInsertionFactor_gevrey 1)
  have hf:endpointInsertion 1=binomial (1/2):=by simp[endpointInsertion]
  have hfunc:(fun g:ℕ=>endpointInsertionFactor (complexity g 1:ℝ) 1)=
      (fun g:ℕ=>Real.sqrt (1+1/(complexity g 1:ℝ))):=by funext g;simp[endpointInsertionFactor]
  rw[hf,hfunc] at hG1
  exact Analysis.GevreyTwoSequence.of_gevreyOne _ _ hs _ hG1

lemma unmarked_cusp_shifted_gevrey_two_sequence (P:PsiTheory):
    Analysis.GevreyTwoSequence (fun g=>(complexity g 1:ℝ))
      (fun g=>cuspCorrection P g 0 0) (complexityShift 1 (formalCusp P 0 0)):=by
  have hshift:=Analysis.GevreyTwoSequence.shift _ _ (Analysis.complexity_real_tendsto_atTop 0) _
    (unmarked_cusp_gevrey_two_sequence P) 1
  apply Analysis.GevreyTwoSequence.congr_scale _ _ _ _ hshift
  filter_upwards[eventually_ge_atTop 2] with g hg
  have he:complexity g 0+1=complexity g 1:=by unfold complexity;omega
  simpa only[Nat.cast_add,Nat.cast_one] using congrArg (fun n:ℕ=>(n:ℝ)) he

lemma unmarked_volume_gevrey_two_sequence (P:PsiTheory):
    Analysis.GevreyTwoSequence (fun g=>(complexity g 1:ℝ))
      (fun g=>volumeModel P g 0/leadingVolume g 0) (canonicalUnmarkedSeries P):=by
  have hs:=Analysis.complexity_real_tendsto_atTop 1
  have h₁:=Analysis.GevreyTwoSequence.mul _ _ _ hs _ _
    unmarked_sqrt_gevrey_two_sequence (unmarked_cusp_shifted_gevrey_two_sequence P)
  have h₂:=Analysis.GevreyTwoSequence.mul _ _ _ hs _ _ h₁ (marked_volume_one_gevrey_two_sequence P)
  change Analysis.GevreyTwoSequence _
    (fun g=>Real.sqrt (1+1/(complexity g 1:ℝ))*cuspCorrection P g 0 0*
      (volumeModel P g 1/leadingVolume g 1)) (canonicalUnmarkedSeries P) at h₂
  apply Analysis.GevreyTwoSequence.congr _ _ _ _ h₂
  filter_upwards[eventually_ge_atTop 2] with g hg
  have hc:(complexity g 1:ℝ)=2*(g:ℝ)-1:=by
    unfold complexity
    rw[Nat.cast_sub (by omega)]
    push_cast
    ring
  simpa only[hc] using (volume_ratio_unmarked_product P g hg).symm
lemma unmarked_absolute_expansion_proof (P:PsiTheory):
    ∃C B c:ℝ,0<C ∧ 0<B ∧ 0<c ∧ ∃G:ℕ,0<G ∧
      (∀j:ℕ,|unmarkedCoefficient P j|≤C*B^j*(j.factorial:ℝ)^2) ∧
      (∀g:ℕ,G≤g→∀K:ℕ,(K:ℝ)≤c*Real.sqrt (complexity g 1:ℝ)→
        |volumeModel P g 0/leadingVolume g 0-
          ∑j∈Finset.range (K+1),unmarkedCoefficient P j/(complexity g 1:ℝ)^j|≤
            C*B^(K+1)*((K+1).factorial:ℝ)^2/(complexity g 1:ℝ)^(K+1)) ∧
      (∃c' a:ℝ,0<c' ∧ c'≤c ∧ 0<a ∧ ∀g:ℕ,G≤g→
        |volumeModel P g 0/leadingVolume g 0-
          ∑j∈Finset.range (⌊c'*Real.sqrt (complexity g 1:ℝ)⌋₊+1),
            unmarkedCoefficient P j/(complexity g 1:ℝ)^j|≤
              C*Real.exp (-a*Real.sqrt (complexity g 1:ℝ))):=by
  have hF:=unmarked_volume_gevrey_two_sequence P
  have hs:=Analysis.complexity_real_tendsto_atTop 1
  obtain ⟨Cf,Bf,hCf,hBf,hcoeff⟩:=Analysis.GevreyTwoSequence.coeff_bound _ _ hs _ hF
  obtain ⟨Ce,Be,c,N,hCe,hBe,hc,herr⟩:=hF
  let C:ℝ:=Cf+Ce
  let B:ℝ:=Bf+Be
  have hC:0<C:=by dsimp[C];positivity
  have hB:0<B:=by dsimp[B];positivity
  have hCfC:Cf≤C:=by dsimp[C];linarith
  have hCeC:Ce≤C:=by dsimp[C];linarith
  have hBfB:Bf≤B:=by dsimp[B];linarith
  have hBeB:Be≤B:=by dsimp[B];linarith
  have hcoeffAll:∀j:ℕ,|unmarkedCoefficient P j|≤C*B^j*(j.factorial:ℝ)^2:=by
    intro j
    apply (hcoeff j).trans
    change Cf*Bf^j*(j.factorial:ℝ)^2≤_
    gcongr
  have herrAll:∀g:ℕ,N≤g→∀K:ℕ,(K:ℝ)≤c*Real.sqrt (complexity g 1:ℝ)→
      |volumeModel P g 0/leadingVolume g 0-
        ∑j∈Finset.range (K+1),unmarkedCoefficient P j/(complexity g 1:ℝ)^j|≤
          C*B^(K+1)*((K+1).factorial:ℝ)^2/(complexity g 1:ℝ)^(K+1):=by
    intro g hg K hK
    have he:=(herr g hg).2 K hK
    change |volumeModel P g 0/leadingVolume g 0-
      ∑j∈Finset.range (K+1),unmarkedCoefficient P j/(complexity g 1:ℝ)^j|≤_ at he
    apply he.trans
    gcongr
  obtain ⟨c',a,H,hc',hc'c,ha,hH,hopt⟩:=Analysis.gevreyTwo_optimal_scalar B c hB hc
  obtain ⟨N₁,hN₁⟩:=eventually_atTop.1 (hs.eventually (eventually_ge_atTop H))
  let G:ℕ:=max N (max N₁ 2)
  refine ⟨C,B,c,hC,hB,hc,G,by dsimp[G];omega,hcoeffAll,
    fun g hg=>herrAll g ((le_max_left _ _).trans hg),c',a,hc',hc'c,ha,?_⟩
  intro g hg
  have hgN:N≤g:=(le_max_left _ _).trans hg
  have hg₁:N₁≤g:=((le_max_left _ _).trans (le_max_right _ _)).trans hg
  let h:ℝ:=complexity g 1
  let K:ℕ:=⌊c'*Real.sqrt h⌋₊
  have hK:(K:ℝ)≤c*Real.sqrt h:=
    (Nat.floor_le (mul_nonneg hc'.le (Real.sqrt_nonneg h))).trans
      (mul_le_mul_of_nonneg_right hc'c (Real.sqrt_nonneg h))
  have he:=herrAll g hgN K hK
  have ht:=hopt h (hN₁ g hg₁)
  change B^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)≤Real.exp (-a*Real.sqrt h) at ht
  apply he.trans
  convert mul_le_mul_of_nonneg_left ht hC.le using 1 <;>ring
end WP.HigherOrder
