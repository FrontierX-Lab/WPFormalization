import WPFormalization.Analysis.TransportGammaComplexification
import WPFormalization.Intersection.CanonicalBackground
/-! All genuine finite Appendix C kernel inputs have holomorphic extensions
on a single convex parameter neighborhood. The finite canonical background
identity lifts every normalized PsiTheory amplitude, including critical and
invalid states, from actual normalized K coefficients. This provides the
bounded-component inputs; it asserts no all-order hierarchy compatibility
or Gevrey bound. -/
set_option maxHeartbeats 800000
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis

lemma HasPhysicalHolomorphicExtension.congr_physical {Ω : Set ℂ} {f g : ℝ → ℝ}
    (hf : HasPhysicalHolomorphicExtension Ω f) (he : ∀ Y∈Icc (0:ℝ) y₀,f Y=g Y) :
    HasPhysicalHolomorphicExtension Ω g := by
  obtain ⟨F,hF,hFr⟩ := hf
  exact ⟨F,hF,fun Y hY => (hFr Y hY).trans (congrArg Complex.ofReal (he Y hY))⟩

lemma HasPhysicalHolomorphicExtension.prod {Ω : Set ℂ} {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i,HasPhysicalHolomorphicExtension Ω (f i)) :
    HasPhysicalHolomorphicExtension Ω (fun Y => ∏ i∈s,f i Y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using HasPhysicalHolomorphicExtension.const Ω 1
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using (hf i).mul ih

lemma finiteBackgroundAmplitude_hasPhysicalHolomorphicExtension (Ω : Set ℂ)
    (P : PsiTheory) (g : ℕ) (d : List ℤ) {N : ℕ} (B m : ℕ) (t : ℝ → Fin N → ℝ)
    (ht : ∀ i,HasPhysicalHolomorphicExtension Ω (fun Y => t Y i)) :
    HasPhysicalHolomorphicExtension Ω (fun Y => finiteBackgroundAmplitude P g d B m (t Y)) := by
  unfold finiteBackgroundAmplitude
  apply HasPhysicalHolomorphicExtension.mul (HasPhysicalHolomorphicExtension.const Ω _)
  apply HasPhysicalHolomorphicExtension.sum
  intro l
  apply HasPhysicalHolomorphicExtension.mul (HasPhysicalHolomorphicExtension.const Ω _)
  exact HasPhysicalHolomorphicExtension.prod Finset.univ _
    (fun i => ((ht i).pow (l i)).div_const _)

lemma normalized_hasPhysicalHolomorphicExtension_of_kernel_coefficients (Ω : Set ℂ)
    (hK : ∀ n : ℕ,HasPhysicalHolomorphicExtension Ω (fun Y => realCoeff (barK Y) n))
    (P : PsiTheory) (g : ℕ) (d : List ℕ) :
    HasPhysicalHolomorphicExtension Ω (fun Y => normalized P g d Y) := by
  by_cases hs : Stable g d.length
  · by_cases hd : d.sum≤dimension g d.length
    · have ht (i : ℕ) : HasPhysicalHolomorphicExtension Ω (fun Y => normalizedBackgroundTime Y i) := by
        unfold normalizedBackgroundTime
        exact (HasPhysicalHolomorphicExtension.const Ω _).mul (hK (i+1))
      have hf := finiteBackgroundAmplitude_hasPhysicalHolomorphicExtension Ω P g (d.map Int.ofNat)
        (deficit g d) (deficit g d)
        (fun Y => fun i : Fin (deficit g d+1) => normalizedBackgroundTime Y i.val)
        (fun i => ht i.val)
      apply hf.congr_physical
      intro Y hY
      exact finiteBackgroundAmplitude_normalized_canonical P g d Y hY hs hd
        (deficit g d+1) (deficit g d) (by omega) (by omega) le_rfl
    · apply (HasPhysicalHolomorphicExtension.const Ω 0).congr_physical
      intro Y hY
      exact (normalized_excess P g d Y (by omega)).symm
  · apply (HasPhysicalHolomorphicExtension.const Ω 0).congr_physical
    intro Y hY
    exact (normalized_unstable P g d Y hs).symm

lemma normalized_real_kernel_coefficients_have_extensions (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R Ω) (hR0 : R (y₀:ℂ)=0)
    (hraw : ∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) (hunit : ∀ z∈Ω,complexAUnit z≠0) :
    ∀ n : ℕ,HasPhysicalHolomorphicExtension Ω (fun Y => realCoeff (barK Y) n) ∧
      HasPhysicalHolomorphicExtension Ω (fun Y => realCoeff (barH Y) n) := by
  have hc := normalized_coefficients_holomorphic_on_common_domain Ω hΩ hcover R hR hR0 hraw hunit
  intro n
  constructor
  · refine ⟨regularizedKernelCoeff K R n,(hc n).1,?_⟩
    intro Y hY
    rw [((hc n).2.2 Y hY).1]
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using barK_realCoefficients Y n
  · refine ⟨regularizedKernelCoeff H R n,(hc n).2.1,?_⟩
    intro Y hY
    rw [((hc n).2.2 Y hY).2]
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using barH_realCoefficients Y n

lemma canonicalDilatonCoefficient_hasPhysicalHolomorphicExtension (Ω : Set ℂ)
    (hH : ∀ n : ℕ,HasPhysicalHolomorphicExtension Ω (fun Y => realCoeff (barH Y) n)) (d : ℕ) :
    HasPhysicalHolomorphicExtension Ω (fun Y => canonicalDilatonCoefficient Y d) := by
  by_cases hd : 1≤d
  · simpa only [canonicalDilatonCoefficient,ite_eq_left hd] using (hH (d-1)).div_const 3
  · simpa only [canonicalDilatonCoefficient,ite_eq_right hd] using HasPhysicalHolomorphicExtension.const Ω 0

lemma common_holomorphic_finite_kernel_inputs :
    ∃ Ω : Set ℂ,IsOpen Ω ∧ Convex ℝ Ω ∧ (∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧
      HasPhysicalHolomorphicExtension Ω A ∧ HasPhysicalHolomorphicExtension Ω (fun Y => (A Y)⁻¹) ∧
      (∀ j : ℕ,HasPhysicalHolomorphicExtension Ω (WP.HigherOrder.kernelMoment j) ∧
        HasPhysicalHolomorphicExtension Ω (WP.HigherOrder.bMoment j)) ∧
      (∀ n : ℕ,HasPhysicalHolomorphicExtension Ω (fun Y => weight Y n) ∧
        HasPhysicalHolomorphicExtension Ω (fun Y => theta Y n) ∧
        HasPhysicalHolomorphicExtension Ω (fun Y => canonicalDilatonCoefficient Y n) ∧
        HasPhysicalHolomorphicExtension Ω (fun Y => realCoeff (barK Y) n) ∧
        HasPhysicalHolomorphicExtension Ω (fun Y => realCoeff (barH Y) n)) ∧
      (∀ (P : PsiTheory) (g : ℕ) (d : List ℕ),HasPhysicalHolomorphicExtension Ω (fun Y => normalized P g d Y)) := by
  obtain ⟨Ω,hΩ,hconv,hcover,R,Q,Ahat,hR,hQ,hA,hmatch,hmom,hcoeff,hunit,hraw,hR0,hR'⟩ :=
    common_holomorphic_all_kernel_moments
  have hreal := normalized_real_kernel_coefficients_have_extensions Ω hΩ hcover R hR hR0 hraw
    (fun z hz => (hunit z hz).2.2.1)
  refine ⟨Ω,hΩ,hconv,hcover,⟨Ahat,hA,fun Y hY => (hmatch Y hY).2⟩,?_,?_,?_,?_⟩
  · refine ⟨fun z => (Ahat z)⁻¹,fun z hz => (hA z hz).inv (hunit z hz).2.1,?_⟩
    intro Y hY
    dsimp only
    rw [(hmatch Y hY).2,Complex.ofReal_inv]
  · intro j
    exact ⟨⟨complexKernelMoment R j,(hmom j).2.1,fun Y hY => ((hmom j).2.2 Y hY).2⟩,
      ⟨complexBMoment R j,(hmom j).1,fun Y hY => ((hmom j).2.2 Y hY).1⟩⟩
  · intro n
    exact ⟨⟨complexWeightCoeff R n,(hcoeff n).2.1,fun Y hY => ((hcoeff n).2.2 Y hY).2⟩,
      ⟨complexThetaCoeff R n,(hcoeff n).1,fun Y hY => ((hcoeff n).2.2 Y hY).1⟩,
      canonicalDilatonCoefficient_hasPhysicalHolomorphicExtension Ω (fun j => (hreal j).2) n,
      (hreal n).1,(hreal n).2⟩
  · exact normalized_hasPhysicalHolomorphicExtension_of_kernel_coefficients Ω (fun n => (hreal n).1)
end WP.Analysis
