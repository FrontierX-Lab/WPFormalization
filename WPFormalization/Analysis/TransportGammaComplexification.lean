import WPFormalization.Analysis.WeightMomentComplexification
import WPFormalization.HigherOrder.CriticalGamma
/-! The actual finite Appendix C transport coefficient is lifted by finite
algebra from the proved common holomorphic kernel data. Its genuine critical
zero and the simple zero of the analytic root branch give a removable
holomorphic quotient by A*r. Real analytic, continuous and uniformly bounded
extensions retain the original quotient on the physical interior only.
No continuity claim is made for the totalized raw quotient at criticality. -/
set_option maxHeartbeats 800000
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace WP.Analysis

def HasPhysicalHolomorphicExtension (Ω : Set ℂ) (f : ℝ → ℝ) : Prop :=
  ∃ F : ℂ → ℂ,AnalyticOnNhd ℂ F Ω ∧ ∀ Y∈Icc (0:ℝ) y₀,F (Y:ℂ)=(f Y:ℂ)

namespace HasPhysicalHolomorphicExtension
lemma const (Ω : Set ℂ) (c : ℝ) : HasPhysicalHolomorphicExtension Ω (fun _ => c) :=
  ⟨fun _ => (c:ℂ),analyticOnNhd_const,fun _ _ => rfl⟩
lemma add {Ω : Set ℂ} {f g : ℝ → ℝ} (hf : HasPhysicalHolomorphicExtension Ω f)
    (hg : HasPhysicalHolomorphicExtension Ω g) : HasPhysicalHolomorphicExtension Ω (fun Y => f Y+g Y) := by
  obtain ⟨F,hF,hFr⟩ := hf
  obtain ⟨G,hG,hGr⟩ := hg
  refine ⟨fun z => F z+G z,fun z hz => (hF z hz).add (hG z hz),?_⟩
  intro Y hY
  dsimp only
  rw [hFr Y hY,hGr Y hY,Complex.ofReal_add]
lemma sub {Ω : Set ℂ} {f g : ℝ → ℝ} (hf : HasPhysicalHolomorphicExtension Ω f)
    (hg : HasPhysicalHolomorphicExtension Ω g) : HasPhysicalHolomorphicExtension Ω (fun Y => f Y-g Y) := by
  obtain ⟨F,hF,hFr⟩ := hf
  obtain ⟨G,hG,hGr⟩ := hg
  refine ⟨fun z => F z-G z,fun z hz => (hF z hz).sub (hG z hz),?_⟩
  intro Y hY
  dsimp only
  rw [hFr Y hY,hGr Y hY,Complex.ofReal_sub]
lemma mul {Ω : Set ℂ} {f g : ℝ → ℝ} (hf : HasPhysicalHolomorphicExtension Ω f)
    (hg : HasPhysicalHolomorphicExtension Ω g) : HasPhysicalHolomorphicExtension Ω (fun Y => f Y*g Y) := by
  obtain ⟨F,hF,hFr⟩ := hf
  obtain ⟨G,hG,hGr⟩ := hg
  refine ⟨fun z => F z*G z,fun z hz => (hF z hz).mul (hG z hz),?_⟩
  intro Y hY
  dsimp only
  rw [hFr Y hY,hGr Y hY,Complex.ofReal_mul]
lemma neg {Ω : Set ℂ} {f : ℝ → ℝ} (hf : HasPhysicalHolomorphicExtension Ω f) :
    HasPhysicalHolomorphicExtension Ω (fun Y => -f Y) := by
  obtain ⟨F,hF,hFr⟩ := hf
  refine ⟨fun z => -F z,fun z hz => (hF z hz).neg,?_⟩
  intro Y hY
  dsimp only
  rw [hFr Y hY,Complex.ofReal_neg]
lemma pow {Ω : Set ℂ} {f : ℝ → ℝ} (hf : HasPhysicalHolomorphicExtension Ω f) (n : ℕ) :
    HasPhysicalHolomorphicExtension Ω (fun Y => f Y^n) := by
  obtain ⟨F,hF,hFr⟩ := hf
  refine ⟨fun z => F z^n,fun z hz => (hF z hz).pow n,?_⟩
  intro Y hY
  dsimp only
  rw [hFr Y hY,Complex.ofReal_pow]
lemma div_const {Ω : Set ℂ} {f : ℝ → ℝ} (hf : HasPhysicalHolomorphicExtension Ω f) (c : ℝ) :
    HasPhysicalHolomorphicExtension Ω (fun Y => f Y/c) := by
  simpa only [div_eq_mul_inv] using hf.mul (const Ω c⁻¹)
lemma ite {Ω : Set ℂ} (b : Prop) [Decidable b] {f g : ℝ → ℝ}
    (hf : HasPhysicalHolomorphicExtension Ω f) (hg : HasPhysicalHolomorphicExtension Ω g) :
    HasPhysicalHolomorphicExtension Ω (fun Y => if b then f Y else g Y) := by
  by_cases h : b
  · simpa only [if_pos h] using hf
  · simpa only [if_neg h] using hg
lemma sum {Ω : Set ℂ} {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i,HasPhysicalHolomorphicExtension Ω (f i)) :
    HasPhysicalHolomorphicExtension Ω (fun Y => ∑ i∈s,f i Y) := by
  classical
  choose F hF hFr using hf
  refine ⟨fun z => ∑ i∈s,F i z,?_,?_⟩
  · intro z hz
    apply Finset.analyticAt_fun_sum
    intro i hi
    exact hF i z hz
  intro Y hY
  dsimp only
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  exact hFr i Y hY
end HasPhysicalHolomorphicExtension

def HasPolynomialPhysicalExtension (Ω : Set ℂ) (f : ℝ → Polynomial ℝ) : Prop :=
  ∀ n,HasPhysicalHolomorphicExtension Ω (fun Y => (f Y).coeff n)
namespace HasPolynomialPhysicalExtension
lemma const (Ω : Set ℂ) (p : Polynomial ℝ) : HasPolynomialPhysicalExtension Ω (fun _ => p) :=
  fun n => HasPhysicalHolomorphicExtension.const Ω (p.coeff n)
lemma C {Ω : Set ℂ} {f : ℝ → ℝ} (hf : HasPhysicalHolomorphicExtension Ω f) :
    HasPolynomialPhysicalExtension Ω (fun Y => Polynomial.C (f Y)) := by
  intro n
  by_cases hn : n=0
  · subst n
    simpa only [Polynomial.coeff_C,ite_true] using hf
  · have he : (fun Y => (Polynomial.C (f Y)).coeff n)=(fun _ => (0:ℝ)) := by
      funext Y
      simp only [Polynomial.coeff_C,ite_eq_right hn]
    rw [he]
    exact HasPhysicalHolomorphicExtension.const Ω 0
lemma add {Ω : Set ℂ} {f g : ℝ → Polynomial ℝ} (hf : HasPolynomialPhysicalExtension Ω f)
    (hg : HasPolynomialPhysicalExtension Ω g) : HasPolynomialPhysicalExtension Ω (fun Y => f Y+g Y) := by
  intro n
  simpa only [Polynomial.coeff_add] using (hf n).add (hg n)
lemma sub {Ω : Set ℂ} {f g : ℝ → Polynomial ℝ} (hf : HasPolynomialPhysicalExtension Ω f)
    (hg : HasPolynomialPhysicalExtension Ω g) : HasPolynomialPhysicalExtension Ω (fun Y => f Y-g Y) := by
  intro n
  simpa only [Polynomial.coeff_sub] using (hf n).sub (hg n)
lemma mul {Ω : Set ℂ} {f g : ℝ → Polynomial ℝ} (hf : HasPolynomialPhysicalExtension Ω f)
    (hg : HasPolynomialPhysicalExtension Ω g) : HasPolynomialPhysicalExtension Ω (fun Y => f Y*g Y) := by
  intro n
  simpa only [Polynomial.coeff_mul] using HasPhysicalHolomorphicExtension.sum
    (Finset.HasAntidiagonal.antidiagonal n) (fun i Y => (f Y).coeff i.1*(g Y).coeff i.2)
    (fun i => (hf i.1).mul (hg i.2))
lemma pow {Ω : Set ℂ} {f : ℝ → Polynomial ℝ} (hf : HasPolynomialPhysicalExtension Ω f) (n : ℕ) :
    HasPolynomialPhysicalExtension Ω (fun Y => f Y^n) := by
  induction n with
  | zero => simpa only [pow_zero] using const Ω 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf
end HasPolynomialPhysicalExtension

end WP.Analysis
namespace WP.Analysis
open WP.HigherOrder
lemma transportGamma_hasPhysicalHolomorphicExtension (Ω : Set ℂ)
    (hA : HasPhysicalHolomorphicExtension Ω A)
    (hAi : HasPhysicalHolomorphicExtension Ω (fun Y => (A Y)⁻¹))
    (hQ : HasPhysicalHolomorphicExtension Ω Theta)
    (hM : ∀ j,HasPhysicalHolomorphicExtension Ω (WP.HigherOrder.kernelMoment j))
    (hB : ∀ j,HasPhysicalHolomorphicExtension Ω (bMoment j))
    (hθ : ∀ n,HasPhysicalHolomorphicExtension Ω (fun Y => theta Y n))
    (hw : ∀ n,HasPhysicalHolomorphicExtension Ω (fun Y => weight Y n)) (p : ℕ) :
    HasPhysicalHolomorphicExtension Ω (transportGamma p) := by
  have hM1 : HasPhysicalHolomorphicExtension Ω moment₁ := by
    have he : WP.HigherOrder.kernelMoment 1=moment₁ := funext kernelMoment_one
    simpa only [he] using hM 1
  have hβ (q : ℕ) : HasPhysicalHolomorphicExtension Ω (transportBeta q) := by
    unfold transportBeta
    apply_rules (maxDepth := 300) only [hA,hQ,hM1,
      HasPhysicalHolomorphicExtension.neg,HasPhysicalHolomorphicExtension.const,HasPhysicalHolomorphicExtension.add,HasPhysicalHolomorphicExtension.sub,
      HasPhysicalHolomorphicExtension.mul,HasPhysicalHolomorphicExtension.div_const]
  have hα (q : ℕ) : HasPhysicalHolomorphicExtension Ω (alpha q) := by
    unfold alpha
    apply_rules (maxDepth := 300) only [hA,hQ,hM1,
      HasPhysicalHolomorphicExtension.neg,HasPhysicalHolomorphicExtension.const,HasPhysicalHolomorphicExtension.add,HasPhysicalHolomorphicExtension.sub,
      HasPhysicalHolomorphicExtension.mul,HasPhysicalHolomorphicExtension.div_const]
  have hC (q : ℕ) : HasPolynomialPhysicalExtension Ω (cubicIncrement q) := by
    unfold cubicIncrement
    dsimp only
    apply_rules (maxDepth := 300) only [hA,hQ,hM1,hM,hβ,hα,hθ,hw,
      HasPolynomialPhysicalExtension.const,HasPolynomialPhysicalExtension.C,HasPolynomialPhysicalExtension.add,
      HasPolynomialPhysicalExtension.sub,HasPolynomialPhysicalExtension.mul,HasPolynomialPhysicalExtension.pow,
      HasPhysicalHolomorphicExtension.neg,HasPhysicalHolomorphicExtension.const,HasPhysicalHolomorphicExtension.add,HasPhysicalHolomorphicExtension.sub,
      HasPhysicalHolomorphicExtension.mul,HasPhysicalHolomorphicExtension.div_const,HasPhysicalHolomorphicExtension.neg]
  have hSig (q : ℕ) : HasPhysicalHolomorphicExtension Ω (sigmaB q) := by
    unfold sigmaB
    dsimp only
    apply_rules (maxDepth := 300) only [hC,hB,
      HasPhysicalHolomorphicExtension.neg,HasPhysicalHolomorphicExtension.const,HasPhysicalHolomorphicExtension.add,HasPhysicalHolomorphicExtension.sub,
      HasPhysicalHolomorphicExtension.mul,HasPhysicalHolomorphicExtension.div_const]
  have hR (q : ℕ) (k : ℝ) : HasPhysicalHolomorphicExtension Ω (fun Y => rInfinity q Y k) := by
    unfold rInfinity
    apply_rules (maxDepth := 300) only [hA,hQ,hM1,hβ,
      HasPhysicalHolomorphicExtension.neg,HasPhysicalHolomorphicExtension.const,HasPhysicalHolomorphicExtension.add,HasPhysicalHolomorphicExtension.sub,
      HasPhysicalHolomorphicExtension.mul,HasPhysicalHolomorphicExtension.div_const]
  have hS (q : ℕ) (k : ℝ) : HasPhysicalHolomorphicExtension Ω (fun Y => sInfinity q Y k) := by
    unfold sInfinity
    apply_rules (maxDepth := 300) only [hA,hQ,hM1,hβ,hα,
      HasPhysicalHolomorphicExtension.neg,HasPhysicalHolomorphicExtension.const,HasPhysicalHolomorphicExtension.add,HasPhysicalHolomorphicExtension.sub,
      HasPhysicalHolomorphicExtension.mul,HasPhysicalHolomorphicExtension.div_const]
  have hΔ (q t : ℕ) : HasPhysicalHolomorphicExtension Ω (exceptionalIncrement q t) := by
    unfold exceptionalIncrement
    apply_rules (maxDepth := 300) only [hA,hw,hθ,hR,hS,
      HasPhysicalHolomorphicExtension.neg,HasPhysicalHolomorphicExtension.const,HasPhysicalHolomorphicExtension.add,HasPhysicalHolomorphicExtension.sub,
      HasPhysicalHolomorphicExtension.mul,HasPhysicalHolomorphicExtension.div_const,HasPhysicalHolomorphicExtension.pow,
      HasPhysicalHolomorphicExtension.neg,HasPhysicalHolomorphicExtension.ite,HasPhysicalHolomorphicExtension.sum]
    all_goals
      intro i
      first | exact (hw i).mul (hR q _) | exact (hw i).mul (hS q _)
  unfold transportGamma
  simp only [div_eq_mul_inv]
  apply_rules (maxDepth := 300) only [hA,hAi,hβ,hSig,hΔ,hθ,
    HasPhysicalHolomorphicExtension.neg,HasPhysicalHolomorphicExtension.const,HasPhysicalHolomorphicExtension.add,HasPhysicalHolomorphicExtension.sub,
    HasPhysicalHolomorphicExtension.mul,HasPhysicalHolomorphicExtension.pow]
end WP.Analysis
namespace WP.Analysis
open WP.HigherOrder
lemma transportGamma_quotient_complex_extension (p : ℕ) :
    ∃ Ω : Set ℂ,IsOpen Ω ∧ (∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧
      ∃ F : ℂ → ℂ,AnalyticOnNhd ℂ F Ω ∧
        ∀ Y∈Ico (0:ℝ) y₀,F (Y:ℂ)=((transportGamma p Y/(A Y*r Y):ℝ):ℂ) := by
  obtain ⟨U,hU,hconv,hcover,R,Q,Ahat,hR,hQ,hA,hmatch,hmom,hcoeff,hunit,hraw,hR0,hR'⟩ :=
    common_holomorphic_all_kernel_moments
  have hAe : HasPhysicalHolomorphicExtension U A := ⟨Ahat,hA,fun Y hY => (hmatch Y hY).2⟩
  have hAie : HasPhysicalHolomorphicExtension U (fun Y => (A Y)⁻¹) := by
    refine ⟨fun z => (Ahat z)⁻¹,fun z hz => (hA z hz).inv (hunit z hz).2.1,?_⟩
    intro Y hY
    dsimp only
    rw [(hmatch Y hY).2,Complex.ofReal_inv]
  have hQe : HasPhysicalHolomorphicExtension U Theta := ⟨Q,hQ,fun Y hY => (hmatch Y hY).1⟩
  have hMe (j : ℕ) : HasPhysicalHolomorphicExtension U (WP.HigherOrder.kernelMoment j) :=
    ⟨complexKernelMoment R j,(hmom j).2.1,fun Y hY => ((hmom j).2.2 Y hY).2⟩
  have hBe (j : ℕ) : HasPhysicalHolomorphicExtension U (bMoment j) :=
    ⟨complexBMoment R j,(hmom j).1,fun Y hY => ((hmom j).2.2 Y hY).1⟩
  have hθe (n : ℕ) : HasPhysicalHolomorphicExtension U (fun Y => theta Y n) :=
    ⟨complexThetaCoeff R n,(hcoeff n).1,fun Y hY => ((hcoeff n).2.2 Y hY).1⟩
  have hwe (n : ℕ) : HasPhysicalHolomorphicExtension U (fun Y => weight Y n) :=
    ⟨complexWeightCoeff R n,(hcoeff n).2.1,fun Y hY => ((hcoeff n).2.2 Y hY).2⟩
  obtain ⟨G,hG,hGmatch⟩ := transportGamma_hasPhysicalHolomorphicExtension U hAe hAie hQe hMe hBe hθe hwe p
  have hc : (y₀:ℂ)∈U := hcover y₀ ⟨y₀_pos.le,le_rfl⟩
  have hG0 : G (y₀:ℂ)=0 := by rw [hGmatch y₀ ⟨y₀_pos.le,le_rfl⟩,transportGamma_critical];rfl
  have hdR := dslope_analyticOnNhd_complex U hU R hR y₀ hc
  have hdG := dslope_analyticOnNhd_complex U hU G hG y₀ hc
  let Ω : Set ℂ := {z | z∈U ∧ dslope R (y₀:ℂ) z≠0}
  have hΩU : Ω⊆U := fun z hz => hz.1
  have hΩ : IsOpen Ω := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    filter_upwards [hU.mem_nhds hz.1,(hdR z hz.1).continuousAt.eventually_ne hz.2] with ζ hζ hRζ
    exact ⟨hζ,hRζ⟩
  have hΩcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω := by
    intro Y hY
    refine ⟨hcover Y hY,?_⟩
    by_cases he : Y=y₀
    · subst Y
      rw [dslope_same,hR']
      norm_num
    · have hYi : Y∈Ico (0:ℝ) y₀ := ⟨hY.1,lt_of_le_of_ne hY.2 he⟩
      have hRne : R (Y:ℂ)≠0 := by rw [hraw Y hYi];exact_mod_cast (r_pos Y hYi).ne'
      intro hzero
      have hf := sub_smul_dslope R (y₀:ℂ) (Y:ℂ)
      simp only [hzero,smul_zero,hR0,sub_zero] at hf
      exact hRne hf.symm
  let F : ℂ → ℂ := fun z => dslope G (y₀:ℂ) z/(Ahat z*dslope R (y₀:ℂ) z)
  refine ⟨Ω,hΩ,hΩcover,F,?_,?_⟩
  · intro z hz
    exact (hdG z hz.1).div ((hA z hz.1).mul (hdR z hz.1))
      (mul_ne_zero (hunit z hz.1).2.1 hz.2)
  intro Y hYi
  have hYc : Y∈Icc (0:ℝ) y₀ := ⟨hYi.1,hYi.2.le⟩
  have hδ : (Y:ℂ)-(y₀:ℂ)≠0 := sub_ne_zero.mpr (by exact_mod_cast ne_of_lt hYi.2)
  have hAa : Ahat (Y:ℂ)≠0 := (hunit _ (hcover Y hYc)).2.1
  have hRa : R (Y:ℂ)≠0 := by rw [hraw Y hYi];exact_mod_cast (r_pos Y hYi).ne'
  have hFval : F (Y:ℂ)=G (Y:ℂ)/(Ahat (Y:ℂ)*R (Y:ℂ)) := by
    dsimp only [F]
    rw [dslope_of_ne G (by exact_mod_cast ne_of_lt hYi.2),
      dslope_of_ne R (by exact_mod_cast ne_of_lt hYi.2)]
    simp only [slope,hG0,hR0,vsub_eq_sub,sub_zero,smul_eq_mul]
    field_simp [hδ,hAa,hRa] <;> ring
  rw [hGmatch Y hYc,(hmatch Y hYc).2,hraw Y hYi] at hFval
  simpa only [Complex.ofReal_div,Complex.ofReal_mul] using hFval

lemma transportGamma_quotient_continuous_extension (p : ℕ) :
    ∃ q : ℝ → ℝ,ContinuousOn q (Icc (0:ℝ) y₀) ∧
      ∀ Y∈Ico (0:ℝ) y₀,q Y=transportGamma p Y/(A Y*r Y) := by
  obtain ⟨Ω,hΩ,hcover,F,hF,hmatch⟩ := transportGamma_quotient_complex_extension p
  refine ⟨fun Y => (F (Y:ℂ)).re,?_,?_⟩
  · intro Y hY
    exact ((Complex.continuous_re.continuousAt.comp (hF _ (hcover Y hY)).continuousAt).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  · intro Y hY
    dsimp only
    rw [hmatch Y hY,Complex.ofReal_re]
end WP.Analysis
namespace WP.Analysis
open WP.HigherOrder
lemma transportGamma_quotient_real_analytic_extension (p : ℕ) :
    ∃ q : ℝ → ℝ,(∀ Y∈Icc (0:ℝ) y₀,AnalyticAt ℝ q Y) ∧
      ∀ Y∈Ico (0:ℝ) y₀,q Y=transportGamma p Y/(A Y*r Y) := by
  obtain ⟨Ω,hΩ,hcover,F,hF,hmatch⟩ := transportGamma_quotient_complex_extension p
  refine ⟨fun Y => (F (Y:ℂ)).re,?_,?_⟩
  · intro Y hY
    have hc : AnalyticAt ℝ (fun t : ℝ => F (t:ℂ)) Y :=
      (hF _ (hcover Y hY)).restrictScalars.comp (Complex.ofRealCLM.analyticAt Y)
    exact (Complex.reCLM.analyticAt _).comp hc
  · intro Y hY
    dsimp only
    rw [hmatch Y hY,Complex.ofReal_re]

lemma transportGamma_quotient_uniform_bound (p : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ Y∈Ico (0:ℝ) y₀,|transportGamma p Y/(A Y*r Y)|≤C := by
  obtain ⟨q,hq,hmatch⟩ := transportGamma_quotient_continuous_extension p
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) y₀)).bddAbove_image hq.norm
  refine ⟨max B 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro Y hY
  rw [←hmatch Y hY,←Real.norm_eq_abs]
  exact (hB ⟨Y,⟨hY.1,hY.2.le⟩,rfl⟩).trans (le_max_left _ _)
end WP.Analysis
