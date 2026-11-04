import WPFormalization.Intersection.ComplexHomogeneity
import WPFormalization.HigherOrder.SmallComponentBounds
/-! The genuine bounded-component estimate on the same complex neighborhood
as the kernel geometric bounds. Nonempty tuples use the proved homogeneous
positive-recursion comparison and the actual real complexity bound. The empty
tuple is handled separately by the true finite dilaton identity and the b_d
geometric sum; Gamma(h+1)/h=Gamma(h) preserves the claimed exponential scale.
The neighborhood works for all genera, marking counts and degrees, including
invalid states. No recursive-coefficient or Gevrey estimate is assumed. -/
set_option maxHeartbeats 800000
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis

def complexSmallW (P : PsiTheory) (R : ℂ → ℂ) (g : ℕ) (d : List ℕ) (z : ℂ) : ℂ :=
  (4:ℂ)^g*complexNormalized P R g d z

lemma norm_complexSmallW (P : PsiTheory) (R : ℂ → ℂ) (g : ℕ) (d : List ℕ) (z : ℂ) :
    ‖complexSmallW P R g d z‖=(4:ℝ)^g*‖complexNormalized P R g d z‖ := by
  rw [complexSmallW,norm_mul,norm_pow]
  norm_num

lemma complexSmallW_homogeneous_upper (Ω : Set ℂ) (hconn : IsPreconnected Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (P : PsiTheory) (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff K R n) Ω)
    (hKr : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n)
    (z : ℂ) (hz : z∈Ω) (u : ℝ) (hu : 1≤u) (hθ : ∀ l,‖complexThetaCoeff R l z‖≤u)
    (g : ℕ) (d : List ℕ) (hn : 1≤d.length) :
    ‖complexSmallW P R g d z‖≤u^(complexity g d.length)*WP.HigherOrder.smallW P y₀ g d := by
  rw [norm_complexSmallW]
  have hc := complexNormalized_homogeneous_upper Ω hconn hcover P R hK hKr z hz u hu hθ g d hn
  exact (mul_le_mul_of_nonneg_left hc (by positivity : (0:ℝ)≤4^g)).trans_eq (by unfold WP.HigherOrder.smallW;ring)

lemma finite_norm_sum_of_geometric (a : ℕ → ℂ) (ρ C : ℝ) (hρ : 1<ρ) (hC : 0≤C)
    (hbound : ∀ d : ℕ,‖a d‖≤C/ρ^d) (N : ℕ) :
    ∑ d∈Finset.range N,‖a d‖≤C/(1-ρ⁻¹) := by
  have hρp : 0<ρ := zero_lt_one.trans hρ
  have hInv : ‖(ρ⁻¹:ℝ)‖<1 := by
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hρp)]
    exact (inv_lt_one₀ hρp).mpr hρ
  have hg := hasSum_geometric_of_norm_lt_one hInv
  calc
    _ ≤ ∑ d∈Finset.range N,C/ρ^d := Finset.sum_le_sum (fun d hd => hbound d)
    _ = C*∑ d∈Finset.range N,(ρ⁻¹)^d := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [inv_pow,div_eq_mul_inv]
    _ ≤ C*∑' d : ℕ,(ρ⁻¹)^d := mul_le_mul_of_nonneg_left
      (hg.summable.sum_le_tsum _ (fun d hd => pow_nonneg (inv_nonneg.mpr hρp.le) d)) hC
    _ = C/(1-ρ⁻¹) := by rw [hg.tsum_eq];rfl

lemma complexSmallW_dilaton (Ω : Set ℂ) (hconn : IsPreconnected Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (P : PsiTheory) (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff K R n) Ω)
    (hKr : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n)
    (hH : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff H R n) Ω)
    (hHr : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff H R n (Y:ℂ)=WP.coeff (barH Y) n)
    (g p : ℕ) (hs : Stable g p) (z : ℂ) (hz : z∈Ω) :
    (complexity g p:ℂ)*complexSmallW P R g (List.replicate p 0) z=
      ∑ d∈Finset.range (dimension g (p+1)+1),complexDilatonCoefficient R d z*
        complexSmallW P R g (d::List.replicate p 0) z := by
  calc
    _ = (4:ℂ)^g*((complexity g p:ℂ)*complexNormalized P R g (List.replicate p 0) z) := by unfold complexSmallW;ring
    _ = (4:ℂ)^g*∑ d∈Finset.range (dimension g (p+1)+1),complexDilatonCoefficient R d z*
        complexNormalized P R g (d::List.replicate p 0) z := by
      rw [complexNormalized_dilaton Ω hconn hcover P R hK hKr hH hHr g p hs z hz]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      unfold complexSmallW
      ring

lemma complexSmallW_empty_upper (Ω : Set ℂ) (hconn : IsPreconnected Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (P : PsiTheory) (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff K R n) Ω)
    (hKr : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n)
    (hH : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff H R n) Ω)
    (hHr : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff H R n (Y:ℂ)=WP.coeff (barH Y) n)
    (S ρ C : ℝ) (hS : 1≤S) (hρ : 1<ρ) (hC : 0≤C)
    (hnonempty : ∀ g : ℕ,∀ d : List ℕ,Stable g d.length → 1≤d.length → ∀ z∈Ω,
      ‖complexSmallW P R g d z‖≤Real.Gamma (complexity g d.length:ℝ)*S^(complexity g d.length))
    (hb : ∀ z∈Ω,∀ d : ℕ,‖complexDilatonCoefficient R d z‖≤C/ρ^d)
    (g : ℕ) (hs : Stable g 0) (z : ℂ) (hz : z∈Ω) :
    ‖complexSmallW P R g [] z‖≤Real.Gamma (complexity g 0:ℝ)*(C/(1-ρ⁻¹)*S)*S^(complexity g 0) := by
  let h := complexity g 0
  have hh : 1≤h := by dsimp [h];unfold complexity;unfold Stable at hs;omega
  have hhp : (0:ℝ)<h := by exact_mod_cast hh
  have hS0 : 0≤S := by linarith
  have hg1 : Stable g 1 := by unfold Stable at *;omega
  have hc : complexity g 1=h+1 := by dsimp [h];unfold complexity;unfold Stable at hs;omega
  have hsum := complexSmallW_dilaton Ω hconn hcover P R hK hKr hH hHr g 0 hs z hz
  simp only [List.replicate_zero,Nat.zero_add] at hsum
  have hineq : (h:ℝ)*‖complexSmallW P R g [] z‖≤(C/(1-ρ⁻¹))*
      (Real.Gamma ((h+1:ℕ):ℝ)*S^(h+1)) := by
    calc
      _ = ‖(h:ℂ)*complexSmallW P R g [] z‖ := by rw [norm_mul];simp
      _ = ‖∑ d∈Finset.range (dimension g 1+1),complexDilatonCoefficient R d z*complexSmallW P R g [d] z‖ := by
        exact congrArg norm hsum
      _ ≤ ∑ d∈Finset.range (dimension g 1+1),‖complexDilatonCoefficient R d z*complexSmallW P R g [d] z‖ := norm_sum_le _ _
      _ ≤ ∑ d∈Finset.range (dimension g 1+1),‖complexDilatonCoefficient R d z‖*(Real.Gamma ((h+1:ℕ):ℝ)*S^(h+1)) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        simpa only [List.length_singleton,hc] using hnonempty g [d] (by simpa using hg1) (by simp) z hz
      _ = (∑ d∈Finset.range (dimension g 1+1),‖complexDilatonCoefficient R d z‖)*
          (Real.Gamma ((h+1:ℕ):ℝ)*S^(h+1)) := by rw [Finset.sum_mul]
      _ ≤ (C/(1-ρ⁻¹))*(Real.Gamma ((h+1:ℕ):ℝ)*S^(h+1)) :=
        mul_le_mul_of_nonneg_right (finite_norm_sum_of_geometric _ ρ C hρ hC (hb z hz) _)
          (mul_nonneg (Real.Gamma_pos_of_pos (by positivity)).le (pow_nonneg hS0 _))
  have hGamma : Real.Gamma ((h+1:ℕ):ℝ)=(h:ℝ)*Real.Gamma (h:ℝ) := by
    rw [Nat.cast_add,Nat.cast_one,Real.Gamma_add_one hhp.ne']
  apply (mul_le_mul_iff_right₀ hhp).mp
  calc
    (h:ℝ)*‖complexSmallW P R g [] z‖ ≤ (C/(1-ρ⁻¹))*(Real.Gamma ((h+1:ℕ):ℝ)*S^(h+1)) := hineq
    _ = (h:ℝ)*(Real.Gamma (complexity g 0:ℝ)*(C/(1-ρ⁻¹)*S)*S^(complexity g 0)) := by
      rw [hGamma,pow_succ]
      dsimp only [h]
      ring
end WP.Analysis
namespace WP.Analysis
lemma complexSmallW_uniform_of_kernel_control (Ω : Set ℂ) (hconn : IsPreconnected Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (P : PsiTheory) (R : ℂ → ℂ)
    (hK : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff K R n) Ω)
    (hKr : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n)
    (hH : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff H R n) Ω)
    (hHr : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff H R n (Y:ℂ)=WP.coeff (barH Y) n)
    (u ρ C : ℝ) (hu : 1≤u) (hρ : 1<ρ) (hC : 0<C)
    (hθ : ∀ z∈Ω,∀ l,‖complexThetaCoeff R l z‖≤u)
    (hb : ∀ z∈Ω,∀ d : ℕ,‖complexDilatonCoefficient R d z‖≤C/ρ^d) :
    ∃ T : ℝ,1≤T ∧ ∀ g : ℕ,∀ d : List ℕ,Stable g d.length → ∀ z∈Ω,
      ‖complexSmallW P R g d z‖≤Real.Gamma (complexity g d.length:ℝ)*T^(complexity g d.length) := by
  obtain ⟨B,hB,hReal⟩ := WP.HigherOrder.smallW_real_uniform_complexity_bound P
  have hu0 : 0≤u := by linarith
  let S : ℝ := u*B
  have hS : 1≤S := one_le_mul_of_one_le_of_one_le hu hB
  have hS0 : 0≤S := by linarith
  have hNonempty : ∀ g : ℕ,∀ d : List ℕ,Stable g d.length → 1≤d.length → ∀ z∈Ω,
      ‖complexSmallW P R g d z‖≤Real.Gamma (complexity g d.length:ℝ)*S^(complexity g d.length) := by
    intro g d hs hn z hz
    have hm := complexSmallW_homogeneous_upper Ω hconn hcover P R hK hKr z hz u hu (hθ z hz) g d hn
    calc
      _ ≤ u^(complexity g d.length)*WP.HigherOrder.smallW P y₀ g d := hm
      _ ≤ u^(complexity g d.length)*|WP.HigherOrder.smallW P y₀ g d| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg hu0 _)
      _ ≤ u^(complexity g d.length)*(Real.Gamma (complexity g d.length:ℝ)*B^(complexity g d.length)) :=
        mul_le_mul_of_nonneg_left (hReal g d hs hn y₀ ⟨y₀_pos.le,le_rfl⟩) (pow_nonneg hu0 _)
      _ = _ := by dsimp only [S];rw [mul_pow];ring
  let Kb : ℝ := C/(1-ρ⁻¹)
  let V : ℝ := max 1 (Kb*S)
  let T : ℝ := S*V
  have hV : 1≤V := le_max_left _ _
  have hST : S≤T := le_mul_of_one_le_right hS0 hV
  refine ⟨T,hS.trans hST,?_⟩
  intro g d hs z hz
  have hh : 1≤complexity g d.length := by unfold complexity;unfold Stable at hs;omega
  have hG : 0≤Real.Gamma (complexity g d.length:ℝ) :=
    (Real.Gamma_pos_of_pos (by exact_mod_cast (show 0<complexity g d.length by omega))).le
  by_cases hn : 1≤d.length
  · exact (hNonempty g d hs hn z hz).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hS0 hST _) hG)
  · have hd0 : d=[] := by
      cases d with
      | nil => rfl
      | cons a d => simp at hn
    subst d
    have hs0 : Stable g 0 := by simpa using hs
    have hh0 : complexity g 0≠0 := by simpa using (show complexity g ([]:List ℕ).length≠0 by omega)
    have hp : Kb*S≤V^(complexity g 0) := (le_max_right 1 (Kb*S)).trans (le_self_pow₀ hV hh0)
    have hf : (Kb*S)*S^(complexity g 0)≤T^(complexity g 0) := by
      calc
        (Kb*S)*S^(complexity g 0) ≤ V^(complexity g 0)*S^(complexity g 0) :=
          mul_le_mul_of_nonneg_right hp (pow_nonneg hS0 _)
        _ = S^(complexity g 0)*V^(complexity g 0) := mul_comm _ _
        _ = (S*V)^(complexity g 0) := (mul_pow S V (complexity g 0)).symm
    have he := complexSmallW_empty_upper Ω hconn hcover P R hK hKr hH hHr S ρ C hS hρ hC.le hNonempty hb g hs0 z hz
    calc
      _ ≤ Real.Gamma (complexity g 0:ℝ)*(Kb*S)*S^(complexity g 0) := he
      _ = Real.Gamma (complexity g 0:ℝ)*((Kb*S)*S^(complexity g 0)) := by ring
      _ ≤ Real.Gamma (complexity g 0:ℝ)*T^(complexity g 0) := mul_le_mul_of_nonneg_left hf hG

lemma common_complex_small_component_bounds :
    ∃ (Ω : Set ℂ) (R : ℂ → ℂ) (ρ C : ℝ),IsOpen Ω ∧ Convex ℝ Ω ∧
      (∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧ 1<ρ ∧ 0<C ∧ AnalyticOnNhd ℂ R Ω ∧
      (∀ z∈Ω,complexAUnit z≠0 ∧ complexDeflatedCoeff R 0 z≠0) ∧
      (∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ)) ∧ R y₀=0 ∧ deriv R y₀=-3 ∧
      (∀ n : ℕ,AnalyticOnNhd ℂ (complexThetaCoeff R n) Ω ∧
        AnalyticOnNhd ℂ (complexWeightCoeff R n) Ω ∧ AnalyticOnNhd ℂ (complexDilatonCoefficient R n) Ω) ∧
      (∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,complexThetaCoeff R n (Y:ℂ)=(theta Y n:ℂ) ∧
        complexWeightCoeff R n (Y:ℂ)=(weight Y n:ℂ) ∧ complexDilatonCoefficient R n (Y:ℂ)=(canonicalDilatonCoefficient Y n:ℂ)) ∧
      (∀ z∈Ω,∀ n : ℕ,‖complexThetaCoeff R n z‖≤C ∧ ‖complexWeightCoeff R n z‖≤C/ρ^n ∧
        ‖complexDilatonCoefficient R n z‖≤C/ρ^n) ∧
      (∀ n : ℕ,complexThetaCoeff R n (y₀:ℂ)=1) ∧
      (∀ (P : PsiTheory) (g : ℕ) (d : List ℕ),AnalyticOnNhd ℂ (complexSmallW P R g d) Ω ∧
        ∀ Y∈Icc (0:ℝ) y₀,complexSmallW P R g d (Y:ℂ)=(WP.HigherOrder.smallW P Y g d:ℂ)) ∧
      (∀ P : PsiTheory,∃ T : ℝ,1≤T ∧ ∀ g : ℕ,∀ d : List ℕ,Stable g d.length → ∀ z∈Ω,
        ‖complexSmallW P R g d z‖≤Real.Gamma (complexity g d.length:ℝ)*T^(complexity g d.length)) := by
  obtain ⟨Ω,R,ρ,C,hΩ,hconv,hcover,hρ,hC,hR,hunit,hraw,hR0,hR',hcoefs,hmatch,hbounds,hcrit⟩ :=
    common_complex_geometric_kernel_bounds
  have hcoeff := normalized_coefficients_holomorphic_on_common_domain Ω hΩ hcover R hR hR0 hraw
    (fun z hz => (hunit z hz).1)
  have hKa : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff K R n) Ω := fun n => (hcoeff n).1
  have hHa : ∀ n : ℕ,AnalyticOnNhd ℂ (regularizedKernelCoeff H R n) Ω := fun n => (hcoeff n).2.1
  have hKr : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff K R n (Y:ℂ)=WP.coeff (barK Y) n :=
    fun n Y hY => ((hcoeff n).2.2 Y hY).1
  have hHr : ∀ n : ℕ,∀ Y∈Icc (0:ℝ) y₀,regularizedKernelCoeff H R n (Y:ℂ)=WP.coeff (barH Y) n :=
    fun n Y hY => ((hcoeff n).2.2 Y hY).2
  have hC1 : 1≤C := by
    have hh := (hbounds (y₀:ℂ) (hcover y₀ ⟨y₀_pos.le,le_rfl⟩) 0).1
    simpa only [hcrit 0,norm_one] using hh
  refine ⟨Ω,R,ρ,C,hΩ,hconv,hcover,hρ,hC,hR,hunit,hraw,hR0,hR',hcoefs,hmatch,hbounds,hcrit,?_,?_⟩
  · intro P g d
    constructor
    · intro z hz
      exact analyticAt_const.mul (complexNormalized_analyticOnNhd Ω P R hKa g d z hz)
    · intro Y hY
      unfold complexSmallW WP.HigherOrder.smallW
      rw [complexNormalized_restrict_closed P R hKr g d Y hY]
      push_cast
      rfl
  · intro P
    exact complexSmallW_uniform_of_kernel_control Ω hconv.isPreconnected hcover P R hKa hKr hHa hHr C ρ C hC1 hρ hC
      (fun z hz l => (hbounds z hz l).1) (fun z hz d => (hbounds z hz d).2.2)
end WP.Analysis
