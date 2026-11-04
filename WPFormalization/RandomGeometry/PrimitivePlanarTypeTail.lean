import WPFormalization.RandomGeometry.PrimitivePlanarCoefficientIdentity
import WPFormalization.Volumes.VolumeRatiosEndpoints
import WPFormalization.Volumes.PlanarInverseBoundary
/-! The actual planar type weights have a summable critical majorant.
Their tails therefore vanish uniformly over every physical cusp weight. -/
noncomputable section
namespace WP.RandomGeometry
open Set Filter
open scoped Topology

lemma primitive_planar_weight_eq_inverse_coefficient (P:PsiTheory)(j:ℕ):
    primitivePlanarWeight P (j+2)=
      realCoeff (PositiveConvolution.planarInverse P) (j+1)/(j+2:ℕ):=by
  have hd:dimension 0 (j+3)=j:=by unfold dimension;omega
  have hc:realCoeff (PositiveConvolution.planarInverse P) (j+1)=
      volumeModel P 0 (j+3)/((2*Real.pi^2)^j*((j+1).factorial:ℝ)):=by
    change realCoeff (iteratedDeriv 2 (Phi P 0)) (j+1)=_
    simpa only[show j+1+2=j+3 by omega,hd] using
      marked_realCoeff_volume P 0 2 (j+1)
  have hf:((j+2).factorial:ℝ)=((j+2:ℕ):ℝ)*((j+1).factorial:ℝ):=by
    exact_mod_cast (Nat.factorial_succ (j+1))
  unfold primitivePlanarWeight
  rw[hc,show j+2+1=j+3 by omega,show j+2-2=j by omega,hf]
  field_simp

lemma primitive_planar_weight_two (P:PsiTheory):
    primitivePlanarWeight P 2=1/2:=by
  have he:=primitive_planar_weight_eq_inverse_coefficient P 0
  norm_num[realCoeff,PositiveConvolution.planarInverse_first_coefficient] at he
  exact he

lemma primitive_planar_weight_nonneg (P:PsiTheory)(j:ℕ):
    0≤primitivePlanarWeight P (j+2):=by
  rw[primitive_planar_weight_eq_inverse_coefficient]
  exact div_nonneg ((PositiveConvolution.planarInverse_positiveJets P).coefficient_nonneg (j+1)).1
    (Nat.cast_nonneg _)

theorem primitive_planar_critical_summable (P:PsiTheory):
    Summable (fun j:ℕ=>primitivePlanarWeight P (j+2)*xCritical^j):=by
  have hs:Summable (fun j:ℕ=>realCoeff (PositiveConvolution.planarInverse P) (j+1)*xCritical^(j+1)):=
    (summable_nat_add_iff 1).mpr (PositiveConvolution.planarInverse_boundary_summable P).1
  have hxc:0<xCritical:=Analysis.xCritical_pos_parameter
  apply Summable.of_nonneg_of_le (fun j=>mul_nonneg (primitive_planar_weight_nonneg P j) (pow_nonneg hxc.le _)) _ (hs.div_const xCritical)
  intro j
  rw[primitive_planar_weight_eq_inverse_coefficient,pow_succ]
  have hc:0≤realCoeff (PositiveConvolution.planarInverse P) (j+1):=
    ((PositiveConvolution.planarInverse_positiveJets P).coefficient_nonneg (j+1)).1
  have hdiv:realCoeff (PositiveConvolution.planarInverse P) (j+1)/(j+2:ℕ)≤
      realCoeff (PositiveConvolution.planarInverse P) (j+1):=
    div_le_self hc (by norm_cast;omega)
  have hm:=mul_le_mul_of_nonneg_right hdiv (pow_nonneg hxc.le j)
  simpa only[←mul_assoc,mul_div_cancel_right₀ _ hxc.ne'] using hm

def primitivePlanarTypeTail (P:PsiTheory)(K:ℕ)(x:ℝ):ℝ:=
  ∑'j:ℕ,primitivePlanarWeight P (j+K+2)*x^(j+K)

lemma primitive_planar_type_tail_summable (P:PsiTheory)(K:ℕ)(x:ℝ)
    (hx:x∈Icc (0:ℝ) xCritical):
    Summable (fun j:ℕ=>primitivePlanarWeight P (j+K+2)*x^(j+K)):=by
  have hs:Summable (fun j:ℕ=>primitivePlanarWeight P (j+K+2)*xCritical^(j+K)):=
    (summable_nat_add_iff K).mpr (primitive_planar_critical_summable P)
  apply Summable.of_nonneg_of_le
    (fun j=>mul_nonneg (primitive_planar_weight_nonneg P (j+K)) (pow_nonneg hx.1 _)) _ hs
  intro j
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hx.2 _) (primitive_planar_weight_nonneg P (j+K))

lemma primitive_planar_type_tail_le_critical (P:PsiTheory)(K:ℕ)(x:ℝ)
    (hx:x∈Icc (0:ℝ) xCritical):
    0≤primitivePlanarTypeTail P K x ∧
      primitivePlanarTypeTail P K x≤primitivePlanarTypeTail P K xCritical:=by
  refine ⟨tsum_nonneg (fun j=>mul_nonneg (primitive_planar_weight_nonneg P (j+K)) (pow_nonneg hx.1 _)),?_⟩
  apply (primitive_planar_type_tail_summable P K x hx).tsum_le_tsum _
    (primitive_planar_type_tail_summable P K xCritical ⟨Analysis.xCritical_pos_parameter.le,le_rfl⟩)
  intro j
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hx.2 _) (primitive_planar_weight_nonneg P (j+K))

lemma primitive_planar_type_tail_critical_tendsto_zero (P:PsiTheory):
    Tendsto (fun K:ℕ=>primitivePlanarTypeTail P K xCritical) atTop (𝓝 0):=by
  exact tendsto_sum_nat_add (f:=fun j:ℕ=>primitivePlanarWeight P (j+2)*xCritical^j)

theorem primitive_planar_type_tail_uniform (P:PsiTheory):
    ∀ε:ℝ,0<ε→∃K:ℕ,∀N:ℕ,K≤N→∀x∈Icc (0:ℝ) xCritical,
      primitivePlanarTypeTail P N x≤ε:=by
  intro ε hε
  obtain ⟨K,hK⟩:=Filter.eventually_atTop.mp
    ((primitive_planar_type_tail_critical_tendsto_zero P).eventually (eventually_lt_nhds hε))
  exact ⟨K,fun N hN x hx=>((primitive_planar_type_tail_le_critical P N x hx).2).trans (hK N hN).le⟩
end WP.RandomGeometry
