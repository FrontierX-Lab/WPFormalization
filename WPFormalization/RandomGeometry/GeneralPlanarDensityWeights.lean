import WPFormalization.RandomGeometry.PrimitivePlanarTypeTail
import Mathlib.Analysis.Normed.Group.FunctionSeries

noncomputable section
namespace WP.RandomGeometry
open Set Filter
open scoped Topology

/-- The actual planar type coefficient; unstable types zero and one carry
    no planar curve intensity. -/
def generalPlanarTypeWeight (P : PsiTheory) (k : ℕ) (x : ℝ) : ℝ :=
  if 2 ≤ k then 2*primitivePlanarWeight P k*x^(k-2) else 0

lemma general_planar_type_weight_formula (P : PsiTheory) (k : ℕ) (hk : 2 ≤ k) (x : ℝ) :
    generalPlanarTypeWeight P k x =
      2*volumeModel P 0 (k+1)/(k.factorial:ℝ)*(x/(2*Real.pi^2))^(k-2) := by
  simp only [generalPlanarTypeWeight,if_pos hk,primitivePlanarWeight,div_pow]
  ring

lemma general_planar_type_weight_add_two (P : PsiTheory) (j : ℕ) (x : ℝ) :
    generalPlanarTypeWeight P (j+2) x = 2*(primitivePlanarWeight P (j+2)*x^j) := by
  simp [generalPlanarTypeWeight,show 2 ≤ j+2 by omega,Nat.add_sub_cancel,mul_assoc]

@[simp] lemma general_planar_type_weight_zero (P : PsiTheory) (x : ℝ) :
    generalPlanarTypeWeight P 0 x = 0 := by simp [generalPlanarTypeWeight]

@[simp] lemma general_planar_type_weight_one (P : PsiTheory) (x : ℝ) :
    generalPlanarTypeWeight P 1 x = 0 := by simp [generalPlanarTypeWeight]

@[simp] lemma general_planar_type_weight_two (P : PsiTheory) (x : ℝ) :
    generalPlanarTypeWeight P 2 x = 1 := by
  simp [generalPlanarTypeWeight,primitive_planar_weight_two]

lemma general_planar_type_weight_nonneg (P : PsiTheory) (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ generalPlanarTypeWeight P k x := by
  by_cases hk : 2 ≤ k
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [Nat.add_comm 2,general_planar_type_weight_add_two]
    exact mul_nonneg (by norm_num) (mul_nonneg (primitive_planar_weight_nonneg P j) (pow_nonneg hx j))
  · simp only [generalPlanarTypeWeight,if_neg hk,le_refl]

lemma general_planar_type_weight_continuous (P : PsiTheory) (k : ℕ) :
    Continuous (generalPlanarTypeWeight P k) := by
  unfold generalPlanarTypeWeight
  split_ifs <;> fun_prop

lemma general_planar_type_weight_at_zero (P : PsiTheory) (k : ℕ) :
    generalPlanarTypeWeight P k 0 = if k=2 then 1 else 0 := by
  by_cases hk : k=2
  · simp [hk]
  · by_cases hk2 : 2 ≤ k
    · have he : k-2 ≠ 0 := by omega
      simp [generalPlanarTypeWeight,hk2,hk,zero_pow he]
    · simp [generalPlanarTypeWeight,hk2,hk]

lemma general_planar_type_weight_le_critical (P : PsiTheory) (k : ℕ) (x : ℝ)
    (hx : x ∈ Icc (0:ℝ) xCritical) :
    generalPlanarTypeWeight P k x ≤ generalPlanarTypeWeight P k xCritical := by
  by_cases hk : 2 ≤ k
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [Nat.add_comm 2,general_planar_type_weight_add_two,general_planar_type_weight_add_two]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hx.2 j)
        (primitive_planar_weight_nonneg P j)) (by norm_num)
  · simp [generalPlanarTypeWeight,hk]

theorem general_planar_type_weight_summable (P : PsiTheory) (x : ℝ)
    (hx : x ∈ Icc (0:ℝ) xCritical) :
    Summable (fun k : ℕ => generalPlanarTypeWeight P k x) := by
  apply (summable_nat_add_iff 2).mp
  simp only [general_planar_type_weight_add_two]
  exact (primitive_planar_type_tail_summable P 0 x hx).mul_left 2

def generalPlanarTotalWeight (P : PsiTheory) (x : ℝ) : ℝ :=
  ∑' k : ℕ,generalPlanarTypeWeight P k x

lemma general_planar_total_weight_continuousOn (P : PsiTheory) :
    ContinuousOn (generalPlanarTotalWeight P) (Icc (0:ℝ) xCritical) := by
  apply continuousOn_tsum (fun k => (general_planar_type_weight_continuous P k).continuousOn)
    (general_planar_type_weight_summable P xCritical ⟨Analysis.xCritical_pos_parameter.le,le_rfl⟩)
  intro k x hx
  rw [Real.norm_eq_abs,abs_of_nonneg (general_planar_type_weight_nonneg P k x hx.1)]
  exact general_planar_type_weight_le_critical P k x hx

@[simp] lemma general_planar_total_weight_zero (P : PsiTheory) :
    generalPlanarTotalWeight P 0 = 1 := by
  simp [generalPlanarTotalWeight,general_planar_type_weight_at_zero]

lemma general_planar_total_weight_nonneg (P : PsiTheory) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ generalPlanarTotalWeight P x :=
  tsum_nonneg (fun k => general_planar_type_weight_nonneg P k x hx)

lemma general_planar_total_weight_le_critical (P : PsiTheory) (x : ℝ)
    (hx : x ∈ Icc (0:ℝ) xCritical) :
    generalPlanarTotalWeight P x ≤ generalPlanarTotalWeight P xCritical := by
  exact (general_planar_type_weight_summable P x hx).tsum_le_tsum
    (fun k => general_planar_type_weight_le_critical P k x hx)
    (general_planar_type_weight_summable P xCritical ⟨Analysis.xCritical_pos_parameter.le,le_rfl⟩)

lemma general_planar_type_weight_tail_eq (P : PsiTheory) (K : ℕ) (x : ℝ) :
    (∑' j:ℕ,generalPlanarTypeWeight P (j+K+2) x) = 2*primitivePlanarTypeTail P K x := by
  simp only [general_planar_type_weight_add_two,primitivePlanarTypeTail,tsum_mul_left]

theorem general_planar_type_weight_tail_uniform (P : PsiTheory) :
    ∀ ε:ℝ,0<ε → ∃ K:ℕ,∀ N:ℕ,K≤N → ∀ x ∈ Icc (0:ℝ) xCritical,
      (∑' j:ℕ,generalPlanarTypeWeight P (j+N+2) x) ≤ ε := by
  intro ε hε
  obtain ⟨K,hK⟩ := primitive_planar_type_tail_uniform P (ε/2) (half_pos hε)
  refine ⟨K,fun N hN x hx => ?_⟩
  rw [general_planar_type_weight_tail_eq]
  linarith [hK N hN x hx]

end WP.RandomGeometry
