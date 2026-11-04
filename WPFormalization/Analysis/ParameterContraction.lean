import Mathlib
noncomputable section
namespace WP.Analysis
open Set
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
def parameterContraction (t : ℝ) : E × ℂ →L[ℂ] E × ℂ :=
  (ContinuousLinearMap.fst ℂ E ℂ).prod
    ((t:ℂ) • ContinuousLinearMap.snd ℂ E ℂ)
@[simp] lemma parameterContraction_apply (t : ℝ) (p : E × ℂ) :
    parameterContraction t p=(p.1,(t:ℂ)*p.2) := rfl
lemma parameterContraction_continuous :
    Continuous (parameterContraction (E:=E)) := by
  exact (ContinuousLinearMap.prodₗᵢ ℂ).continuous.comp
    (continuous_const.prodMk (Complex.continuous_ofReal.smul continuous_const))
lemma parameterContraction_norm_le (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖parameterContraction (E:=E) t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  simp only [parameterContraction_apply,Prod.norm_def,one_mul,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
  apply max_le
  · exact le_max_left _ _
  · exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans (le_max_right _ _)
lemma parameterContraction_multilinear_continuous (n : ℕ)
    (P : ContinuousMultilinearMap ℂ (fun _ : Fin n=>E × ℂ) G) :
    Continuous (fun t : ℝ=>P.compContinuousLinearMap (fun _=>parameterContraction t)) := by
  exact (ContinuousMultilinearMap.compContinuousLinearMapLRight P).cont.comp
    (continuous_pi (fun _=>parameterContraction_continuous))
lemma parameterContraction_multilinear_norm_le (n : ℕ)
    (P : ContinuousMultilinearMap ℂ (fun _ : Fin n=>E × ℂ) G)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖P.compContinuousLinearMap (fun _=>parameterContraction t)‖ ≤ ‖P‖ := by
  apply (P.norm_compContinuousLinearMap_le _).trans
  apply mul_le_of_le_one_right (norm_nonneg _)
  calc ∏ i : Fin n, ‖parameterContraction (E:=E) t‖ ≤ ∏ _i : Fin n, (1:ℝ) :=
        Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _) (fun _ _=>parameterContraction_norm_le t ht)
       _ = 1 := by simp
end WP.Analysis
