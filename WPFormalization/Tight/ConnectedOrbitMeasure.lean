import Mathlib

noncomputable section
namespace WP.TightConnected
open Set Filter Finset MeasureTheory
open scoped Topology BigOperators ENNReal Pointwise

lemma connected_window_dilation (k : ℕ) (α : ℝ) (hα : 0<α)
    (I : Fin k→Set ℝ) (f : (Fin k→ℝ)→ℝ) :
    (∫x : Fin k→ℝ in {x|∀i,α*x i∈I i},f x) =
      (α^k)⁻¹ * ∫x : Fin k→ℝ in {x|∀i,x i∈I i},f (fun i=>x i/α) := by
  let W : Set (Fin k→ℝ) := {x|∀i,x i∈I i}
  have hs : α⁻¹ • W = {x : Fin k→ℝ|∀i,α*x i∈I i} := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩ i
      simpa only [Pi.smul_apply,smul_eq_mul,←mul_assoc,mul_inv_cancel₀ hα.ne',one_mul] using hy i
    · intro hx
      refine ⟨fun i=>α*x i,hx,?_⟩
      funext i
      simp [Pi.smul_apply,smul_eq_mul,hα.ne']
  have he := Measure.setIntegral_comp_smul (volume : Measure (Fin k→ℝ)) f W (inv_ne_zero hα.ne')
  rw [hs] at he
  simp only [Module.finrank_pi,Fintype.card_fin,smul_eq_mul,inv_pow,inv_inv,
    abs_of_pos (pow_pos hα k)] at he
  have hfun : (fun x : Fin k→ℝ=>f (α⁻¹ • x)) = fun x=>f (fun i=>x i/α) := by
    funext x
    congr 1
    funext i
    simp [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  rw [hfun] at he
  rw [he]
  field_simp

end WP.TightConnected
