import WPFormalization.Volumes.TransportPrimitive

/-! Exact genus and cusp ratios of the prescribed finite marked model. The complexity, Gamma, root-power and square-root factors are retained before cancellation. No coefficient asymptotic is assumed. -/

noncomputable section
namespace WP.Analysis
open Set

lemma ratioModel_genus_identity (g p : ℕ) (hg : 2 ≤ g) (Y : ℝ)
    (hY : Y ∈ Ico 0 y₀) :
    markedModel (g-1) (p+2) Y = 4*r Y*markedModel g p Y := by
  have hc : complexity (g-1) (p+2) = complexity g p := by
    unfold complexity
    omega
  have he : g = (g-1)+1 := by omega
  have hp : ((p+2:ℕ):ℝ)/2 = (p:ℝ)/2+1 := by push_cast; ring
  have hr : 0 < r Y := r_pos Y hY
  simp only [markedModel,hc,hp,Real.rpow_eq_pow,Real.rpow_add hr,Real.rpow_one]
  rw [show (4:ℝ)⁻¹^g = (4:ℝ)⁻¹^(g-1)*(4:ℝ)⁻¹ by rw [←pow_succ,←he]]
  ring

lemma ratioModel_genus_ratio (g p : ℕ) (hg : 2 ≤ g) (Y : ℝ)
    (hY : Y ∈ Ico 0 y₀) :
    markedModel (g-1) (p+2) Y / markedModel g p Y = 4*r Y := by
  rw [ratioModel_genus_identity g p hg Y hY]
  exact mul_div_cancel_right₀ _ (markedModel_pos_parameter g p (by unfold Stable;omega) Y hY).ne'

lemma ratioModel_cusp_identity (g p : ℕ) (hs : Stable g p) (Y : ℝ)
    (hY : Y ∈ Ico 0 y₀) :
    markedModel g (p+1) Y = markedModel g p Y *
      ((complexity g p:ℝ)/(A Y*a Y*r Y))*
      Real.sqrt ((complexity g p:ℝ)/(complexity g p+1:ℕ)) := by
  have hc : complexity g (p+1) = complexity g p+1 := by
    unfold Stable at hs
    unfold complexity
    omega
  have hh : 0 < (complexity g p:ℝ) := by
    exact_mod_cast (show 0 < complexity g p by unfold Stable at hs;unfold complexity;omega)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hr : 0 < r Y := r_pos Y hY
  have hA : 0 < A Y := marked_A_pos Y ⟨hY.1,hY.2.le⟩
  have ha : 0 < a Y := a_pos Y hY
  have hp : ((p+1:ℕ):ℝ)/2 = (p:ℝ)/2+1/2 := by push_cast; ring
  have hZ : Z Y = A Y*a Y*r Y*Real.sqrt (r Y) := by
    unfold Z
    rw [Real.rpow_eq_pow,show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hr,Real.rpow_one,←Real.sqrt_eq_rpow]
    ring
  have hsqrt : Real.sqrt (Real.pi*((complexity g p:ℝ)+1)) *
      Real.sqrt ((complexity g p:ℝ)/(complexity g p+1:ℕ)) =
      Real.sqrt (Real.pi*(complexity g p:ℝ)) := by
    rw [←Real.sqrt_mul (mul_pos hpi (by positivity)).le]
    congr 1
    push_cast
    field_simp
  have hsn : Real.sqrt (Real.pi*((complexity g p:ℝ)+1)) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos hpi (by positivity))).ne'
  have hsq : Real.sqrt ((complexity g p:ℝ)/(complexity g p+1:ℕ)) =
      Real.sqrt (Real.pi*(complexity g p:ℝ))/Real.sqrt (Real.pi*((complexity g p:ℝ)+1)) := by
    apply (eq_div_iff hsn).mpr
    linarith [hsqrt]
  have hsqrtpos : Real.sqrt (Real.pi*(complexity g p:ℝ)) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos hpi hh)).ne'
  have hrs : Real.sqrt (r Y) ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  rw [hsq]
  simp only [markedModel,hc,hp,Real.rpow_eq_pow,Real.rpow_add hr,←Real.sqrt_eq_rpow,pow_succ]
  simp only [Nat.cast_add,Nat.cast_one,Real.Gamma_add_one hh.ne']
  rw [hZ]
  field_simp [hA.ne',ha.ne',hr.ne',hrs,hsn,hsqrtpos]
  <;> ring

end WP.Analysis
