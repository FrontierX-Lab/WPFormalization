import WPFormalization.HigherOrder.PureEndpoint
import WPFormalization.HigherOrder.FirstOrder
import WPFormalization.External.AsymptoticFirstOrder
import WPFormalization.Analysis.EndpointFirstOrderAlgebra

/-! The actual critical amplitude has the canonical first correction t_p.
Classical fixed-order PI and Gamma inputs are instantiated in the exact endpoint
identity. The finite marking step preserves the specified coefficient and
quadratic inverse-complexity error, including p=0. -/
noncomputable section
namespace WP.HigherOrder
lemma exactEndpoint_base_first_error (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, 2 ≤ G ∧ ∀ g ≥ G,
      |exactEndpoint P g 0-(1+firstEndpointConstant 0/(complexity g 0:ℝ))| ≤
        C/(complexity g 0:ℝ)^2 := by
  obtain ⟨CP,hCP,GP,hGP,hP⟩ := External.painleve_first_correction_error
  obtain ⟨CG,x₀,hCG,hx₀,hG⟩ := External.gamma_ratio_first_correction_error (3/2) 0
  obtain ⟨N,hN⟩ := exists_nat_ge x₀
  let EP : ℝ := 4*CP+1/16
  let EM : ℝ := ((1+|(-1/8:ℝ)|+|3/8|)^2+
    4*(1+|(-1/8:ℝ)|+|3/8|)*(EP+CG)+(EP+CG)^2)
  let EF : ℝ := ((1+|(1/4:ℝ)|+|-4/5|)^2+
    4*(1+|(1/4:ℝ)|+|-4/5|)*(EM+16/25)+(EM+16/25)^2)
  have hEP : 0 < EP := by dsimp [EP];positivity
  have hEM : 0 < EM := by dsimp [EM];positivity
  have hEF : 0 < EF := by dsimp [EF];positivity
  refine ⟨EF,hEF,max GP (N+2),by omega,?_⟩
  intro g hg
  have hgP : GP ≤ g := (le_max_left _ _).trans hg
  have hgN : N+2 ≤ g := (le_max_right _ _).trans hg
  have hg2 : 2 ≤ g := by omega
  let h : ℝ := complexity g 0
  have hhr : h=2*(g:ℝ)-2 := by dsimp [h,complexity];rw [Nat.cast_sub (by omega)];push_cast;ring
  have hgR : 0 < (g:ℝ) := by exact_mod_cast (show 0 < g by omega)
  have hh1 : 1 ≤ h := by
    rw [hhr]
    have hg2R : (2:ℝ) ≤ g := by exact_mod_cast hg2
    linarith
  have hh : 0 < h := by linarith
  have hgh : h ≤ 2*(g:ℝ) := by linarith
  have hxh : x₀ ≤ h := by
    have hNg : (N:ℝ)+2 ≤ g := by exact_mod_cast hgN
    linarith
  have hpi : |External.normalizedZeroInstanton g-(1+(-1/8:ℝ)/(h+1/2))| ≤ 4*CP/(h+1/2)^2 := by
    have he := hP g hgP
    have hEq : 1-1/(8*(2*(g:ℝ)-3/2))=1+(-1/8:ℝ)/(h+1/2) := by
      rw [show 2*(g:ℝ)-3/2=h+1/2 by linarith]
      field_simp <;> ring
    rw [hEq] at he
    apply he.trans
    apply (div_le_div_iff₀ (sq_pos_of_pos hgR) (by positivity : 0 < (h+1/2)^2)).2
    have hscale : (h+1/2)^2 ≤ 4*(g:ℝ)^2 := by rw [hhr];nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hscale hCP.le]
  have hp := Analysis.first_order_shift_error (External.normalizedZeroInstanton g) 1 (-1/8) h
    (1/2) (1/8) (4*CP) hh (by norm_num) (by norm_num) (by positivity) (by norm_num) hpi
  have hgma : |Real.Gamma (h+3/2)/(Real.Gamma h*Real.rpow h (3/2))-
      (1+(3/8:ℝ)/h)| ≤ CG/h^2 := by
    convert hG h hxh using 1 <;> norm_num <;> ring
  have hi : |(1+4/(5*h))⁻¹-(1+(-4/5:ℝ)/h)| ≤ (16/25:ℝ)/h^2 := by
    have he := Analysis.inverse_one_add_second_error (4/(5*h)) (by positivity)
    convert he using 1 <;> ring
  have hprod := Analysis.unit_first_order_product (-1/8) (3/8)
    (External.normalizedZeroInstanton g) (Real.Gamma (h+3/2)/(Real.Gamma h*Real.rpow h (3/2)))
    EP CG h hEP.le hCG.le hh1 (by convert hp using 1 <;> dsimp [EP] <;> norm_num) hgma
  have hprod' : |External.normalizedZeroInstanton g*
      (Real.Gamma (h+3/2)/(Real.Gamma h*Real.rpow h (3/2)))-(1+(1/4:ℝ)/h)| ≤ EM/h^2 := by
    convert hprod using 1 <;> norm_num
  have hfinal := Analysis.unit_first_order_product (1/4) (-4/5)
    (External.normalizedZeroInstanton g*(Real.Gamma (h+3/2)/(Real.Gamma h*Real.rpow h (3/2))))
    (1+4/(5*h))⁻¹ EM (16/25) h hEM.le (by norm_num) hh1 hprod' hi
  rw [exactEndpoint_base P g hg2]
  change |External.normalizedZeroInstanton g*
      (Real.Gamma (h+3/2)/(Real.Gamma h*Real.rpow h (3/2)))/(1+4/(5*h))-
      (1+firstEndpointConstant 0/h)| ≤ EF/h^2
  convert hfinal using 1 <;> norm_num [firstEndpointConstant,div_eq_mul_inv]
end WP.HigherOrder
namespace WP.HigherOrder
lemma firstEndpointConstant_succ (p : ℕ) :
    firstEndpointConstant (p+1)=firstEndpointConstant p+(1/2-(p:ℝ)/5) := by
  unfold firstEndpointConstant
  push_cast
  ring
lemma exactEndpoint_first_error (P : PsiTheory) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, 2 ≤ G ∧ ∀ g ≥ G,
      |exactEndpoint P g p-(1+firstEndpointConstant p/(complexity g p:ℝ))| ≤
        C/(complexity g p:ℝ)^2 := by
  induction p with
  | zero => exact exactEndpoint_base_first_error P
  | succ p ih =>
      obtain ⟨C,hC,G,hG,hE⟩ := ih
      let b : ℝ := 1/2-(p:ℝ)/5
      let S : ℝ := (1+|-(p:ℝ)/5|+|(1/2:ℝ)|)^2+
        4*(1+|-(p:ℝ)/5|+|(1/2:ℝ)|)*(0+1/8)+(0+1/8)^2
      let M : ℝ := (1+|firstEndpointConstant p|+|b|)^2+
        4*(1+|firstEndpointConstant p|+|b|)*(C+S)+(C+S)^2
      have hS : 0 < S := by dsimp [S];positivity
      have hM : 0 < M := by dsimp [M];positivity
      refine ⟨4*(M+|firstEndpointConstant (p+1)|),by positivity,G,hG,?_⟩
      intro g hg
      have hg2 : 2 ≤ g := hG.trans hg
      let h : ℝ := complexity g p
      have hh1 : 1 ≤ h := by dsimp [h];exact_mod_cast (show 1 ≤ complexity g p by unfold complexity;omega)
      have hh : 0 < h := by linarith
      have hsqrt : |Real.sqrt (1+1/h)-(1+(1/2:ℝ)/h)| ≤ (1/8:ℝ)/h^2 := by
        have he := Analysis.sqrt_one_add_second_error (1/h) (by positivity)
        convert he using 1 <;> ring
      have hfactor := Analysis.unit_first_order_product (-(p:ℝ)/5) (1/2)
        (1-(p:ℝ)/(5*h)) (Real.sqrt (1+1/h)) 0 (1/8) h
        (by norm_num) (by norm_num) hh1 (by
          have heq : 1-(p:ℝ)/(5*h)=1+(-(p:ℝ)/5)/h := by field_simp <;> ring
          rw [heq]
          simp) hsqrt
      have hf : |(1-(p:ℝ)/(5*h))*Real.sqrt (1+1/h)-(1+b/h)| ≤ S/h^2 := by
        convert hfactor using 1 <;> dsimp [b] <;> ring
      have he := Analysis.unit_first_order_product (firstEndpointConstant p) b
        (exactEndpoint P g p) ((1-(p:ℝ)/(5*h))*Real.sqrt (1+1/h))
        C S h hC.le hS.le hh1 (hE g hg) hf
      have he' : |exactEndpoint P g (p+1)-(1+firstEndpointConstant (p+1)/h)| ≤ M/h^2 := by
        rw [exactEndpoint_step P g p hg2,mul_assoc]
        convert he using 1 <;> rw [firstEndpointConstant_succ] <;> rfl
      have hshift := Analysis.reverse_unit_shift_error _ (firstEndpointConstant (p+1)) M h hM.le hh1 he'
      have hc : (complexity g (p+1):ℝ)=h+1 := by
        have hn : complexity g (p+1)=complexity g p+1 := by unfold complexity;omega
        rw [hn,Nat.cast_add,Nat.cast_one]
      rwa [hc]
end WP.HigherOrder
