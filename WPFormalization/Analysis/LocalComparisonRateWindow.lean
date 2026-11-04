import Mathlib

noncomputable section
namespace WP.Analysis

lemma local_comparison_fixed_order_selection (ctail E : ℝ)
    (hc : 0 < ctail) (hE : 0 < E) :
    ∃ A : ℝ, 0 < A ∧ ∃ N K : ℕ,
      1 ≤ N ∧ Odd K ∧ K+1=2*N ∧ ctail*A=4 ∧
      256*E*A+4 ≤ (N:ℝ) := by
  let A : ℝ := 4/ctail
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨N,hN⟩ := exists_nat_ge (256*E*A+4)
  have hN1 : 1 ≤ N := by
    have hp : 0 < 256*E*A := by positivity
    by_contra hn
    have hz : N=0 := by omega
    simp only [hz,Nat.cast_zero] at hN
    linarith
  refine ⟨A,hA,N,2*N-1,hN1,?_,by omega,?_,hN⟩
  · exact ⟨N-1,by omega⟩
  · dsimp [A]
    field_simp

lemma local_comparison_sqrt_error (D h : ℝ) (N : ℕ)
    (hD : 0 ≤ D) (hh : 0 < h) :
    Real.sqrt (D/h^(2*N)) = Real.sqrt D/h^N := by
  rw [show 2*N=N*2 by omega,pow_mul,Real.sqrt_div hD,Real.sqrt_sq (by positivity)]

lemma local_comparison_fixed_order_point_error (A E D Dreal h : ℝ) (N : ℕ)
    (hA : 0 < A) (hE : 0 < E) (hD : 0 < D) (hDr : 0 < Dreal)
    (hh : 1 ≤ h) (hN : 256*E*A+4 ≤ (N:ℝ)) :
    4*Real.sqrt (Dreal/h^(2*N)) *
        (D*Real.exp (E*(16*Real.sqrt (A*Real.log h))^2)) ≤
      (4*Real.sqrt Dreal*D)/h^4 := by
  have hp : 0 < h := by linarith
  have hl : 0 ≤ Real.log h := Real.log_nonneg hh
  have hAl : 0 ≤ A*Real.log h := mul_nonneg hA.le hl
  have hsq := Real.sq_sqrt hAl
  have hN4 : 4 ≤ N := by
    by_contra hn
    have hnR : (N:ℝ) < 4 := by exact_mod_cast (show N < 4 by omega)
    have hpos : 0 < 256*E*A := by positivity
    linarith
  have hexponent : 256*E*A ≤ ((N-4:ℕ):ℝ) := by
    rw [Nat.cast_sub hN4]
    norm_num
    linarith
  have he : Real.exp (E*(16*Real.sqrt (A*Real.log h))^2) ≤ h^(N-4) := by
    have hx : E*(16*Real.sqrt (A*Real.log h))^2 = 256*E*A*Real.log h := by
      rw [mul_pow,hsq]
      ring
    rw [hx]
    have hx' := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hexponent hl)
    simpa only [Real.exp_nat_mul,Real.exp_log hp] using hx'
  rw [local_comparison_sqrt_error Dreal h N hDr.le hp]
  calc
    _ ≤ 4*(Real.sqrt Dreal/h^N)*(D*h^(N-4)) := by gcongr
    _ = _ := by
      have hpow : h^N=h^(N-4)*h^4 := by
        rw [←pow_add]
        congr 1
        omega
      rw [hpow]
      field_simp
      <;> ring

lemma local_comparison_gaussian_tail (A ctail h : ℝ)
    (hA : 0 < A) (hc : 0 < ctail) (hh : 1 ≤ h) (hAc : 3 ≤ ctail*A) :
    Real.exp (-ctail*(Real.sqrt (A*Real.log h))^2) ≤ 1/h^3 := by
  have hp : 0 < h := by linarith
  have hl : 0 ≤ Real.log h := Real.log_nonneg hh
  have hsq := Real.sq_sqrt (mul_nonneg hA.le hl)
  have he : -ctail*(Real.sqrt (A*Real.log h))^2 ≤ -(3*Real.log h) := by
    rw [hsq]
    nlinarith only [mul_le_mul_of_nonneg_right hAc hl]
  apply (Real.exp_le_exp.mpr he).trans
  rw [Real.exp_neg,show (3:ℝ)*Real.log h=(3:ℕ)*Real.log h by norm_num,
    Real.exp_nat_mul,Real.exp_log hp,one_div]

lemma local_comparison_fixed_order_budget (B cbudget Dreal H₀ : ℝ) (N K : ℕ)
    (hB : 0 < B) (hcb : 0 < cbudget) (hDr : 0 < Dreal) (hN : 1 ≤ N) :
    ∃ H : ℝ, 0 < H ∧ H₀ ≤ H ∧ ∀ h : ℝ, H ≤ h →
      2 ≤ h ∧ (K:ℝ) ≤ cbudget*Real.sqrt h ∧
      2*B*((K+1:ℕ):ℝ)^2 ≤ h ∧
      0 < Dreal/h^(2*N) ∧ Dreal/h^(2*N) ≤ 1/2 := by
  let H : ℝ := 2+|H₀|+2*Dreal+2*B*((K+1:ℕ):ℝ)^2+((K:ℝ)/cbudget)^2
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨H,hH,?_,?_⟩
  · have habs := le_abs_self H₀
    dsimp [H]
    nlinarith [sq_nonneg ((K:ℝ)/cbudget),
      mul_nonneg hB.le (sq_nonneg (((K+1:ℕ):ℝ)))]
  · intro h hh
    have hg2 : 2 ≤ h := by
      dsimp [H] at hh
      nlinarith [sq_nonneg ((K:ℝ)/cbudget),abs_nonneg H₀,
        mul_nonneg hB.le (sq_nonneg (((K+1:ℕ):ℝ)))]
    have hg0 : 0 < h := by linarith
    have hKsq : ((K:ℝ)/cbudget)^2 ≤ h := by
      dsimp [H] at hh
      nlinarith [abs_nonneg H₀,mul_nonneg hB.le (sq_nonneg (((K+1:ℕ):ℝ)))]
    have hK : (K:ℝ) ≤ cbudget*Real.sqrt h := by
      have hs : (K:ℝ)/cbudget ≤ Real.sqrt h := (Real.le_sqrt (by positivity) hg0.le).mpr hKsq
      simpa only [mul_comm] using (div_le_iff₀ hcb).mp hs
    have hbudget : 2*B*((K+1:ℕ):ℝ)^2 ≤ h := by
      dsimp [H] at hh
      nlinarith [sq_nonneg ((K:ℝ)/cbudget),abs_nonneg H₀]
    have hD2 : 2*Dreal ≤ h := by
      dsimp [H] at hh
      nlinarith [sq_nonneg ((K:ℝ)/cbudget),abs_nonneg H₀,
        mul_nonneg hB.le (sq_nonneg (((K+1:ℕ):ℝ)))]
    have hpow : h ≤ h^(2*N) := by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ h) (show 1 ≤ 2*N by omega)
    refine ⟨hg2,hK,hbudget,by positivity,?_⟩
    apply (div_le_iff₀ (by positivity : 0 < h^(2*N))).mpr
    linarith

end WP.Analysis
