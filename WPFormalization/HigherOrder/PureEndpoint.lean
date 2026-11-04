import WPFormalization.External.Painleve
import WPFormalization.External.SpecialFunctions
import WPFormalization.Intersection.CriticalCoefficient

/-! The actual pure-psi endpoint and its leading normalization.

This module bridges normalized critical amplitudes to the fixed rational
Painleve coefficients through the classical Itzykson--Zuber identity. All
normalizing constants are evaluated exactly. The p=0 formula is the actual
identity FE14, and the marking step is derived from string and dilaton.
Classical Painleve and fixed-shift Gamma errors then prove an inverse-genus
error for the actual normalized endpoint at every fixed p.

No all-order remainder or matching to an interior marked generating function
is assumed or proved here. The separate pureC normalization by the critical
harmonic model still requires its negative-binomial/Stirling estimate.
-/
noncomputable section
namespace WP.HigherOrder
open Filter
open scoped Topology

lemma pow_three_four_conversion (g : ℕ) (hg : 1 ≤ g) :
    (3:ℝ)^(3*g-3)*4^g = 108^g/27 := by
  apply (eq_div_iff (by norm_num : (27:ℝ) ≠ 0)).mpr
  have he : 3*g-3+3 = 3*g := by omega
  calc
    _ = ((3:ℝ)^(3*g-3)*3^3)*4^g := by ring
    _ = (3:ℝ)^(3*g)*4^g := by rw [← pow_add,he]
    _ = ((3:ℝ)^3)^g*4^g := by rw [pow_mul]
    _ = (108:ℝ)^g := by rw [← mul_pow]; norm_num

/-- The actual unmarked critical amplitude has exactly the paper's IZ normalization. -/
lemma criticalAmplitude_itzykson_zuber (P : PsiTheory) (g : ℕ) (hg : 2 ≤ g) :
    normalized P g [] y₀ = -(108:ℝ)^g*(zeroInstantonCoefficient g : ℝ)/
      (27*((5*g-5:ℕ):ℝ)*((5*g-3:ℕ):ℝ)) := by
  have hst : Stable g 0 := by unfold Stable; omega
  have hn : normalized P g [] y₀ =
      (3:ℝ)^(3*g-3)*pure P g (List.replicate (3*g-3) 2)/(3*g-3).factorial := by
    simp [normalized,deficit,dimension,hst]
  rw [hn,External.itzykson_zuber P g hg,External.phiCoefficient]
  have hf : ((3*g-3).factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (3*g-3)
  have hpow : (3:ℝ)^(3*g-3)*(2^g*2^g) = 108^g/27 := by
    rw [← mul_pow]
    norm_num only [show (2:ℝ)*2=4 by norm_num]
    exact pow_three_four_conversion g (by omega)
  have hd₁ : (((5*g-5:ℕ):ℝ)) ≠ 0 := by exact_mod_cast (show 5*g-5 ≠ 0 by omega)
  have hd₂ : (((5*g-3:ℕ):ℝ)) ≠ 0 := by exact_mod_cast (show 5*g-3 ≠ 0 by omega)
  field_simp [hf,hd₁,hd₂] at hpow ⊢
  linear_combination -(zeroInstantonCoefficient g : ℝ)*hpow

lemma painleveAction_pos : 0 < External.painleveAction := by
  unfold External.painleveAction
  positivity

lemma stokesAmplitude_pos : 0 < External.stokesAmplitude := by
  unfold External.stokesAmplitude
  exact div_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (mul_pos (by norm_num) (Real.sqrt_pos.2 Real.pi_pos))

/-- An exact bridge to the fixed PI normalization, retaining every constant. -/
lemma criticalAmplitude_normalized_painleve (P : PsiTheory) (g : ℕ) (hg : 2 ≤ g) :
    normalized P g [] y₀ = External.normalizedZeroInstanton g *
      ((108:ℝ)^g * External.stokesAmplitude * Real.Gamma (2*(g:ℝ)-1/2) /
        (27*Real.pi*Real.rpow External.painleveAction (2*(g:ℝ)-1/2)*
          ((5*g-5:ℕ):ℝ)*((5*g-3:ℕ):ℝ))) := by
  rw [criticalAmplitude_itzykson_zuber P g hg]
  unfold External.normalizedZeroInstanton
  have hS : External.stokesAmplitude ≠ 0 := ne_of_gt stokesAmplitude_pos
  have hA : Real.rpow External.painleveAction (2*(g:ℝ)-1/2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos painleveAction_pos _)
  have hgR : 0 < 2*(g:ℝ)-1/2 := by
    have : (2:ℝ) ≤ g := by exact_mod_cast hg
    linarith
  have hG : Real.Gamma (2*(g:ℝ)-1/2) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hgR)
  generalize hν : 2*(g:ℝ)-1/2 = ν at *
  field_simp [hS,hA,hG] <;> ring

lemma normalized_critical_zeros (P : PsiTheory) (g p : ℕ) (hg : 2 ≤ g) :
    normalized P g (List.replicate p 0) y₀ =
      (3:ℝ)^(dimension g p)*P.psi g (List.replicate p 0 ++ List.replicate (dimension g p) 2)/
        (dimension g p).factorial := by
  have hst : Stable g p := by unfold Stable; omega
  simp [normalized,hst,deficit,pure,oddFactorial]

/-- Actual critical amplitudes satisfy the string/dilaton insertion step. -/
lemma criticalAmplitude_step (P : PsiTheory) (g p : ℕ) (hg : 2 ≤ g) :
    normalized P g (List.replicate (p+1) 0) y₀ =
      (3*(5*(g:ℝ)-5+2*p))*normalized P g (List.replicate p 0) y₀ := by
  have hm : dimension g (p+1) = dimension g p+1 := by unfold dimension; omega
  rw [normalized_critical_zeros P g (p+1) hg,hm,psi_zeros_twos_step P g p (dimension g p) hg,
    normalized_critical_zeros P g p hg]
  have hf : ((dimension g p).factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hmR : (dimension g p:ℝ) = 3*(g:ℝ)+p-3 := by
    unfold dimension
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [pow_succ,Nat.factorial_succ,Nat.cast_mul]
  push_cast
  field_simp [hf]
  rw [hmR]
  ring

lemma criticalAmplitude_product (P : PsiTheory) (g p : ℕ) (hg : 2 ≤ g) :
    normalized P g (List.replicate p 0) y₀ =
      (∏ i ∈ Finset.range p, 3*(5*(g:ℝ)-5+2*i))*normalized P g [] y₀ := by
  induction p with
  | zero => simp
  | succ p ih =>
      rw [criticalAmplitude_step P g p hg,ih,Finset.prod_range_succ]
      ring

lemma painleveAction_sq : External.painleveAction^2 = (192/25:ℝ) := by
  unfold External.painleveAction
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  nlinarith

lemma stokesAmplitude_sq : External.stokesAmplitude^2 = Real.sqrt 3/(4*Real.pi) := by
  have hq : (Real.rpow 3 (1/4:ℝ))^2 = Real.sqrt 3 := by
    calc
      _ = Real.rpow (Real.rpow 3 (1/4:ℝ)) (2:ℝ) := (Real.rpow_natCast _ 2).symm
      _ = Real.rpow 3 ((1/4:ℝ)*2) := (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3) _ _).symm
      _ = Real.sqrt 3 := by norm_num [Real.sqrt_eq_rpow]
  unfold External.stokesAmplitude
  rw [div_pow,hq,mul_pow,Real.sq_sqrt Real.pi_pos.le]
  norm_num

lemma stokes_endpoint_normalization :
    External.stokesAmplitude*Real.sqrt External.painleveAction*Real.sqrt Real.pi/Real.sqrt (2/15:ℝ) = 3 := by
  let z := External.stokesAmplitude*Real.sqrt External.painleveAction*Real.sqrt Real.pi/Real.sqrt (2/15:ℝ)
  have hz : 0 ≤ z := by
    dsimp [z]
    exact div_nonneg (mul_nonneg (mul_nonneg stokesAmplitude_pos.le
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hz₂ : z^2 = 9 := by
    dsimp [z]
    rw [div_pow,mul_pow,mul_pow,stokesAmplitude_sq,
      Real.sq_sqrt painleveAction_pos.le,Real.sq_sqrt Real.pi_pos.le,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2/15)]
    unfold External.painleveAction
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    field_simp
    nlinarith
  change z = 3
  nlinarith

lemma painleveAction_rpow (g : ℕ) :
    Real.rpow External.painleveAction (2*(g:ℝ)-1/2) =
      (192/25:ℝ)^g/Real.sqrt External.painleveAction := by
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_sub painleveAction_pos,show 2*(g:ℝ) = ((2*g:ℕ):ℝ) by push_cast; ring,
    Real.rpow_natCast,pow_mul,painleveAction_sq]
  congr 1
  norm_num [Real.sqrt_eq_rpow]

lemma endpoint_power_conversion (g : ℕ) (hg : 1 ≤ g) :
    (108:ℝ)^g*4^g/(15/2:ℝ)^(2*g-2) = (225/4:ℝ)*(192/25:ℝ)^g := by
  have he : 2*g-2+2 = 2*g := by omega
  have hp : (15/2:ℝ)^(2*g-2) ≠ 0 := pow_ne_zero _ (by norm_num)
  apply (div_eq_iff hp).mpr
  have hh : (15/2:ℝ)^(2*g-2)*(15/2:ℝ)^2 = (15/2:ℝ)^(2*g) := by rw [← pow_add,he]
  have hbase : (192/25:ℝ)^g*(15/2:ℝ)^(2*g) = (432:ℝ)^g := by
    rw [pow_mul,← mul_pow]
    congr 1
    norm_num
  have hpow : (108:ℝ)^g*4^g = (432:ℝ)^g := by rw [← mul_pow]; norm_num
  rw [hpow,← hbase,← hh]
  ring

/- The paper's actual normalized pure-psi endpoint, with a*=2/15. -/
@[blueprint "eq:FE14"]
def exactEndpoint (P : PsiTheory) (g p : ℕ) : ℝ :=
  Real.pi*normalized P g (List.replicate p 0) y₀ /
    (Real.Gamma (complexity g p)/(4:ℝ)^g*(15/2:ℝ)^(complexity g p)*
      Real.sqrt ((2/15:ℝ)/(Real.pi*(complexity g p))))

/-- The actual p=0 identity of FE14, with h₀=2g−2. -/
lemma exactEndpoint_base (P : PsiTheory) (g : ℕ) (hg : 2 ≤ g) :
    exactEndpoint P g 0 = External.normalizedZeroInstanton g *
      (Real.Gamma (((2*g-2:ℕ):ℝ)+3/2) /
        (Real.Gamma ((2*g-2:ℕ):ℝ)*Real.rpow ((2*g-2:ℕ):ℝ) (3/2))) /
      (1+4/(5*((2*g-2:ℕ):ℝ))) := by
  let h : ℝ := ((2*g-2:ℕ):ℝ)
  have hh : 0 < h := by dsimp [h]; exact_mod_cast (by omega : 0 < 2*g-2)
  have hh₀ : h ≠ 0 := ne_of_gt hh
  have hhR : h = 2*(g:ℝ)-2 := by
    dsimp [h]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hν : 2*(g:ℝ)-1/2 = h+3/2 := by linarith
  have hd₁ : ((5*g-5:ℕ):ℝ) = (5/2:ℝ)*h := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rw [hhR]
    ring
  have hd₂ : ((5*g-3:ℕ):ℝ) = (5/2:ℝ)*h+2 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rw [hhR]
    ring
  have hR : Real.rpow h (3/2:ℝ) = h*Real.sqrt h := by
    simp only [Real.rpow_eq_pow]
    rw [show (3/2:ℝ) = 1+1/2 by norm_num,Real.rpow_add hh,Real.rpow_one]
    congr 1
    norm_num [Real.sqrt_eq_rpow]
  have hG : Real.Gamma h ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hh)
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hsA : Real.sqrt External.painleveAction ≠ 0 := ne_of_gt (Real.sqrt_pos.2 painleveAction_pos)
  have hsh : Real.sqrt h ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hh)
  have hsπ : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  have hsa : Real.sqrt (2/15:ℝ) ≠ 0 := by positivity
  have hN : (15/2:ℝ)^(2*g-2) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hQ : (192/25:ℝ)^g ≠ 0 := pow_ne_zero _ (by norm_num)
  have h₄ : (4:ℝ)^g ≠ 0 := pow_ne_zero _ (by norm_num)
  have hd : (5/2:ℝ)*h+2 ≠ 0 := by positivity
  have he : 1+4/(5*h) ≠ 0 := by positivity
  change exactEndpoint P g 0 = External.normalizedZeroInstanton g *
    (Real.Gamma (h+3/2)/(Real.Gamma h*Real.rpow h (3/2))) /(1+4/(5*h))
  rw [hR]
  unfold exactEndpoint
  simp only [List.replicate_zero,complexity,Nat.add_zero]
  rw [criticalAmplitude_normalized_painleve P g hg,painleveAction_rpow,hd₁,hd₂,hν]
  change Real.pi * (External.normalizedZeroInstanton g *
      ((108:ℝ)^g * External.stokesAmplitude * Real.Gamma (h+3/2) /
        (27*Real.pi*((192/25:ℝ)^g/Real.sqrt External.painleveAction)*
          ((5/2:ℝ)*h)*((5/2:ℝ)*h+2)))) /
      (Real.Gamma h/(4:ℝ)^g*(15/2:ℝ)^(2*g-2)*Real.sqrt ((2/15:ℝ)/(Real.pi*h))) = _
  rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 2/15),Real.sqrt_mul Real.pi_pos.le]
  calc
    _ = External.normalizedZeroInstanton g * Real.Gamma (h+3/2)/Real.Gamma h *
        (((108:ℝ)^g*4^g/(15/2:ℝ)^(2*g-2))/(27*(192/25:ℝ)^g)) *
        (External.stokesAmplitude*Real.sqrt External.painleveAction*Real.sqrt Real.pi/Real.sqrt (2/15:ℝ)) *
        Real.sqrt h / (((5/2:ℝ)*h)*((5/2:ℝ)*h+2)) := by
      field_simp [hG,hπ,hsA,hsh,hsπ,hsa,hN,hQ,h₄,hh₀,hd] <;> ring
    _ = External.normalizedZeroInstanton g * (Real.Gamma (h+3/2)/(Real.Gamma h*(h*Real.sqrt h))) /
        (1+4/(5*h)) := by
      rw [endpoint_power_conversion g (by omega),stokes_endpoint_normalization]
      field_simp [hG,hQ,hsh,hh₀,hd,he]
      ring_nf
      simp only [Real.sq_sqrt hh.le]
      ring

lemma product_relative_error (x y M N t : ℝ) (ht : 1 ≤ t) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hx : |x-1| ≤ M/t) (hy : |y-1| ≤ N/t) :
    |x*y-1| ≤ (M+N+M*N)/t := by
  have ht₀ : 0 < t := by linarith
  have hN' : N/t ≤ N := by
    apply (div_le_iff₀ ht₀).2
    nlinarith
  have hy' : |y| ≤ 1+N := by
    calc
      |y| = |(y-1)+1| := by ring_nf
      _ ≤ |y-1|+1 := by simpa using abs_add_le (y-1) 1
      _ ≤ 1+N := by linarith
  calc
    |x*y-1| = |(x-1)*y+(y-1)| := by congr 1; ring
    _ ≤ |(x-1)*y|+|y-1| := abs_add_le _ _
    _ = |x-1| * |y|+|y-1| := by rw [abs_mul]
    _ ≤ (M/t)*(1+N)+N/t := by
      exact add_le_add (mul_le_mul hx hy' (abs_nonneg _) (div_nonneg hM ht₀.le)) hy
    _ = (M+N+M*N)/t := by ring

lemma inverse_one_add_error (u : ℝ) (hu : 0 ≤ u) : |(1+u)⁻¹-1| ≤ u := by
  have hn : 1+u ≠ 0 := by positivity
  have he : (1+u)⁻¹-1 = -(u/(1+u)) := by field_simp [hn]; ring
  rw [he,abs_neg,abs_of_nonneg (div_nonneg hu (by positivity))]
  apply (div_le_iff₀ (by positivity : 0 < 1+u)).2
  nlinarith

/-- A genuine endpoint estimate deduced from classical PI and fixed-shift Gamma inputs. -/
lemma exactEndpoint_base_error (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, 2 ≤ g₀ ∧ ∀ g ≥ g₀,
      |exactEndpoint P g 0-1| ≤ C/(g:ℝ) := by
  obtain ⟨C₁,hC₁,g₁,hg₁,hPI⟩ := External.painleve_leading_error
  obtain ⟨C₂,x₀,hC₂,hx₀,hGamma⟩ := External.gamma_ratio_error (3/2) 0
  obtain ⟨N,hN⟩ := exists_nat_ge x₀
  let C₁₂ := C₁+C₂+C₁*C₂
  refine ⟨C₁₂+1+C₁₂,by dsimp [C₁₂]; positivity,max g₁ (max 2 N),by omega,?_⟩
  intro g hg
  have hg₁' : g₁ ≤ g := by omega
  have hg₂ : 2 ≤ g := by omega
  have hgN : N ≤ g := by omega
  have hgR : (1:ℝ) ≤ g := by exact_mod_cast (by omega : 1 ≤ g)
  have hg₀ : (0:ℝ) < g := by linarith
  let h : ℝ := ((2*g-2:ℕ):ℝ)
  have hhR : h = 2*(g:ℝ)-2 := by
    dsimp [h]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hgh : (g:ℝ) ≤ h := by
    have hg₂R : (2:ℝ) ≤ g := by exact_mod_cast hg₂
    linarith
  have hh : 0 < h := lt_of_lt_of_le hg₀ hgh
  have hx : x₀ ≤ h := by
    have hNg : (N:ℝ) ≤ g := by exact_mod_cast hgN
    linarith
  let R := Real.Gamma (h+3/2)/(Real.Gamma h*Real.rpow h (3/2))
  have hR : |R-1| ≤ C₂/(g:ℝ) := by
    have hRG : |R-1| ≤ C₂/h := by simpa [R] using hGamma h hx
    exact hRG.trans (div_le_div_of_nonneg_left hC₂.le hg₀ hgh)
  have hPIR : |External.normalizedZeroInstanton g*R-1| ≤ C₁₂/(g:ℝ) := by
    exact product_relative_error _ _ _ _ _ hgR hC₁.le hC₂.le (hPI g hg₁') hR
  have hD : |(1+4/(5*h))⁻¹-1| ≤ 1/(g:ℝ) := by
    have he := inverse_one_add_error (4/(5*h)) (by positivity)
    apply he.trans
    apply (div_le_div_iff₀ (by positivity : 0 < 5*h) hg₀).2
    nlinarith
  have hprod := product_relative_error (External.normalizedZeroInstanton g*R)
    ((1+4/(5*h))⁻¹) C₁₂ 1 (g:ℝ) hgR (by dsimp [C₁₂]; positivity) (by norm_num) hPIR hD
  rw [exactEndpoint_base P g hg₂]
  change |External.normalizedZeroInstanton g*R/(1+4/(5*h))-1| ≤ _
  simpa only [div_eq_mul_inv,mul_one] using hprod

/-- Exact insertion ratio for the actual endpoint normalization. -/
lemma exactEndpoint_step (P : PsiTheory) (g p : ℕ) (hg : 2 ≤ g) :
    exactEndpoint P g (p+1) = exactEndpoint P g p *
      (1-(p:ℝ)/(5*(complexity g p:ℝ))) * Real.sqrt (1+1/(complexity g p:ℝ)) := by
  let h : ℝ := complexity g p
  have hh : 0 < h := by dsimp [h,complexity]; exact_mod_cast (by omega : 0 < 2*g+p-2)
  have hhr : h = 2*(g:ℝ)+p-2 := by
    dsimp [h,complexity]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hc : complexity g (p+1) = complexity g p+1 := by unfold complexity; omega
  have hh₀ : h ≠ 0 := ne_of_gt hh
  have hG : Real.Gamma h ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hh)
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have h₄ : (4:ℝ)^g ≠ 0 := pow_ne_zero _ (by norm_num)
  have hN : (15/2:ℝ)^(complexity g p) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hs : Real.sqrt h ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hh)
  have hs₁ : Real.sqrt (h+1) ≠ 0 := by positivity
  have hsπ : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  have hsa : Real.sqrt (2/15:ℝ) ≠ 0 := by positivity
  have hsqrt : Real.sqrt (1+1/h) = Real.sqrt (h+1)/Real.sqrt h := by
    rw [← Real.sqrt_div (by positivity : 0 ≤ h+1)]
    congr 1
    field_simp [hh₀]
  unfold exactEndpoint
  rw [criticalAmplitude_step P g p hg,hc,pow_succ,Nat.cast_add,Nat.cast_one]
  change Real.pi * (3*(5*(g:ℝ)-5+2*p)*normalized P g (List.replicate p 0) y₀) /
      (Real.Gamma (h+1)/(4:ℝ)^g*((15/2:ℝ)^(complexity g p)*(15/2))*
        Real.sqrt ((2/15:ℝ)/(Real.pi*(h+1)))) =
    (Real.pi*normalized P g (List.replicate p 0) y₀ /
      (Real.Gamma h/(4:ℝ)^g*(15/2:ℝ)^(complexity g p)*Real.sqrt ((2/15:ℝ)/(Real.pi*h)))) *
      (1-(p:ℝ)/(5*h))*Real.sqrt (1+1/h)
  rw [Real.Gamma_add_one hh₀,hsqrt,
    Real.sqrt_div (by norm_num : (0:ℝ) ≤ 2/15),Real.sqrt_mul Real.pi_pos.le,
    Real.sqrt_div (by norm_num : (0:ℝ) ≤ 2/15),Real.sqrt_mul Real.pi_pos.le]
  field_simp [hG,hπ,h₄,hN,hs,hs₁,hsπ,hsa,hh₀]
  rw [hhr]
  ring

lemma sqrt_one_add_error (u : ℝ) (hu : 0 ≤ u) : |Real.sqrt (1+u)-1| ≤ u := by
  have hs₀ := Real.sqrt_nonneg (1+u)
  have hs₁ : 1 ≤ Real.sqrt (1+u) := Real.one_le_sqrt.2 (by linarith)
  have hs₂ := Real.sq_sqrt (by positivity : 0 ≤ 1+u)
  rw [abs_of_nonneg (by linarith : 0 ≤ Real.sqrt (1+u)-1)]
  nlinarith

/-- The actual normalized endpoint has an inverse-genus relative error for
 every fixed marking count, using only classical PI and Gamma asymptotics. -/
lemma exactEndpoint_error (P : PsiTheory) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, 2 ≤ g₀ ∧ ∀ g ≥ g₀,
      |exactEndpoint P g p-1| ≤ C/(g:ℝ) := by
  induction p with
  | zero => exact exactEndpoint_base_error P
  | succ p ih =>
      obtain ⟨C,hC,g₀,hg₀,hE⟩ := ih
      let D : ℝ := p/5
      let C' := C+D+C*D
      have hD : 0 ≤ D := by dsimp [D]; positivity
      have hC' : 0 < C' := by dsimp [C']; positivity
      refine ⟨C'+1+C',by positivity,g₀,hg₀,?_⟩
      intro g hg
      have hg₂ : 2 ≤ g := le_trans hg₀ hg
      have hgR : (1:ℝ) ≤ g := by exact_mod_cast (by omega : 1 ≤ g)
      have hg₀R : (0:ℝ) < g := by linarith
      let h : ℝ := complexity g p
      have hgh : (g:ℝ) ≤ h := by
        dsimp [h,complexity]
        exact_mod_cast (by omega : g ≤ 2*g+p-2)
      have hh : 0 < h := lt_of_lt_of_le hg₀R hgh
      have hA : |(1-(p:ℝ)/(5*h))-1| ≤ D/(g:ℝ) := by
        have hp₀ : 0 ≤ (p:ℝ)/(5*h) := by positivity
        calc
          _ = (p:ℝ)/(5*h) := by rw [sub_sub_cancel_left,abs_neg,abs_of_nonneg hp₀]
          _ = D/h := by dsimp [D]; ring
          _ ≤ D/(g:ℝ) := div_le_div_of_nonneg_left hD hg₀R hgh
      have hS : |Real.sqrt (1+1/h)-1| ≤ 1/(g:ℝ) := by
        exact (sqrt_one_add_error (1/h) (by positivity)).trans
          (div_le_div_of_nonneg_left (by norm_num) hg₀R hgh)
      have hEA : |exactEndpoint P g p*(1-(p:ℝ)/(5*h))-1| ≤ C'/(g:ℝ) :=
        product_relative_error _ _ C D _ hgR hC.le hD (hE g hg) hA
      rw [exactEndpoint_step P g p hg₂]
      simpa only [mul_one] using product_relative_error _ _ C' 1 _ hgR hC'.le (by norm_num) hEA hS

/- The exact finite insertion factor in FE14. -/
@[blueprint "eq:FE14"]
def endpointInsertionFactor (h : ℝ) (p : ℕ) : ℝ :=
  Real.sqrt (1+(p:ℝ)/h)*
    ∏ i ∈ Finset.range p, (1+4*(i:ℝ)/(5*h))/(1+(i:ℝ)/h)

lemma endpointInsertionFactor_zero (h : ℝ) : endpointInsertionFactor h 0 = 1 := by
  simp [endpointInsertionFactor]

lemma endpointInsertionFactor_step (h : ℝ) (hh : 0 < h) (p : ℕ) :
    endpointInsertionFactor h (p+1) = endpointInsertionFactor h p *
      (1-(p:ℝ)/(5*(h+p))) * Real.sqrt (1+1/(h+p)) := by
  have hh₀ : h ≠ 0 := ne_of_gt hh
  have hp₀ : h+(p:ℝ) ≠ 0 := by positivity
  have h₁ : 1+(p:ℝ)/h ≠ 0 := by positivity
  have hs : Real.sqrt (1+((p+1:ℕ):ℝ)/h) =
      Real.sqrt (1+(p:ℝ)/h)*Real.sqrt (1+1/(h+p)) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 1+(p:ℝ)/h)]
    congr 1
    push_cast
    field_simp [hh₀,hp₀]
    ring
  have hf : (1+4*(p:ℝ)/(5*h))/(1+(p:ℝ)/h) = 1-(p:ℝ)/(5*(h+p)) := by
    field_simp [hh₀,hp₀,h₁]
    ring
  simp only [endpointInsertionFactor,Finset.prod_range_succ]
  rw [hs,hf]
  ring

lemma exactEndpoint_factor (P : PsiTheory) (g p : ℕ) (hg : 2 ≤ g) :
    exactEndpoint P g p = exactEndpoint P g 0*endpointInsertionFactor ((2*g-2:ℕ):ℝ) p := by
  have hh : 0 < ((2*g-2:ℕ):ℝ) := by exact_mod_cast (by omega : 0 < 2*g-2)
  have hc (p : ℕ) : (complexity g p:ℝ) = ((2*g-2:ℕ):ℝ)+p := by
    have hn : complexity g p = (2*g-2)+p := by unfold complexity; omega
    rw [hn,Nat.cast_add]
  induction p with
  | zero => simp [endpointInsertionFactor_zero]
  | succ p ih =>
      rw [exactEndpoint_step P g p hg,ih,hc,endpointInsertionFactor_step _ hh]
      ring

/- The actual normalized endpoint satisfies the full exact identity FE14. -/
@[blueprint "eq:FE14"]
lemma exactEndpoint_formula (P : PsiTheory) (g p : ℕ) (hg : 2 ≤ g) :
    exactEndpoint P g p = External.normalizedZeroInstanton g *
      (Real.Gamma (((2*g-2:ℕ):ℝ)+3/2) /
        (Real.Gamma ((2*g-2:ℕ):ℝ)*Real.rpow ((2*g-2:ℕ):ℝ) (3/2))) *
      endpointInsertionFactor ((2*g-2:ℕ):ℝ) p /(1+4/(5*((2*g-2:ℕ):ℝ))) := by
  rw [exactEndpoint_factor P g p hg,exactEndpoint_base P g hg]
  ring

end WP.HigherOrder
