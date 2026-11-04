import WPFormalization.HigherOrder.PureEndpoint

/-! The central negative-binomial factor and the actual pure-psi endpoint.

The normalization N at h=2n,m=3n is evaluated against the ordinary Gamma
Stirling main terms exactly. The classical Gamma error then gives N=1+O(1/n).
An exact numerical identity E=pi*C_pure*N transports the already proved actual
endpoint estimate to the normalized all-twos intersection number. Finally the
classical string reduction and a proved finite-product bound handle each fixed
number of zero markings.

`endpoint_pure_limit_proof` is the original paper target with its full O(1/g)
rate. It has no additional hypotheses beyond PsiTheory, and uses only the
explicit classical external PI/IZ/Gamma inputs, not paper comparison, profile,
kernel moment or asymptotic assumptions. This module avoids importing Marked,
so the original statement there can use this proof without a cycle.
-/
noncomputable section
namespace WP.HigherOrder

/-- The central negative-binomial normalization at h=2n, m=3n. -/
def negativeBinomialNormalization (n : ℕ) : ℝ :=
  Real.sqrt (15*Real.pi*n)/(3*n)*(108/3125:ℝ)^n*
    Real.Gamma (5*(n:ℝ))/(Real.Gamma (2*(n:ℝ))*Real.Gamma (3*(n:ℝ)))

lemma gammaStirlingMain_nat (n : ℕ) (hn : 0 < n) :
    External.gammaStirlingMain (n:ℝ) =
      Real.sqrt (2*Real.pi)*(n:ℝ)^n/Real.sqrt n*Real.exp (-(n:ℝ)) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  unfold External.gammaStirlingMain
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_sub hnR,Real.rpow_natCast]
  have hs : (n:ℝ)^(1/2:ℝ) = Real.sqrt n := by norm_num [Real.sqrt_eq_rpow]
  rw [hs]
  ring

lemma central_sqrt_identity (n : ℝ) (hn : 0 ≤ n) :
    Real.sqrt (15*Real.pi*n)*Real.sqrt (2*n)*Real.sqrt (3*n) =
      3*n*Real.sqrt (2*Real.pi)*Real.sqrt (5*n) := by
  have hleft : 0 ≤ Real.sqrt (15*Real.pi*n)*Real.sqrt (2*n)*Real.sqrt (3*n) := by positivity
  have hright : 0 ≤ 3*n*Real.sqrt (2*Real.pi)*Real.sqrt (5*n) := by positivity
  have hs : (Real.sqrt (15*Real.pi*n)*Real.sqrt (2*n)*Real.sqrt (3*n))^2 =
      (3*n*Real.sqrt (2*Real.pi)*Real.sqrt (5*n))^2 := by
    simp only [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 15*Real.pi*n),
      Real.sq_sqrt (by positivity : 0 ≤ 2*n),Real.sq_sqrt (by positivity : 0 ≤ 3*n),
      Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi),Real.sq_sqrt (by positivity : 0 ≤ 5*n)]
    ring
  nlinarith

/-- The ordinary Stirling main terms give exactly the central NB normalization. -/
lemma central_stirling_main (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (15*Real.pi*n)/(3*n)*(108/3125:ℝ)^n*
      External.gammaStirlingMain (5*(n:ℝ)) /
        (External.gammaStirlingMain (2*(n:ℝ))*External.gammaStirlingMain (3*(n:ℝ))) = 1 := by
  have hn₀ : (n:ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hmain (k : ℕ) (hk : 0 < k) :
      External.gammaStirlingMain ((k:ℝ)*n) =
        Real.sqrt (2*Real.pi)*((k:ℝ)*n)^(k*n)/Real.sqrt ((k:ℝ)*n)*Real.exp (-((k:ℝ)*n)) := by
    simpa only [Nat.cast_mul] using gammaStirlingMain_nat (k*n) (Nat.mul_pos hk (by omega))
  have hm₅ := hmain 5 (by norm_num)
  have hm₂ := hmain 2 (by norm_num)
  have hm₃ := hmain 3 (by norm_num)
  norm_num only [Nat.cast_ofNat] at hm₅ hm₂ hm₃
  rw [hm₅,hm₂,hm₃]
  have hp (k : ℕ) : ((k:ℝ)*n)^(k*n) = ((k:ℝ)^k)^n*(n:ℝ)^(k*n) := by
    rw [mul_pow,pow_mul]
  have hp₅ := hp 5
  have hp₂ := hp 2
  have hp₃ := hp 3
  norm_num only [Nat.cast_ofNat] at hp₅ hp₂ hp₃
  rw [hp₅,hp₂,hp₃]
  norm_num only [show (5:ℝ)^5=3125 by norm_num,show (2:ℝ)^2=4 by norm_num,
    show (3:ℝ)^3=27 by norm_num]
  have he : Real.exp (-(5*(n:ℝ))) = Real.exp (-(2*(n:ℝ)))*Real.exp (-(3*(n:ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpN : (n:ℝ)^(5*n) = (n:ℝ)^(2*n)*(n:ℝ)^(3*n) := by
    rw [← pow_add]
    congr 1
    omega
  have hpB : (108/3125:ℝ)^n*3125^n = 4^n*27^n := by
    rw [← mul_pow,← mul_pow]
    congr 1
    norm_num
  have hs := central_sqrt_identity (n:ℝ) hnR.le
  have h₂ : Real.sqrt (2*(n:ℝ)) ≠ 0 := by positivity
  have h₃ : Real.sqrt (3*(n:ℝ)) ≠ 0 := by positivity
  have h₅ : Real.sqrt (5*(n:ℝ)) ≠ 0 := by positivity
  have hπ : Real.sqrt (2*Real.pi) ≠ 0 := by positivity
  have h₄n : (4:ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have h₂₇n : (27:ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hn₂ : (n:ℝ)^(2*n) ≠ 0 := pow_ne_zero _ hn₀
  have hn₃ : (n:ℝ)^(3*n) ≠ 0 := pow_ne_zero _ hn₀
  rw [he,hpN]
  have hpow : (108/3125:ℝ)^n*3125^n*(n:ℝ)^(2*n)*(n:ℝ)^(3*n) =
      4^n*27^n*(n:ℝ)^(2*n)*(n:ℝ)^(3*n) := by rw [hpB]
  field_simp [hn₀,h₂,h₃,h₅,hπ,h₄n,h₂₇n,hn₂,hn₃,Real.exp_ne_zero]
  simp only [← mul_comm (2:ℝ) (n:ℝ),← mul_comm (3:ℝ) (n:ℝ),
    ← mul_comm (5:ℝ) (n:ℝ),← mul_comm (2:ℝ) Real.pi]
  linear_combination (4:ℝ)^n*27^n*hs +
    Real.sqrt (15*Real.pi*n)*Real.sqrt (2*(n:ℝ))*Real.sqrt (3*(n:ℝ))*hpB

/-- The actual Gamma value divided by its classical leading Stirling term. -/
def gammaStirlingRelative (x : ℝ) : ℝ := Real.Gamma x/External.gammaStirlingMain x

lemma gammaStirlingMain_pos (x : ℝ) (hx : 0 < x) : 0 < External.gammaStirlingMain x := by
  unfold External.gammaStirlingMain
  exact mul_pos (mul_pos (Real.sqrt_pos.2 (by positivity))
    (Real.rpow_pos_of_pos hx _)) (Real.exp_pos _)

lemma negativeBinomialNormalization_stirling (n : ℕ) (hn : 1 ≤ n) :
    negativeBinomialNormalization n = gammaStirlingRelative (5*(n:ℝ))/
      (gammaStirlingRelative (2*(n:ℝ))*gammaStirlingRelative (3*(n:ℝ))) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hm₂ : External.gammaStirlingMain (2*(n:ℝ)) ≠ 0 :=
    ne_of_gt (gammaStirlingMain_pos _ (by positivity))
  have hm₃ : External.gammaStirlingMain (3*(n:ℝ)) ≠ 0 :=
    ne_of_gt (gammaStirlingMain_pos _ (by positivity))
  have hm₅ : External.gammaStirlingMain (5*(n:ℝ)) ≠ 0 :=
    ne_of_gt (gammaStirlingMain_pos _ (by positivity))
  have hg₂ : Real.Gamma (2*(n:ℝ)) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hg₃ : Real.Gamma (3*(n:ℝ)) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hpref : Real.sqrt (15*Real.pi*n)/(3*n)*(108/3125:ℝ)^n =
      External.gammaStirlingMain (2*(n:ℝ))*External.gammaStirlingMain (3*(n:ℝ))/
        External.gammaStirlingMain (5*(n:ℝ)) := by
    apply (eq_div_iff hm₅).2
    have he := (div_eq_iff (mul_ne_zero hm₂ hm₃)).1 (central_stirling_main n hn)
    simpa using he
  unfold negativeBinomialNormalization gammaStirlingRelative
  rw [hpref]
  field_simp [hm₂,hm₃,hm₅,hg₂,hg₃]

lemma quotient_relative_error (x y M N t : ℝ) (ht : 0 < t) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hy₀ : 1/2 ≤ y) (hx : |x-1| ≤ M/t) (hy : |y-1| ≤ N/t) :
    |x/y-1| ≤ 2*(M+N)/t := by
  have hypos : 0 < y := by linarith
  have hyne : y ≠ 0 := ne_of_gt hypos
  have he : x/y-1 = ((x-1)-(y-1))/y := by field_simp [hyne]; ring
  have hMN : 0 ≤ M/t+N/t := by positivity
  calc
    |x/y-1| = |(x-1)-(y-1)|/y := by rw [he,abs_div,abs_of_pos hypos]
    _ ≤ (|x-1|+|y-1|)/y := div_le_div_of_nonneg_right (abs_sub _ _) hypos.le
    _ ≤ (M/t+N/t)/y := div_le_div_of_nonneg_right (add_le_add hx hy) hypos.le
    _ ≤ (M/t+N/t)*2 := by
      apply (div_le_iff₀ hypos).2
      nlinarith [mul_nonneg hMN (show 0 ≤ y-1/2 by linarith)]
    _ = 2*(M+N)/t := by ring

/-- The central NB error follows from the ordinary Gamma error at 2n,3n,5n. -/
lemma negativeBinomialNormalization_error :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n ≥ n₀,
      |negativeBinomialNormalization n-1| ≤ C/(n:ℝ) := by
  obtain ⟨C,x₀,hC,hx₀,hGamma⟩ := External.gamma_stirling_error
  let M := C+C+C*C
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨N,hN⟩ := exists_nat_ge (max x₀ (2*M))
  refine ⟨2*(C+M),by positivity,max 1 N,by omega,?_⟩
  intro n hn
  have hn₁ : 1 ≤ n := by omega
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn₁
  have hn₀ : (0:ℝ) < n := by linarith
  have hx : x₀ ≤ (n:ℝ) := by
    have hNn : (N:ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
    exact le_trans (le_trans (le_max_left _ _) hN) hNn
  have hMn : 2*M ≤ (n:ℝ) := by
    have hNn : (N:ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
    exact le_trans (le_trans (le_max_right _ _) hN) hNn
  have hG (k : ℕ) (hk : 1 ≤ k) : |gammaStirlingRelative ((k:ℝ)*n)-1| ≤ C/(n:ℝ) := by
    have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hkn : (n:ℝ) ≤ (k:ℝ)*n := by nlinarith
    exact (hGamma ((k:ℝ)*n) (le_trans hx hkn)).trans
      (div_le_div_of_nonneg_left hC.le hn₀ hkn)
  have hG₂ : |gammaStirlingRelative (2*(n:ℝ))-1| ≤ C/(n:ℝ) := by simpa using hG 2 (by norm_num)
  have hG₃ : |gammaStirlingRelative (3*(n:ℝ))-1| ≤ C/(n:ℝ) := by simpa using hG 3 (by norm_num)
  have hG₅ : |gammaStirlingRelative (5*(n:ℝ))-1| ≤ C/(n:ℝ) := by simpa using hG 5 (by norm_num)
  have hprod := product_relative_error _ _ C C (n:ℝ) hnR hC.le hC.le hG₂ hG₃
  have hhalf : M/(n:ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hn₀).2
    linarith
  have hy : 1/2 ≤ gammaStirlingRelative (2*(n:ℝ))*gammaStirlingRelative (3*(n:ℝ)) := by
    have hlow := (abs_le.1 hprod).1
    change -(M/(n:ℝ)) ≤ _ at hlow
    linarith
  rw [negativeBinomialNormalization_stirling n hn₁]
  exact quotient_relative_error _ _ C M _ hn₀ hC.le hM.le hy hG₅ hprod

/-- Exact bridge between the actual endpoint and the normalized all-twos intersection. -/
lemma exactEndpoint_eq_pureC_mul_negativeBinomial (P : PsiTheory) (n : ℕ) (hn : 1 ≤ n) :
    exactEndpoint P (n+1) 0 = Real.pi*pureC P (n+1) (List.replicate (3*n) 2)*
      negativeBinomialNormalization n := by
  have hg : 2 ≤ n+1 := by omega
  have hc₀ : complexity (n+1) 0 = 2*n := by unfold complexity; omega
  have hc₃ : complexity (n+1) (3*n) = 5*n := by unfold complexity; omega
  have hd : dimension (n+1) 0 = 3*n := by unfold dimension; omega
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn₀ : (n:ℝ) ≠ 0 := ne_of_gt hnR
  have hΓ₂ : Real.Gamma (2*(n:ℝ)) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hΓ₃ : Real.Gamma (3*(n:ℝ)) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hΓ₅ : Real.Gamma (5*(n:ℝ)) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hfac : ((3*n).factorial:ℝ) = 3*(n:ℝ)*Real.Gamma (3*(n:ℝ)) := by
    rw [← Real.Gamma_nat_eq_factorial,Real.Gamma_add_one (by positivity : ((3*n:ℕ):ℝ) ≠ 0)]
    norm_num [Nat.cast_mul]
  have hp : pureC P (n+1) (List.replicate (3*n) 2) =
      (4:ℝ)^(n+1)*15^(3*n)/(3^(5*n)*Real.Gamma (5*(n:ℝ)))*P.psi (n+1) (List.replicate (3*n) 2) := by
    have he := pureC_zeros_twos_formula P (n+1) 0 (3*n)
    simpa [hc₃,Nat.cast_mul] using he
  have hs : Real.sqrt ((2/15:ℝ)/(Real.pi*(2*(n:ℝ)))) = 1/Real.sqrt (15*Real.pi*n) := by
    have hroot : Real.sqrt (15*Real.pi*n)*Real.sqrt ((2/15:ℝ)/(Real.pi*(2*(n:ℝ)))) = 1 := by
      rw [← Real.sqrt_mul (by positivity : 0 ≤ 15*Real.pi*n)]
      have he : 15*Real.pi*(n:ℝ)*((2/15:ℝ)/(Real.pi*(2*(n:ℝ)))) = 1 := by
        field_simp
      rw [he,Real.sqrt_one]
    apply (eq_div_iff (by positivity : Real.sqrt (15*Real.pi*n) ≠ 0)).2
    nlinarith
  have hpow : (15:ℝ)^(3*n)*(108/3125:ℝ)^n*(15/2:ℝ)^(2*n) = 3^(3*n)*3^(5*n) := by
    rw [← pow_add,show 3*n+5*n=8*n by omega,pow_mul,pow_mul,pow_mul]
    rw [← mul_pow,← mul_pow]
    congr 1
    norm_num
  unfold exactEndpoint negativeBinomialNormalization
  rw [normalized_critical_zeros P (n+1) 0 hg,hc₀,hd,hp,hfac]
  simp only [List.replicate_zero,List.nil_append,Nat.cast_mul,Nat.cast_ofNat]
  rw [hs]
  have hroot₀ : Real.sqrt (15*Real.pi*n) ≠ 0 := by positivity
  have h₄ : (4:ℝ)^(n+1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h₃ : (3:ℝ)^(5*n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h₁₅ : (15/2:ℝ)^(2*n) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hn₀,hΓ₂,hΓ₃,hΓ₅,hroot₀,h₄,h₃,h₁₅]
  linear_combination -(P.psi (n+1) (List.replicate (3*n) 2))*hpow

/-- The all-twos normalized intersection has inverse-genus error about 1/pi. -/
lemma pureC_twos_error (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, 2 ≤ g₀ ∧ ∀ g ≥ g₀,
      |Real.pi*pureC P g (List.replicate (3*g-3) 2)-1| ≤ C/(g:ℝ) := by
  obtain ⟨C₁,hC₁,g₁,hg₁,hE⟩ := exactEndpoint_base_error P
  obtain ⟨C₂,hC₂,n₂,hn₂,hN⟩ := negativeBinomialNormalization_error
  obtain ⟨N,hNhalf⟩ := exists_nat_ge (2*C₂)
  refine ⟨4*(C₁+C₂),by positivity,max g₁ (max (n₂+1) (N+1)),by omega,?_⟩
  intro g hg
  have hg₁' : g₁ ≤ g := by omega
  have hg₂ : 2 ≤ g := by omega
  let n := g-1
  have hn₁ : 1 ≤ n := by dsimp [n]; omega
  have hn₂' : n₂ ≤ n := by dsimp [n]; omega
  have hnN : N ≤ n := by dsimp [n]; omega
  have hnEq : n+1 = g := by dsimp [n]; omega
  have hm : 3*n = 3*g-3 := by dsimp [n]; omega
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hgR : 0 < (g:ℝ) := by exact_mod_cast (by omega : 0 < g)
  have hng : (n:ℝ) ≤ g := by exact_mod_cast (by dsimp [n]; omega : n ≤ g)
  have hgn : (g:ℝ) ≤ 2*n := by exact_mod_cast (by dsimp [n]; omega : g ≤ 2*n)
  have hEn : |exactEndpoint P g 0-1| ≤ C₁/(n:ℝ) :=
    (hE g hg₁').trans (div_le_div_of_nonneg_left hC₁.le hnR hng)
  have hNN : 2*C₂ ≤ (n:ℝ) := by
    have hNn : (N:ℝ) ≤ n := by exact_mod_cast hnN
    linarith
  have hhalf : C₂/(n:ℝ) ≤ 1/2 := by apply (div_le_iff₀ hnR).2; linarith
  have hy : 1/2 ≤ negativeBinomialNormalization n := by
    have hlow := (abs_le.1 (hN n hn₂')).1
    linarith
  have hq := quotient_relative_error (exactEndpoint P g 0) (negativeBinomialNormalization n)
    C₁ C₂ (n:ℝ) hnR hC₁.le hC₂.le hy hEn (hN n hn₂')
  have hb := exactEndpoint_eq_pureC_mul_negativeBinomial P n hn₁
  rw [hnEq,hm] at hb
  have hy₀ : negativeBinomialNormalization n ≠ 0 := by linarith
  have he : exactEndpoint P g 0/negativeBinomialNormalization n =
      Real.pi*pureC P g (List.replicate (3*g-3) 2) := by rw [hb]; field_simp [hy₀]
  rw [he] at hq
  apply hq.trans
  apply (div_le_div_iff₀ hnR hgR).2
  nlinarith [mul_nonneg (show 0 ≤ C₁+C₂ by positivity) (show 0 ≤ 2*(n:ℝ)-g by linarith)]

/-- A finite recursive constant for products with inverse-scale relative errors. -/
def productErrorConstant (M : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => productErrorConstant M n+M+productErrorConstant M n*M

lemma productErrorConstant_nonneg (M : ℝ) (hM : 0 ≤ M) (n : ℕ) :
    0 ≤ productErrorConstant M n := by
  induction n with
  | zero => simp [productErrorConstant]
  | succ n ih => simp only [productErrorConstant]; positivity

lemma finite_product_relative_error (f : ℕ → ℝ) (M t : ℝ) (hM : 0 ≤ M) (ht : 1 ≤ t)
    (n : ℕ) (hf : ∀ i < n, |f i-1| ≤ M/t) :
    |(∏ i ∈ Finset.range n, f i)-1| ≤ productErrorConstant M n/t := by
  induction n with
  | zero => simp [productErrorConstant]
  | succ n ih =>
      rw [Finset.prod_range_succ]
      exact product_relative_error _ _ _ M t ht (productErrorConstant_nonneg M hM n) hM
        (ih (fun i hi => hf i (by omega))) (hf n (by omega))

lemma endpoint_string_factor_error (g p i : ℕ) (hg : 2 ≤ g) (hi : i < p) :
    |5*((dimension g p:ℝ)-i)/(3*(2*(g:ℝ)-3+p+dimension g p-2*i))-1| ≤ ((p:ℝ)+3)/g := by
  have hgR : (2:ℝ) ≤ g := by exact_mod_cast hg
  have hiR : (i:ℝ)+1 ≤ p := by exact_mod_cast (Nat.succ_le_of_lt hi)
  have hi₀ : (0:ℝ) ≤ i := by positivity
  have hp₀ : (0:ℝ) ≤ p := by positivity
  have hm : (dimension g p:ℝ) = 3*(g:ℝ)+p-3 := by
    unfold dimension
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  let D : ℝ := 3*(2*(g:ℝ)-3+p+dimension g p-2*i)
  have hD : (g:ℝ) ≤ D := by dsimp [D]; rw [hm]; linarith
  have hD₀ : 0 < D := by linarith
  have hg₀ : (0:ℝ) < g := by linarith
  have he : 5*((dimension g p:ℝ)-i)/D-1 = (3-p+(i:ℝ))/D := by
    field_simp [ne_of_gt hD₀]
    dsimp [D]
    rw [hm]
    ring
  have hn : |3-(p:ℝ)+i| ≤ (p:ℝ)+3 := by rw [abs_le]; constructor <;> linarith
  change |5*((dimension g p:ℝ)-i)/D-1| ≤ _
  rw [he,abs_div,abs_of_pos hD₀]
  exact (div_le_div_of_nonneg_right hn hD₀.le).trans
    (div_le_div_of_nonneg_left (by positivity) hg₀ hD)

/-- The original paper endpoint pureC limit, with its inverse-genus rate. -/
lemma endpoint_pure_limit_proof (P : PsiTheory) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀,
      |pureC P g (List.replicate p 0 ++ List.replicate (dimension g p) 2)-1/Real.pi| ≤ C/(g:ℝ) := by
  obtain ⟨C,hC,g₀,hg₀,hB⟩ := pureC_twos_error P
  let D := productErrorConstant ((p:ℝ)+3) p
  have hD : 0 ≤ D := productErrorConstant_nonneg _ (by positivity) p
  refine ⟨(C+D+C*D)/Real.pi,by positivity,g₀,?_⟩
  intro g hg
  have hg₂ : 2 ≤ g := le_trans hg₀ hg
  have hgR : (1:ℝ) ≤ g := by exact_mod_cast (by omega : 1 ≤ g)
  let F (i : ℕ) : ℝ := 5*((dimension g p:ℝ)-i)/(3*(2*(g:ℝ)-3+p+dimension g p-2*i))
  have hF : |(∏ i ∈ Finset.range p, F i)-1| ≤ D/(g:ℝ) :=
    finite_product_relative_error F _ _ (by positivity) hgR p
      (fun i hi => endpoint_string_factor_error g p i hg₂ hi)
  have hprod := product_relative_error (Real.pi*pureC P g (List.replicate (3*g-3) 2))
    (∏ i ∈ Finset.range p, F i) C D (g:ℝ) hgR hC.le hD (hB g hg) hF
  have hp : p ≤ dimension g p := by unfold dimension; omega
  have hs : dimension g p-p = 3*g-3 := by unfold dimension; omega
  have hstr := pureC_zeros_twos_reduce P g p (dimension g p) hg₂ hp
  rw [hs] at hstr
  have he : Real.pi*pureC P g (List.replicate p 0 ++ List.replicate (dimension g p) 2) =
      (Real.pi*pureC P g (List.replicate (3*g-3) 2))*(∏ i ∈ Finset.range p, F i) := by
    rw [hstr]
    dsimp [F]
    ring
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hscale : pureC P g (List.replicate p 0 ++ List.replicate (dimension g p) 2)-1/Real.pi =
      (Real.pi*pureC P g (List.replicate p 0 ++ List.replicate (dimension g p) 2)-1)/Real.pi := by
    field_simp [hπ]
  rw [hscale,abs_div,abs_of_pos Real.pi_pos,he]
  exact (div_le_div_of_nonneg_right hprod Real.pi_pos.le).trans_eq (by ring)

end WP.HigherOrder
