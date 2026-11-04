import WPFormalization.HigherOrder.PainleveFormalRecurrences
/-! Explicit factorial bounds for the actual rational Painleve coefficients, proved from their canonical recurrences. No analytic large-order estimate is assumed here. -/
noncomputable section
namespace WP.HigherOrder
lemma factorial_positive_product_le (a b : ℕ) :
    (a+1).factorial*(b+1).factorial ≤ (a+b+1).factorial := by
  induction a with
  | zero => simp
  | succ a ih =>
      calc
        _ = (a+2)*((a+1).factorial*(b+1).factorial) := by rw [Nat.factorial_succ];ring
        _ ≤ (a+2)*(a+b+1).factorial := Nat.mul_le_mul_left _ ih
        _ ≤ (a+b+2)*(a+b+1).factorial := Nat.mul_le_mul_right _ (by omega)
        _ = (a+b+1+1).factorial := (Nat.factorial_succ (a+b+1)).symm
        _ = _ := by congr 1;omega
lemma factorial_interior_product_le (n j : ℕ) (hj : j∈Finset.Icc 1 n) :
    j.factorial*(n+1-j).factorial ≤ n.factorial := by
  have hj' := Finset.mem_Icc.mp hj
  have he := factorial_positive_product_le (j-1) (n-j)
  have h1 : j-1+1=j := by omega
  have h2 : n-j+1=n+1-j := by omega
  have h3 : j-1+(n-j)+1=n := by omega
  simpa only [h1,h2,h3] using he
lemma zeroInstantonCoefficient_factorial_bound (g : ℕ) :
    |zeroInstantonCoefficient g| ≤ (g.factorial:ℚ)^2 := by
  induction g using Nat.strong_induction_on with
  | h g ih =>
      rcases g with _|n
      · norm_num
      · by_cases hn : n=0
        · subst n;norm_num
        have hn1 : 1 ≤ n := by omega
        have hnQ : (1:ℚ) ≤ n := by exact_mod_cast hn1
        have hcoef : |(25*(n:ℚ)^2-1)/48| ≤ (n:ℚ)^2 := by
          rw [abs_of_nonneg (by nlinarith : 0 ≤ (25*(n:ℚ)^2-1)/48)]
          nlinarith
        have hterm (j : ℕ) (hj : j∈Finset.Icc 1 n) :
            |zeroInstantonCoefficient j*zeroInstantonCoefficient (n+1-j)| ≤ (n.factorial:ℚ)^2 := by
          have hj' := Finset.mem_Icc.mp hj
          have hjB := ih j (by omega)
          have hkB := ih (n+1-j) (by omega)
          have hfQ : (j.factorial:ℚ)*(n+1-j).factorial ≤ n.factorial := by
            exact_mod_cast factorial_interior_product_le n j hj
          rw [abs_mul]
          calc
            _ ≤ (j.factorial:ℚ)^2*((n+1-j).factorial:ℚ)^2 := mul_le_mul hjB hkB (abs_nonneg _) (sq_nonneg _)
            _ = ((j.factorial:ℚ)*(n+1-j).factorial)^2 := by ring
            _ ≤ _ := pow_le_pow_left₀ (by positivity) hfQ 2
        have hsum : |∑ j∈Finset.Icc 1 n,zeroInstantonCoefficient j*zeroInstantonCoefficient (n+1-j)| ≤
            (n:ℚ)*(n.factorial:ℚ)^2 := by
          calc
            _ ≤ ∑ j∈Finset.Icc 1 n,|zeroInstantonCoefficient j*zeroInstantonCoefficient (n+1-j)| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ j∈Finset.Icc 1 n,(n.factorial:ℚ)^2 := Finset.sum_le_sum hterm
            _ = _ := by simp
        rw [zeroInstantonCoefficient_recursion]
        calc
          _ ≤ |((25*(n:ℚ)^2-1)/48)*zeroInstantonCoefficient n|+
              |(1/2:ℚ)*(∑ j∈Finset.Icc 1 n,zeroInstantonCoefficient j*zeroInstantonCoefficient (n+1-j))| := abs_sub _ _
          _ ≤ (n:ℚ)^2*(n.factorial:ℚ)^2+(1/2:ℚ)*((n:ℚ)*(n.factorial:ℚ)^2) := by
            rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℚ) ≤ 1/2)]
            exact add_le_add (mul_le_mul hcoef (ih n (by omega)) (abs_nonneg _) (sq_nonneg _))
              (mul_le_mul_of_nonneg_left hsum (by norm_num))
          _ ≤ _ := by
            rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
            nlinarith [sq_nonneg (n.factorial:ℚ),
              mul_nonneg (show (0:ℚ) ≤ 3*(n:ℚ)/2+1 by positivity) (sq_nonneg (n.factorial:ℚ))]
end WP.HigherOrder
namespace WP.HigherOrder
lemma factorial_square_le_double (g : ℕ) : (g.factorial:ℚ)^2 ≤ (2*g).factorial := by
  have h := Nat.le_of_dvd (Nat.factorial_pos (g+g)) (Nat.factorial_mul_factorial_dvd_factorial_add g g)
  rw [←two_mul] at h
  rw [pow_two]
  exact_mod_cast h
lemma jumpPotential_factorial_bound (g : ℕ) :
    |jumpPotential g| ≤ (8:ℚ)^g*((2*g).factorial:ℚ) := by
  by_cases h0 : g=0
  · subst g;norm_num [jumpPotential]
  by_cases h1 : g=1
  · subst g;norm_num
  have hg : 2 ≤ g := by omega
  simp only [jumpPotential,h0,ite_false,h1,zero_sub,abs_neg,abs_mul]
  have hp : 0 ≤ (192/25:ℚ)^g := by positivity
  rw [abs_of_nonneg hp]
  calc
    _ ≤ (g.factorial:ℚ)^2*(192/25:ℚ)^g :=
      mul_le_mul_of_nonneg_right (zeroInstantonCoefficient_factorial_bound g) hp
    _ ≤ ((2*g).factorial:ℚ)*(8:ℚ)^g := mul_le_mul (factorial_square_le_double g)
      (pow_le_pow_left₀ (by norm_num) (by norm_num) g) hp (by positivity)
    _ = _ := by ring
lemma geometric_small_prefix (N : ℕ) :
    (∑ g∈Finset.Icc 1 N,(1/128:ℚ)^g) ≤ 1/64 := by
  have he := geom_sum_Ico_le_of_lt_one (K:=ℚ) (m:=1) (n:=N+1)
    (by norm_num : (0:ℚ) ≤ 1/128) (by norm_num : (1/128:ℚ)<1)
  have hsets : Finset.Ico 1 (N+1)=Finset.Icc 1 N := by
    ext k
    simp only [Finset.mem_Ico,Finset.mem_Icc]
    omega
  rw [hsets] at he
  exact he.trans (by norm_num)
lemma jumpCoefficient_factorial_bound (j : ℕ) :
    |jumpCoefficient j| ≤ (32:ℚ)^j*(j.factorial:ℚ) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
      cases j with
      | zero => norm_num
      | succ n =>
          let N : ℕ := (n+2)/2
          have hterm (g : ℕ) (hg : g∈Finset.Icc 1 N) :
              |jumpPotential g*jumpCoefficient (n+2-2*g)| ≤
                (32:ℚ)^(n+2)*(1/128:ℚ)^g*((n+2).factorial:ℚ) := by
            have hg' := Finset.mem_Icc.mp hg
            have hb : 2*g ≤ n+2 := by dsimp [N] at hg';omega
            have hk : n+2-2*g < n+1 := by omega
            have hfac : ((2*g).factorial:ℚ)*((n+2-2*g).factorial:ℚ) ≤ (n+2).factorial := by
              have hd := Nat.le_of_dvd (Nat.factorial_pos (2*g+(n+2-2*g)))
                (Nat.factorial_mul_factorial_dvd_factorial_add (2*g) (n+2-2*g))
              rw [show 2*g+(n+2-2*g)=n+2 by omega] at hd
              exact_mod_cast hd
            have hpower : (8:ℚ)^g*32^(n+2-2*g)=32^(n+2)*(1/128)^g := by
              rw [show n+2=(n+2-2*g)+2*g by omega,pow_add,pow_mul]
              rw [mul_assoc,←mul_pow]
              norm_num
              ring
            rw [abs_mul]
            calc
              _ ≤ ((8:ℚ)^g*((2*g).factorial:ℚ))*((32:ℚ)^(n+2-2*g)*(n+2-2*g).factorial) :=
                mul_le_mul (jumpPotential_factorial_bound g) (ih _ hk) (abs_nonneg _) (by positivity)
              _ = ((8:ℚ)^g*32^(n+2-2*g))*(((2*g).factorial:ℚ)*(n+2-2*g).factorial) := by ring
              _ ≤ ((8:ℚ)^g*32^(n+2-2*g))*((n+2).factorial:ℚ) := mul_le_mul_of_nonneg_left hfac (by positivity)
              _ = _ := by rw [hpower] <;> ring
          have hsum : |∑ g∈Finset.Icc 1 N,jumpPotential g*jumpCoefficient (n+2-2*g)| ≤
              ((32:ℚ)^(n+2)/64)*((n+2).factorial:ℚ) := by
            calc
              _ ≤ ∑ g∈Finset.Icc 1 N,|jumpPotential g*jumpCoefficient (n+2-2*g)| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ g∈Finset.Icc 1 N,(32:ℚ)^(n+2)*(1/128:ℚ)^g*((n+2).factorial:ℚ) := Finset.sum_le_sum hterm
              _ = ((32:ℚ)^(n+2)*((n+2).factorial:ℚ))*(∑ g∈Finset.Icc 1 N,(1/128:ℚ)^g) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro g hg
                ring
              _ ≤ ((32:ℚ)^(n+2)*((n+2).factorial:ℚ))*(1/64:ℚ) :=
                mul_le_mul_of_nonneg_left (geometric_small_prefix N) (by positivity)
              _ = _ := by ring
          have hn0 : (0:ℚ) ≤ n := by positivity
          have hnp : (0:ℚ)<n+1 := by positivity
          have hfirst : |((n+1:ℕ):ℚ)*n*jumpCoefficient n| ≤
              ((n:ℚ)+1)*n*((32:ℚ)^n*(n.factorial:ℚ)) := by
            rw [abs_mul,abs_of_nonneg (by positivity : (0:ℚ)≤((n+1:ℕ):ℚ)*n)]
            simpa only [Nat.cast_add,Nat.cast_one] using
              mul_le_mul_of_nonneg_left (ih n (by omega)) (by positivity : (0:ℚ)≤((n+1:ℕ):ℚ)*n)
          rw [jumpCoefficient_recursion,abs_div,abs_neg,abs_of_pos (by positivity : (0:ℚ)<2*(n+1:ℕ))]
          apply (div_le_iff₀ (by positivity : (0:ℚ)<2*(n+1:ℕ))).2
          apply ((abs_add_le _ _).trans (add_le_add hfirst hsum)).trans
          have hf1 : ((n+1).factorial:ℚ)=((n:ℚ)+1)*(n.factorial:ℚ) := by rw [Nat.factorial_succ];push_cast;rfl
          have hf2 : ((n+2).factorial:ℚ)=((n:ℚ)+2)*((n:ℚ)+1)*(n.factorial:ℚ) := by
            rw [Nat.factorial_succ,Nat.factorial_succ]
            push_cast
            ring
          have hp1 : (32:ℚ)^(n+1)=(32:ℚ)^n*32 := pow_succ _ _
          have hp2 : (32:ℚ)^(n+2)=(32:ℚ)^n*1024 := by rw [pow_succ,pow_succ];ring
          rw [hf1,hf2,hp1,hp2,Nat.cast_add,Nat.cast_one]
          have hc : (n:ℚ)+16*((n:ℚ)+2) ≤ 64*((n:ℚ)+1) := by nlinarith
          convert mul_le_mul_of_nonneg_left hc
            (show (0:ℚ)≤(32:ℚ)^n*((n:ℚ)+1)*(n.factorial:ℚ) by positivity) using 1 <;> ring
end WP.HigherOrder
namespace WP.HigherOrder
lemma zeroInstantonCoefficient_real_factorial_bound (g : ℕ) :
    |(zeroInstantonCoefficient g:ℝ)| ≤ (g.factorial:ℝ)^2 := by
  exact_mod_cast zeroInstantonCoefficient_factorial_bound g
lemma jumpCoefficient_real_factorial_bound (j : ℕ) :
    |(jumpCoefficient j:ℝ)| ≤ (32:ℝ)^j*(j.factorial:ℝ) := by
  exact_mod_cast jumpCoefficient_factorial_bound j
end WP.HigherOrder
