import Mathlib
/-! Finite scaled coefficient convolution preserves common holomorphic domains and Gevrey-two factorial bounds. The coefficient and parameter estimates are proved explicitly. -/
noncomputable section
open Set
namespace WP.Analysis
def scaledSeriesConvolution (G:ℕ→ℂ→ℂ) (c:ℕ→ℝ) (t:ℂ→ℂ) (j:ℕ) (z:ℂ):ℂ:=
  ∑i∈Finset.range (j+1),G i z*(c (j-i):ℂ)*t z^(j-i)
lemma scaledSeriesConvolution_analyticOnNhd (G:ℕ→ℂ→ℂ) (c:ℕ→ℝ) (t:ℂ→ℂ) (Ω:Set ℂ)
    (hG:∀i,AnalyticOnNhd ℂ (G i) Ω) (ht:AnalyticOnNhd ℂ t Ω) (j:ℕ):
    AnalyticOnNhd ℂ (scaledSeriesConvolution G c t j) Ω := by
  intro z hz
  apply Finset.analyticAt_fun_sum
  intro i hi
  exact ((hG i z hz).mul analyticAt_const).mul ((ht z hz).pow _)
lemma scaledSeriesConvolution_gevreyTwo_bound (G:ℕ→ℂ→ℂ) (c:ℕ→ℝ) (t:ℂ→ℂ)
    (Cg Bg Cp Bp T:ℝ) (hCg:0≤Cg) (hBg:0≤Bg) (hCp:0≤Cp) (hBp:0≤Bp) (hT:0≤T)
    (z:ℂ) (hG:∀i,‖G i z‖≤Cg*Bg^i*(i.factorial:ℝ)^2)
    (hc:∀i,|c i|≤Cp*Bp^i*(i.factorial:ℝ)) (ht:‖t z‖≤T) (j:ℕ) :
    ‖scaledSeriesConvolution G c t j z‖≤Cg*Cp*(2*max Bg (Bp*T))^j*(j.factorial:ℝ)^2 := by
  let M:ℝ:=max Bg (Bp*T)
  have hM:0≤M:=hBg.trans (le_max_left _ _)
  have hc2(n:ℕ):|c n|≤Cp*Bp^n*(n.factorial:ℝ)^2 := by
    have hfac:1≤(n.factorial:ℝ):=by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
    have hf:(n.factorial:ℝ)≤(n.factorial:ℝ)^2:=by nlinarith
    exact (hc n).trans (mul_le_mul_of_nonneg_left hf (mul_nonneg hCp (pow_nonneg hBp n)))
  have hterm(i:ℕ)(hi:i∈Finset.range (j+1)):
      ‖G i z*(c (j-i):ℂ)*t z^(j-i)‖≤Cg*Cp*M^j*(j.factorial:ℝ)^2 := by
    have hij:i≤j:=Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hsum:i+(j-i)=j:=Nat.add_sub_of_le hij
    have hfact:(i.factorial:ℝ)*((j-i).factorial:ℝ)≤(j.factorial:ℝ):=by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos j) (Nat.factorial_mul_factorial_dvd_factorial hij)
    have hf2:((i.factorial:ℝ)*((j-i).factorial:ℝ))^2≤(j.factorial:ℝ)^2:=
      pow_le_pow_left₀ (by positivity) hfact 2
    have hpow:Bg^i*(Bp*T)^(j-i)≤M^j := by
      calc _ ≤ M^i*M^(j-i):=mul_le_mul (pow_le_pow_left₀ hBg (le_max_left _ _) _)
                (pow_le_pow_left₀ (mul_nonneg hBp hT) (le_max_right _ _) _) (by positivity) (by positivity)
           _ = _:=by rw[←pow_add,hsum]
    rw[norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    calc _ ≤ (Cg*Bg^i*(i.factorial:ℝ)^2)*(Cp*Bp^(j-i)*((j-i).factorial:ℝ)^2)*T^(j-i) := by
               exact mul_le_mul (mul_le_mul (hG i) (hc2 (j-i)) (abs_nonneg _) (by positivity))
                 (pow_le_pow_left₀ (norm_nonneg _) ht _) (by positivity) (by positivity)
         _ = Cg*Cp*(Bg^i*(Bp*T)^(j-i))*((i.factorial:ℝ)*((j-i).factorial:ℝ))^2 := by
               rw[mul_pow,mul_pow]
               ring
         _ ≤ _:=mul_le_mul (mul_le_mul_of_nonneg_left hpow (mul_nonneg hCg hCp)) hf2 (by positivity) (by positivity)
  calc _ ≤ ∑i∈Finset.range (j+1),‖G i z*(c (j-i):ℂ)*t z^(j-i)‖:=norm_sum_le _ _
       _ ≤ ∑i∈Finset.range (j+1),Cg*Cp*M^j*(j.factorial:ℝ)^2:=Finset.sum_le_sum hterm
       _ = (j+1:ℕ)*(Cg*Cp*M^j*(j.factorial:ℝ)^2):=by simp
       _ ≤ (2:ℝ)^j*(Cg*Cp*M^j*(j.factorial:ℝ)^2) := by
             apply mul_le_mul_of_nonneg_right _ (by positivity)
             exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n:=j))
       _ = _:=by dsimp only[M];rw[mul_pow];ring
end WP.Analysis
