import WPFormalization.RandomGeometry.BoltzmannCuspLaw
import WPFormalization.Tight.ConnectedCoefficientAlgebra

noncomputable section
namespace WP.BoltzmannCusp
open Set
lemma phi_first_moment_hasSum (P : PsiTheory) (g : ℕ) (x : ℝ)
    (hx : x∈Ico 0 xCritical) :
    HasSum (fun n:ℕ=>(n:ℝ)*realCoeff (Phi P g) n*x^n) (x*markedF P g 1 x) := by
  have hs := TightConnected.connected_real_taylor_hasSum _ x
    (marked_generating_hasSum P g 1 (x:ℂ)
      (by rw [Complex.norm_of_nonneg hx.1];exact hx.2))
  have hs' : HasSum (fun n:ℕ=>((n+1:ℕ):ℝ)*realCoeff (Phi P g) (n+1)*x^(n+1))
      (x*markedF P g 1 x) := by
    change HasSum _ (markedF P g 1 x) at hs
    convert hs.mul_left x using 1
    funext n
    rw [iteratedDeriv_one,TightConnected.connected_realCoeff_deriv]
    simp only [Nat.cast_add,Nat.cast_one,pow_succ]
    ring
  have ht := (hasSum_nat_add_iff (f:=fun n:ℕ=>(n:ℝ)*realCoeff (Phi P g) n*x^n) 1).mp hs'
  simpa only [Finset.sum_range_one,Nat.cast_zero,zero_mul,zero_add,add_zero] using ht

lemma phi_second_factorial_moment_hasSum (P : PsiTheory) (g : ℕ) (x : ℝ)
    (hx : x∈Ico 0 xCritical) :
    HasSum (fun n:ℕ=>(n:ℝ)*((n:ℝ)-1)*realCoeff (Phi P g) n*x^n)
      (x^2*markedF P g 2 x) := by
  have hs := TightConnected.connected_real_taylor_hasSum _ x
    (marked_generating_hasSum P g 2 (x:ℂ)
      (by rw [Complex.norm_of_nonneg hx.1];exact hx.2))
  have hs' : HasSum (fun n:ℕ=>((n+2:ℕ):ℝ)*(((n+2:ℕ):ℝ)-1)*realCoeff (Phi P g) (n+2)*x^(n+2))
      (x^2*markedF P g 2 x) := by
    change HasSum _ (markedF P g 2 x) at hs
    convert hs.mul_left (x^2) using 1
    funext n
    rw [show iteratedDeriv 2 (Phi P g)=deriv (deriv (Phi P g)) by
      rw [show 2=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one],
      TightConnected.connected_realCoeff_deriv,TightConnected.connected_realCoeff_deriv]
    simp only [Nat.cast_add,Nat.cast_one,pow_add,pow_two]
    ring
  have ht := (hasSum_nat_add_iff (f:=fun n:ℕ=>(n:ℝ)*((n:ℝ)-1)*realCoeff (Phi P g) n*x^n) 2).mp hs'
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.cast_zero,Nat.cast_one,
    zero_mul,mul_zero,sub_self,add_zero,zero_add] using ht

lemma phi_second_moment_hasSum (P : PsiTheory) (g : ℕ) (x : ℝ)
    (hx : x∈Ico 0 xCritical) :
    HasSum (fun n:ℕ=>(n:ℝ)^2*realCoeff (Phi P g) n*x^n)
      (x^2*markedF P g 2 x+x*markedF P g 1 x) := by
  convert (phi_second_factorial_moment_hasSum P g x hx).add (phi_first_moment_hasSum P g x hx) using 1
  funext n
  ring
end WP.BoltzmannCusp
namespace WP.BoltzmannCusp
open Set MeasureTheory ProbabilityTheory
lemma weight_first_moment_hasSum (P:PsiTheory) (g:ℕ) (x:ℝ) (hx:x∈Ico 0 xCritical) :
    HasSum (fun n:ℕ=>weight P g x n*(n:ℝ))
      (x*markedF P g 1 x/markedF P g 0 x) := by
  convert (phi_first_moment_hasSum P g x hx).div_const (markedF P g 0 x) using 1
  funext n
  dsimp only [weight]
  ring
lemma weight_second_moment_hasSum (P:PsiTheory) (g:ℕ) (x:ℝ) (hx:x∈Ico 0 xCritical) :
    HasSum (fun n:ℕ=>weight P g x n*(n:ℝ)^2)
      ((x^2*markedF P g 2 x+x*markedF P g 1 x)/markedF P g 0 x) := by
  convert (phi_second_moment_hasSum P g x hx).div_const (markedF P g 0 x) using 1
  funext n
  dsimp only [weight]
  ring
lemma law_integrable_count (P:PsiTheory) (g:ℕ) (hg:2≤g) (hf0:0 < markedF P g 0 0)
    (x:ℝ) (hx:x∈Ico 0 xCritical) (hfx:0 < markedF P g 0 x) :
    Integrable (fun n:ℕ=>(n:ℝ)) (law P g hg hf0 x hx hfx:Measure ℕ) := by
  apply pmfOfWeights_integrable
  simpa only [Real.norm_eq_abs,Nat.abs_cast] using
    (weight_first_moment_hasSum P g x hx).summable
lemma law_integrable_count_sq (P:PsiTheory) (g:ℕ) (hg:2≤g) (hf0:0 < markedF P g 0 0)
    (x:ℝ) (hx:x∈Ico 0 xCritical) (hfx:0 < markedF P g 0 x) :
    Integrable (fun n:ℕ=>(n:ℝ)^2) (law P g hg hf0 x hx hfx:Measure ℕ) := by
  apply pmfOfWeights_integrable
  simpa only [Real.norm_eq_abs,abs_sq] using
    (weight_second_moment_hasSum P g x hx).summable
lemma law_mean (P:PsiTheory) (g:ℕ) (hg:2≤g) (hf0:0 < markedF P g 0 0)
    (x:ℝ) (hx:x∈Ico 0 xCritical) (hfx:0 < markedF P g 0 x) :
    ∫n:ℕ,(n:ℝ) ∂(law P g hg hf0 x hx hfx:Measure ℕ)=
      x*markedF P g 1 x/markedF P g 0 x :=
  (pmfOfWeights_integral _ _ _ _).trans (weight_first_moment_hasSum P g x hx).tsum_eq
lemma law_second_moment (P:PsiTheory) (g:ℕ) (hg:2≤g) (hf0:0 < markedF P g 0 0)
    (x:ℝ) (hx:x∈Ico 0 xCritical) (hfx:0 < markedF P g 0 x) :
    ∫n:ℕ,(n:ℝ)^2 ∂(law P g hg hf0 x hx hfx:Measure ℕ)=
      (x^2*markedF P g 2 x+x*markedF P g 1 x)/markedF P g 0 x :=
  (pmfOfWeights_integral _ _ _ _).trans (weight_second_moment_hasSum P g x hx).tsum_eq
lemma law_memLp_count (P:PsiTheory) (g:ℕ) (hg:2≤g) (hf0:0 < markedF P g 0 0)
    (x:ℝ) (hx:x∈Ico 0 xCritical) (hfx:0 < markedF P g 0 x) :
    MemLp (fun n:ℕ=>(n:ℝ)) 2 (law P g hg hf0 x hx hfx:Measure ℕ) := by
  exact (memLp_two_iff_integrable_sq (by fun_prop)).mpr (law_integrable_count_sq P g hg hf0 x hx hfx)
lemma law_variance (P:PsiTheory) (g:ℕ) (hg:2≤g) (hf0:0 < markedF P g 0 0)
    (x:ℝ) (hx:x∈Ico 0 xCritical) (hfx:0 < markedF P g 0 x) :
    variance (fun n:ℕ=>(n:ℝ)) (law P g hg hf0 x hx hfx:Measure ℕ)=
      x^2*markedF P g 2 x/markedF P g 0 x+
        x*markedF P g 1 x/markedF P g 0 x-(x*markedF P g 1 x/markedF P g 0 x)^2 := by
  rw [variance_eq_sub (law_memLp_count P g hg hf0 x hx hfx),law_mean]
  change (∫n:ℕ,(n:ℝ)^2 ∂(law P g hg hf0 x hx hfx:Measure ℕ))-_=_
  rw [law_second_moment]
  ring
end WP.BoltzmannCusp
namespace WP.BoltzmannCusp
open Set MeasureTheory ProbabilityTheory
lemma law_integrable_count_factorial_two (P:PsiTheory) (g:ℕ) (hg:2≤g)
    (hf0:0 < markedF P g 0 0) (x:ℝ) (hx:x∈Ico 0 xCritical) (hfx:0 < markedF P g 0 x) :
    Integrable (fun n:ℕ=>(n:ℝ)*((n:ℝ)-1)) (law P g hg hf0 x hx hfx:Measure ℕ) := by
  have hf : (fun n:ℕ=>(n:ℝ)*((n:ℝ)-1))=(fun n:ℕ=>(n:ℝ)^2-(n:ℝ)) := by funext n;ring
  rw [hf]
  exact (law_integrable_count_sq P g hg hf0 x hx hfx).sub (law_integrable_count P g hg hf0 x hx hfx)
lemma law_second_factorial_moment (P:PsiTheory) (g:ℕ) (hg:2≤g)
    (hf0:0 < markedF P g 0 0) (x:ℝ) (hx:x∈Ico 0 xCritical) (hfx:0 < markedF P g 0 x) :
    ∫n:ℕ,(n:ℝ)*((n:ℝ)-1) ∂(law P g hg hf0 x hx hfx:Measure ℕ)=
      x^2*markedF P g 2 x/markedF P g 0 x := by
  have hf : (fun n:ℕ=>(n:ℝ)*((n:ℝ)-1))=(fun n:ℕ=>(n:ℝ)^2-(n:ℝ)) := by funext n;ring
  rw [hf,integral_sub (law_integrable_count_sq P g hg hf0 x hx hfx)
    (law_integrable_count P g hg hf0 x hx hfx),law_second_moment,law_mean]
  ring
end WP.BoltzmannCusp
