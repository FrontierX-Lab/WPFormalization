import WPFormalization.Analysis.GaussianGevreyTails
/-! Exact finite Gaussian model expansion and its uniform Gevrey-two error.
The amplitude sum is an actual integral on a finite real segment. Its Taylor
moments extend to the full real axis with the displayed exponential tail.
The derived coefficients are auxiliary transformed Gaussian coefficients;
identification with the prescribed CG3 coefficients is a separate obligation. -/
noncomputable section
open MeasureTheory Set
namespace WP.Analysis

def gaussianAmplitudeIntegral (f:ℕ → ℂ → ℂ) (h r:ℝ) (s:ℕ):ℂ :=
  (Real.sqrt h:ℂ)/(h:ℂ)^s*(∫x:ℝ in Icc (-r) r,Real.exp (-(h/2)*x^2) • f s (x:ℂ))
def gaussianTaylorIntegral (f:ℕ → ℂ → ℂ) (h r:ℝ) (K s:ℕ):ℂ :=
  (Real.sqrt h:ℂ)/(h:ℂ)^s*(∫x:ℝ in Icc (-r) r,Real.exp (-(h/2)*x^2) •
    (f s (x:ℂ)-∑m ∈ Finset.range (2*(K+1-s)),WP.coeff (f s) m*(x:ℂ)^m))
def gaussianPolynomialTailIntegral (f:ℕ → ℂ → ℂ) (h r:ℝ) (K s:ℕ):ℂ :=
  (Real.sqrt h:ℂ)/(h:ℂ)^s*(∫x:ℝ in (Icc (-r) r)ᶜ,Real.exp (-(h/2)*x^2) •
    (∑m ∈ Finset.range (2*(K+1-s)),WP.coeff (f s) m*(x:ℂ)^m))
def gaussianPolynomialAmplitude (f:ℕ → ℂ → ℂ) (h:ℝ) (K s:ℕ):ℂ :=
  (Real.sqrt (2*Real.pi):ℂ)/(h:ℂ)^s*
    (∑a ∈ Finset.range (K+1-s),WP.coeff (f s) (2*a)*(Nat.doubleFactorial (2*a-1):ℂ)/(h:ℂ)^a)

lemma gaussian_local_amplitude_integrable (f:ℂ → ℂ) (R r h:ℝ) (_hR:0<R) (hrR:r ≤ R)
    (hf:DifferentiableOn ℂ f (Metric.closedBall 0 R)) :
    IntegrableOn (fun x:ℝ=>Real.exp (-(h/2)*x^2) • f (x:ℂ)) (Icc (-r) r) := by
  have hmaps:MapsTo (fun x:ℝ=>(x:ℂ)) (Icc (-r) r) (Metric.closedBall 0 R) := by
    intro x hx
    rw [Metric.mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs]
    exact (abs_le.mpr ⟨by linarith [hx.1],hx.2⟩).trans hrR
  have hfc:=hf.continuousOn.comp Complex.continuous_ofReal.continuousOn hmaps
  have hg:Continuous (fun x:ℝ=>Real.exp (-(h/2)*x^2)) := by fun_prop
  exact (hg.continuousOn.smul hfc).integrableOn_Icc

lemma gaussian_polynomial_integrable (h:ℝ) (hh:0<h) (N:ℕ) (c:ℕ → ℂ) :
    Integrable (fun x:ℝ=>Real.exp (-(h/2)*x^2) • (∑m ∈ Finset.range (2*N),c m*(x:ℂ)^m)) := by
  have heq : (fun x:ℝ=>Real.exp (-(h/2)*x^2) •
      (∑m ∈ Finset.range (2*N),c m*(x:ℂ)^m))=
      (fun x:ℝ=>∑m ∈ Finset.range (2*N),c m*(Real.exp (-(h/2)*x^2) • (x:ℂ)^m)) := by
    funext x
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    change (Real.exp (-(h/2)*x^2):ℂ)*(c m*(x:ℂ)^m)=c m*((Real.exp (-(h/2)*x^2):ℂ)*(x:ℂ)^m)
    ring
  rw [heq]
  exact integrable_finsetSum _ (fun m hm=>(gaussian_complex_monomial_integrable (h/2) (half_pos hh) m).const_mul (c m))

lemma gaussian_amplitude_remainder_identity (f:ℕ → ℂ → ℂ) (h r R:ℝ) (hh:0<h)
    (hR:0<R) (hrR:r ≤ R) (s K:ℕ)
    (hf:DifferentiableOn ℂ (f s) (Metric.closedBall 0 R)) :
    gaussianAmplitudeIntegral f h r s-gaussianPolynomialAmplitude f h K s=
      gaussianTaylorIntegral f h r K s-gaussianPolynomialTailIntegral f h r K s := by
  let P:ℝ → ℂ := fun x=>∑m ∈ Finset.range (2*(K+1-s)),WP.coeff (f s) m*(x:ℂ)^m
  let g:ℝ → ℂ := fun x=>Real.exp (-(h/2)*x^2) • P x
  have hgi:Integrable g := gaussian_polynomial_integrable h hh (K+1-s) (WP.coeff (f s))
  have hfi:=gaussian_local_amplitude_integrable (f s) R r h hR hrR hf
  have hP : gaussianPolynomialAmplitude f h K s=
      (Real.sqrt h:ℂ)/(h:ℂ)^s*(∫x:ℝ,g x) := by
    have he:=gaussian_polynomial_exact h hh (K+1-s) (WP.coeff (f s))
    change (Real.sqrt h:ℂ)*(∫x:ℝ,g x)=_ at he
    dsimp only [gaussianPolynomialAmplitude]
    calc _ = ((Real.sqrt (2*Real.pi):ℂ)*
          (∑a ∈ Finset.range (K+1-s),WP.coeff (f s) (2*a)*(Nat.doubleFactorial (2*a-1):ℂ)/(h:ℂ)^a))/(h:ℂ)^s := by ring
         _ = ((Real.sqrt h:ℂ)*(∫x:ℝ,g x))/(h:ℂ)^s := by rw [he]
         _ = _ := by ring
  have hsub : (∫x:ℝ in Icc (-r) r,Real.exp (-(h/2)*x^2) • (f s (x:ℂ)-P x))=
      (∫x:ℝ in Icc (-r) r,Real.exp (-(h/2)*x^2) • f s (x:ℂ))-(∫x:ℝ in Icc (-r) r,g x) := by
    simp_rw [smul_sub]
    exact integral_sub hfi hgi.integrableOn
  have hsplit : (∫x:ℝ in Icc (-r) r,g x)+(∫x:ℝ in (Icc (-r) r)ᶜ,g x)=∫x:ℝ,g x :=
    integral_add_compl measurableSet_Icc hgi
  rw [hP]
  change (Real.sqrt h:ℂ)/(h:ℂ)^s*(∫x:ℝ in Icc (-r) r,Real.exp (-(h/2)*x^2) • f s (x:ℂ))-
      (Real.sqrt h:ℂ)/(h:ℂ)^s*(∫x:ℝ,g x)=
      (Real.sqrt h:ℂ)/(h:ℂ)^s*(∫x:ℝ in Icc (-r) r,Real.exp (-(h/2)*x^2) • (f s (x:ℂ)-P x))-
      (Real.sqrt h:ℂ)/(h:ℂ)^s*(∫x:ℝ in (Icc (-r) r)ᶜ,g x)
  rw [hsub,←hsplit]
  ring

lemma gaussian_model_remainder_identity (f:ℕ → ℂ → ℂ) (h r R:ℝ) (hh:0<h)
    (hR:0<R) (hrR:r ≤ R) (J K:ℕ) (hKJ:K ≤ J)
    (hf:∀s,DifferentiableOn ℂ (f s) (Metric.closedBall 0 R)) :
    (∑s ∈ Finset.range (J+1),gaussianAmplitudeIntegral f h r s)-
      (∑s ∈ Finset.range (K+1),gaussianPolynomialAmplitude f h K s)=
      (∑s ∈ Finset.range (K+1),gaussianTaylorIntegral f h r K s)-
        (∑s ∈ Finset.range (K+1),gaussianPolynomialTailIntegral f h r K s)+
      (∑n ∈ Finset.range (J-K),gaussianAmplitudeIntegral f h r (K+1+n)) := by
  have hsplit : (∑s ∈ Finset.range (J+1),gaussianAmplitudeIntegral f h r s)=
      (∑s ∈ Finset.range (K+1),gaussianAmplitudeIntegral f h r s)+
        (∑n ∈ Finset.range (J-K),gaussianAmplitudeIntegral f h r (K+1+n)) := by
    have he:=Finset.sum_range_add_sum_Ico (gaussianAmplitudeIntegral f h r) (m:=K+1) (n:=J+1) (by omega)
    rw [Finset.sum_Ico_eq_sum_range,show J+1-(K+1)=J-K by omega] at he
    exact he.symm
  rw [hsplit]
  calc _ = (∑s ∈ Finset.range (K+1),
          (gaussianAmplitudeIntegral f h r s-gaussianPolynomialAmplitude f h K s))+
          (∑n ∈ Finset.range (J-K),gaussianAmplitudeIntegral f h r (K+1+n)) := by
            rw [Finset.sum_sub_distrib]
            ring
       _ = (∑s ∈ Finset.range (K+1),
          (gaussianTaylorIntegral f h r K s-gaussianPolynomialTailIntegral f h r K s))+
          (∑n ∈ Finset.range (J-K),gaussianAmplitudeIntegral f h r (K+1+n)) := by
            congr 1
            apply Finset.sum_congr rfl
            intro s hs
            exact gaussian_amplitude_remainder_identity f h r R hh hR hrR s K (hf s)
       _ = _ := by rw [Finset.sum_sub_distrib]
lemma gaussian_model_remainder_bound (f:ℕ → ℂ → ℂ) (C B R r h:ℝ)
    (hC:0 ≤ C) (hB:0 ≤ B) (hR:0<R) (hr:0<r) (hrR:r ≤ R/2) (hh:0<h)
    (hf:∀s,DifferentiableOn ℂ (f s) (Metric.closedBall 0 R))
    (hbound:∀s z,z ∈ Metric.closedBall (0:ℂ) R → ‖f s z‖ ≤ C*B^s*(s.factorial:ℝ)^2)
    (J K:ℕ) (hKJ:K ≤ J) (hwindow:B*((J:ℝ)+1)^2/h ≤ 1/2)
    (hsmall:8*((K:ℝ)+1) ≤ h) :
    ‖(∑s ∈ Finset.range (J+1),gaussianAmplitudeIntegral f h r s)-
        (∑s ∈ Finset.range (K+1),gaussianPolynomialAmplitude f h K s)‖ ≤
      (2*C*(Real.sqrt (4*Real.pi)+Real.sqrt (2*Real.pi)))*
        (2*max B (4/R^2))^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)+
      4*C*Real.sqrt (8*Real.pi)*(2*max 1 R⁻¹)^(2*(K+1))*Real.exp (-(h/4)*r^2) := by
  have hsphere:∀s z,z ∈ Metric.sphere (0:ℂ) R → ‖f s z‖ ≤ C*B^s*(s.factorial:ℝ)^2 :=
    fun s z hz=>hbound s z (Metric.sphere_subset_closedBall hz)
  have hlocal:∀s x,x ∈ Icc (-r) r → ‖f s (x:ℂ)‖ ≤ C*B^s*(s.factorial:ℝ)^2 := by
    intro s x hx
    apply hbound s (x:ℂ)
    rw [Metric.mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs]
    exact (abs_le.mpr ⟨by linarith [hx.1],hx.2⟩).trans (by linarith)
  have hwinK:B*((K:ℝ)+1)^2/h ≤ 1/2 := by
    apply le_trans _ hwindow
    apply div_le_div_of_nonneg_right _ hh.le
    apply mul_le_mul_of_nonneg_left _ hB
    gcongr
  have hT:=gaussian_gevrey_two_taylor_family f C B R r h hC hB hR hr hrR hh hf hsphere K
  have hO:=gaussian_gevrey_two_polynomial_tail_family f C B R r h hC hB hR hr hh hf hsphere K hwinK hsmall
  have hA:=gaussian_gevrey_two_unused_amplitude_family f C B r h hC hB hh hlocal J K hwindow
  change ‖∑s ∈ Finset.range (K+1),gaussianTaylorIntegral f h r K s‖ ≤ _ at hT
  change ‖∑s ∈ Finset.range (K+1),gaussianPolynomialTailIntegral f h r K s‖ ≤ _ at hO
  change ‖∑n ∈ Finset.range (J-K),gaussianAmplitudeIntegral f h r (K+1+n)‖ ≤ _ at hA
  have hBB:B ≤ 2*max B (4/R^2) := by
    have hm : (0:ℝ) ≤ (max B (4/R^2)) := hB.trans (le_max_left _ _)
    linarith [le_max_left B (4/R^2)]
  have hpow:B^(K+1) ≤ (2*max B (4/R^2))^(K+1) := pow_le_pow_left₀ hB hBB _
  have hA':‖∑n ∈ Finset.range (J-K),gaussianAmplitudeIntegral f h r (K+1+n)‖ ≤
      2*C*Real.sqrt (2*Real.pi)*(2*max B (4/R^2))^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1) := by
    apply hA.trans
    gcongr
  rw [gaussian_model_remainder_identity f h r R hh hR (by linarith) J K hKJ hf]
  calc _ ≤ ‖∑s ∈ Finset.range (K+1),gaussianTaylorIntegral f h r K s‖+
          ‖∑s ∈ Finset.range (K+1),gaussianPolynomialTailIntegral f h r K s‖+
          ‖∑n ∈ Finset.range (J-K),gaussianAmplitudeIntegral f h r (K+1+n)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
       _ ≤ (2*C*Real.sqrt (4*Real.pi))*(2*max B (4/R^2))^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)+
            4*C*Real.sqrt (8*Real.pi)*(2*max 1 R⁻¹)^(2*(K+1))*Real.exp (-(h/4)*r^2)+
            2*C*Real.sqrt (2*Real.pi)*(2*max B (4/R^2))^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1) :=
          add_le_add (add_le_add hT hO) hA'
       _ = _ := by ring
def gaussianModelCoefficient (f:ℕ → ℂ → ℂ) (j:ℕ):ℂ :=
  ∑s ∈ Finset.range (j+1),WP.coeff (f s) (2*(j-s))*(Nat.doubleFactorial (2*(j-s)-1):ℂ)
lemma gaussian_polynomial_amplitudes_regroup (f:ℕ → ℂ → ℂ) (h:ℝ) (K:ℕ) :
    (∑s ∈ Finset.range (K+1),gaussianPolynomialAmplitude f h K s)=
      (Real.sqrt (2*Real.pi):ℂ)*∑j ∈ Finset.range (K+1),gaussianModelCoefficient f j/(h:ℂ)^j := by
  let F:ℕ → ℕ → ℂ := fun s a=>(Real.sqrt (2*Real.pi):ℂ)*
    (WP.coeff (f s) (2*a)*(Nat.doubleFactorial (2*a-1):ℂ))/(h:ℂ)^(s+a)
  have hleft:(∑s ∈ Finset.range (K+1),gaussianPolynomialAmplitude f h K s)=
      ∑s ∈ Finset.range (K+1),∑a ∈ Finset.range (K+1-s),F s a := by
    apply Finset.sum_congr rfl
    intro s hs
    dsimp only [gaussianPolynomialAmplitude]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    dsimp only [F]
    rw [pow_add]
    field_simp
  have hright:(Real.sqrt (2*Real.pi):ℂ)*∑j ∈ Finset.range (K+1),gaussianModelCoefficient f j/(h:ℂ)^j=
      ∑j ∈ Finset.range (K+1),∑s ∈ Finset.range (j+1),F s (j-s) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [gaussianModelCoefficient]
    rw [Finset.sum_div,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    dsimp only [F]
    rw [Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hs))]
    ring
  rw [hleft,hright]
  exact (Finset.sum_range_diag_flip (K+1) F).symm

lemma gaussian_polynomial_outer_exponential_absorption (D a c t:ℝ) (hD:1 ≤ D)
    (_ha:0<a) (_hc:0 ≤ c) (ht:0 ≤ t) (hca:2*c*Real.log D ≤ a/2)
    (K:ℕ) (hK:(K:ℝ) ≤ c*t) :
    D^(2*(K+1))*Real.exp (-a*t) ≤ D^2*Real.exp (-(a/2)*t) := by
  have hDp:0<D := lt_of_lt_of_le zero_lt_one hD
  have hlog:0 ≤ Real.log D := Real.log_nonneg hD
  have hpow:D^(2*(K+1))=D^2*Real.exp (2*(K:ℝ)*Real.log D) := by
    rw [show 2*(K+1)=2+2*K by omega,pow_add]
    congr 1
    calc D^(2*K)=(Real.exp (Real.log D))^(2*K) := by rw [Real.exp_log hDp]
         _ = _ := by rw [←Real.exp_nat_mul];congr 1;push_cast;ring
  rw [hpow,mul_assoc,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (sq_nonneg _)
  have h1:2*(K:ℝ)*Real.log D ≤ (2*c*Real.log D)*t := by nlinarith
  have h2:(2*c*Real.log D)*t ≤ (a/2)*t := mul_le_mul_of_nonneg_right hca ht
  linarith
lemma doubleFactorial_even_sub_one_bound (a:ℕ) :
    (Nat.doubleFactorial (2*a-1):ℝ) ≤ (2:ℝ)^a*(a.factorial:ℝ) := by
  induction a with
  | zero=>simp
  | succ a ih=>
    rw [show 2*(a+1)-1=2*a+1 by omega,Nat.doubleFactorial_add_one]
    push_cast
    calc _ ≤ ((2:ℝ)*a+1)*((2:ℝ)^a*(a.factorial:ℝ)) := by gcongr
         _ ≤ (2:ℝ)^(a+1)*((a+1).factorial:ℝ) := by
           rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
           nlinarith [pow_nonneg (by norm_num:(0:ℝ) ≤ 2) a]
lemma gaussian_model_coefficients_gevrey_two (f:ℕ → ℂ → ℂ) (C B R:ℝ)
    (hC:0 ≤ C) (hB:0 ≤ B) (hR:0<R)
    (hf:∀s,DifferentiableOn ℂ (f s) (Metric.closedBall 0 R))
    (hbound:∀s z,z ∈ Metric.sphere (0:ℂ) R → ‖f s z‖ ≤ C*B^s*(s.factorial:ℝ)^2) (j:ℕ) :
    ‖gaussianModelCoefficient f j‖ ≤ C*(2*max B (2/R^2))^j*(j.factorial:ℝ)^2 := by
  let D:ℝ:=2/R^2
  let E:ℝ:=max B D
  have hD:0 ≤ D := by dsimp[D];positivity
  have hE:0 ≤ E := hB.trans (le_max_left _ _)
  have hterm(s:ℕ)(hs:s ∈ Finset.range (j+1)):
      ‖WP.coeff (f s) (2*(j-s))*(Nat.doubleFactorial (2*(j-s)-1):ℂ)‖ ≤ C*E^j*(j.factorial:ℝ)^2 := by
    let a:ℕ:=j-s
    have hplus:s+a=j := Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hs))
    have hc:=coeff_norm_le_circle_bound (f s) R (C*B^s*(s.factorial:ℝ)^2) hR (hf s) (hbound s) (2*a)
    have hd:=doubleFactorial_even_sub_one_bound a
    have heq:(C*B^s*(s.factorial:ℝ)^2/R^(2*a))*((2:ℝ)^a*(a.factorial:ℝ))=
        C*(B^s*D^a)*((s.factorial:ℝ)^2*(a.factorial:ℝ)) := by
      dsimp only [D]
      rw [div_pow,pow_mul]
      ring
    have hp:B^s*D^a ≤ E^j := by
      calc _ ≤ E^s*E^a := by
                  exact mul_le_mul (pow_le_pow_left₀ hB (le_max_left B D) s)
                    (pow_le_pow_left₀ hD (le_max_right B D) a) (by positivity) (by positivity)
           _ = _ := by rw [←pow_add,hplus]
    have hfac:=gaussian_factorial_convolution s a
    rw [hplus] at hfac
    calc _ = ‖WP.coeff (f s) (2*a)‖*(Nat.doubleFactorial (2*a-1):ℝ) := by
                simp only [norm_mul,Complex.norm_natCast];rfl
         _ ≤ (C*B^s*(s.factorial:ℝ)^2/R^(2*a))*((2:ℝ)^a*(a.factorial:ℝ)) :=
              mul_le_mul hc hd (by positivity) (by positivity)
         _ = _ := heq
         _ ≤ _ := by gcongr
  unfold gaussianModelCoefficient
  calc _ ≤ ∑s ∈ Finset.range (j+1),‖WP.coeff (f s) (2*(j-s))*(Nat.doubleFactorial (2*(j-s)-1):ℂ)‖ := norm_sum_le _ _
       _ ≤ ∑s ∈ Finset.range (j+1),C*E^j*(j.factorial:ℝ)^2 := Finset.sum_le_sum hterm
       _ = ((j+1:ℕ):ℝ)*(C*E^j*(j.factorial:ℝ)^2) := by simp
       _ ≤ (2:ℝ)^j*(C*E^j*(j.factorial:ℝ)^2) := by
         apply mul_le_mul_of_nonneg_right _ (by positivity)
         exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n:=j))
       _ = _ := by dsimp only [E,D];rw [mul_pow];ring

lemma gaussian_shrinking_radius_exponent (τ h:ℝ) (hh:0<h) :
    (h/4)*(τ/Real.sqrt (Real.sqrt h))^2=(τ^2/4)*Real.sqrt h := by
  have hs:0<Real.sqrt h := Real.sqrt_pos.mpr hh
  rw [div_pow,Real.sq_sqrt hs.le]
  field_simp
  nlinarith [Real.sq_sqrt hh.le]
end WP.Analysis
