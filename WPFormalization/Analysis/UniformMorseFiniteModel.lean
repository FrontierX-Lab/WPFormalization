import WPFormalization.Analysis.FixedMorseIntegral
/-! Uniform finite-amplitude Morse comparison. The native Gevrey-two budget bounds the whole amplitude prefix by a common constant; the genuine endpoint connectors and shrinking-cutoff Gaussian tails are controlled explicitly. No stationary-phase estimate is assumed. -/
noncomputable section
open Set MeasureTheory
namespace WP.Analysis

def finiteMorseAmplitude (a:ℕ→ℂ→ℂ) (h:ℝ) (J:ℕ) (z:ℂ):ℂ :=
  ∑s∈Finset.range (J+1),a s z/(h:ℂ)^s

def finiteMorseSourceIntegral (φ:ℂ→ℂ) (a:ℕ→ℂ→ℂ) (h r:ℝ) (J:ℕ):ℂ :=
  (Real.sqrt h:ℂ)*(∫u:ℝ in (-r)..r,Complex.exp ((h:ℂ)*φ (u:ℂ))*finiteMorseAmplitude a h J (u:ℂ))

lemma finiteMorseAmplitude_norm_bound (a:ℕ→ℂ→ℂ) (C B h:ℝ) (J:ℕ) (z:ℂ)
    (hC:0≤C) (hB:0≤B) (hh:0<h)
    (ha:∀s≤J,‖a s z‖≤C*B^s*(s.factorial:ℝ)^2)
    (hwindow:B*((J:ℝ)+1)^2/h≤1/2) :
    ‖finiteMorseAmplitude a h J z‖≤2*C := by
  calc _ ≤ ∑s∈Finset.range (J+1),‖a s z/(h:ℂ)^s‖:=norm_sum_le _ _
       _ ≤ ∑s∈Finset.range (J+1),C*(B^s*(s.factorial:ℝ)^2/h^s) := by
         apply Finset.sum_le_sum
         intro s hs
         rw[norm_div,norm_pow,Complex.norm_of_nonneg hh.le]
         exact (div_le_div_of_nonneg_right (ha s (Nat.le_of_lt_succ (Finset.mem_range.mp hs))) (pow_nonneg hh.le _)).trans_eq (by ring)
       _ = C*∑s∈Finset.range (J+1),B^s*(s.factorial:ℝ)^2/h^s := (Finset.mul_sum _ _ _).symm
       _ ≤ C*2:=mul_le_mul_of_nonneg_left (gaussian_gevrey_prefix_bound B h hB hh J hwindow) hC
       _ = _:=by ring

lemma finiteMorseAmplitude_transform (a b:ℕ→ℂ→ℂ) (U:ℂ→ℂ) (h:ℝ) (J:ℕ) (z:ℂ)
    (ha:∀s≤J,a s (U z)*deriv U z=b s z) :
    finiteMorseAmplitude a h J (U z)*deriv U z=finiteMorseAmplitude b h J z := by
  dsimp only[finiteMorseAmplitude]
  rw[Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  calc a s (U z)/(h:ℂ)^s*deriv U z=(a s (U z)*deriv U z)/(h:ℂ)^s := by ring
       _ = _:=by rw[ha s (Nat.le_of_lt_succ (Finset.mem_range.mp hs))]

lemma finiteMorseSource_gaussian_eq (b:ℕ→ℂ→ℂ) (h r R:ℝ) (J:ℕ)
    (hr:0≤r) (hrR:r<R) (hb:∀s≤J,DifferentiableOn ℂ (b s) (Metric.ball 0 R)) :
    finiteMorseSourceIntegral (fun z:ℂ=>-z^2/2) b h r J=
      ∑s∈Finset.range (J+1),gaussianAmplitudeIntegral b h r s := by
  have hm:MapsTo (fun u:ℝ=>(u:ℂ)) (Icc (-r) r) (Metric.ball 0 R) := by
    intro u hu
    rw[Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs]
    exact (abs_le.mpr ⟨by linarith[hu.1],hu.2⟩).trans_lt hrR
  have hi(s:ℕ)(hs:s∈Finset.range (J+1)):
      IntervalIntegrable (fun u:ℝ=>Complex.exp ((h:ℂ)*(-(u:ℂ)^2/2))*b s (u:ℂ)/(h:ℂ)^s) volume (-r) r := by
    have hc:ContinuousOn (fun u:ℝ=>Complex.exp ((h:ℂ)*(-(u:ℂ)^2/2))*b s (u:ℂ)/(h:ℂ)^s) (Icc (-r) r) :=
      (((show Continuous (fun u:ℝ=>Complex.exp ((h:ℂ)*(-(u:ℂ)^2/2))) by fun_prop).continuousOn).mul
        ((hb s (Nat.le_of_lt_succ (Finset.mem_range.mp hs))).continuousOn.comp Complex.continuous_ofReal.continuousOn hm)).div_const _
    exact hc.intervalIntegrable_of_Icc (by linarith)
  have he:(fun u:ℝ=>Complex.exp ((h:ℂ)*(-(u:ℂ)^2/2))*finiteMorseAmplitude b h J (u:ℂ))=
      (fun u:ℝ=>∑s∈Finset.range (J+1),Complex.exp ((h:ℂ)*(-(u:ℂ)^2/2))*b s (u:ℂ)/(h:ℂ)^s) := by
    funext u
    dsimp only[finiteMorseAmplitude]
    rw[Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  dsimp only[finiteMorseSourceIntegral]
  rw[he,intervalIntegral.integral_finsetSum hi,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  simp_rw [div_eq_mul_inv,intervalIntegral.integral_mul_const]
  dsimp only[gaussianAmplitudeIntegral]
  have hg:(∫u:ℝ in (-r)..r,Complex.exp ((h:ℂ)*(-(u:ℂ)^2/2))*b s (u:ℂ))=
      ∫u:ℝ in Icc (-r) r,Real.exp (-(h/2)*u^2) • b s (u:ℂ) := by
    rw[intervalIntegral.integral_of_le (by linarith:-r≤r),←integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    change Complex.exp ((h:ℂ)*(-(u:ℂ)^2/2))*b s (u:ℂ)=(Real.exp (-(h/2)*u^2):ℂ)*b s (u:ℂ)
    rw[Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  simp only[div_eq_mul_inv] at hg
  rw[hg]
  ring

lemma uniform_finite_morse_connector_bound (φ U:ℂ→ℂ) (a b:ℕ→ℂ→ℂ)
    (C B Cw h r R S:ℝ) (J:ℕ) (ep en:ℂ)
    (hC:0≤C) (hB:0≤B) (hCw:0≤Cw) (hh:0<h) (hr:0<r) (hrR:r<R) (hrS:r<S)
    (hφ:DifferentiableOn ℂ φ (Metric.ball 0 S))
    (ha:∀s≤J,DifferentiableOn ℂ (a s) (Metric.ball 0 S))
    (hb:∀s≤J,DifferentiableOn ℂ (b s) (Metric.ball 0 R))
    (hU:DifferentiableOn ℂ U (Metric.ball 0 R))
    (hmap:MapsTo U (Metric.ball 0 R) (Metric.ball 0 S))
    (hjet:∀z∈Metric.ball (0:ℂ) R,φ (U z)=-z^2/2 ∧ ∀s≤J,a s (U z)*deriv U z=b s z)
    (hbound:∀s≤J,∀z∈Metric.ball (0:ℂ) R,‖b s z‖≤C*B^s*(s.factorial:ℝ)^2)
    (hwindow:B*((J:ℝ)+1)^2/h≤1/2)
    (hep:‖ep‖≤r/4) (hen:‖en‖≤r/4) (hclose:‖ep‖+‖en‖≤2*Cw*r^2)
    (hp:‖(r:ℂ)+ep‖<R) (hn:‖-(r:ℂ)+en‖<R)
    (hUp:U ((r:ℂ)+ep)=(r:ℂ)) (hUn:U (-(r:ℂ)+en)= -(r:ℂ)) :
    ‖finiteMorseSourceIntegral φ a h r J-
      ∑s∈Finset.range (J+1),gaussianAmplitudeIntegral b h r s‖≤
        4*C*Cw*Real.sqrt h*r^2*Real.exp (-(h/4)*r^2) := by
  have haSum:DifferentiableOn ℂ (finiteMorseAmplitude a h J) (Metric.ball 0 S) := by
    intro z hz
    apply DifferentiableWithinAt.fun_sum
    intro s hs
    exact (ha s (Nat.le_of_lt_succ (Finset.mem_range.mp hs)) z hz).div_const _
  have hc:=fixed_morse_integral_connector_bound φ (finiteMorseAmplitude a h J) U
    (finiteMorseAmplitude b h J) h (2*C) r R S ep en hh (by positivity) hr hrR hrS hφ haSum hU hmap
    (fun z hz=>⟨(hjet z hz).1,finiteMorseAmplitude_transform a b U h J z (hjet z hz).2⟩)
    (fun z hz=>finiteMorseAmplitude_norm_bound b C B h J z hC hB hh
      (fun s hs=>hbound s hs z hz) hwindow) hep hen hp hn hUp hUn
  rw[←finiteMorseSource_gaussian_eq b h r R J hr.le hrR hb]
  change ‖(Real.sqrt h:ℂ)*_-(Real.sqrt h:ℂ)*_‖≤_
  rw[←mul_sub,norm_mul,Complex.norm_of_nonneg (Real.sqrt_nonneg h)]
  have he:(fun u:ℝ=>Complex.exp ((h:ℂ)*(-(u:ℂ)^2/2))*finiteMorseAmplitude b h J (u:ℂ))=
      (fun u:ℝ=>Complex.exp (-(h:ℂ)/2*(u:ℂ)^2)*finiteMorseAmplitude b h J (u:ℂ)) := by
    funext u
    congr 2
    ring
  rw[he]
  apply (mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg h)).trans
  calc _ ≤ Real.sqrt h*(2*C*Real.exp (-(h/4)*r^2)*(2*Cw*r^2)) := by
             gcongr
       _ = _:=by ring
end WP.Analysis

namespace WP.Analysis
lemma gaussian_shrinking_cutoff_prefactor (τ h:ℝ) (hh:0<h) :
    Real.sqrt h*(τ/Real.sqrt (Real.sqrt h))^2=τ^2 := by
  have hs:0<Real.sqrt h:=Real.sqrt_pos.mpr hh
  rw[div_pow,Real.sq_sqrt hs.le]
  field_simp

lemma finite_morse_gaussian_remainder_from_connector (φ:ℂ→ℂ) (a b:ℕ→ℂ→ℂ)
    (C B R r h D:ℝ) (J K:ℕ)
    (hC:0≤C) (hB:0≤B) (hR:0<R) (hr:0<r) (hrR:r≤R/2) (hh:0<h)
    (hb:∀s,DifferentiableOn ℂ (b s) (Metric.closedBall 0 R))
    (hbound:∀s z,z∈Metric.closedBall (0:ℂ) R→‖b s z‖≤C*B^s*(s.factorial:ℝ)^2)
    (hKJ:K≤J) (hwindow:B*((J:ℝ)+1)^2/h≤1/2) (hsmall:8*((K:ℝ)+1)≤h)
    (hc:‖finiteMorseSourceIntegral φ a h r J-∑s∈Finset.range (J+1),gaussianAmplitudeIntegral b h r s‖≤
      D*Real.exp (-(h/4)*r^2)) :
    ‖finiteMorseSourceIntegral φ a h r J-
      (Real.sqrt (2*Real.pi):ℂ)*∑j∈Finset.range (K+1),gaussianModelCoefficient b j/(h:ℂ)^j‖≤
      (2*C*(Real.sqrt (4*Real.pi)+Real.sqrt (2*Real.pi)))*
        (2*max B (4/R^2))^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)+
      (4*C*Real.sqrt (8*Real.pi)*(2*max 1 R⁻¹)^(2*(K+1))+D)*Real.exp (-(h/4)*r^2) := by
  have hg:=gaussian_model_remainder_bound b C B R r h hC hB hR hr hrR hh hb hbound J K hKJ hwindow hsmall
  rw[gaussian_polynomial_amplitudes_regroup] at hg
  calc _ ≤ ‖finiteMorseSourceIntegral φ a h r J-∑s∈Finset.range (J+1),gaussianAmplitudeIntegral b h r s‖+
      ‖(∑s∈Finset.range (J+1),gaussianAmplitudeIntegral b h r s)-
        (Real.sqrt (2*Real.pi):ℂ)*∑j∈Finset.range (K+1),gaussianModelCoefficient b j/(h:ℂ)^j‖:=norm_sub_le_norm_sub_add_norm_sub _ _ _
       _ ≤ _:=by have ht:=add_le_add hc hg;convert ht using 1 <;>ring

lemma shrinking_morse_exponential_absorption (C D E τ h c:ℝ) (K:ℕ)
    (hC:0≤C) (hD:1≤D) (hE:0≤E) (hτ:0<τ) (hh:0<h) (hc:0≤c)
    (hca:2*c*Real.log D≤(τ^2/4)/2) (hK:(K:ℝ)≤c*Real.sqrt h) :
    (C*D^(2*(K+1))+E)*Real.exp (-(h/4)*(τ/Real.sqrt (Real.sqrt h))^2)≤
      (C*D^2+E)*Real.exp (-(τ^2/8)*Real.sqrt h) := by
  have he0:-(h/4)*(τ/Real.sqrt (Real.sqrt h))^2=-(τ^2/4)*Real.sqrt h := by
    linear_combination -(gaussian_shrinking_radius_exponent τ h hh)
  rw[he0]
  have ht:=gaussian_polynomial_outer_exponential_absorption D (τ^2/4) c (Real.sqrt h) hD
    (by positivity) hc (Real.sqrt_nonneg h) hca K hK
  have he:Real.exp (-(τ^2/4)*Real.sqrt h)≤Real.exp (-(τ^2/8)*Real.sqrt h) := by
    apply Real.exp_le_exp.mpr
    nlinarith[sq_nonneg τ,Real.sqrt_nonneg h]
  calc _ = C*(D^(2*(K+1))*Real.exp (-(τ^2/4)*Real.sqrt h))+E*Real.exp (-(τ^2/4)*Real.sqrt h) := by ring
       _ ≤ C*(D^2*Real.exp (-((τ^2/4)/2)*Real.sqrt h))+E*Real.exp (-(τ^2/8)*Real.sqrt h) :=
         add_le_add (mul_le_mul_of_nonneg_left ht hC) (mul_le_mul_of_nonneg_left he hE)
       _ = _:=by congr 1 <;>ring
end WP.Analysis
