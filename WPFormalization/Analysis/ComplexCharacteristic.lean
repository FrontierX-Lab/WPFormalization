import WPFormalization.Statements.Kernels
import WPFormalization.Analysis.AffineIntegral
import WPFormalization.Analysis.BesselBranches
/-! The complex characteristic identity behind Lemma 2.1 / Eq.(A.1).
The square-root branch is t*sqrt(1-4u/t²), valid on the exterior region
4Y<norm(t)². Differentiation under the actual kernel integral and FTC prove
the exact correction formula; no deformed zero distribution is assumed. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology

def complexCharacteristicK (t u : ℂ) : ℂ :=
  ∫ s : ℝ in (0)..1, deriv X (t^2/4*(1-(s:ℂ)^2)+u*(s:ℂ)^2)
lemma complexCharacteristicK_eq (t u : ℂ) :
    complexCharacteristicK t u = K u ((t^2-4*u)/2) := by
  apply intervalIntegral.integral_congr
  intro s hs
  apply congrArg (deriv X)
  ring
lemma complexCharacteristicK_hasDerivAt (t u : ℂ) :
    HasDerivAt (complexCharacteristicK t)
      (∫ s : ℝ in (0)..1, (s:ℂ)^2*deriv (deriv X)
        (t^2/4*(1-(s:ℂ)^2)+u*(s:ℂ)^2)) u := by
  have hg : Differentiable ℂ (deriv X) := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_X_differentiable 1
  change HasDerivAt (fun w : ℂ => ∫ s : ℝ in (0)..1,
    deriv X (t^2/4*(1-(s:ℂ)^2)+w*(s:ℂ)^2)) _ _
  simpa only [one_mul] using
    hasDerivAt_affineIntegral (fun _=>1) (fun s=>t^2/4*(1-(s:ℂ)^2))
      (fun s=>(s:ℂ)^2) continuous_const (by fun_prop) (by fun_prop) (deriv X) hg u
lemma complexCharacteristicK_relation (t u : ℂ) :
    complexCharacteristicK t u - (t^2-4*u)/2*deriv (complexCharacteristicK t) u = deriv X u := by
  have hg : Differentiable ℂ (deriv X) := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_X_differentiable 1
  have hi : (∫ s : ℝ in (0)..1, (s:ℂ)^2*deriv (deriv X)
      (t^2/4*(1-(s:ℂ)^2)+u*(s:ℂ)^2)) =
      ∫ s : ℝ in (0)..1, (s:ℂ)^2*deriv (deriv X)
        (u+((t^2-4*u)/2)/2*(1-(s:ℂ)^2)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    apply congrArg (fun v : ℂ => (s:ℂ)^2*deriv (deriv X) v)
    ring
  have hd := (complexCharacteristicK_hasDerivAt t u).deriv.trans hi
  exact (congrArg₂ (fun x y : ℂ=>x-(t^2-4*u)/2*y) (complexCharacteristicK_eq t u) hd).trans
    (kernelIntegral_first_moment (deriv X) hg u ((t^2-4*u)/2))
lemma complexSqrt_hasDerivAt_inv {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt Complex.sqrt (1/(2*Complex.sqrt z)) z := by
  convert Complex.hasDerivAt_sqrt hz using 1
  rw [show (-1/2:ℂ)=-(2:ℂ)⁻¹ by norm_num,Complex.cpow_neg]
  simp only [Complex.sqrt,one_div,mul_inv_rev]
  ring

def characteristicRoot (t u : ℂ) : ℂ := Complex.sqrt (1-4*u/t^2)
lemma characteristicRoot_sq (t u : ℂ) (ht : t ≠ 0) :
    t^2*(characteristicRoot t u)^2 = t^2-4*u := by
  unfold characteristicRoot
  rw [complex_sqrt_sq]
  field_simp
lemma characteristicRoot_hasDerivAt (t u : ℂ)
    (hslit : 1-4*u/t^2 ∈ Complex.slitPlane) :
    HasDerivAt (characteristicRoot t) ((-4/t^2)/(2*characteristicRoot t u)) u := by
  have hp := (((hasDerivAt_id u).const_mul 4).div_const (t^2)).const_sub 1
  change HasDerivAt (fun v : ℂ => Complex.sqrt (1-4*v/t^2)) _ u
  convert (complexSqrt_hasDerivAt_inv hslit).comp u hp using 1 <;>
    dsimp only [characteristicRoot,Function.comp_def,id_eq] <;> ring

def weightedComplexCharacteristic (t u : ℂ) : ℂ :=
  t*characteristicRoot t u*complexCharacteristicK t u
lemma weightedComplexCharacteristic_hasDerivAt (t u : ℂ) (ht : t ≠ 0)
    (hslit : 1-4*u/t^2 ∈ Complex.slitPlane) :
    HasDerivAt (weightedComplexCharacteristic t)
      (-2*deriv X u/(t*characteristicRoot t u)) u := by
  have hr := characteristicRoot_hasDerivAt t u hslit
  have hK := complexCharacteristicK_hasDerivAt t u
  have hq2 := characteristicRoot_sq t u ht
  have hrel := complexCharacteristicK_relation t u
  have hq : characteristicRoot t u ≠ 0 := by
    intro he
    have hsq : (characteristicRoot t u)^2 = 1-4*u/t^2 := complex_sqrt_sq _
    rw [he,zero_pow (by norm_num : (2:ℕ) ≠ 0)] at hsq
    exact Complex.zero_notMem_slitPlane (hsq ▸ hslit)
  have hd := (hr.const_mul t).mul hK
  have hKd : (∫ s : ℝ in (0)..1, (s:ℂ)^2*deriv (deriv X)
      (t^2/4*(1-(s:ℂ)^2)+u*(s:ℂ)^2)) = deriv (complexCharacteristicK t) u := hK.deriv.symm
  rw [hKd] at hd
  convert hd using 1
  · rfl
  · field_simp [ht,hq]
    linear_combination 4*hrel-2*deriv (complexCharacteristicK t) u*hq2
lemma characteristicRoot_ne_zero (t u : ℂ)
    (hslit : 1-4*u/t^2 ∈ Complex.slitPlane) : characteristicRoot t u ≠ 0 := by
  intro he
  have hsq : (characteristicRoot t u)^2 = 1-4*u/t^2 := complex_sqrt_sq _
  rw [he,zero_pow (by norm_num : (2:ℕ) ≠ 0)] at hsq
  exact Complex.zero_notMem_slitPlane (hsq ▸ hslit)
lemma characteristic_slit_of_norm (Y : ℝ) (hY : 0 ≤ Y) (t : ℂ)
    (ht : 4*Y < ‖t‖^2) (u : ℝ) (hu : u ∈ Icc 0 Y) :
    1-4*(u:ℂ)/t^2 ∈ Complex.slitPlane := by
  have hn : 0 < ‖t‖^2 := lt_of_le_of_lt (by positivity) ht
  have hv : ‖4*(u:ℂ)/t^2‖ < 1 := by
    rw [norm_div,norm_mul,norm_pow]
    norm_num only [Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_of_nonneg hu.1]
    apply (div_lt_one hn).2
    linarith [hu.2]
  apply Or.inl
  have hr := (le_abs_self (4*(u:ℂ)/t^2).re).trans (Complex.abs_re_le_norm _)
  simp only [Complex.sub_re,Complex.one_re]
  linarith
lemma complex_characteristic_identity (Y : ℝ) (hY : 0 ≤ Y) (t : ℂ)
    (ht : 4*Y < ‖t‖^2) :
    t*characteristicRoot t Y*K Y ((t^2-4*Y)/2) = Complex.sin t-
      2*(∫ u : ℝ in (0)..Y, deriv X u/(t*characteristicRoot t u)) := by
  have ht0 : t ≠ 0 := by
    intro he
    simp only [he,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)] at ht
    linarith
  have hs (u : ℝ) (hu : u ∈ Icc 0 Y) := characteristic_slit_of_norm Y hY t ht u hu
  have hqCont : ContinuousOn (fun u : ℝ => characteristicRoot t u) (Icc 0 Y) := by
    change ContinuousOn (fun u : ℝ => Complex.sqrt (1-4*(u:ℂ)/t^2)) _
    exact Complex.continuousOn_sqrt.comp (by fun_prop) hs
  have hD : Continuous (fun u : ℝ => deriv X u) := by
    have hg : Continuous (deriv X) := by
      simpa only [iteratedDeriv_one] using (iteratedDeriv_X_differentiable 1).continuous
    exact hg.comp Complex.continuous_ofReal
  have hInt : IntervalIntegrable
      (fun u : ℝ => -2*deriv X u/(t*characteristicRoot t u)) volume 0 Y := by
    apply ContinuousOn.intervalIntegrable_of_Icc hY
    exact ((continuous_const.mul hD).continuousOn).div (hqCont.const_mul t)
      (fun u hu => mul_ne_zero ht0 (characteristicRoot_ne_zero t u (hs u hu)))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=(0:ℝ)) (b:=Y)
    (fun u hu => (weightedComplexCharacteristic_hasDerivAt t u ht0
      (hs u (by simpa only [uIcc_of_le hY] using hu))).comp_ofReal) hInt
  have hzero : weightedComplexCharacteristic t 0 = Complex.sin t := by
    change t*Complex.sqrt (1-4*0/t^2)*complexCharacteristicK t 0 = _
    simp only [mul_zero,zero_div,sub_zero,Complex.sqrt_one,mul_one]
    rw [complexCharacteristicK_eq]
    simp only [mul_zero,sub_zero]
    simpa only [rootKernel,K] using rootKernel_sine t
  simp only [Complex.ofReal_zero] at hFTC
  rw [hzero] at hFTC
  have hFTC' : (-2:ℂ)*(∫ u : ℝ in (0)..Y, deriv X u/(t*characteristicRoot t u)) =
      weightedComplexCharacteristic t Y-Complex.sin t := by
    rw [← intervalIntegral.integral_const_mul]
    simpa only [mul_div_assoc] using hFTC
  have hh : weightedComplexCharacteristic t Y = Complex.sin t-
      2*(∫ u : ℝ in (0)..Y, deriv X u/(t*characteristicRoot t u)) := by
    linear_combination -hFTC'
  simpa only [weightedComplexCharacteristic,complexCharacteristicK_eq] using hh
end WP.Analysis
