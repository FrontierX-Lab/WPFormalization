import Mathlib
/-! Coefficientwise differentiation of analytic parameter families of formal series.
Finite product rules yield the normalized-logarithm parameter equation. -/
noncomputable section
namespace WP.Analysis
open Filter
open scoped Topology
abbrev PSeries := PowerSeries ℂ
def coefficientDeriv (F : ℂ → PSeries) (Y : ℂ) : PSeries :=
  PowerSeries.mk (fun n => deriv (fun W => PowerSeries.coeff n (F W)) Y)
@[simp] lemma coefficientDeriv_coeff (F : ℂ → PSeries) (Y : ℂ) (n : ℕ) :
    PowerSeries.coeff n (coefficientDeriv F Y) = deriv (fun W => PowerSeries.coeff n (F W)) Y :=
  PowerSeries.coeff_mk _ _
lemma coefficientDeriv_congr (F G : ℂ → PSeries) (Y : ℂ) (he : F =ᶠ[𝓝 Y] G) :
    coefficientDeriv F Y = coefficientDeriv G Y := by
  ext n
  simp only [coefficientDeriv_coeff]
  have hc : (fun W => PowerSeries.coeff n (F W)) =ᶠ[𝓝 Y] (fun W => PowerSeries.coeff n (G W)) :=
    he.mono (fun W hW => congrArg (PowerSeries.coeff n) hW)
  exact hc.deriv_eq
lemma coefficientDeriv_neg (F : ℂ → PSeries) (Y : ℂ) :
    coefficientDeriv (fun W => -F W) Y = -coefficientDeriv F Y := by
  ext n
  simp only [coefficientDeriv_coeff,map_neg]
  exact deriv.neg
lemma coefficientDeriv_mul (F G : ℂ → PSeries) (Y : ℂ)
    (hF : ∀ n, AnalyticAt ℂ (fun W => PowerSeries.coeff n (F W)) Y)
    (hG : ∀ n, AnalyticAt ℂ (fun W => PowerSeries.coeff n (G W)) Y) :
    coefficientDeriv (fun W => F W*G W) Y = coefficientDeriv F Y*G Y+F Y*coefficientDeriv G Y := by
  ext n
  simp only [coefficientDeriv_coeff,map_add,PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [deriv_fun_sum (A := fun i W => PowerSeries.coeff i (F W)*PowerSeries.coeff (n-i) (G W)) (fun i hi => (hF i).differentiableAt.mul (hG (n-i)).differentiableAt)]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [deriv_fun_mul (hF i).differentiableAt (hG (n-i)).differentiableAt]
lemma coefficientDeriv_derivative (F : ℂ → PSeries) (Y : ℂ) :
    coefficientDeriv (fun W => PowerSeries.derivative (F W)) Y =
      PowerSeries.derivative (coefficientDeriv F Y) := by
  ext n
  simp only [coefficientDeriv_coeff,PowerSeries.coeff_derivative]
  rw [deriv_mul_const_field]
lemma coefficientDeriv_C (a : ℂ → ℂ) (Y : ℂ) :
    coefficientDeriv (fun W => PowerSeries.C (a W)) Y = PowerSeries.C (deriv a Y) := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp

lemma coefficientDeriv_log_ratio (F T : ℂ → PSeries) (Y : ℂ)
    (hF : ∀ n, AnalyticAt ℂ (fun W => PowerSeries.coeff n (F W)) Y)
    (hT : ∀ n, AnalyticAt ℂ (fun W => PowerSeries.coeff n (T W)) Y)
    (hf0 : PowerSeries.constantCoeff (F Y) ≠ 0)
    (hlog : (fun W => PowerSeries.derivative (T W)*F W) =ᶠ[𝓝 Y]
      (fun W => -PowerSeries.derivative (F W)))
    (hT0 : ∀ᶠ W in 𝓝 Y, PowerSeries.constantCoeff (T W) = 0) :
    coefficientDeriv T Y =
      PowerSeries.C (PowerSeries.constantCoeff (coefficientDeriv F Y)/PowerSeries.constantCoeff (F Y))-
        coefficientDeriv F Y*(F Y)⁻¹ := by
  let f := F Y
  let t := T Y
  let g := coefficientDeriv F Y
  let u := coefficientDeriv T Y
  let w := PowerSeries.C (PowerSeries.constantCoeff g/PowerSeries.constantCoeff f)-g*f⁻¹
  have hTder : ∀ n, AnalyticAt ℂ (fun W => PowerSeries.coeff n (PowerSeries.derivative (T W))) Y := by
    intro n
    simp only [PowerSeries.coeff_derivative]
    exact (hT (n+1)).mul analyticAt_const
  have hd := coefficientDeriv_congr _ _ Y hlog
  rw [coefficientDeriv_mul _ _ _ hTder hF,coefficientDeriv_derivative,
    coefficientDeriv_neg,coefficientDeriv_derivative] at hd
  change PowerSeries.derivative u*f+PowerSeries.derivative t*g = -PowerSeries.derivative g at hd
  have hlog0 : PowerSeries.derivative t*f = -PowerSeries.derivative f := hlog.eq_of_nhds
  have ht : PowerSeries.derivative t = -PowerSeries.derivative f*f⁻¹ := by
    calc
      _ = (PowerSeries.derivative t*f)*f⁻¹ := by
        rw [mul_assoc,PowerSeries.mul_inv_cancel f hf0,mul_one]
      _ = _ := by rw [hlog0]
  have huD : PowerSeries.derivative u =
      -(PowerSeries.derivative g+PowerSeries.derivative t*g)*f⁻¹ := by
    have hm : PowerSeries.derivative u*f = -(PowerSeries.derivative g+PowerSeries.derivative t*g) := by
      linear_combination hd
    calc
      _ = (PowerSeries.derivative u*f)*f⁻¹ := by
        rw [mul_assoc,PowerSeries.mul_inv_cancel f hf0,mul_one]
      _ = _ := by rw [hm]
  have hwD : PowerSeries.derivative w =
      -(PowerSeries.derivative g+PowerSeries.derivative t*g)*f⁻¹ := by
    dsimp only [w]
    simp only [map_sub,PowerSeries.derivative_C,zero_sub,Derivation.leibniz,smul_eq_mul,
      PowerSeries.derivative_inv']
    rw [ht]
    ring
  have hu0 : PowerSeries.constantCoeff u = 0 := by
    have hz : (fun W => PowerSeries.coeff 0 (T W)) =ᶠ[𝓝 Y] (fun _ => 0) := by
      filter_upwards [hT0] with W hW
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hW
    simpa only [u,coefficientDeriv,PowerSeries.constantCoeff_mk,deriv_const] using hz.deriv_eq
  have hw0 : PowerSeries.constantCoeff w = 0 := by
    simp [w,div_eq_mul_inv]
  change u = w
  exact PowerSeries.derivative.ext (huD.trans hwD.symm) (hu0.trans hw0.symm)

def shiftSeries (p : PSeries) : PSeries := PowerSeries.mk (fun n => PowerSeries.coeff (n+1) p)
@[simp] lemma shiftSeries_coeff (p : PSeries) (n : ℕ) :
    PowerSeries.coeff n (shiftSeries p) = PowerSeries.coeff (n+1) p := by simp [shiftSeries]
lemma X_mul_shiftSeries (p : PSeries) :
    PowerSeries.X*shiftSeries p = p-PowerSeries.C (PowerSeries.constantCoeff p) := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp
lemma shiftSeries_mul_inv (p : PSeries) (hp : PowerSeries.constantCoeff p ≠ 0) :
    shiftSeries p*p⁻¹ = -shiftSeries (PowerSeries.C (PowerSeries.constantCoeff p)*p⁻¹) := by
  apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ℂ))
  calc
    PowerSeries.X*(shiftSeries p*p⁻¹) = (p-PowerSeries.C (PowerSeries.constantCoeff p))*p⁻¹ := by
      rw [← mul_assoc,X_mul_shiftSeries]
    _ = 1-PowerSeries.C (PowerSeries.constantCoeff p)*p⁻¹ := by
      rw [sub_mul,PowerSeries.mul_inv_cancel p hp]
    _ = -(PowerSeries.C (PowerSeries.constantCoeff p)*p⁻¹-1) := by ring
    _ = PowerSeries.X*(-shiftSeries (PowerSeries.C (PowerSeries.constantCoeff p)*p⁻¹)) := by
      rw [mul_neg,X_mul_shiftSeries]
      simp [hp]
lemma coefficientDeriv_log_pde (F T : ℂ → PSeries) (Y : ℂ) (α : ℂ)
    (hF : ∀ n, AnalyticAt ℂ (fun W => PowerSeries.coeff n (F W)) Y)
    (hT : ∀ n, AnalyticAt ℂ (fun W => PowerSeries.coeff n (T W)) Y)
    (hf0 : PowerSeries.constantCoeff (F Y) ≠ 0)
    (hlog : (fun W => PowerSeries.derivative (T W)*F W) =ᶠ[𝓝 Y]
      (fun W => -PowerSeries.derivative (F W)))
    (hT0 : ∀ᶠ W in 𝓝 Y, PowerSeries.constantCoeff (T W) = 0)
    (hparam : coefficientDeriv F Y = 2*PowerSeries.derivative (F Y)+PowerSeries.C α*shiftSeries (F Y)) :
    coefficientDeriv T Y =
      PowerSeries.C (PowerSeries.constantCoeff (coefficientDeriv F Y)/PowerSeries.constantCoeff (F Y))+
        2*PowerSeries.derivative (T Y)+
          PowerSeries.C α*shiftSeries (PowerSeries.C (PowerSeries.constantCoeff (F Y))*(F Y)⁻¹) := by
  have ht : PowerSeries.derivative (T Y) = -PowerSeries.derivative (F Y)*(F Y)⁻¹ := by
    have h := hlog.eq_of_nhds
    calc
      _ = (PowerSeries.derivative (T Y)*F Y)*(F Y)⁻¹ := by
        rw [mul_assoc,PowerSeries.mul_inv_cancel (F Y) hf0,mul_one]
      _ = _ := by rw [h]
  rw [coefficientDeriv_log_ratio F T Y hF hT hf0 hlog hT0]
  conv_lhs => rw [hparam]
  calc
    _ = PowerSeries.C (PowerSeries.constantCoeff (2*PowerSeries.derivative (F Y)+PowerSeries.C α*shiftSeries (F Y))/PowerSeries.constantCoeff (F Y))-
        2*(PowerSeries.derivative (F Y)*(F Y)⁻¹)-PowerSeries.C α*(shiftSeries (F Y)*(F Y)⁻¹) := by ring
    _ = _ := by
      rw [shiftSeries_mul_inv (F Y) hf0,ht,← hparam]
      ring
end WP.Analysis
