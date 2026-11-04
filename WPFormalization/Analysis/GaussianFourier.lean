import Mathlib
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma gaussian_fourier_normalized (v q:ℝ)(hv:0<v) :
    (((2*Real.pi:ℝ):ℂ)⁻¹)*(∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*Complex.exp (-(v:ℂ)/2*(t:ℂ)^2)) =
      ((Real.exp (-q^2/(2*v))/Real.sqrt (2*Real.pi*v):ℝ):ℂ) := by
  have hb : 0<((v:ℂ)/2).re := by norm_num; linarith
  have hi := fourierIntegral_gaussian (b:=(v:ℂ)/2) hb (-(q:ℂ))
  have hf : (fun t:ℝ=>Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*Complex.exp (-(v:ℂ)/2*(t:ℂ)^2)) =
      (fun t:ℝ=>Complex.exp (Complex.I*(-(q:ℂ))*(t:ℂ))*Complex.exp (-((v:ℂ)/2)*(t:ℂ)^2)) := by
    ext t
    congr 1 <;> congr 1 <;> ring
  rw [hf,hi]
  have hbase : (Real.pi:ℂ)/((v:ℂ)/2) = ((Real.pi/(v/2):ℝ):ℂ) := by push_cast; rfl
  have hpow : (((Real.pi/(v/2):ℝ):ℂ)^(1/2:ℂ)) = ((Real.sqrt (Real.pi/(v/2)):ℝ):ℂ) := by
    rw [Real.sqrt_eq_rpow]
    simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
      (Complex.ofReal_cpow (by positivity : 0≤Real.pi/(v/2)) (1/2:ℝ)).symm
  have he : -(-(q:ℂ))^2/(4*((v:ℂ)/2)) = ((-q^2/(2*v):ℝ):ℂ) := by
    push_cast
    field_simp
    <;> ring
  rw [hbase,hpow,he,←Complex.ofReal_exp]
  have hp : 0<2*Real.pi := by positivity
  have hs : 0<Real.sqrt (2*Real.pi*v) := Real.sqrt_pos.mpr (by positivity)
  have hprod : Real.sqrt (Real.pi/(v/2))*Real.sqrt (2*Real.pi*v)=2*Real.pi := by
    rw [←Real.sqrt_mul (by positivity : 0≤Real.pi/(v/2))]
    have hprod : Real.pi/(v/2)*(2*Real.pi*v)=(2*Real.pi)^2 := by field_simp
    rw [hprod,Real.sqrt_sq hp.le]
  have hscale : Real.sqrt (Real.pi/(v/2))/(2*Real.pi)=1/Real.sqrt (2*Real.pi*v) := by
    apply (div_eq_div_iff (ne_of_gt hp) (ne_of_gt hs)).mpr
    simpa only [one_mul] using hprod
  have hreal : (2*Real.pi)⁻¹*Real.sqrt (Real.pi/(v/2))*Real.exp (-q^2/(2*v)) =
      Real.exp (-q^2/(2*v))/Real.sqrt (2*Real.pi*v) := by
    calc (2*Real.pi)⁻¹*Real.sqrt (Real.pi/(v/2))*Real.exp (-q^2/(2*v)) =
            (Real.sqrt (Real.pi/(v/2))/(2*Real.pi))*Real.exp (-q^2/(2*v)) := by ring
         _ = _ := by rw [hscale]; ring
  have hreal' : (2*Real.pi)⁻¹*(Real.sqrt (Real.pi/(v/2))*Real.exp (-q^2/(2*v))) =
      Real.exp (-q^2/(2*v))/Real.sqrt (2*Real.pi*v) := by simpa only [mul_assoc] using hreal
  exact_mod_cast hreal'
end WP.Analysis

namespace WP.Analysis
lemma gaussian_mass_scaling (v d:ℝ)(hv:0<v)(h:ℕ)(hh:0<h) :
    Real.sqrt (h:ℝ)*(Real.exp (-d^2/(2*(h:ℝ)*v))/Real.sqrt (2*Real.pi*(h:ℝ)*v)) =
      Real.exp (-(d/Real.sqrt (h:ℝ))^2/(2*v))/Real.sqrt (2*Real.pi*v) := by
  let r := Real.sqrt (h:ℝ)
  have hr : 0<r := Real.sqrt_pos.mpr (by exact_mod_cast hh)
  have hrs : r^2=(h:ℝ) := Real.sq_sqrt (by positivity)
  have hden : Real.sqrt (2*Real.pi*(h:ℝ)*v)=r*Real.sqrt (2*Real.pi*v) := by
    rw [show 2*Real.pi*(h:ℝ)*v=(h:ℝ)*(2*Real.pi*v) by ring,Real.sqrt_mul (show (0:ℝ)≤h by positivity)]
  have he : -d^2/(2*(h:ℝ)*v)=-(d/r)^2/(2*v) := by
    rw [div_pow,hrs]
    field_simp
    <;> ring
  change r*(Real.exp (-d^2/(2*(h:ℝ)*v))/Real.sqrt (2*Real.pi*(h:ℝ)*v)) =
      Real.exp (-(d/r)^2/(2*v))/Real.sqrt (2*Real.pi*v)
  rw [hden,he]
  field_simp
end WP.Analysis
