import WPFormalization.HigherOrder.PhaseFamilyModel
import WPFormalization.Volumes.CriticalModelGrowth
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
noncomputable section
namespace WP.Analysis
open Set
open WP.HigherOrder
lemma phaseFamilyModel_centered_circle_bound (S:ℂ→ℂ)(H:ℕ→ℂ→ℂ)
    (h x ρ B D:ℝ)(J:ℕ)(hh:0<h)(hx:0<x)(hxρ:x≤ρ)(hB:0<B)(hD:0≤D)
    (hbudget:2*B*((J:ℝ)+1)^2≤h)
    (hH:∀s z,‖z‖≤ρ→‖H s z‖≤D*B^s*(s.factorial:ℝ)^2)
    (hphase:∀θ:ℝ,(S ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))-S (x:ℂ)).re≤-(x/2)*(1-Real.cos θ)):
    ∀θ:ℝ,‖Complex.exp (-((h:ℂ)*S (x:ℂ)))*
      phaseFamilyModel S H h J ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖≤
      2*D*Real.exp (-(h*x/2)*(1-Real.cos θ)):=by
  intro θ
  let z:ℂ:=(x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)
  have hz:‖z‖≤ρ:=by
    dsimp[z]
    rw[norm_mul,Complex.norm_of_nonneg hx.le,Complex.norm_exp_ofReal_mul_I,mul_one]
    exact hxρ
  have hsum:‖∑s∈Finset.range (J+1),(h:ℂ)⁻¹^s*H s z‖≤2*D:=by
    convert finite_gevrey_two_sum_norm (fun s=>H s z) D B h J hD hB hh (fun s=>hH s z hz) hbudget using 1
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    rw[div_eq_mul_inv,inv_pow,mul_comm]
  have he:Complex.exp (-((h:ℂ)*S (x:ℂ)))*phaseFamilyModel S H h J z=
      Complex.exp ((h:ℂ)*(S z-S (x:ℂ)))*(∑s∈Finset.range (J+1),(h:ℂ)⁻¹^s*H s z):=by
    rw[phaseFamilyModel,←mul_assoc,←Complex.exp_add]
    congr 2
    ring
  rw[he,norm_mul,Complex.norm_exp]
  have hexp:Real.exp (((h:ℂ)*(S z-S (x:ℂ))).re)≤Real.exp (-(h*x/2)*(1-Real.cos θ)):=by
    apply Real.exp_le_exp.mpr
    simp only[Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    have ht:=mul_le_mul_of_nonneg_left (hphase θ) hh.le
    dsimp[z] at *
    convert ht using 1 <;>ring
  exact (mul_le_mul hexp hsum (norm_nonneg _) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
lemma phaseFamilyModel_centered_outer_bound (S:ℂ→ℂ)(H:ℕ→ℂ→ℂ)
    (h x ρ B D δ:ℝ)(J k:ℕ)(hh:0<h)(hx:0<x)(hxρ:x≤ρ)(hB:0<B)(hD:0≤D)
    (hbudget:2*B*((J:ℝ)+1)^2≤h)(hδ:0<δ)(hδπ:δ≤Real.pi)
    (hH:∀s z,‖z‖≤ρ→‖H s z‖≤D*B^s*(s.factorial:ℝ)^2)
    (hphase:∀θ:ℝ,(S ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))-S (x:ℂ)).re≤-(x/2)*(1-Real.cos θ)):
    ∀θ:ℝ,δ≤|θ|→|θ|≤Real.pi→
      ‖Complex.exp (-(k:ℂ)*(θ:ℂ)*Complex.I)*Complex.exp (-((h:ℂ)*S (x:ℂ)))*
        phaseFamilyModel S H h J ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖≤
        2*D*Real.exp (-(x*δ^2/Real.pi^2)*h):=by
  intro θ hθδ hθπ
  rw[mul_assoc,norm_mul]
  have hunit:‖Complex.exp (-(k:ℂ)*(θ:ℂ)*Complex.I)‖=1:=by rw[Complex.norm_exp];simp
  rw[hunit,one_mul]
  apply (phaseFamilyModel_centered_circle_bound S H h x ρ B D J hh hx hxρ hB hD hbudget hH hphase θ).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity:0≤2*D)
  apply Real.exp_le_exp.mpr
  have hcos:2/Real.pi^2*θ^2≤1-Real.cos θ:=by linarith[Real.cos_le_one_sub_mul_cos_sq hθπ]
  have hsq:δ^2≤θ^2:=by nlinarith[sq_abs θ]
  have h1:=mul_le_mul_of_nonneg_left hcos (by positivity:0≤h*x/2)
  have h2:=mul_le_mul_of_nonneg_left hsq (by positivity:0≤h*x/Real.pi^2)
  have he:h*x/2*(2/Real.pi^2*θ^2)=h*x/Real.pi^2*θ^2:=by ring
  rw[he] at h1
  convert neg_le_neg (h2.trans h1) using 1 <;>ring
end WP.Analysis
