import WPFormalization.HigherOrder.FirstExtractedScaledEuler
import WPFormalization.Volumes.CriticalInversePsi
import WPFormalization.HigherOrder.FirstExtractedLogB
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma critical_iteratedEuler_analyticAt (f:ℝ→ℝ)(x:ℝ)(hf:AnalyticAt ℝ f x)(n:ℕ):
    AnalyticAt ℝ ((WP.euler^[n]) f) x:=by
  induction n with
  | zero=>exact hf
  | succ n ih=>
    rw[Function.iterate_succ_apply']
    exact analyticAt_id.mul ih.deriv

def CriticalKernelUnits.secondPsiUnit (k : CriticalKernelUnits) : ℂ→ℂ :=
  k.scaledEulerUnit 4 k.varianceUnit

def CriticalKernelUnits.thirdPsiUnit (k : CriticalKernelUnits) : ℂ→ℂ :=
  k.scaledEulerUnit 6 k.secondPsiUnit
lemma CriticalKernelUnits.secondPsiUnit_analytic (k : CriticalKernelUnits) :
    AnalyticAt ℂ k.secondPsiUnit 0 := k.scaledEulerUnit_analytic 4 _ k.varianceUnit_analytic
lemma CriticalKernelUnits.thirdPsiUnit_analytic (k : CriticalKernelUnits) :
    AnalyticAt ℂ k.thirdPsiUnit 0 := k.scaledEulerUnit_analytic 6 _ k.secondPsiUnit_analytic
lemma CriticalKernelUnits.secondPsiUnit_zero (k : CriticalKernelUnits) :
    k.secondPsiUnit 0 = ((20*y₀^3:ℝ):ℂ) := by
  rw [secondPsiUnit,k.scaledEulerUnit_zero,k.varianceUnit_zero]
  push_cast
  ring
lemma CriticalKernelUnits.thirdPsiUnit_zero (k : CriticalKernelUnits) :
    k.thirdPsiUnit 0 = ((120*y₀^4:ℝ):ℂ) := by
  rw [thirdPsiUnit,k.scaledEulerUnit_zero,k.secondPsiUnit_zero]
  push_cast
  ring
lemma CriticalKernelUnits.secondPsiUnit_physical (k : CriticalKernelUnits) :
    ∀ᶠδ:ℝ in 𝓝 0,0<δ→k.secondPsiUnit (δ:ℂ)=
      (((euler^[2]) Psi (XR (y₀-δ))*δ^6:ℝ):ℂ) := by
  simpa only [secondPsiUnit,Function.iterate_succ_apply',Function.iterate_one,Function.iterate_zero,id_eq,Nat.reduceAdd] using
    k.scaledEulerUnit_physical (euler Psi) k.varianceUnit 4 (by norm_num)
      k.varianceUnit_analytic
      (fun x hx=>(critical_iteratedEuler_analyticAt Psi x
        (Psi_analyticAt_interior x ⟨hx.1.le,hx.2⟩) 1).differentiableAt)
      k.varianceUnit_physical
lemma CriticalKernelUnits.thirdPsiUnit_physical (k : CriticalKernelUnits) :
    ∀ᶠδ:ℝ in 𝓝 0,0<δ→k.thirdPsiUnit (δ:ℂ)=
      (((euler^[3]) Psi (XR (y₀-δ))*δ^8:ℝ):ℂ) := by
  simpa only [thirdPsiUnit,Function.iterate_succ_apply'] using
    k.scaledEulerUnit_physical ((euler^[2]) Psi) k.secondPsiUnit 6 (by norm_num)
      k.secondPsiUnit_analytic
      (fun x hx=>(critical_iteratedEuler_analyticAt Psi x
        (Psi_analyticAt_interior x ⟨hx.1.le,hx.2⟩) 2).differentiableAt)
      k.secondPsiUnit_physical

def CriticalKernelUnits.firstGaussianUnit (k : CriticalKernelUnits)
    (B1 B2 : ℂ→ℂ) (δ:ℂ) : ℂ :=
  -(B2 δ+(B1 δ)^2)/(2*k.varianceUnit δ) +
    B1 δ*k.secondPsiUnit δ/(2*(k.varianceUnit δ)^2) +
    k.thirdPsiUnit δ/(8*(k.varianceUnit δ)^2) -
    5*(k.secondPsiUnit δ)^2/(24*(k.varianceUnit δ)^3) + k.inversePsiUnit δ/12

lemma CriticalKernelUnits.firstGaussianUnit_analytic (k : CriticalKernelUnits)
    (B1 B2 : ℂ→ℂ) (hB1:AnalyticAt ℂ B1 0) (hB2:AnalyticAt ℂ B2 0) :
    AnalyticAt ℂ (k.firstGaussianUnit B1 B2) 0 := by
  have hv : k.varianceUnit 0 ≠ 0 := by
    rw [k.varianceUnit_zero]
    exact_mod_cast (mul_pos (by norm_num : (0:ℝ)<5) (sq_pos_of_pos y₀_pos)).ne'
  apply AnalyticAt.add
  · apply AnalyticAt.sub
    · apply AnalyticAt.add
      · apply AnalyticAt.add
        · exact (hB2.add (hB1.pow 2)).neg.div (analyticAt_const.mul k.varianceUnit_analytic) (mul_ne_zero (by norm_num) hv)
        · exact (hB1.mul k.secondPsiUnit_analytic).div
            (analyticAt_const.mul (k.varianceUnit_analytic.pow 2)) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hv))
      · exact k.thirdPsiUnit_analytic.div (analyticAt_const.mul (k.varianceUnit_analytic.pow 2))
          (mul_ne_zero (by norm_num) (pow_ne_zero 2 hv))
    · exact (analyticAt_const.mul (k.secondPsiUnit_analytic.pow 2)).div
        (analyticAt_const.mul (k.varianceUnit_analytic.pow 3)) (mul_ne_zero (by norm_num) (pow_ne_zero 3 hv))
  · exact k.inversePsiUnit_analytic.div_const

lemma CriticalKernelUnits.firstGaussianUnit_zero (k : CriticalKernelUnits)
    (p : ℕ) (B1 B2 : ℂ→ℂ)
    (hB1:B1 0=(-(p:ℝ)*y₀/2:ℝ)) (hB2:B2 0=(-(p:ℝ)*y₀^2:ℝ)) :
    k.firstGaussianUnit B1 B2 0 = ((-((p:ℝ)^2+4*p)/40-1/15:ℝ):ℂ) := by
  rw [CriticalKernelUnits.firstGaussianUnit,hB1,hB2,k.secondPsiUnit_zero,k.thirdPsiUnit_zero,
    k.varianceUnit_zero,k.inversePsiUnit_zero]
  push_cast
  have hy : (y₀:ℂ) ≠ 0 := by exact_mod_cast y₀_pos.ne'
  field_simp
  <;> ring

def CriticalKernelUnits.secondLogBUnit (k : CriticalKernelUnits) (Q:ℂ→ℂ) (p:ℕ) : ℂ→ℂ :=
  k.scaledEulerUnit 2 (k.scaledLogBUnit Q p)
lemma CriticalKernelUnits.secondLogBUnit_analytic (k : CriticalKernelUnits)
    (Q:ℂ→ℂ) (hQ:AnalyticAt ℂ Q 0) (hQ0:Q 0=1) (p:ℕ) :
    AnalyticAt ℂ (k.secondLogBUnit Q p) 0 :=
  k.scaledEulerUnit_analytic 2 _ (k.scaledLogBUnit_analytic Q hQ hQ0 p)
lemma CriticalKernelUnits.secondLogBUnit_zero (k : CriticalKernelUnits) (Q:ℂ→ℂ) (p:ℕ) :
    k.secondLogBUnit Q p 0 = ((-(p:ℝ)*y₀^2:ℝ):ℂ) := by
  rw [secondLogBUnit,k.scaledEulerUnit_zero,k.scaledLogBUnit_zero]
  push_cast
  ring

lemma CriticalKernelUnits.secondLogBUnit_physical (k : CriticalKernelUnits)
    (Q:ℂ→ℂ) (hQ:AnalyticAt ℂ Q 0) (hQ0:Q 0=1)
    (hQphys:∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(Theta (y₀-δ):ℂ)) (p:ℕ)
    (hb:∀x∈Ioo (0:ℝ) xCritical,AnalyticAt ℝ (fun t=>Real.log (extractionB p t)) x) :
    ∀ᶠδ:ℝ in 𝓝 0,0<δ→k.secondLogBUnit Q p (δ:ℂ)=
      (((euler^[2]) (fun t=>Real.log (extractionB p t)) (XR (y₀-δ))*δ^4:ℝ):ℂ) := by
  simpa only [secondLogBUnit,Function.iterate_succ_apply',Function.iterate_one,
    Function.iterate_zero,id_eq,Nat.reduceAdd] using
    k.scaledEulerUnit_physical (euler (fun t=>Real.log (extractionB p t)))
      (k.scaledLogBUnit Q p) 2 (by norm_num)
      (k.scaledLogBUnit_analytic Q hQ hQ0 p)
      (fun x hx=>(analyticAt_id.mul (hb x hx).deriv).differentiableAt)
      (k.scaledLogBUnit_physical Q hQ hQ0 hQphys p (fun x hx=>(hb x hx).differentiableAt))


lemma CriticalKernelUnits.firstGaussianUnit_physical (k : CriticalKernelUnits)
    (Q:ℂ→ℂ) (hQ:AnalyticAt ℂ Q 0) (hQ0:Q 0=1)
    (hQphys:∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(Theta (y₀-δ):ℂ)) (p:ℕ)
    (hb:∀x∈Ioo (0:ℝ) xCritical,AnalyticAt ℝ (fun t=>Real.log (extractionB p t)) x) :
    ∀ᶠδ:ℝ in 𝓝 0,0<δ→
      k.firstGaussianUnit (k.scaledLogBUnit Q p) (k.secondLogBUnit Q p) (δ:ℂ)=
        ((-(((euler^[2]) (fun t => Real.log (extractionB p t))) (XR (y₀-δ)) +
          ((euler (fun t => Real.log (extractionB p t))) (XR (y₀-δ)))^2) /
            (2 * euler Psi (XR (y₀-δ))) +
          (euler (fun t => Real.log (extractionB p t))) (XR (y₀-δ)) * ((euler^[2]) Psi) (XR (y₀-δ)) /
            (2 * (euler Psi (XR (y₀-δ)))^2) +
          ((euler^[3]) Psi) (XR (y₀-δ)) / (8 * (euler Psi (XR (y₀-δ)))^2) -
          5 * (((euler^[2]) Psi) (XR (y₀-δ)))^2 / (24 * (euler Psi (XR (y₀-δ)))^3) +
          1/(12*Psi (XR (y₀-δ))):ℝ):ℂ) := by
  filter_upwards [k.varianceUnit_physical,k.secondPsiUnit_physical,k.thirdPsiUnit_physical,
    k.inversePsiUnit_physical,
    k.scaledLogBUnit_physical Q hQ hQ0 hQphys p (fun x hx=>(hb x hx).differentiableAt),
    k.secondLogBUnit_physical Q hQ hQ0 hQphys p hb] with δ hv h2 h3 hi hb1 hb2 hδ
  rw [CriticalKernelUnits.firstGaussianUnit,hv hδ,h2 hδ,h3 hδ,hi hδ,hb1 hδ,hb2 hδ]
  push_cast
  have hn : (δ:ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  field_simp [hn]
  <;> ring

end WP.Analysis
