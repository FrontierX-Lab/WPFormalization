import WPFormalization.HigherOrder.ComplexCanonicalInputs
import WPFormalization.HigherOrder.ComplexShiftBounds
import WPFormalization.Analysis.FactorialKernelMoments
import Mathlib.Analysis.Complex.LocallyUniformLimit
/-! Analyticity of genuine finite formal operations and coefficientwise sums.
The sum theorem requires a genuine uniform summable bound, so pointwise
convergence is never substituted for a holomorphic normal-convergence proof. -/
set_option maxHeartbeats 800000
noncomputable section
open Set PowerSeries
namespace WP.HigherOrder.ComplexCanonical

/-- Analyticity of the actual coefficients through the displayed order. -/
def AnalyticCoefficients (Ω : Set ℂ) (N : ℕ) (F : ℂ → Series) : Prop :=
  ∀ n≤N,AnalyticOnNhd ℂ (fun z=>PowerSeries.coeff n (F z)) Ω

namespace AnalyticCoefficients
variable {Ω : Set ℂ} {N : ℕ} {F G : ℂ → Series}

lemma mono (hF : AnalyticCoefficients Ω N F) {M : ℕ} (hMN : M≤N) :
    AnalyticCoefficients Ω M F := fun n hn=>hF n (hn.trans hMN)

lemma const (f : Series) : AnalyticCoefficients Ω N (fun _=>f) :=
  fun _ _=>analyticOnNhd_const

lemma C {a : ℂ → ℂ} (ha : AnalyticOnNhd ℂ a Ω) :
    AnalyticCoefficients Ω N (fun z=>PowerSeries.C (a z)) := by
  intro n hn
  by_cases h : n=0
  · subst n
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.constantCoeff_C] using ha
  · have he : (fun z=>PowerSeries.coeff n (PowerSeries.C (a z)))=(fun _ : ℂ=>0) := by
      funext z
      simp only [PowerSeries.coeff_C,ite_eq_right h]
    rw [he]
    exact analyticOnNhd_const

lemma add (hF : AnalyticCoefficients Ω N F) (hG : AnalyticCoefficients Ω N G) :
    AnalyticCoefficients Ω N (fun z=>F z+G z) := by
  intro n hn z hz
  have he : (fun w=>PowerSeries.coeff n (F w+G w))=
      ((fun w=>PowerSeries.coeff n (F w))+(fun w=>PowerSeries.coeff n (G w))) := by
    funext w
    exact map_add _ _ _
  rw [he]
  exact (hF n hn z hz).add (hG n hn z hz)

lemma neg (hF : AnalyticCoefficients Ω N F) :
    AnalyticCoefficients Ω N (fun z=>-F z) := by
  intro n hn z hz
  have he : (fun w=>PowerSeries.coeff n (-F w))=-(fun w=>PowerSeries.coeff n (F w)) := by
    funext w
    exact map_neg _ _
  rw [he]
  exact (hF n hn z hz).neg

lemma sub (hF : AnalyticCoefficients Ω N F) (hG : AnalyticCoefficients Ω N G) :
    AnalyticCoefficients Ω N (fun z=>F z-G z) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

lemma mul (hF : AnalyticCoefficients Ω N F) (hG : AnalyticCoefficients Ω N G) :
    AnalyticCoefficients Ω N (fun z=>F z*G z) := by
  intro n hn z hz
  simp_rw [PowerSeries.coeff_mul]
  apply Finset.analyticAt_fun_sum
  intro i hi
  have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hi
  exact (hF i.1 (by omega) z hz).mul (hG i.2 (by omega) z hz)

lemma pow (hF : AnalyticCoefficients Ω N F) (k : ℕ) :
    AnalyticCoefficients Ω N (fun z=>F z^k) := by
  induction k with
  | zero => simpa only [pow_zero] using const (Ω:=Ω) (N:=N) 1
  | succ k ih => simpa only [pow_succ] using ih.mul hF

lemma sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → Series)
    (hf : ∀ i∈s,AnalyticCoefficients Ω N (f i)) :
    AnalyticCoefficients Ω N (fun z=>∑ i∈s,f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using const (Ω:=Ω) (N:=N) 0
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (by simp)).add
      (ih (fun j hj=>hf j (by simp [hj])))

lemma prod {ι : Type*} (s : Finset ι) (f : ι → ℂ → Series)
    (hf : ∀ i∈s,AnalyticCoefficients Ω N (f i)) :
    AnalyticCoefficients Ω N (fun z=>∏ i∈s,f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using const (Ω:=Ω) (N:=N) 1
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using (hf i (by simp)).mul
      (ih (fun j hj=>hf j (by simp [hj])))

lemma setCoeff (hF : AnalyticCoefficients Ω N F) (k : ℕ) {a : ℂ → ℂ}
    (ha : AnalyticOnNhd ℂ a Ω) :
    AnalyticCoefficients Ω N (fun z=>ComplexCanonical.setCoeff (F z) k (a z)) := by
  intro n hn
  by_cases h : n=k
  · subst n
    simpa only [ComplexCanonical.setCoeff,PowerSeries.coeff_mk,ite_true] using ha
  · simpa only [ComplexCanonical.setCoeff,PowerSeries.coeff_mk,ite_eq_right h] using hF n hn

lemma shift (hF : AnalyticCoefficients Ω N F) (c : ℂ) :
    AnalyticCoefficients Ω N (fun z=>complexityShift c (F z)) := by
  intro n hn z hz
  simp_rw [complexityShift,shiftVariable,WP.HigherOrder.complex_shift_coeff_sum]
  apply Finset.analyticAt_fun_sum
  intro i hi
  exact (hF i (by have h:=Finset.mem_range.mp hi;omega) z hz).mul analyticAt_const

lemma inv (hF : AnalyticCoefficients Ω N F)
    (h0 : ∀ z∈Ω,PowerSeries.constantCoeff (F z)≠0) :
    AnalyticCoefficients Ω N (fun z=>(F z)⁻¹) := by
  have hc : AnalyticOnNhd ℂ (fun z=>PowerSeries.constantCoeff (F z)) Ω := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hF 0 (Nat.zero_le N)
  have hci : AnalyticOnNhd ℂ (fun z=>(PowerSeries.constantCoeff (F z))⁻¹) Ω :=
    fun z hz=>(hc z hz).inv (h0 z hz)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hn0 : n=0
    · subst n
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.constantCoeff_inv] using hci
    · have he : (fun z=>PowerSeries.coeff n ((F z)⁻¹))=(fun z=>
          -(PowerSeries.constantCoeff (F z))⁻¹ *
            ∑ i∈Finset.HasAntidiagonal.antidiagonal n,if i.2<n then
              PowerSeries.coeff i.1 (F z)*PowerSeries.coeff i.2 ((F z)⁻¹) else 0) := by
        funext z
        rw [PowerSeries.coeff_inv,ite_eq_right hn0]
      rw [he]
      intro z hz
      apply (hci z hz).neg.mul
      apply Finset.analyticAt_fun_sum
      intro i hi
      by_cases hlt : i.2<n
      · simp only [ite_eq_left hlt]
        have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hi
        exact (hF i.1 (by omega) z hz).mul (ih i.2 hlt (by omega) z hz)
      · simp only [ite_eq_right hlt]
        exact analyticAt_const

/-- The genuine coefficient sums converge, and their coefficients are holomorphic,
from one summable majorant for each retained order, uniform on the open domain. -/
lemma coefficientSum (hΩ : IsOpen Ω) (f : ℕ → ℂ → Series)
    (hf : ∀ l,AnalyticCoefficients Ω N (f l))
    (hb : ∀ n≤N,∃ u : ℕ → ℝ,Summable u ∧
      ∀ l z,z∈Ω → ‖PowerSeries.coeff n (f l z)‖≤u l) :
    (∀ n≤N,∀ z∈Ω,Summable (fun l=>PowerSeries.coeff n (f l z))) ∧
      AnalyticCoefficients Ω N (fun z=>ComplexCanonical.coefficientSum (fun l=>f l z)) := by
  constructor
  · intro n hn z hz
    obtain ⟨u,hu,hbu⟩ := hb n hn
    exact Summable.of_norm_bounded hu (fun l=>hbu l z hz)
  · intro n hn
    obtain ⟨u,hu,hbu⟩ := hb n hn
    have hd := Complex.differentiableOn_tsum_of_summable_norm hu
      (fun l=>(hf l n hn).differentiableOn) hΩ (fun l z hz=>hbu l z hz)
    simpa only [ComplexCanonical.coefficientSum,PowerSeries.coeff_mk] using hd.analyticOnNhd hΩ

lemma geometric_polynomial_summable (ρ : ℝ) (hρ : 1<ρ) (k : ℕ) :
    Summable (fun l : ℕ=>((l:ℝ)+1)^k/ρ^l) := by
  obtain ⟨C,B,hC,hB,hf⟩ := WP.Analysis.geometric_factorial_moment_bound ρ 1 hρ zero_lt_one
  have hs := (hf (fun l : ℕ=>1/ρ^l) (by
    intro l
    rw [abs_of_nonneg (by positivity : (0:ℝ)≤1/ρ^l)]) k).1
  have he : (fun n : ℕ=>((n:ℝ)+1)^k*|1/ρ^n|)=(fun n : ℕ=>((n:ℝ)+1)^k/ρ^n) := by
    funext n
    rw [abs_of_nonneg (by positivity : (0:ℝ)≤1/ρ^n)]
    ring
  rw [he] at hs
  exact hs

lemma polynomial_shift_bound (S : ℝ) (hS : 0≤S) (l k : ℕ) :
    (S+l+1)^k≤(S+1)^k*((l:ℝ)+1)^k := by
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [mul_nonneg hS (show (0:ℝ)≤l from Nat.cast_nonneg l)]

/-- Polynomially growing actual coefficient families can be summed with any
geometrically controlled analytic weight, with normal convergence on Ω. -/
lemma geometric_weighted_coefficientSum (hΩ : IsOpen Ω) (ρ C : ℝ) (hρ : 1<ρ) (hC : 0≤C)
    (a : ℕ → ℂ → ℂ) (ha : ∀ l,AnalyticOnNhd ℂ (a l) Ω)
    (hageom : ∀ l z,z∈Ω → ‖a l z‖≤C/ρ^l)
    (f : ℕ → ℂ → Series) (hf : ∀ l,AnalyticCoefficients Ω N (f l))
    (hb : ∀ n≤N,∃ (B S : ℝ) (k : ℕ),0≤B ∧ 0≤S ∧
      ∀ l z,z∈Ω → ‖PowerSeries.coeff n (f l z)‖≤B*(S+l+1)^k) :
    (∀ n≤N,∀ z∈Ω,Summable (fun l=>a l z*PowerSeries.coeff n (f l z))) ∧
      AnalyticCoefficients Ω N (fun z=>ComplexCanonical.coefficientSum
        (fun l=>PowerSeries.C (a l z)*f l z)) := by
  have hg : ∀ l,AnalyticCoefficients Ω N (fun z=>PowerSeries.C (a l z)*f l z) :=
    fun l=>(AnalyticCoefficients.C (ha l)).mul (hf l)
  have hmajor : ∀ n≤N,∃ u : ℕ → ℝ,Summable u ∧
      ∀ l z,z∈Ω → ‖PowerSeries.coeff n (PowerSeries.C (a l z)*f l z)‖≤u l := by
    intro n hn
    obtain ⟨B,S,k,hB,hS,hbound⟩ := hb n hn
    let D : ℝ := C*B*(S+1)^k
    refine ⟨fun l=>D*(((l:ℝ)+1)^k/ρ^l),(geometric_polynomial_summable ρ hρ k).mul_left D,?_⟩
    intro l z hz
    rw [PowerSeries.coeff_C_mul,norm_mul]
    calc
      _ ≤ (C/ρ^l)*(B*(S+l+1)^k) :=
        mul_le_mul (hageom l z hz) (hbound l z hz) (norm_nonneg _) (by positivity)
      _ ≤ (C/ρ^l)*(B*((S+1)^k*((l:ℝ)+1)^k)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (polynomial_shift_bound S hS l k) hB) (by positivity)
      _ = D*(((l:ℝ)+1)^k/ρ^l) := by dsimp only [D];ring
  have hsum := coefficientSum hΩ _ hg hmajor
  constructor
  · intro n hn z hz
    simpa only [PowerSeries.coeff_C_mul] using hsum.1 n hn z hz
  · exact hsum.2

end AnalyticCoefficients
end WP.HigherOrder.ComplexCanonical
