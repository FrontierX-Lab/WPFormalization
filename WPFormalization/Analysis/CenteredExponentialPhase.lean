import WPFormalization.Analysis.EulerExponentialJets
/-! Exact centered exponential phases: joint analyticity, vanishing first jets and normalized quadratic jet. Every formula uses the actual complex Euler operator. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
def centeredExponentialSlice (S:ℂ → ℂ) (z c u:ℂ):ℂ:=
  S (z*Complex.exp (c*u))-S z-c*u*complexEuler S z
lemma centeredExponentialSlice_taylor (S:ℂ → ℂ) (z c:ℂ) (hS:AnalyticAt ℂ S z) :
    taylor (centeredExponentialSlice S z c)=
      taylor (fun u:ℂ=>S (z*Complex.exp (c*u)))-PowerSeries.C (S z)-
        PowerSeries.C (c*complexEuler S z)*PowerSeries.X := by
  have ht:AnalyticAt ℂ (fun u:ℂ=>z*Complex.exp (c*u)) 0 := by fun_prop
  have hp:(z*Complex.exp (c*(0:ℂ)))=z := by simp
  have ha:AnalyticAt ℂ (fun u:ℂ=>S (z*Complex.exp (c*u))) 0 := hS.comp_of_eq ht hp
  have he:centeredExponentialSlice S z c=
      (fun u:ℂ=>(S (z*Complex.exp (c*u))-S z)-(c*complexEuler S z)*u) := by
    funext u
    dsimp only [centeredExponentialSlice]
    ring
  rw [he,taylor_sub (f:=fun u:ℂ=>S (z*Complex.exp (c*u))-S z)
    (g:=fun u:ℂ=>(c*complexEuler S z)*u) (ha.sub analyticAt_const) (by fun_prop),
    taylor_sub ha analyticAt_const,taylor_const,taylor_const_mul,taylor_id]
lemma centeredExponentialSlice_jets (S:ℂ → ℂ) (z c:ℂ) (hS:AnalyticAt ℂ S z) :
    centeredExponentialSlice S z c 0=0 ∧ deriv (centeredExponentialSlice S z c) 0=0 ∧
      iteratedDeriv 2 (centeredExponentialSlice S z c) 0=c^2*((complexEuler^[2]) S) z := by
  have ht:=centeredExponentialSlice_taylor S z c hS
  have h1:=congrArg (PowerSeries.coeff 1) ht
  have h2:=congrArg (PowerSeries.coeff 2) ht
  have hc1:=coeff_exponential_tilt S z c hS 1
  have hc2:=coeff_exponential_tilt S z c hS 2
  simp only [Function.iterate_one,pow_one,Nat.factorial_one,Nat.cast_one,div_one] at hc1
  simp only [map_sub,taylor_coeff,PowerSeries.coeff_C,PowerSeries.coeff_C_mul,PowerSeries.coeff_X] at h1 h2
  norm_num only [ite_true,ite_false,mul_one,mul_zero,sub_zero,zero_sub] at h1 h2
  rw [hc1] at h1
  rw [hc2] at h2
  refine ⟨by simp [centeredExponentialSlice],?_,?_⟩
  · simpa [WP.coeff] using h1
  · dsimp only [WP.coeff] at h2
    norm_num only [Nat.factorial_two,Nat.cast_ofNat] at h2
    linear_combination 2*h2

def centeredExponentialPhase (S L:ℂ → ℂ) (p:ℂ × ℂ):ℂ:=
  centeredExponentialSlice S p.1 (Complex.I*L p.1) p.2
lemma centeredExponentialPhase_analyticAt (S L:ℂ → ℂ) (z:ℂ)
    (hS:AnalyticAt ℂ S z) (hL:AnalyticAt ℂ L z):
    AnalyticAt ℂ (centeredExponentialPhase S L) (z,0) := by
  have hL:AnalyticAt ℂ (fun p:ℂ × ℂ=>L p.1) (z,0) := hL.comp analyticAt_fst
  have hν:AnalyticAt ℂ (fun p:ℂ × ℂ=>complexEuler S p.1) (z,0) :=
    (complexEuler_analyticAt S z hS).comp (f:=fun p:ℂ × ℂ=>p.1) (x:=(z,0)) analyticAt_fst
  have harg:AnalyticAt ℂ (fun p:ℂ × ℂ=>p.1*Complex.exp ((Complex.I*L p.1)*p.2)) (z,0) :=
    analyticAt_fst.mul (((analyticAt_const.mul hL).mul analyticAt_snd).cexp)
  have harg0:((z,0):ℂ × ℂ).1*Complex.exp ((Complex.I*L ((z,0):ℂ × ℂ).1)*((z,0):ℂ × ℂ).2)=z := by simp
  exact ((hS.comp_of_eq harg harg0).sub (hS.comp analyticAt_fst)).sub
    (((analyticAt_const.mul hL).mul analyticAt_snd).mul hν)
lemma centeredExponentialPhase_second (S L:ℂ → ℂ) (z:ℂ) (hS:AnalyticAt ℂ S z)
    (hnorm:(L z)^2*((complexEuler^[2]) S) z=1):
    iteratedDeriv 2 (fun u:ℂ=>centeredExponentialPhase S L (z,u)) 0=-1 := by
  have he:=(centeredExponentialSlice_jets S z (Complex.I*L z) hS).2.2
  change iteratedDeriv 2 (centeredExponentialSlice S z (Complex.I*L z)) 0=-1
  rw [he,mul_pow,Complex.I_sq]
  linear_combination -hnorm
end WP.Analysis
