import WPFormalization.HigherOrder.PoissonFamilyFiniteAlgebra
import WPFormalization.Analysis.PoissonPhaseCoefficient
noncomputable section
namespace WP.HigherOrder
def phaseFamilyModel (S:ℂ→ℂ) (H:ℕ→ℂ→ℂ) (h:ℝ) (J:ℕ) (z:ℂ):ℂ:=
  Complex.exp ((h:ℂ)*S z)*(∑s∈Finset.range (J+1),(h:ℂ)⁻¹^s*H s z)
lemma phaseAmplitude_weighted_sum (Z:ℂ × ℂ → ℂ) (H:ℕ→ℂ→ℂ) (a:ℂ) (J:ℕ) (v:ℂ × ℂ):
    phaseAmplitude Z (fun z=>∑s∈Finset.range (J+1),a^s*H s z) v=
      ∑s∈Finset.range (J+1),a^s*phaseAmplitude Z (H s) v:=by
  simp only[phaseAmplitude,Finset.sum_mul,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s hs
  ring
lemma phaseFamilyModel_coefficient (S x Q:ℂ→ℂ) (Z q:ℂ × ℂ → ℂ)
    (R:ℝ) (hR:0<R) (hS:AnalyticAt ℂ S 0)
    (hq:AnalyticOnNhd ℂ q (Metric.ball 0 R ×ˢ Metric.ball 0 R))
    (hdata:∀u ν:ℂ,‖u‖<R→‖ν‖<R→phaseQuotient Z u ν=q (u,ν)∧q (u,ν)≠0∧
      Z (u,ν)=u*q (u,ν)∧S (Z (u,ν))-u-ν*Complex.log (q (u,ν))=
        S (x ν)-ν+ν*Complex.log (Q ν))
    (H:ℕ→ℂ→ℂ) (hH:∀s,AnalyticAt ℂ (H s) 0)
    (h:ℝ) (hh:0<h) (k J:ℕ) (hν:‖(k:ℂ)/(h:ℂ)‖<R):
    let ν:ℂ:=(k:ℂ)/(h:ℂ)
    WP.coeff (phaseFamilyModel S H h J) k=
      Complex.exp ((h:ℂ)*(S (x ν)-ν+ν*Complex.log (Q ν)))*(h:ℂ)^k/(k.factorial:ℂ)*
        poissonFamilyOperator (fun s=>phaseAmplitude Z (H s)) J h k:=by
  let a:ℂ:=(h:ℂ)⁻¹
  let Hsum:ℂ→ℂ:=fun z=>∑s∈Finset.range (J+1),a^s*H s z
  have hHsum:AnalyticAt ℂ Hsum 0:=Finset.analyticAt_fun_sum _ (fun s hs=>analyticAt_const.mul (hH s))
  have hh0:(h:ℂ)≠0:=by exact_mod_cast hh.ne'
  have hk0:(k.factorial:ℂ)≠0:=by exact_mod_cast k.factorial_ne_zero
  let ν:ℂ:=(k:ℂ)/(h:ℂ)
  have hνeq:ν=(((k:ℝ)/h:ℝ):ℂ):=by simp only[ν,Complex.ofReal_div,Complex.ofReal_natCast]
  have he:=Analysis.poisson_phase_coefficient_identity S x Q Z q R hR hS hq hdata Hsum hHsum (h:ℂ) k hh0 hν
  change WP.coeff (fun z=>Complex.exp ((h:ℂ)*S z)*Hsum z) k=_
  rw[he]
  have ho:poissonFamilyOperator (fun s=>phaseAmplitude Z (H s)) J h k=
      (k.factorial:ℂ)/(h:ℂ)^k*
        WP.coeff (fun u=>Complex.exp ((h:ℂ)*u)*phaseAmplitude Z Hsum (u,ν)) k:=by
    unfold poissonFamilyOperator poissonCoefficientOperator
    congr 1
    apply congrArg (fun f:ℂ→ℂ=>WP.coeff f k)
    funext u
    simp only[hνeq]
    change Complex.exp ((h:ℂ)*u)*(∑s∈Finset.range (J+1),a^s*phaseAmplitude Z (H s) (u,(((k:ℝ)/h:ℝ):ℂ)))=
      Complex.exp ((h:ℂ)*u)*phaseAmplitude Z Hsum (u,(((k:ℝ)/h:ℝ):ℂ))
    rw[←phaseAmplitude_weighted_sum]
  rw[ho]
  field_simp <;> rfl
end WP.HigherOrder
namespace WP.HigherOrder
lemma phaseFamilyModel_coefficient_of_terms (S:ℂ→ℂ) (H:ℕ→ℂ→ℂ)
    (f:ℕ→ℂ × ℂ → ℂ) (h:ℝ) (hh:0<h) (k J:ℕ) (T:ℂ)
    (hS:AnalyticAt ℂ S 0) (hH:∀s,AnalyticAt ℂ (H s) 0)
    (hf:∀s,AnalyticAt ℂ (fun u=>f s (u,(((k:ℝ)/h:ℝ):ℂ))) 0)
    (ht:∀s,WP.coeff (fun z=>Complex.exp ((h:ℂ)*S z)*H s z) k=
      T*WP.coeff (fun u=>Complex.exp ((h:ℂ)*u)*f s (u,(((k:ℝ)/h:ℝ):ℂ))) k):
    WP.coeff (phaseFamilyModel S H h J) k=
      T*(h:ℂ)^k/(k.factorial:ℂ)*poissonFamilyOperator f J h k:=by
  let a:ℂ:=(h:ℂ)⁻¹
  have hsrc:phaseFamilyModel S H h J=(fun z=>∑s∈Finset.range (J+1),a^s*(Complex.exp ((h:ℂ)*S z)*H s z)):=by
    funext z
    rw[phaseFamilyModel,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  have hexp:AnalyticAt ℂ (fun z=>Complex.exp ((h:ℂ)*S z)) 0:=(analyticAt_const.mul hS).cexp
  have hleft:WP.coeff (phaseFamilyModel S H h J) k=
      ∑s∈Finset.range (J+1),a^s*WP.coeff (fun z=>Complex.exp ((h:ℂ)*S z)*H s z) k:=by
    rw[hsrc]
    rw[Analysis.coeff_finite_sum (Finset.range (J+1))
      (fun s z=>a^s*(Complex.exp ((h:ℂ)*S z)*H s z)) (by
        intro s hs
        simpa only[Pi.mul_def] using (analyticAt_const (v:=a^s)).mul (hexp.mul (hH s))) k]
    simp only[Analysis.coeff_const_mul]
  have htrg:(fun u=>Complex.exp ((h:ℂ)*u)*(∑s∈Finset.range (J+1),a^s*f s (u,(((k:ℝ)/h:ℝ):ℂ))))=
      (fun u=>∑s∈Finset.range (J+1),a^s*(Complex.exp ((h:ℂ)*u)*f s (u,(((k:ℝ)/h:ℝ):ℂ)))):=by
    funext u
    rw[Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  have hr:poissonFamilyOperator f J h k=(k.factorial:ℂ)/(h:ℂ)^k*
      (∑s∈Finset.range (J+1),a^s*WP.coeff (fun u=>Complex.exp ((h:ℂ)*u)*f s (u,(((k:ℝ)/h:ℝ):ℂ))) k):=by
    unfold poissonFamilyOperator poissonCoefficientOperator
    rw[htrg]
    have hexpu:AnalyticAt ℂ (fun u:ℂ=>Complex.exp ((h:ℂ)*u)) 0:=by fun_prop
    rw[Analysis.coeff_finite_sum (Finset.range (J+1))
      (fun s u=>a^s*(Complex.exp ((h:ℂ)*u)*f s (u,(((k:ℝ)/h:ℝ):ℂ)))) (by
        intro s hs
        simpa only[Pi.mul_def] using (analyticAt_const (v:=a^s)).mul (hexpu.mul (hf s))) k]
    simp only[Analysis.coeff_const_mul]
  rw[hleft,hr]
  simp_rw[ht]
  have he:(∑s∈Finset.range (J+1),a^s*(T*WP.coeff (fun u=>Complex.exp ((h:ℂ)*u)*f s (u,(((k:ℝ)/h:ℝ):ℂ))) k))=
      T*(∑s∈Finset.range (J+1),a^s*WP.coeff (fun u=>Complex.exp ((h:ℂ)*u)*f s (u,(((k:ℝ)/h:ℝ):ℂ))) k):=by
    rw[Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  rw[he]
  have hh0:(h:ℂ)≠0:=by exact_mod_cast hh.ne'
  have hk0:(k.factorial:ℂ)≠0:=by exact_mod_cast k.factorial_ne_zero
  field_simp
end WP.HigherOrder
