import WPFormalization.Analysis.ExtractionPolynomialJets
import WPFormalization.Analysis.ExtractionRawLogJets
import WPFormalization.Analysis.RealAnalyticTrace
import WPFormalization.HigherOrder.MarkedExtensionProof
import WPFormalization.Volumes.PlanarInverse
/-! The original marked Taylor polynomials are the actual tilted jets of the canonical marked coefficient family. The physical germ family is constructed from the proved common complex extension and actual planar inverse. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
lemma markedTaylorPolynomial_eval_of_jets (P:PsiTheory) (p:ℕ) (x:ℝ) (w:ℂ)
    (A:ℕ→ℂ→ℂ) (hA:∀s,AnalyticAt ℂ (A s) 0)
    (hjets:∀s q:ℕ,WP.coeff (A s) q=
      (Complex.I*w/(Real.sqrt (WP.euler WP.Psi x):ℂ))^q*
        (((((WP.euler^[q]) (fun x:ℝ=>HigherOrder.markedCoefficient P p s (inverseY x))) x:ℝ):ℂ))/(q.factorial:ℂ))
    (n N:ℕ) (hN:n/2≤N) :
    WP.coeff (fun τ:ℂ=>∑s∈Finset.range (N+1),τ^(2*s)*A s τ) n=
      Polynomial.eval₂ Complex.ofRealHom (Complex.I*w) (HigherOrder.markedTaylorPolynomial P p x n) := by
  have hterm(s:ℕ):AnalyticAt ℂ (fun τ:ℂ=>τ^(2*s)*A s τ) 0:=(analyticAt_id.pow _).mul (hA s)
  have hsum:=coeff_finite_sum (Finset.range (N+1)) (fun (s:ℕ) (τ:ℂ)=>τ^(2*s)*A s τ) (fun s hs=>hterm s) n
  rw[hsum]
  have hc:∀s,WP.coeff (fun τ:ℂ=>τ^(2*s)*A s τ) n=
      if 2*s≤n then WP.coeff (A s) (n-2*s) else 0 := fun s=>coeff_id_pow_mul (A s) (hA s) _ _
  simp_rw[hc]
  have he:(∑s∈Finset.range (N+1),if 2*s≤n then WP.coeff (A s) (n-2*s) else 0)=
      ∑s∈Finset.range (n/2+1),WP.coeff (A s) (n-2*s) := by
    symm
    calc _ = ∑s∈Finset.range (n/2+1),if 2*s≤n then WP.coeff (A s) (n-2*s) else 0 := by
                apply Finset.sum_congr rfl
                intro s hs
                rw[if_pos (by have hh:=Finset.mem_range.mp hs;omega)]
         _ = _ := by
           apply Finset.sum_subset (Finset.range_mono (by omega))
           intro s hs hsn
           rw[if_neg (by simp only[Finset.mem_range] at hsn;omega)]
  rw[he]
  simp only[HigherOrder.markedTaylorPolynomial,Polynomial.eval₂_finsetSum,Polynomial.eval₂_monomial,
    Complex.ofRealHom_eq_coe]
  apply Finset.sum_congr rfl
  intro s hs
  rw[hjets]
  push_cast
  simp only[div_pow,mul_pow]
  ring

lemma canonical_marked_weight_germ_family (P:PsiTheory) (p:ℕ) (hp:1≤p)
    (x:ℝ) (hx:x∈Set.Ioo (0:ℝ) xCritical) :
    ∃Γ:ℕ→ℂ→ℂ,∀s,AnalyticAt ℂ (Γ s) (x:ℂ) ∧
      (fun t:ℝ=>Γ s (t:ℂ))=ᶠ[𝓝 x]
        (fun t:ℝ=>(HigherOrder.markedCoefficient P p s (inverseY t):ℂ)) := by
  obtain ⟨C,B,hC,hB,Ω,aC,f,hΩ,hcover,hf,hrest,hbound⟩:=
    HigherOrder.markedCoefficient_common_complex_gevrey_two P p hp
  let Γ:ℕ→ℂ→ℂ:=fun s z=>f s (PositiveConvolution.planarInverse P z)
  have hxI:x∈Set.Ico (0:ℝ) xCritical:=⟨hx.1.le,hx.2⟩
  have hxN:‖(x:ℂ)‖<xCritical:=by rw[Complex.norm_of_nonneg hx.1.le];exact hx.2
  have hy:inverseY x∈Set.Ico (0:ℝ) y₀:=(inverseY_branch x hxI).1
  have hyΩ:(inverseY x:ℂ)∈Ω:=hcover _ ⟨hy.1,hy.2.le⟩
  refine ⟨Γ,?_⟩
  intro s
  constructor
  · exact ((hf s).2 _ hyΩ).comp_of_eq (PositiveConvolution.planarInverse_analyticAt P (x:ℂ) hxN)
      (PositiveConvolution.planarInverse_ofReal P x hxI)
  · filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    dsimp only[Γ]
    rw [PositiveConvolution.planarInverse_ofReal P t ⟨ht.1.le,ht.2⟩]
    have hty:inverseY t∈Set.Ico (0:ℝ) y₀:=(inverseY_branch t ⟨ht.1.le,ht.2⟩).1
    exact (hrest s _ ⟨hty.1,hty.2.le⟩).2
lemma markedTaylorPolynomial_actual_tilt_jets (P:PsiTheory) (p:ℕ) (x:ℝ) (w:ℂ)
    (Γ:ℕ→ℂ→ℂ)
    (hΓ:∀s,AnalyticAt ℂ (Γ s) (x:ℂ) ∧
      (fun t:ℝ=>Γ s (t:ℂ))=ᶠ[𝓝 x]
        (fun t:ℝ=>(HigherOrder.markedCoefficient P p s (inverseY t):ℂ)))
    (n N:ℕ) (hN:n/2≤N) :
    WP.coeff (fun τ:ℂ=>∑s∈Finset.range (N+1),τ^(2*s)*
      Γ s ((x:ℂ)*Complex.exp ((Complex.I*w/(Real.sqrt (WP.euler WP.Psi x):ℂ))*τ))) n=
      Polynomial.eval₂ Complex.ofRealHom (Complex.I*w) (HigherOrder.markedTaylorPolynomial P p x n) := by
  let c:ℂ:=Complex.I*w/(Real.sqrt (WP.euler WP.Psi x):ℂ)
  let A:ℕ→ℂ→ℂ:=fun s τ=>Γ s ((x:ℂ)*Complex.exp (c*τ))
  have hA(s:ℕ):AnalyticAt ℂ (A s) 0 := (hΓ s).1.comp_of_eq (by fun_prop) (by simp)
  apply markedTaylorPolynomial_eval_of_jets P p x w A hA _ n N hN
  intro s q
  have hreal:AnalyticAt ℝ (fun t:ℝ=>HigherOrder.markedCoefficient P p s (inverseY t)) x :=
    analyticAt_real_of_complex_trace (Γ s) _ x (hΓ s).1 (hΓ s).2
  exact coeff_exponential_tilt_real_jets (Γ s) _ x c (hΓ s).1 hreal (hΓ s).2 q
end WP.Analysis
