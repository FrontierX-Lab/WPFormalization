import WPFormalization.Critical.CutVertexPartition

/-! The complete specified-partition Gamma sum is bounded by the actual ordered positive-complexity coefficient sum. This derives the critical genus exponent for every admissible finite family of stable genus allocations. -/
noncomputable section
namespace WP.Critical
open Finset
namespace CutVertexPartition
variable {Q u v w:ℕ} (R:CutVertexPartition Q u v w)

/-- The actual genus and cusp-allocation Gamma weights for the prescribed
vertex partition are bounded by the full ordered complexity allocation. -/
lemma gamma_sum_coefficient_majorant (g k n:ℕ) (hg:w+2≤g)
    (p:Fin Q→ℕ) (hp:∀i,1≤p i) (hpsum:(∑c:Fin Q,p c)=2*k)
    (h01:∀i,p (R.oneVertex i)=1) (h02:∀i,p (R.twoVertex i)=2)
    (s:Finset (Fin w→ℕ))
    (hs:∀b∈s,(∀i,Stable (b i) (p (R.stableVertex i))) ∧
      (∑c:Fin Q,R.genusVector b c)+k+1=g+Q) :
    (∑b∈s,∑σ:Fin n→Fin Q,∏c:Fin Q,
      Real.Gamma (complexity (R.genusVector b c) (p c+cutCuspHistogram σ c))) ≤
        (n.factorial:ℝ)*PowerSeries.coeff n (cutCuspAllocationSeries u v*
          cutStableAllocationSeries w (2*g-2+u-w)) := by
  have hstable : ∀b∈s,(∀i,Stable (b i) (p (R.stableVertex i))) ∧
      (∑i:Fin w,complexity (b i) (p (R.stableVertex i)))=(2*g-2+u-w)+w := by
    intro b hb
    exact ⟨(hs b hb).1,R.stableComplexity_budget g k hg p b h01 h02 (hs b hb).1 hpsum (hs b hb).2⟩
  calc
    _ = ∑b∈s,(n.factorial:ℝ)*PowerSeries.coeff n
        (cutCuspAllocationSeries u v*
          (∏i:Fin w,cutStableCuspSeries (complexity (b i) (p (R.stableVertex i))))) := by
      apply sum_congr rfl
      intro b hb
      rw [cutCuspLabels_gamma_series n Q (R.genusVector b) p hp,
        R.localSeries_product p b h01 h02 (hs b hb).1]
    _ = (n.factorial:ℝ)*(∑b∈s,PowerSeries.coeff n
        (cutCuspAllocationSeries u v*
          (∏i:Fin w,cutStableCuspSeries (complexity (b i) (p (R.stableVertex i)))))) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (cutStableGenus_coefficient_majorant n (fun i=>p (R.stableVertex i)) s hstable
        (cutCuspAllocationSeries u v) (cutCuspAllocation_coeff_nonneg u v)) (Nat.cast_nonneg _)

/-- The exact numerical Gamma sum of any admissible finite genus family has
the original critical genus exponent, uniformly over the cusp count. -/
lemma gamma_sum_genus_rate (k:ℕ) (p:Fin Q→ℕ) (hp:∀i,1≤p i)
    (hpsum:(∑c:Fin Q,p c)=2*k)
    (h01:∀i,p (R.oneVertex i)=1) (h02:∀i,p (R.twoVertex i)=2)
    (hw:1≤w) (A:ℝ) (hA:0<A) :
    ∃C:ℝ,0<C ∧ ∃G:ℕ,∀g≥G,∀n:ℕ,(n:ℝ)≤A*Real.sqrt g →
      ∀s:Finset (Fin w→ℕ),
      (∀b∈s,(∀i,Stable (b i) (p (R.stableVertex i))) ∧
        (∑c:Fin Q,R.genusVector b c)+k+1=g+Q) →
      ((∑b∈s,∑σ:Fin n→Fin Q,∏c:Fin Q,
        Real.Gamma (complexity (R.genusVector b c) (p c+cutCuspHistogram σ c)))/
          Real.Gamma ((2*g+n-2:ℕ):ℝ)) ≤ C*(g:ℝ)^(1-(w:ℝ)-(v:ℝ)/2) := by
  obtain ⟨C,hC,G,hbound⟩:=cutCuspAllocationSum_genus_rate u v w hw A hA
  refine ⟨C,hC,max G (w+2),?_⟩
  intro g hg n hn s hs
  have hpΓ : 0<Real.Gamma (((2*g+n-2:ℕ):ℝ)) := by
    apply Real.Gamma_pos_of_pos
    exact_mod_cast (by omega:0<2*g+n-2)
  have he:=R.gamma_sum_coefficient_majorant g k n (by omega) p hp hpsum h01 h02 s hs
  have hb:=div_le_div_of_nonneg_right he hpΓ.le
  have hm:=hbound g (by omega) n hn
  exact hb.trans (by convert hm using 1 <;>ring)

end CutVertexPartition
end WP.Critical
