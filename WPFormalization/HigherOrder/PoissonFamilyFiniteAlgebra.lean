import WPFormalization.HigherOrder.PoissonFamilyCoefficients
import WPFormalization.Analysis.PoissonTruncationBounds
noncomputable section
namespace WP.HigherOrder
def poissonFamilyOperator (f:ℕ→ℂ × ℂ → ℂ) (J:ℕ) (h:ℝ) (k:ℕ):ℂ:=
  poissonCoefficientOperator h k (fun u=>∑s∈Finset.range (J+1),(h:ℂ)⁻¹^s*f s (u,(((k:ℝ)/h:ℝ):ℂ)))
lemma poissonFamilyOperator_eq_sum (f:ℕ→ℂ × ℂ → ℂ) (J:ℕ) (h:ℝ) (k:ℕ)
    (ha:∀s,s≤J→AnalyticAt ℂ (fun u:ℂ=>f s (u,(((k:ℝ)/h:ℝ):ℂ))) 0):
    poissonFamilyOperator f J h k=
      ∑s∈Finset.range (J+1),(h:ℂ)⁻¹^s*
        poissonCoefficientOperator h k (fun u=>f s (u,(((k:ℝ)/h:ℝ):ℂ))):=by
  rw[poissonFamilyOperator,poissonCoefficientOperator_sum _ _ _ _ (by
    intro s hs
    exact analyticAt_const.mul (ha s (Nat.le_of_lt_succ (Finset.mem_range.mp hs))))]
  apply Finset.sum_congr rfl
  intro s hs
  exact poissonCoefficientOperator_const_mul _ _ _ _
lemma poissonFamilyRemainder_exact (f:ℕ→ℂ × ℂ → ℂ) (K:ℕ) (h:ℝ) (k:ℕ)
    (ha:∀s,s≤K→AnalyticAt ℂ (fun u:ℂ=>f s (u,(((k:ℝ)/h:ℝ):ℂ))) 0):
    poissonFamilyOperator f K h k-
      ∑n∈Finset.range (K+1),(h:ℂ)⁻¹^n*poissonFamilyCoefficient f n (((k:ℝ)/h:ℝ):ℂ)=
    ∑s∈Finset.range (K+1),(h:ℂ)⁻¹^s*
      (poissonCoefficientOperator h k (fun u=>f s (u,(((k:ℝ)/h:ℝ):ℂ)))-
        ∑i∈Finset.range (K-s+1),(h:ℂ)⁻¹^i*poissonCentralAmplitude (f s) i (((k:ℝ)/h:ℝ):ℂ)):=by
  have he:=Analysis.weighted_triangle_sum (h:ℂ)⁻¹
    (fun s i=>poissonCentralAmplitude (f s) i (((k:ℝ)/h:ℝ):ℂ)) K
  simp only[poissonFamilyCoefficient]
  rw[poissonFamilyOperator_eq_sum f K h k ha,←he,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  ring
lemma poissonFamilyOperator_tail (f:ℕ→ℂ × ℂ → ℂ) (J K:ℕ) (hJK:K≤J) (h:ℝ) (k:ℕ)
    (ha:∀s,s≤J→AnalyticAt ℂ (fun u:ℂ=>f s (u,(((k:ℝ)/h:ℝ):ℂ))) 0):
    poissonFamilyOperator f J h k=poissonFamilyOperator f K h k+
      ∑i∈Finset.range (J-K),(h:ℂ)⁻¹^(K+1+i)*
        poissonCoefficientOperator h k (fun u=>f (K+1+i) (u,(((k:ℝ)/h:ℝ):ℂ))):=by
  rw[poissonFamilyOperator_eq_sum f J h k ha,poissonFamilyOperator_eq_sum f K h k (by intro s hs;exact ha s (hs.trans hJK))]
  rw[show J+1=(K+1)+(J-K) by omega,Finset.sum_range_add]
end WP.HigherOrder
