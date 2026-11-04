import WPFormalization.HigherOrder.PoissonFamilyExpansion
import WPFormalization.HigherOrder.PoissonFamilyCoefficientBounds
noncomputable section
namespace WP.HigherOrder
open Set
lemma normalizedPoissonFamilyOperator_uniform_expansion (f:ℕ→ℂ × ℂ → ℂ) (R A B:ℝ)
    (hR:0<R) (hA:0<A) (hB:0<B)
    (hfa:∀s,AnalyticOnNhd ℂ (f s) (Metric.ball 0 R))
    (hfb:∀s v,v∈Metric.ball (0:ℂ × ℂ) R→‖f s v‖≤A*B^s*(s.factorial:ℝ)^2)
    (hf0:f 0 (0,0)=1):
    ∃ν₀ C D:ℝ,0<ν₀∧ν₀<R∧0<C∧0<D∧
      (∀ν:ℂ,‖ν‖≤ν₀→1/2≤‖poissonFamilyCoefficient f 0 ν‖)∧
      (∀n,AnalyticOnNhd ℂ (normalizedPoissonFamilyCoefficient f n) (Metric.ball 0 ν₀)∧
        ∀ν:ℂ,‖ν‖<ν₀→‖normalizedPoissonFamilyCoefficient f n ν‖≤C*D^n*(n.factorial:ℝ)^2)∧
      ∀(h:ℝ)(k K J:ℕ),0<h→(k:ℝ)/h≤ν₀→(K:ℝ)≤h/2→K≤J→2*B*((J:ℝ)+1)^2≤h→
        ‖poissonFamilyOperator f J h k/poissonFamilyCoefficient f 0 (((k:ℝ)/h:ℝ):ℂ)-
          ∑n∈Finset.range (K+1),(h:ℂ)⁻¹^n*normalizedPoissonFamilyCoefficient f n (((k:ℝ)/h:ℝ):ℂ)‖≤
          C*D^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=by
  obtain ⟨νe,Ce,De,hνe,hνeR,hCe,hDe,herr⟩:=poissonFamilyOperator_uniform_expansion f R A B hR hA hB hfa hfb
  obtain ⟨νn,Cn,Dn,hνn,hνnR,hCn,hDn,hunit,hcoef⟩:=normalizedPoissonFamilyCoefficient_uniform_bounds f R A B hR hA hB hfa hfb hf0
  let ν₀:ℝ:=min νe (νn/2)
  let C:ℝ:=max (2*Ce) Cn
  let D:ℝ:=max De Dn
  have hν₀:0<ν₀:=lt_min hνe (half_pos hνn)
  have hν₀n:ν₀<νn:=(min_le_right _ _).trans_lt (half_lt_self hνn)
  have hν₀e:ν₀≤νe:=min_le_left _ _
  have hC:0<C:=(by positivity:0<2*Ce).trans_le (le_max_left _ _)
  have hD:0<D:=hDe.trans_le (le_max_left _ _)
  have hunit'(ν:ℂ) (hν:‖ν‖≤ν₀):(1/2:ℝ)≤‖poissonFamilyCoefficient f 0 ν‖:=
    hunit ν (hν.trans_lt hν₀n)
  refine ⟨ν₀,C,D,hν₀,hν₀e.trans_lt hνeR,hC,hD,hunit',?_,?_⟩
  · intro n
    refine ⟨(hcoef n).1.mono (Metric.ball_subset_ball hν₀n.le),?_⟩
    intro ν hν
    apply ((hcoef n).2 ν (hν.trans hν₀n)).trans
    gcongr
    · exact le_max_right _ _
    · exact le_max_right _ _
  · intro h k K J hh hν hK hKJ hw
    let ν:ℂ:=(((k:ℝ)/h:ℝ):ℂ)
    have hνnrm:‖ν‖≤ν₀:=by
      dsimp[ν]
      rw[Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      exact hν
    have hden:(1/2:ℝ)≤‖poissonFamilyCoefficient f 0 ν‖:=hunit' ν hνnrm
    have hdenp:0<‖poissonFamilyCoefficient f 0 ν‖:=lt_of_lt_of_le (by norm_num:0<(1/2:ℝ)) hden
    have he:=herr h k K J hh (hν.trans hν₀e) hK hKJ hw
    have hquot:poissonFamilyOperator f J h k/poissonFamilyCoefficient f 0 ν-
        ∑n∈Finset.range (K+1),(h:ℂ)⁻¹^n*normalizedPoissonFamilyCoefficient f n ν=
        (poissonFamilyOperator f J h k-∑n∈Finset.range (K+1),(h:ℂ)⁻¹^n*poissonFamilyCoefficient f n ν)/
          poissonFamilyCoefficient f 0 ν:=by
      simp only[normalizedPoissonFamilyCoefficient,div_eq_mul_inv,sub_mul,Finset.sum_mul,mul_assoc]
    change ‖poissonFamilyOperator f J h k/poissonFamilyCoefficient f 0 ν-
      ∑n∈Finset.range (K+1),(h:ℂ)⁻¹^n*normalizedPoissonFamilyCoefficient f n ν‖≤_
    rw[hquot,norm_div]
    have hscaled:‖poissonFamilyOperator f J h k-
        ∑n∈Finset.range (K+1),(h:ℂ)⁻¹^n*poissonFamilyCoefficient f n ν‖/
        ‖poissonFamilyCoefficient f 0 ν‖≤(2*Ce)*De^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=by
      apply (div_le_iff₀ hdenp).mpr
      have hm:=mul_le_mul_of_nonneg_left hden
        (by positivity:0≤(2*Ce)*De^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1))
      change ‖poissonFamilyOperator f J h k-
        ∑n∈Finset.range (K+1),(h:ℂ)⁻¹^n*poissonFamilyCoefficient f n ν‖ ≤
        Ce*De^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1) at he
      calc
        _ ≤ Ce*De^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1) := he
        _ = (2*Ce*De^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1))*(1/2) := by ring
        _ ≤ _ := hm
    apply hscaled.trans
    gcongr
    · exact le_max_left _ _
    · exact le_max_left _ _
end WP.HigherOrder
