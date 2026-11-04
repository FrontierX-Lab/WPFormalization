import WPFormalization.RandomGeometry.PrimitiveCoefficientRatio
import WPFormalization.RandomGeometry.PrimitivePlanarTypeTail
/-! The actual zero-boundary one-curve integral on the primitive scale.
The coefficient comparison holds for every type through k=n. -/
noncomputable section
namespace WP.RandomGeometry
open Set

def primitivePlanarEffectiveScale (g n:ℕ):ℝ:=
  (n:ℝ)*primitiveSaddleX g n/(4*(2*Real.pi^2))

def primitivePlanarFirstBase (P:PsiTheory)(g n k:ℕ)(L:ℝ):ℝ:=
  (n.choose k:ℝ)*volumeModel P 0 (k+1)*volumeModel P g (n-k+1)/volumeModel P g n*L^2/2

lemma primitive_planar_first_base_bound (P:PsiTheory):
    ∃H:ℝ,0<H ∧ ∀g n:ℕ,2≤g→2≤n→
      H≤ min (2*(g:ℝ)-1) ((n-1:ℕ):ℝ)→
      let x:=primitiveSaddleX g n
      let q:=primitivePlanarEffectiveScale g n
      0<q ∧ ∀k:ℕ,2≤k→k≤n→∀T:ℝ,
        primitivePlanarFirstBase P g n k (T/Real.sqrt q)≤
          6*T^2*primitivePlanarWeight P k*x^(k-2):=by
  obtain ⟨H,hH,hbound⟩:=primitive_coefficient_ratio P
  refine ⟨H,hH,?_⟩
  intro g n hg hn hsize
  let x:=primitiveSaddleX g n
  let q:=primitivePlanarEffectiveScale g n
  have hb:=hbound g n (by omega) hsize
  have hxp:0<x:=hb.1.1
  have hnp:0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have hP:0<2*Real.pi^2:=by positivity
  have hq:0<q:=div_pos (mul_pos hnp hxp) (by positivity)
  refine ⟨hq,?_⟩
  intro k hk hkn T
  have ha:0≤primitivePlanarWeight P k:=by
    simpa only[Nat.sub_add_cancel hk] using primitive_planar_weight_nonneg P (k-2)
  have hr:=hb.2.2 (k-1) (by omega)
  rw[show n-1-(k-1)=n-k by omega] at hr
  have hpow:x^(k-1)=x^(k-2)*x:=by rw[show k-1=k-2+1 by omega,pow_succ]
  unfold primitivePlanarFirstBase
  rw[primitive_planar_coefficient_identity P g n k hg hk hkn]
  calc
    _≤primitivePlanarWeight P k*((n:ℝ)/(2*Real.pi^2))*(3*x^(k-1))*(T/Real.sqrt q)^2/2:=by gcongr
    _=6*T^2*primitivePlanarWeight P k*x^(k-2):=by
      rw[div_pow,Real.sq_sqrt hq.le,hpow]
      dsimp[q,primitivePlanarEffectiveScale]
      change primitivePlanarWeight P k*((n:ℝ)/(2*Real.pi^2))*(3*(x^(k-2)*x))*
        (T^2/((n:ℝ)*x/(4*(2*Real.pi^2))))/2=_
      field_simp [hnp.ne',hxp.ne',hP.ne']
      <;>ring

lemma primitive_planar_first_base_type_tail (P:PsiTheory):
    ∃H:ℝ,0<H ∧ ∀g n:ℕ,2≤g→2≤n→
      H≤ min (2*(g:ℝ)-1) ((n-1:ℕ):ℝ)→∀K:ℕ,∀T:ℝ,
      (∑j∈Finset.range (n-K-1),primitivePlanarFirstBase P g n (j+K+2)
          (T/Real.sqrt (primitivePlanarEffectiveScale g n)))≤
        6*T^2*primitivePlanarTypeTail P K (primitiveSaddleX g n):=by
  obtain ⟨H₁,hH₁,hbound⟩:=primitive_planar_first_base_bound P
  obtain ⟨H₂,hH₂,hsaddle⟩:=primitive_coefficient_ratio P
  let H:ℝ:=max H₁ H₂
  refine ⟨H,hH₁.trans_le (le_max_left _ _),?_⟩
  intro g n hg hn hsize K T
  have hsize₁:H₁≤ min (2*(g:ℝ)-1) ((n-1:ℕ):ℝ):=(le_max_left _ _).trans hsize
  have hsize₂:H₂≤ min (2*(g:ℝ)-1) ((n-1:ℕ):ℝ):=(le_max_right _ _).trans hsize
  have hb:=(hbound g n hg hn hsize₁).2
  have hx:primitiveSaddleX g n∈Icc (0:ℝ) xCritical:=by
    have ht:=(hsaddle g n (by omega) hsize₂).1
    exact ⟨ht.1.le,ht.2.le⟩
  let f:ℕ→ℝ:=fun j=>primitivePlanarWeight P (j+K+2)*(primitiveSaddleX g n)^(j+K)
  have hf:Summable f:=primitive_planar_type_tail_summable P K _ hx
  have hnonneg:∀j,0≤f j:=fun j=>mul_nonneg (primitive_planar_weight_nonneg P (j+K)) (pow_nonneg hx.1 _)
  have hfinite:(∑j∈Finset.range (n-K-1),f j)≤primitivePlanarTypeTail P K (primitiveSaddleX g n):=
    hf.sum_le_tsum _ (fun j hj=>hnonneg j)
  calc
    _≤∑j∈Finset.range (n-K-1),6*T^2*f j:=by
      apply Finset.sum_le_sum
      intro j hj
      have hjn:j<n-K-1:=Finset.mem_range.mp hj
      have he:=hb (j+K+2) (by omega) (by omega) T
      simpa only[f,show j+K+2-2=j+K by omega,mul_assoc] using he
    _=6*T^2*(∑j∈Finset.range (n-K-1),f j):=by rw[Finset.mul_sum]
    _≤_:=mul_le_mul_of_nonneg_left hfinite (by positivity)

end WP.RandomGeometry
