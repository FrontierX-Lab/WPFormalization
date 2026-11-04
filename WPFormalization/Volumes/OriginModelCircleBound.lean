import WPFormalization.Volumes.StrongOriginSource
import WPFormalization.Volumes.OriginFiniteModel
import WPFormalization.Volumes.CriticalModelGrowth
/-! Full-circle decay of the literal finite marked model.
A genuine phase decay and the explicit native Gevrey order budget bound the
actual finite amplitude sum. The denominator is controlled by the actual
base amplitude and correction factor. This is a model-circle bound, not an
assertion of a generating-function comparison on that circle. -/
noncomputable section
namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma normalizedFiniteMarkedModel_amplitude_sum (P:PsiTheory)(g p J:ℕ)
    (S Bc:ℂ→ℂ)(L:ℕ→ℂ→ℂ)(z:ℂ):
    normalizedFiniteMarkedModel P g p S Bc L J z=
      Complex.exp ((complexity g p:ℂ)*S z)*
        (∑j∈Finset.range (J+1),originMarkedAmplitude P p j Bc L z/(complexity g p:ℂ)^j):=by
  unfold normalizedFiniteMarkedModel finiteMarkedFactor originMarkedAmplitude
  rw[Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  ring

lemma origin_model_circle_decay_at (P:PsiTheory)(g p J:ℕ)
    (S Bc:ℂ→ℂ)(L:ℕ→ℂ→ℂ)(B D ρ x:ℝ)
    (hB:0<B)(hD:0<D)(hx:x∈Ioo (0:ℝ) ρ)(hh:0<(complexity g p:ℝ))
    (hbudget:2*B*((J:ℝ)+1)^2≤(complexity g p:ℝ))
    (hAb:∀j z,‖z‖≤ρ→‖originMarkedAmplitude P p j Bc L z‖≤D*B^j*(j.factorial:ℝ)^2)
    (hBc:‖Bc (x:ℂ)-1‖≤1/2)
    (hP:1/2≤‖finiteMarkedFactor L (complexity g p:ℝ) J (PositiveConvolution.planarInverse P (x:ℂ))‖)
    (hphase:∀θ:ℝ,(S ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))-S (x:ℂ)).re≤-(x/2)*(1-Real.cos θ)):
    normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)≠0 ∧
      ∀θ:ℝ,‖normalizedFiniteMarkedModel P g p S Bc L J
        ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))/normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)‖≤
        8*D*Real.exp (-((complexity g p:ℝ)*x/2)*(1-Real.cos θ)):=by
  let h:ℝ:=complexity g p
  let M:ℂ→ℂ:=normalizedFiniteMarkedModel P g p S Bc L J
  have hcast:(complexity g p:ℂ)=(h:ℂ):=by simp only[h,Complex.ofReal_natCast]
  have hnormExp(z:ℂ):‖Complex.exp ((complexity g p:ℂ)*S z)‖=Real.exp (h*(S z).re):=by
    rw[hcast,Complex.norm_exp]
    congr 1
    simp only[Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hBclower:1/2≤‖Bc (x:ℂ)‖:=(Analysis.near_one_norm_bounds _ hBc).1
  have hden:Real.exp (h*(S (x:ℂ)).re)/4≤‖M (x:ℂ)‖:=by
    dsimp only[M]
    unfold normalizedFiniteMarkedModel
    rw[norm_mul,norm_mul,hnormExp]
    have he:0<Real.exp (h*(S (x:ℂ)).re):=Real.exp_pos _
    have hmul:(1/4:ℝ)≤‖Bc (x:ℂ)‖*‖finiteMarkedFactor L h J (PositiveConvolution.planarInverse P (x:ℂ))‖:=by
      nlinarith[mul_le_mul hBclower hP (by norm_num:(0:ℝ)≤1/2) (norm_nonneg (Bc (x:ℂ)))]
    nlinarith[mul_le_mul_of_nonneg_left hmul he.le]
  have hdenpos:0<‖M (x:ℂ)‖:=lt_of_lt_of_le (by positivity) hden
  refine ⟨norm_pos_iff.mp hdenpos,?_⟩
  intro θ
  let z:ℂ:=(x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)
  have hz:‖z‖≤ρ:=by
    simp only[z,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_of_nonneg hx.1.le]
    exact hx.2.le
  have hsum:‖∑j∈Finset.range (J+1),originMarkedAmplitude P p j Bc L z/(h:ℂ)^j‖≤2*D:=
    Analysis.finite_gevrey_two_sum_norm _ D B h J hD.le hB hh (fun j=>hAb j z hz) hbudget
  have hnum:‖M z‖≤2*D*Real.exp (h*(S z).re):=by
    dsimp only[M]
    rw[normalizedFiniteMarkedModel_amplitude_sum,norm_mul,hnormExp,hcast]
    nlinarith[mul_le_mul_of_nonneg_left hsum (Real.exp_pos (h*(S z).re)).le]
  have hratio:‖M z/M (x:ℂ)‖≤8*D*Real.exp (h*((S z).re-(S (x:ℂ)).re)):=by
    rw[norm_div]
    apply (div_le_iff₀ hdenpos).mpr
    calc
      _≤2*D*Real.exp (h*(S z).re):=hnum
      _=(8*D*Real.exp (h*((S z).re-(S (x:ℂ)).re)))*(Real.exp (h*(S (x:ℂ)).re)/4):=by
        rw[mul_sub,Real.exp_sub]
        field_simp
        <;>ring
      _≤_:=mul_le_mul_of_nonneg_left hden (by positivity)
  apply hratio.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity:0≤8*D)
  apply Real.exp_le_exp.mpr
  have hp:=hphase θ
  rw[Complex.sub_re] at hp
  have ht:=mul_le_mul_of_nonneg_left hp hh.le
  dsimp only[z] at *
  nlinarith
end WP.HigherOrder
