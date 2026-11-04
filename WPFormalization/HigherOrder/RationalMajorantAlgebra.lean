import WPFormalization.HigherOrder.PositiveSeriesBounds
import WPFormalization.HigherOrder.MergerMajorant
/-! The true formal geometric majorant dominates every power of exp(t). Algebraic identities for V, the cusp inverse W, and the loss tail Z follow from their genuine unit equations. No convergence or hierarchy estimate is assumed. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries

def geometricMajorant : Series := (1-PowerSeries.X)⁻¹
lemma geometricMajorant_coeff (n:ℕ) : PowerSeries.coeff n geometricMajorant=1 := by
  have h:=inverse_linear_pow_coeff (1:ℝ) 1 n (by norm_num)
  simpa [geometricMajorant] using h
lemma geometricMajorant_coeff_nonneg : ∀n,0 ≤ PowerSeries.coeff n geometricMajorant := by
  intro n;rw[geometricMajorant_coeff];norm_num
lemma exp_coeff_le_geometricMajorant (n:ℕ) :
    PowerSeries.coeff n (PowerSeries.exp ℝ) ≤ PowerSeries.coeff n geometricMajorant := by
  rw[geometricMajorant_coeff]
  have he:PowerSeries.coeff n (PowerSeries.exp ℝ)=1/(n.factorial:ℝ):=by norm_num[PowerSeries.coeff_exp]
  rw[he,one_div]
  have hf:(1:ℝ) ≤ (n.factorial:ℝ):=by exact_mod_cast (Nat.succ_le_of_lt n.factorial_pos)
  exact inv_le_one_of_one_le₀ hf
lemma exp_pow_coeff_le_geometricMajorant (r n:ℕ) :
    PowerSeries.coeff n ((PowerSeries.exp ℝ)^r) ≤ PowerSeries.coeff n (geometricMajorant^r) :=
  coeff_pow_mono exp_coeff_nonneg exp_coeff_le_geometricMajorant r n

lemma geometricMajorant_eq_of_equation (V:Series) (hV:V=1+PowerSeries.X*V) :
    V=geometricMajorant := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp)).mpr
  linear_combination hV
lemma inverse_cusp_majorant_eq_of_equation (C W:Series) (hC:PowerSeries.constantCoeff C=1)
    (hW:W=1+(C-1)*W) : W=(2-C)⁻¹ := by
  have htwo:PowerSeries.constantCoeff (2:Series)=2:=by
    have ht:(2:Series)=1+1:=by norm_num
    rw[ht,map_add,map_one]
    norm_num
  have hunit:PowerSeries.constantCoeff (2-C)≠0:=by rw[map_sub,htwo,hC];norm_num
  apply (PowerSeries.eq_inv_iff_mul_eq_one hunit).mpr
  linear_combination hW
lemma loss_majorant_eq_of_equation (Q Z:Series) (hQ:PowerSeries.constantCoeff Q=0)
    (hZ:Z=Q^2+Q*Z) : Z=Q^2*(1-Q)⁻¹ := by
  have hunit:PowerSeries.constantCoeff (1-Q)≠0:=by simp[hQ]
  have he:(1-Q)*Z=Q^2:=by linear_combination hZ
  calc
    Z=(1-Q)⁻¹*((1-Q)*Z):=by rw[←mul_assoc,PowerSeries.inv_mul_cancel _ hunit,one_mul]
    _=(1-Q)⁻¹*Q^2:=by rw[he]
    _=_:=by ring
end WP.HigherOrder
