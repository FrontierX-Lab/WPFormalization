import WPFormalization.HigherOrder.ShiftExtraction
import Mathlib.Analysis.Complex.Basic

/-! Exact finite extraction and normalized norm bounds for the genuine complex substitution t/(1-ct). The estimates require only the indicated finitely many lower-order coefficients. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries
lemma complex_inverse_linear_pow_eq_rescale (c:ℂ) (a:ℕ) :
    ((1-C c*PowerSeries.X:PowerSeries ℂ)⁻¹)^a=
      PowerSeries.rescale c ((PowerSeries.invOneSubPow ℂ a).val) := by
  rw[PowerSeries.inv_pow]
  symm
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp)).mpr
  have he:=(PowerSeries.invOneSubPow ℂ a).val_inv
  rw[PowerSeries.invOneSubPow_inv_eq_one_sub_pow] at he
  have ht:=congrArg (PowerSeries.rescale c) he
  simpa only[map_mul,map_pow,map_sub,map_one,PowerSeries.rescale_X] using ht
lemma complex_inverse_linear_pow_coeff (c:ℂ) (a q:ℕ) (ha:1 ≤ a) :
    PowerSeries.coeff q (((1-C c*PowerSeries.X:PowerSeries ℂ)⁻¹)^a)=
      (Nat.choose (a+q-1) q:ℂ)*c^q := by
  rw[complex_inverse_linear_pow_eq_rescale,PowerSeries.coeff_rescale,
    PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℂ a (by omega),PowerSeries.coeff_mk]
  have he:a-1+q=a+q-1:=by omega
  rw[he]
  have hc:Nat.choose (a+q-1) (a-1)=Nat.choose (a+q-1) q:=Nat.choose_symm_of_eq_add (by omega)
  rw[hc];ring
lemma complex_inverse_linear_pow_coeff_normalized (c:ℂ) (S:ℝ) (a q j:ℕ)
    (haj:a+q ≤ j) (hc:‖c‖ ≤ j) (hS:(j:ℝ) ≤ S) :
    ‖PowerSeries.coeff q (((1-C c*PowerSeries.X:PowerSeries ℂ)⁻¹)^a)‖ ≤ S^(2*q)/(q.factorial:ℝ) := by
  have hS0 : 0  ≤  S := (Nat.cast_nonneg j).trans hS
  by_cases ha:a=0
  · subst a
    cases q with
    | zero=>simp
    | succ q=>simp only[pow_zero,PowerSeries.coeff_one,Nat.succ_ne_zero,ite_false,norm_zero];positivity
  have ha':1 ≤ a:=by omega
  rw[complex_inverse_linear_pow_coeff c a q ha',norm_mul,norm_pow,Complex.norm_natCast]
  have heq:‖c‖^q=|‖c‖|^q:=by rw[abs_of_nonneg (norm_nonneg c)]
  rw[heq]
  have hd:=inverse_linear_pow_coeff_normalized ‖c‖ S a q j ha' haj
    (by simpa only[abs_of_nonneg (norm_nonneg c)] using hc) hS
  rw[inverse_linear_pow_coeff _ _ _ ha',abs_mul,abs_pow,abs_of_nonneg (Nat.cast_nonneg _)] at hd
  exact hd
lemma complex_shift_coeff_sum (c:ℂ) (f:PowerSeries ℂ) (K:ℕ) :
    PowerSeries.coeff K (f.subst (PowerSeries.X*(1-C c*PowerSeries.X)⁻¹))=
      ∑i∈Finset.range (K+1),PowerSeries.coeff i f*
        PowerSeries.coeff (K-i) (((1-C c*PowerSeries.X:PowerSeries ℂ)⁻¹)^i) := by
  have hconst:PowerSeries.constantCoeff (PowerSeries.X*(1-C c*PowerSeries.X:PowerSeries ℂ)⁻¹)=0:=by simp
  rw[PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hconst)]
  have hcoeff (i:ℕ) : PowerSeries.coeff K ((PowerSeries.X*(1-C c*PowerSeries.X:PowerSeries ℂ)⁻¹)^i)=
      if i ≤ K then PowerSeries.coeff (K-i) (((1-C c*PowerSeries.X:PowerSeries ℂ)⁻¹)^i) else 0:=by
    rw[mul_pow,PowerSeries.coeff_X_pow_mul']
  have hs:Function.support (fun i:ℕ=>PowerSeries.coeff i f • PowerSeries.coeff K
      ((PowerSeries.X*(1-C c*PowerSeries.X:PowerSeries ℂ)⁻¹)^i))⊆(Finset.range (K+1):Set ℕ):=by
    intro i hi
    by_contra hn
    have hiK:K < i:=by
      have hh:¬ i < K+1:=by simpa only[Finset.mem_coe,Finset.mem_range] using hn
      omega
    have hz:PowerSeries.coeff K ((PowerSeries.X*(1-C c*PowerSeries.X:PowerSeries ℂ)⁻¹)^i)=0:=by
      rw[hcoeff,if_neg (by omega)]
    exact hi (by simp[hz])
  rw[finsum_eq_sum_of_support_subset _ hs]
  apply Finset.sum_congr rfl
  intro i hi
  rw[hcoeff,if_pos (by have hi':=Finset.mem_range.mp hi;omega)]
  rfl
lemma complex_shift_coeff_exponential_majorant (c:ℂ) (S:ℝ) (f:PowerSeries ℂ) (e:ℕ→ℝ) (K j:ℕ)
    (hK:K ≤ j) (hc:‖c‖ ≤ j) (hS:(j:ℝ) ≤ S) (he:∀i:ℕ,0 ≤ e i)
    (hf:∀i:ℕ,i ≤ K→‖PowerSeries.coeff i f‖ ≤ e i*S^(2*i)) :
    ‖PowerSeries.coeff K (f.subst (PowerSeries.X*(1-C c*PowerSeries.X)⁻¹))‖ ≤
      S^(2*K)*PowerSeries.coeff K ((PowerSeries.exp ℝ)*PowerSeries.mk e) := by
  have hS0:0 ≤ S:=(Nat.cast_nonneg j).trans hS
  rw[exp_series_convolution_coeff,complex_shift_coeff_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑i∈Finset.range (K+1),e i*S^(2*K)/((K-i).factorial:ℝ):=by
      apply Finset.sum_le_sum
      intro i hi
      have hiK:i ≤ K:=by have h:=Finset.mem_range.mp hi;omega
      rw[norm_mul]
      have hd:=complex_inverse_linear_pow_coeff_normalized c S i (K-i) j (by omega) hc hS
      apply (mul_le_mul (hf i hiK) hd (norm_nonneg _) (mul_nonneg (he i) (pow_nonneg hS0 _))).trans_eq
      have hp:S^(2*i)*S^(2*(K-i))=S^(2*K):=by rw[←pow_add];congr 1;omega
      calc
        _ = e i*(S^(2*i)*S^(2*(K-i)))/((K-i).factorial:ℝ):=by ring
        _ = _:=by rw[hp]
    _ = _:=by rw[Finset.mul_sum];apply Finset.sum_congr rfl;intro i hi;ring
end WP.HigherOrder
