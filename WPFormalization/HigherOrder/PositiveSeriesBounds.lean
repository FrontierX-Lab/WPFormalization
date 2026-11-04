import WPFormalization.HigherOrder.NormalizedCoefficientMajorants
/-! Finite coefficient inequalities for nonnegative real formal series. Powers and products preserve coefficient domination; a^j is dominated by (1+a)^r when j<=r. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries
lemma coeff_pow_nonneg {f:Series} (hf:∀k,0 ≤ PowerSeries.coeff k f) (r:ℕ) :
    ∀k,0 ≤ PowerSeries.coeff k (f^r) := by
  simpa only[Finset.prod_const,Finset.card_range] using
    (coeff_prod_nonneg (Finset.range r) (fun _=>f) (fun b hb=>hf))
lemma coeff_mul_mono {f₁ f₂ g₁ g₂:Series}
    (hf₁:∀k,0 ≤ PowerSeries.coeff k f₁) (hf₂:∀k,0 ≤ PowerSeries.coeff k f₂)
    (h₁:∀k,PowerSeries.coeff k f₁ ≤ PowerSeries.coeff k g₁)
    (h₂:∀k,PowerSeries.coeff k f₂ ≤ PowerSeries.coeff k g₂) (n:ℕ) :
    PowerSeries.coeff n (f₁*f₂) ≤ PowerSeries.coeff n (g₁*g₂) := by
  rw[PowerSeries.coeff_mul,PowerSeries.coeff_mul]
  apply Finset.sum_le_sum
  intro ij hij
  exact mul_le_mul (h₁ ij.1) (h₂ ij.2) (hf₂ ij.2) ((hf₁ ij.1).trans (h₁ ij.1))
lemma coeff_pow_mono {f g:Series} (hf:∀k,0 ≤ PowerSeries.coeff k f)
    (hfg:∀k,PowerSeries.coeff k f ≤ PowerSeries.coeff k g) (r n:ℕ) :
    PowerSeries.coeff n (f^r) ≤ PowerSeries.coeff n (g^r) := by
  induction r generalizing n with
  | zero=>rfl
  | succ r ih=>
      rw[pow_succ,pow_succ]
      exact coeff_mul_mono (coeff_pow_nonneg hf r) hf ih hfg n
lemma coeff_power_le_one_add_power {a:Series} (ha:∀k,0 ≤ PowerSeries.coeff k a)
    (j r:ℕ) (hjr:j ≤ r) (n:ℕ) :
    PowerSeries.coeff n (a^j) ≤ PowerSeries.coeff n ((1+a)^r) := by
  rw[add_comm (1:Series) a,add_pow,map_sum]
  simp only[one_pow,mul_one,PowerSeries.coeff_mul_natCast]
  have hc:(1:ℝ) ≤ (r.choose j:ℝ):=by exact_mod_cast Nat.choose_pos hjr
  calc
    _ ≤ PowerSeries.coeff n (a^j)*(r.choose j:ℝ):=by
      simpa only[mul_one] using mul_le_mul_of_nonneg_left hc (coeff_pow_nonneg ha j n)
    _ ≤ ∑i∈Finset.range (r+1),PowerSeries.coeff n (a^i)*(r.choose i:ℝ):=
      Finset.single_le_sum (fun i hi=>mul_nonneg (coeff_pow_nonneg ha i n) (Nat.cast_nonneg _))
        (Finset.mem_range.mpr (by omega))
end WP.HigherOrder
