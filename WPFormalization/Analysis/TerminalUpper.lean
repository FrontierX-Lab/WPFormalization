import WPFormalization.Intersection.PureBackground
import WPFormalization.Intersection.CriticalComparison
import WPFormalization.Analysis.BackgroundMajorant
import WPFormalization.Analysis.KernelCoefficientBound
import WPFormalization.Analysis.HarmonicGlobalLower
noncomputable section
namespace WP.Analysis
open Set
lemma pow_le_exp_mul (a:ℝ)(ha:0 ≤ a)(n:ℕ):a^n ≤ Real.exp (a*n):=by
  have he:a ≤ Real.exp a:=by linarith [Real.add_one_le_exp a]
  have hp:=pow_le_pow_left₀ ha he n
  simpa only [←Real.exp_nat_mul,mul_comm a] using hp
lemma admissible_comparison_sizes (g:ℕ)(d:List ℕ)(hs:Stable g d.length)
    (hd:d.sum ≤ dimension g d.length):
    1 ≤ complexity g d.length ∧ deficit g d ≤ 2*complexity g d.length ∧
      d.count 0 ≤ 3*complexity g d.length:=by
  have hz:d.count 0 ≤ d.length:=List.count_le_length
  unfold Stable at hs
  unfold deficit dimension complexity at *
  omega
lemma ratio_uniform_global_upper (P:PsiTheory):∃C:ℝ,0<C ∧
    ∀g:ℕ,∀d:List ℕ,Stable g d.length→d.sum ≤ dimension g d.length→
      ∀Y∈Icc (0:ℝ) y₀,ratio P g d Y ≤ Real.exp (C*complexity g d.length):=by
  obtain ⟨B,hB,hcoef⟩:=barH_uniform_coefficient_bound
  obtain ⟨c,hc,hc1,hlower⟩:=harmonicCoeff_uniform_exponential_lower
  let C:=10+4*B+c⁻¹
  have hC:0<C:=by dsimp[C];positivity
  refine ⟨C,hC,?_⟩
  intro g d hs hd Y hY
  let h:=complexity g d.length
  let m:=deficit g d
  let Z:=d.count 0
  have hsizes:=admissible_comparison_sizes g d hs hd
  have hh:1 ≤ h:=hsizes.1
  have hm:m ≤ 2*h:=hsizes.2.1
  have hZ:Z ≤ 3*h:=hsizes.2.2
  have hhR:0 ≤ (h:ℝ):=Nat.cast_nonneg _
  have hmR:(m:ℝ) ≤ 2*h:=by exact_mod_cast hm
  have hZR:(Z:ℝ) ≤ 3*h:=by exact_mod_cast hZ
  by_cases hy:Y=y₀
  · subst Y
    have hu:ratio P g d y₀ ≤ (2:ℝ)^Z:=(critical_ratio_zero_bounds P g d hs hd).2
    calc
      _ ≤ (2:ℝ)^Z:=hu
      _ ≤ Real.exp (2*Z):=pow_le_exp_mul 2 (by norm_num) Z
      _ ≤ Real.exp (C*h):=by
        apply Real.exp_le_exp.mpr
        dsimp[C]
        have hBi:0 ≤ B:=by linarith
        have hci:0 ≤ c⁻¹:=(inv_pos.mpr hc).le
        nlinarith
  · have hYi:Y∈Ico 0 y₀:=⟨hY.1,lt_of_le_of_ne hY.2 hy⟩
    let base:ℝ:=(3:ℝ)^h*Real.Gamma h/4^g
    have hbase:0<base:=by
      have hG:0<Real.Gamma h:=Real.Gamma_pos_of_pos (by exact_mod_cast (show 0<h by omega))
      dsimp[base]
      positivity
    have hA:0<harmonicCoeff Y h m:=harmonicCoeff_pos Y h m (by omega) hY
    have hAc:c^h ≤ harmonicCoeff Y h m:=hlower h hh m hm Y hY
    have hupper:=normalized_pure_background_upper P g d hs hd Y hYi
    have hmajor:=background_ascending_majorant h m hh B hB (fun i=>realCoeff (barH Y) (i.val+1))
      (fun i=>hcoef Y hY (i.val+1) (by omega))
    have hNorm:normalized P g d Y ≤ base*((2:ℝ)^Z*((2*B)^m*Real.exp ((h:ℝ)+m))):=by
      exact hupper.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmajor (by positivity)) hbase.le)
    have hemodel:model g d Y=base*harmonicCoeff Y h m:=rfl
    have hRatio:ratio P g d Y ≤ ((2:ℝ)^Z*((2*B)^m*Real.exp ((h:ℝ)+m)))/c^h:=by
      unfold ratio
      rw [hemodel]
      calc
        _ ≤ (base*((2:ℝ)^Z*((2*B)^m*Real.exp ((h:ℝ)+m))))/(base*harmonicCoeff Y h m):=
          div_le_div_of_nonneg_right hNorm (mul_pos hbase hA).le
        _ = ((2:ℝ)^Z*((2*B)^m*Real.exp ((h:ℝ)+m)))/harmonicCoeff Y h m:=by field_simp
        _ ≤ _:=div_le_div_of_nonneg_left (by positivity) (pow_pos hc _) hAc
    have he2:0 ≤ Real.exp (2*(Z:ℝ)):= (Real.exp_pos _).le
    have heB:0 ≤ Real.exp (2*B*(m:ℝ)):= (Real.exp_pos _).le
    have hp2:=pow_le_exp_mul 2 (by norm_num) Z
    have hpB:=pow_le_exp_mul (2*B) (by linarith) m
    have hpc:=pow_le_exp_mul c⁻¹ (inv_pos.mpr hc).le h
    have hprod:((2:ℝ)^Z*((2*B)^m*Real.exp ((h:ℝ)+m)))/c^h ≤
        Real.exp (2*(Z:ℝ))*Real.exp (2*B*(m:ℝ))*Real.exp ((h:ℝ)+m)*Real.exp (c⁻¹*h):=by
      rw [div_eq_mul_inv,←inv_pow]
      have h1:=mul_le_mul hp2 (mul_le_mul_of_nonneg_right hpB (Real.exp_pos _).le)
        (by positivity :0 ≤ (2*B)^m*Real.exp ((h:ℝ)+m)) he2
      have h2:=mul_le_mul h1 hpc (pow_nonneg (inv_pos.mpr hc).le _) (by positivity)
      simpa only [mul_assoc] using h2
    calc
      _ ≤ ((2:ℝ)^Z*((2*B)^m*Real.exp ((h:ℝ)+m)))/c^h:=hRatio
      _ ≤ Real.exp (2*(Z:ℝ))*Real.exp (2*B*(m:ℝ))*Real.exp ((h:ℝ)+m)*Real.exp (c⁻¹*h):=hprod
      _ = Real.exp (2*(Z:ℝ)+2*B*(m:ℝ)+((h:ℝ)+m)+c⁻¹*h):=by simp only [Real.exp_add] <;> ring
      _ ≤ Real.exp (C*h):=by
        apply Real.exp_le_exp.mpr
        dsimp[C]
        nlinarith [mul_nonneg (show 0 ≤ B by linarith) (show 0 ≤ 2*(h:ℝ)-m by linarith)]
end WP.Analysis
