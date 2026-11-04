import WPFormalization.HigherOrder.AuxiliaryMajorantEquations
import WPFormalization.HigherOrder.FiniteLossDomination
import WPFormalization.HigherOrder.ComplexGenusMajorant
/-! Both genuine finite loss operators are bounded by the Z component of the actual polynomial auxiliary solution. The geometric V comparison and the true seven fixed-point equations are instantiated locally, retaining the uniform b>=2B constraint. -/
set_option maxHeartbeats 1000000
noncomputable section
namespace WP.HigherOrder
open PowerSeries

lemma auxiliary_separatingMajorant_bound (b:ℕ) (U:Fin 7→Series) (h0:zeroConstant U)
    (hfixed:formalFixedPoint (auxiliaryMajorantSystem b) U) (hU:∀i j,0 ≤ PowerSeries.coeff j (U i))
    (B:ℝ) (hB:0 ≤ B) (hb:2*B ≤ (b:ℝ)) (K:ℕ) :
    PowerSeries.coeff K (ComplexCanonical.separatingMajorant K B (auxiliarySolutionUnit U 2)
      (auxiliarySolutionUnit U 3) (auxiliarySolutionUnit U 4+auxiliarySolutionUnit U 6)) ≤
      PowerSeries.coeff K ((auxiliarySolutionUnit U 0*auxiliarySolutionUnit U 2)*U 1) := by
  let V:=auxiliarySolutionUnit U 0
  let E:=auxiliarySolutionUnit U 2
  let C:=auxiliarySolutionUnit U 3
  let A:=auxiliarySolutionUnit U 4+auxiliarySolutionUnit U 6
  have hV:=auxiliarySolutionUnit_nonnegative U hU 0
  have hE:=auxiliarySolutionUnit_nonnegative U hU 2
  have hC:=auxiliarySolutionUnit_nonnegative U hU 3
  have hA:∀n,0 ≤ PowerSeries.coeff n A:=by
    intro n
    rw[map_add]
    exact add_nonneg (auxiliarySolutionUnit_nonnegative U hU 4 n) (auxiliarySolutionUnit_nonnegative U hU 6 n)
  have hVeq:V=geometricMajorant:=(auxiliaryMajorant_resolvents b U h0 hfixed).1
  have hExpV:∀n,PowerSeries.coeff n (PowerSeries.exp ℝ) ≤ PowerSeries.coeff n V:=by
    intro n;rw[hVeq];exact exp_coeff_le_geometricMajorant n
  have hExp2:∀n,0 ≤ PowerSeries.coeff n ((PowerSeries.exp ℝ)^2):=coeff_pow_nonneg exp_coeff_nonneg 2
  have hExp2V2:∀n,PowerSeries.coeff n ((PowerSeries.exp ℝ)^2) ≤ PowerSeries.coeff n (V^2):=
    coeff_pow_mono exp_coeff_nonneg hExpV 2
  have hzeq:U 1=(PowerSeries.C (b:ℝ)*PowerSeries.X*((V^2*C)*(1+A)))^2+
      (PowerSeries.C (b:ℝ)*PowerSeries.X*((V^2*C)*(1+A)))*U 1:=by
    have hz:=(auxiliaryMajorant_fixed_equations b U h0 hfixed).2.1
    convert! hz using 1 <;>dsimp[V,C,A,auxiliarySolutionLossArgument]<;>ring
  have hi:=finiteLossSeries_two_coeff_le_tail K B (b:ℝ) hB hb
    ((PowerSeries.exp ℝ)^2*C) (V^2*C) A ((PowerSeries.exp ℝ)*E) (V*E) (U 1)
    (coeff_mul_nonneg hExp2 hC) hA (coeff_mul_nonneg exp_coeff_nonneg hE)
    (fun n=>coeff_mul_mono hExp2 hC hExp2V2 (fun _=>le_rfl) n)
    (fun n=>coeff_mul_mono exp_coeff_nonneg hE hExpV (fun _=>le_rfl) n)
    (hU 1) hzeq
  exact hi

lemma auxiliary_genusSeparatingMajorant_bound (b:ℕ) (U:Fin 7→Series) (h0:zeroConstant U)
    (hfixed:formalFixedPoint (auxiliaryMajorantSystem b) U) (hU:∀i j,0 ≤ PowerSeries.coeff j (U i))
    (B:ℝ) (hB:0 ≤ B) (hb:2*B ≤ (b:ℝ)) (K:ℕ) :
    PowerSeries.coeff K (ComplexCanonical.genusSeparatingMajorant K B
      (auxiliarySolutionUnit U 3) (auxiliarySolutionUnit U 4+auxiliarySolutionUnit U 6)) ≤
      PowerSeries.coeff K (auxiliarySolutionLossArgument b U+U 1) := by
  let V:=auxiliarySolutionUnit U 0
  let C:=auxiliarySolutionUnit U 3
  let A:=auxiliarySolutionUnit U 4+auxiliarySolutionUnit U 6
  have hC:=auxiliarySolutionUnit_nonnegative U hU 3
  have hA:∀n,0 ≤ PowerSeries.coeff n A:=by
    intro n
    rw[map_add]
    exact add_nonneg (auxiliarySolutionUnit_nonnegative U hU 4 n) (auxiliarySolutionUnit_nonnegative U hU 6 n)
  have hVeq:V=geometricMajorant:=(auxiliaryMajorant_resolvents b U h0 hfixed).1
  have hExpV:∀n,PowerSeries.coeff n (PowerSeries.exp ℝ) ≤ PowerSeries.coeff n V:=by
    intro n;rw[hVeq];exact exp_coeff_le_geometricMajorant n
  have hExp2:∀n,0 ≤ PowerSeries.coeff n ((PowerSeries.exp ℝ)^2):=coeff_pow_nonneg exp_coeff_nonneg 2
  have hExp2V2:∀n,PowerSeries.coeff n ((PowerSeries.exp ℝ)^2) ≤ PowerSeries.coeff n (V^2):=
    coeff_pow_mono exp_coeff_nonneg hExpV 2
  have hQeq:PowerSeries.C (b:ℝ)*PowerSeries.X*((V^2*C)*(1+A))=auxiliarySolutionLossArgument b U:=by
    dsimp[V,C,A,auxiliarySolutionLossArgument]
    ring
  have hzeq:U 1=(PowerSeries.C (b:ℝ)*PowerSeries.X*((V^2*C)*(1+A)))^2+
      (PowerSeries.C (b:ℝ)*PowerSeries.X*((V^2*C)*(1+A)))*U 1:=by
    rw[hQeq]
    exact (auxiliaryMajorant_fixed_equations b U h0 hfixed).2.1
  have hOne:∀n,0 ≤ PowerSeries.coeff n (1:Series):=by
    intro n;rw[PowerSeries.coeff_one];split_ifs<;>norm_num
  have hi:=finiteLossSeries_one_coeff_le_tail K B (b:ℝ) hB hb
    ((PowerSeries.exp ℝ)^2*C) (V^2*C) A 1 1 (U 1)
    (coeff_mul_nonneg hExp2 hC) hA hOne
    (fun n=>coeff_mul_mono hExp2 hC hExp2V2 (fun _=>le_rfl) n) (fun _=>le_rfl)
    (hU 1) hzeq
  rw[one_mul,hQeq] at hi
  simpa only[finiteLossSeries,ComplexCanonical.genusSeparatingMajorant,mul_one] using hi
end WP.HigherOrder
