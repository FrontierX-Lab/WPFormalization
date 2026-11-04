import WPFormalization.HigherOrder.AuxiliaryMajorantEquations
/-! Positive-order coefficient identities of the genuine auxiliary solution. These are derived from its proved polynomial equations and give the profile, cusp, high-genus and descent coefficient budgets used by the actual canonical induction. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries
lemma coeff_of_unit_constant_product (f g:Series) (b:ℝ) (h:f=1+PowerSeries.C b*g)
    (K:ℕ) (hK:1 ≤ K) : PowerSeries.coeff K f=b*PowerSeries.coeff K g := by
  rw[h,map_add,PowerSeries.coeff_one,if_neg (by omega),zero_add,PowerSeries.coeff_C_mul]

lemma auxiliary_profile_coefficient_budget (b:ℕ) (U:Fin 7→Series) (h0:zeroConstant U)
    (hfixed:formalFixedPoint (auxiliaryMajorantSystem b) U) (K:ℕ) (hK:1 ≤ K) :
    let V:=auxiliarySolutionUnit U 0
    let E:=auxiliarySolutionUnit U 2
    let C:=auxiliarySolutionUnit U 3
    let A:=auxiliarySolutionUnit U 4+auxiliarySolutionUnit U 6
    PowerSeries.coeff K E=(b:ℝ)*(PowerSeries.coeff K (PowerSeries.X*(V^3*E*C*(1+A)))+
      PowerSeries.coeff K ((V*E)*U 1)) := by
  obtain ⟨hV,hZ,hE,hC,hH,hW,hG⟩:=auxiliaryMajorant_fixed_equations b U h0 hfixed
  let V:=auxiliarySolutionUnit U 0
  let E:=auxiliarySolutionUnit U 2
  let C:=auxiliarySolutionUnit U 3
  let A:=auxiliarySolutionUnit U 4+auxiliarySolutionUnit U 6
  have he:E=1+PowerSeries.C (b:ℝ)*(PowerSeries.X*(V^3*E*C*(1+A))+(V*E)*U 1):=by
    dsimp only[V,E,C,A] at *
    linear_combination hE
  have hc:=coeff_of_unit_constant_product E _ (b:ℝ) he K hK
  rw[map_add] at hc
  exact hc

lemma auxiliary_cusp_coefficient_budget (b:ℕ) (U:Fin 7→Series) (h0:zeroConstant U)
    (hfixed:formalFixedPoint (auxiliaryMajorantSystem b) U) (K:ℕ) (hK:1 ≤ K) :
    PowerSeries.coeff K (auxiliarySolutionUnit U 3)=(b:ℝ)*
      PowerSeries.coeff K (auxiliarySolutionUnit U 0*auxiliarySolutionUnit U 2) := by
  have hC:=(auxiliaryMajorant_fixed_equations b U h0 hfixed).2.2.2.1
  have hc:=coeff_of_unit_constant_product _ _ (b:ℝ) hC K hK
  simpa only[map_sub,PowerSeries.coeff_one,if_neg (by omega : K≠0),sub_zero] using hc

lemma auxiliary_high_genus_coefficient_budget (b:ℕ) (U:Fin 7→Series) (h0:zeroConstant U)
    (hfixed:formalFixedPoint (auxiliaryMajorantSystem b) U) (K:ℕ) (hK:1 ≤ K) :
    PowerSeries.coeff K (auxiliarySolutionUnit U 4)=(b:ℝ)*
      (PowerSeries.coeff K (auxiliarySolutionUnit U 2)+PowerSeries.coeff K (auxiliarySolutionLossArgument b U+U 1)) := by
  have hH:=(auxiliaryMajorant_fixed_equations b U h0 hfixed).2.2.2.2.1
  have hh:auxiliarySolutionUnit U 4=1+PowerSeries.C (b:ℝ)*
      ((auxiliarySolutionUnit U 2-1)+(auxiliarySolutionLossArgument b U+U 1)):=by
    linear_combination hH
  have hc:=coeff_of_unit_constant_product _ _ (b:ℝ) hh K hK
  simpa only[map_add,map_sub,PowerSeries.coeff_one,if_neg (by omega : K≠0),sub_zero] using hc

lemma auxiliary_descent_coefficient_budget (b:ℕ) (U:Fin 7→Series) (h0:zeroConstant U)
    (hfixed:formalFixedPoint (auxiliaryMajorantSystem b) U) (K:ℕ) (hK:1 ≤ K) :
    PowerSeries.coeff K (auxiliarySolutionUnit U 6)=(b:ℝ)*PowerSeries.coeff K
      (auxiliarySolutionUnit U 0*auxiliarySolutionUnit U 4*auxiliarySolutionUnit U 3*auxiliarySolutionUnit U 5) := by
  have hG:=(auxiliaryMajorant_fixed_equations b U h0 hfixed).2.2.2.2.2.2
  have hc:=coeff_of_unit_constant_product _ _ (b:ℝ) hG K hK
  simpa only[map_sub,PowerSeries.coeff_one,if_neg (by omega : K≠0),sub_zero] using hc
end WP.HigherOrder
