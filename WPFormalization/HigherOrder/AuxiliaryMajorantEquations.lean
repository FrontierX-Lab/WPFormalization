import WPFormalization.HigherOrder.PolynomialMajorantSystem
import WPFormalization.HigherOrder.PolynomialSubstitution
import WPFormalization.HigherOrder.RationalMajorantAlgebra
/-! The seven genuine formal-series equations of the polynomial auxiliary majorant, extracted through the proved finite polynomial-evaluation bridge. The V, cusp inverse W and loss tail Z are identified with their actual rational expressions. All assertions follow algebraically from the concrete formal fixed point. -/
set_option maxHeartbeats 1600000
noncomputable section
namespace WP.HigherOrder
open PowerSeries

def auxiliarySolutionUnit (U:Fin 7→Series) (i:Fin 7) : Series := 1+U i
def auxiliarySolutionLossArgument (b:ℕ) (U:Fin 7→Series) : Series :=
  PowerSeries.C (b:ℝ)*PowerSeries.X*(auxiliarySolutionUnit U 0)^2*auxiliarySolutionUnit U 3*
    (1+auxiliarySolutionUnit U 4+auxiliarySolutionUnit U 6)
lemma auxiliaryMajorantFixedPoint_eval (b:ℕ) (U:Fin 7→Series) (h0:zeroConstant U)
    (hfixed:formalFixedPoint (auxiliaryMajorantSystem b) U) (i:Fin 7) :
    U i=MvPolynomial.eval₂ PowerSeries.C (Majorant.argumentSeries U)
      ((auxiliaryMajorantPolynomial b i).map (Nat.castRingHom ℝ)) := by
  ext j
  exact (hfixed i j).trans (Majorant.substitutionCoeff_polynomial _ U h0 j)

lemma auxiliaryMajorant_fixed_equations (b:ℕ) (U:Fin 7→Series) (h0:zeroConstant U)
    (hfixed:formalFixedPoint (auxiliaryMajorantSystem b) U) :
    let V:=auxiliarySolutionUnit U 0
    let Z:=U 1
    let E:=auxiliarySolutionUnit U 2
    let C:=auxiliarySolutionUnit U 3
    let H:=auxiliarySolutionUnit U 4
    let W:=auxiliarySolutionUnit U 5
    let G:=auxiliarySolutionUnit U 6
    let Q:=auxiliarySolutionLossArgument b U
    V=1+PowerSeries.X*V ∧ Z=Q^2+Q*Z ∧
    E=1+PowerSeries.C (b:ℝ)*PowerSeries.X*V^3*E*C*(1+H+G)+PowerSeries.C (b:ℝ)*V*E*Z ∧
    C=1+PowerSeries.C (b:ℝ)*(V*E-1) ∧
    H=1+PowerSeries.C (b:ℝ)*(E-1)+PowerSeries.C (b:ℝ)*(Q+Z) ∧
    W=1+(C-1)*W ∧ G=1+PowerSeries.C (b:ℝ)*(V*H*C*W-1) := by
  have h (i:Fin 7):=auxiliaryMajorantFixedPoint_eval b U h0 hfixed i
  have hV:=h 0
  have hZ:=h 1
  have hE:=h 2
  have hC:=h 3
  have hH:=h 4
  have hW:=h 5
  have hG:=h 6
  simp only[auxiliaryMajorantPolynomial,auxiliaryLossArgument,auxiliaryUnit,auxiliaryVariable,
    auxiliaryFourProductTail] at hV hZ hE hC hH hW hG
  simp[Majorant.argumentSeries,MvPolynomial.eval₂_map] at hV hZ hE hC hH hW hG
  have hb:(b:Series)=PowerSeries.C (b:ℝ):=(map_natCast (PowerSeries.C:ℝ→+*Series) b).symm
  simp only[hb] at hV hZ hE hC hH hW hG
  dsimp only[auxiliarySolutionUnit,auxiliarySolutionLossArgument]
  constructor
  · linear_combination hV
  constructor
  · linear_combination hZ
  constructor
  · linear_combination hE
  constructor
  · linear_combination hC
  constructor
  · linear_combination hH
  constructor
  · linear_combination hW
  · linear_combination hG
lemma auxiliarySolutionUnit_nonnegative (U:Fin 7→Series)
    (hU:∀i j,0 ≤ PowerSeries.coeff j (U i)) (i:Fin 7) (j:ℕ) :
    0 ≤ PowerSeries.coeff j (auxiliarySolutionUnit U i) := by
  rw[auxiliarySolutionUnit,map_add]
  exact add_nonneg (by rw[PowerSeries.coeff_one];split_ifs<;>norm_num) (hU i j)
lemma auxiliaryMajorant_resolvents (b:ℕ) (U:Fin 7→Series) (h0:zeroConstant U)
    (hfixed:formalFixedPoint (auxiliaryMajorantSystem b) U) :
    auxiliarySolutionUnit U 0=geometricMajorant ∧
      auxiliarySolutionUnit U 5=(2-auxiliarySolutionUnit U 3)⁻¹ ∧
      U 1=(auxiliarySolutionLossArgument b U)^2*(1-auxiliarySolutionLossArgument b U)⁻¹ := by
  obtain ⟨hV,hZ,hE,hC,hH,hW,hG⟩:=auxiliaryMajorant_fixed_equations b U h0 hfixed
  have hC0:PowerSeries.constantCoeff (auxiliarySolutionUnit U 3)=1:=by
    have hz:PowerSeries.constantCoeff (U 3)=0:=by simpa only[←PowerSeries.coeff_zero_eq_constantCoeff] using h0 3
    simp[auxiliarySolutionUnit,hz]
  have hQ0:PowerSeries.constantCoeff (auxiliarySolutionLossArgument b U)=0:=by
    simp[auxiliarySolutionLossArgument]
  exact ⟨geometricMajorant_eq_of_equation _ hV,inverse_cusp_majorant_eq_of_equation _ _ hC0 hW,
    loss_majorant_eq_of_equation _ _ hQ0 hZ⟩
end WP.HigherOrder
