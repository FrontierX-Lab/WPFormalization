import WPFormalization.Statements.Majorant
import Mathlib.Algebra.MvPolynomial.PDeriv
set_option maxHeartbeats 1600000
/-! A seven-component polynomial analytic majorant with variable order V,Z,E,C,H,W,G. Nonnegative coefficients, zero constants, strict triangularity and finite-support convergence are proved locally. Its formal solution and exponential coefficient bound use only the existing generic analytic implicit-function input through Lemma C.2. This is not the completed canonical-hierarchy induction. -/
noncomputable section
namespace WP.HigherOrder
abbrev AuxiliaryMajorantPolynomial := MvPolynomial (Option (Fin 7)) ℕ

def auxiliaryVariable (i:Fin 7) : AuxiliaryMajorantPolynomial := MvPolynomial.X (some i)
def auxiliaryUnit (i:Fin 7) : AuxiliaryMajorantPolynomial := 1+auxiliaryVariable i

def auxiliaryLossArgument (b:ℕ) : AuxiliaryMajorantPolynomial :=
  MvPolynomial.C b*MvPolynomial.X none*(auxiliaryUnit 0)^2*auxiliaryUnit 3*
    (1+auxiliaryUnit 4+auxiliaryUnit 6)

def auxiliaryFourProductTail : AuxiliaryMajorantPolynomial :=
  let v:=auxiliaryVariable 0
  let h:=auxiliaryVariable 4
  let c:=auxiliaryVariable 3
  let w:=auxiliaryVariable 5
  (v+h+c+w)+(v*h+v*c+v*w+h*c+h*w+c*w)+
    (v*h*c+v*h*w+v*c*w+h*c*w)+v*h*c*w

def auxiliaryMajorantPolynomial (b:ℕ) (i:Fin 7) : AuxiliaryMajorantPolynomial :=
  let t:=MvPolynomial.X none
  let V:=auxiliaryUnit 0
  let Z:=auxiliaryVariable 1
  let E:=auxiliaryUnit 2
  let C:=auxiliaryUnit 3
  let H:=auxiliaryUnit 4
  let G:=auxiliaryUnit 6
  let Q:=auxiliaryLossArgument b
  match i.val with
  | 0=>t*V
  | 1=>Q^2+Q*Z
  | 2=>MvPolynomial.C b*t*V^3*E*C*(1+H+G)+MvPolynomial.C b*V*E*Z
  | 3=>MvPolynomial.C b*(auxiliaryVariable 0+auxiliaryVariable 2+auxiliaryVariable 0*auxiliaryVariable 2)
  | 4=>MvPolynomial.C b*auxiliaryVariable 2+MvPolynomial.C b*(Q+Z)
  | 5=>auxiliaryVariable 3*auxiliaryUnit 5
  | _=>MvPolynomial.C b*auxiliaryFourProductTail

def auxiliaryMajorantSystem (b:ℕ) (i:Fin 7) : MvPowerSeries (Option (Fin 7)) ℝ :=
  ((auxiliaryMajorantPolynomial b i).map (Nat.castRingHom ℝ):MvPowerSeries (Option (Fin 7)) ℝ)

lemma auxiliaryMajorantSystem_nonnegative (b:ℕ) (i:Fin 7) (α:Option (Fin 7)→₀ℕ) :
    0 ≤ MvPowerSeries.coeff α (auxiliaryMajorantSystem b i) := by
  rw[auxiliaryMajorantSystem,MvPolynomial.coeff_coe,MvPolynomial.coeff_map]
  exact Nat.cast_nonneg _

lemma auxiliaryMajorantPolynomial_zero (b:ℕ) (i:Fin 7) :
    (auxiliaryMajorantPolynomial b i).coeff 0=0 := by
  change MvPolynomial.constantCoeff (auxiliaryMajorantPolynomial b i)=0
  fin_cases i <;> simp[auxiliaryMajorantPolynomial,auxiliaryLossArgument,auxiliaryUnit,
    auxiliaryVariable,auxiliaryFourProductTail]

lemma auxiliaryMajorantSystem_zero (b:ℕ) (i:Fin 7) :
    MvPowerSeries.coeff 0 (auxiliaryMajorantSystem b i)=0 := by
  rw[auxiliaryMajorantSystem,MvPolynomial.coeff_coe,MvPolynomial.coeff_map,auxiliaryMajorantPolynomial_zero]
  simp

lemma auxiliaryMajorantPolynomial_triangular (b:ℕ) (i l:Fin 7) (hil:i.val ≤ l.val) :
    (auxiliaryMajorantPolynomial b i).coeff (Finsupp.single (some l) 1)=0 := by
  have hd:MvPolynomial.constantCoeff (MvPolynomial.pderiv (some l) (auxiliaryMajorantPolynomial b i))=
      (auxiliaryMajorantPolynomial b i).coeff (Finsupp.single (some l) 1):=by
    rw[MvPolynomial.constantCoeff_eq,MvPolynomial.coeff_pderiv]
    simp
  rw[←hd]
  fin_cases i <;> fin_cases l
  all_goals norm_num at hil
  all_goals simp[auxiliaryMajorantPolynomial,auxiliaryLossArgument,auxiliaryUnit,
    auxiliaryVariable,auxiliaryFourProductTail,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow]

lemma auxiliaryMajorantSystem_triangular (b:ℕ) (i l:Fin 7) (hil:i.val ≤ l.val) :
    MvPowerSeries.coeff (Finsupp.single (some l) 1) (auxiliaryMajorantSystem b i)=0 := by
  rw[auxiliaryMajorantSystem,MvPolynomial.coeff_coe,MvPolynomial.coeff_map,
    auxiliaryMajorantPolynomial_triangular b i l hil]
  simp

lemma auxiliaryMajorantSystem_convergent (b:ℕ) : ∃r:ℝ,0<r ∧ ∀i:Fin 7,
    Summable (fun α:Option (Fin 7)→₀ℕ=>MvPowerSeries.coeff α (auxiliaryMajorantSystem b i)*r^(multiDegree α)) := by
  refine ⟨1,by norm_num,?_⟩
  intro i
  simp only[one_pow,mul_one,auxiliaryMajorantSystem,MvPolynomial.coeff_coe]
  apply summable_of_hasFiniteSupport
  have hs:Function.support (fun α=>((auxiliaryMajorantPolynomial b i).map (Nat.castRingHom ℝ)).coeff α)⊆
      (((auxiliaryMajorantPolynomial b i).map (Nat.castRingHom ℝ)).support:Set (Option (Fin 7)→₀ℕ)):=by
    intro α hα
    apply MvPolynomial.mem_support_iff.mpr
    exact hα
  exact (((auxiliaryMajorantPolynomial b i).map (Nat.castRingHom ℝ)).support.finite_toSet).subset hs
lemma auxiliaryMajorantSolution_exists (b:ℕ) :
    ∃U:Fin 7→PowerSeries ℝ,zeroConstant U ∧ formalFixedPoint (auxiliaryMajorantSystem b) U ∧
      (∀i j,0 ≤ PowerSeries.coeff j (U i)) ∧
      ∃C B:ℝ,0<C ∧ 0<B ∧ ∀i j,PowerSeries.coeff j (U i) ≤ C*B^j := by
  obtain ⟨U,h0,hfixed,hunique,hpos,C,ρ,hC,hρ,hbound,hsum,hdom⟩:=
    analytic_majorant 7 (auxiliaryMajorantSystem b) (auxiliaryMajorantSystem_nonnegative b)
      (auxiliaryMajorantSystem_zero b) (auxiliaryMajorantSystem_triangular b)
      (auxiliaryMajorantSystem_convergent b)
  exact ⟨U,h0,hfixed,hpos,C,ρ⁻¹,hC,inv_pos.mpr hρ,hbound⟩
end WP.HigherOrder
