import WPFormalization.Volumes.GrowingBoundaryTheorem
import WPFormalization.Coefficients.InstantonCorrespondence
import WPFormalization.Analysis.WPInstantonContour
import WPFormalization.JT.StringStatement
import WPFormalization.JT.Abel
import WPFormalization.Analysis.JTCriticalReplacement
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Meta.Basic
import Lean.Elab.Command

set_option autoImplicit false
noncomputable section
universe u v
namespace StatementExamples
open WP WP.External WP.Analysis WP.Coefficients WP.JT
open Set Filter MeasureTheory Asymptotics
open scoped Topology

-- A single constant precedes every genus and every nonnegative length vector.
theorem all_lengths (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, 1 ≤ g → ∀ L : Fin n → ℝ,
      (∀ i, 0 ≤ L i) →
      0 ≤ 1-wpVolume G g n L /
        (cuspVolume G g n * ∏ i, (if L i=0 then 1 else Real.sinh (L i/2)/(L i/2))) ∧
      1-wpVolume G g n L /
        (cuspVolume G g n * ∏ i, (if L i=0 then 1 else Real.sinh (L i/2)/(L i/2))) ≤
        C/(g:ℝ) * ∑ i, (L i)^2 :=
  (growing_boundary_factor P G n hn).1

-- The denominator cannot silently vanish on the stable positive-genus range.
theorem cusp_volume_nonzero (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P)
    (g n : ℕ) (hg : 1 ≤ g) (hn : 1 ≤ n) : cuspVolume G g n ≠ 0 := by
  obtain ⟨C,hC,h⟩ := all_lengths P G n hn
  have he := (h g hg (fun _ => 0) (fun _ => le_rfl)).2
  intro hz
  change wpVolume G g n (fun _ => 0) = 0 at hz
  norm_num [cuspVolume, hz] at he

theorem growing_lengths (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P)
    (n : ℕ) (hn : 1 ≤ n) (L : ℕ → Fin n → ℝ)
    (hL : ∀ g i, 0 ≤ L g i)
    (hsmall : ∀ i, Tendsto (fun g : ℕ => L g i / Real.sqrt (g:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun g : ℕ => wpVolume G g n (L g) /
      (Real.sqrt (2/Real.pi) * (4*Real.pi^2)^(2*g+n-3) *
        Real.Gamma (2*(g:ℝ)+n-5/2) *
        ∏ i, (if L g i=0 then 1 else Real.sinh (L g i/2)/(L g i/2))))
      atTop (𝓝 1) :=
  ((growing_boundary_factor P G n hn).2 L hL hsmall).2

-- Negative edge energies do not become zero through a real square root.
theorem critical_negative_energy : edgeEnergy y₀ < 0 := by
  exact div_neg_of_neg_of_pos (neg_neg_of_pos y₀_pos) (sq_pos_of_pos Real.pi_pos)

theorem string_at_negative_energy_nonzero : stringBesselEnergy (edgeEnergy y₀) < 0 := by
  rw [stringBesselEnergy_edge]
  change -xCritical / (2*Real.pi^2) < 0
  exact div_neg_of_neg_of_pos (neg_neg_of_pos xCritical_pos_parameter) (by positivity)

theorem string_literal (Y weight : ℝ) :
    stringBesselEnergy (-Y/Real.pi^2)+weight=0 ↔ XR Y=2*Real.pi^2*weight :=
  string_equation_iff Y weight

theorem genus_amplitude (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P)
    (g : ℕ) (hg : 2 ≤ g) (weight : ℂ) (hweight : ‖2*(Real.pi:ℂ)^2*weight‖ < xCritical) :
    HasSum (fun n : ℕ => (cuspVolume G g n:ℂ)*weight^n/(n.factorial:ℂ))
      ((2*(Real.pi:ℂ)^2)^(3*g-3)*Phi P g (2*(Real.pi:ℂ)^2*weight)) :=
  geometric_defect_amplitude_hasSum P G g hg weight hweight

theorem critical_branch_endpoint : edgeEnergy (inverseY xCritical) = -y₀/Real.pi^2 := by
  rw [inverseY_eq_of_root xCritical y₀ le_rfl rfl]
  rfl

-- Literal original integral, with an independent integrability conclusion.
theorem abel_literal (Y q : ℝ) (hq : 0 ≤ q) :
    IntervalIntegrable
      (fun u => besselI0Energy u / Real.sqrt (-Y/Real.pi^2+q-u))
      volume (-Y/Real.pi^2) (-Y/Real.pi^2+q) ∧
    (1/(4*Real.pi)) *
      (∫ u in (-Y/Real.pi^2)..(-Y/Real.pi^2+q),
        besselI0Energy u / Real.sqrt (-Y/Real.pi^2+q-u)) =
      Real.sqrt q/(2*Real.pi) *
        (K (Y:ℂ) ((-2*Real.pi^2*q:ℝ):ℂ)).re := by
  constructor
  · exact abel_intervalIntegrable besselI0Energy besselI0Energy_continuous
      (-Y/Real.pi^2) q hq
  · exact abel_density_kernel Y q hq

theorem abel_zero_window (Y : ℝ) :
    (1/(4*Real.pi)) *
      (∫ u in (-Y/Real.pi^2)..(-Y/Real.pi^2),
        besselI0Energy u / Real.sqrt (-Y/Real.pi^2-u)) = 0 := by simp

theorem undeformed_density (E : ℝ) (hE : 0 ≤ E) :
    (1/(4*Real.pi)) * (∫ u in (0:ℝ)..E, besselI0Energy u/Real.sqrt (E-u)) =
      Real.sinh (2*Real.pi*Real.sqrt E)/(4*Real.pi^2) := by
  simpa only [abelDensity, edgeEnergy, neg_zero, zero_div] using
    abel_density_undeformed E hE

theorem critical_edge_with_endpoint :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ q ∈ Icc (0:ℝ) δ,
      |abelDensity y₀ (-y₀/Real.pi^2+q) -
        (Real.pi*criticalB/3)*q^(3/2:ℝ)| ≤ C*q^(5/2:ℝ) :=
  abel_density_critical_bound

theorem actual_circle_limit (g k : ℕ) (hg : 1 ≤ g) (hk : k ≤ 3*g-2) :
    Tendsto (fun R : ℝ => (Real.Gamma (complexity g 1):ℂ) *
      ((2*(Real.pi:ℂ)*Complex.I)⁻¹ *
        ∮ w in C(0,R), w^(2*k)/(instantonAction w)^(complexity g 1)))
      (𝓝[>] (0:ℝ)) (𝓝 ((2*(4:ℝ)^(-(k:ℤ))*oneBoundaryBracketModel g k:ℝ):ℂ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [instanton_small_circle_normalization g k hg hk] with R hR
  simpa only [normalizedCircleIntegral, instantonIntegrand, div_eq_mul_inv, inv_pow] using hR.symm

theorem nonzero_residue_probe : residueAtZero (instantonIntegrand 1 1) = (3/2:ℂ) := by
  have h := instanton_residue 1 1 0 (by norm_num)
  simpa only [unscaledCoeff_zero, pow_zero, pow_one, mul_one, Complex.ofReal_one] using h

-- One and the same analytic function is the true fixed-circle expression
-- off zero and has the stated Taylor coefficient at its removable origin.
theorem contour_expression_coefficient (g k : ℕ) (hg : 1 ≤ g) (hk : k ≤ 3*g-2) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ R ∈ Ioo (0:ℝ) ε, ∀ L : ℂ, L ≠ 0 →
        F L = (Real.Gamma (complexity g 1):ℂ)/L *
          ∮ w in C(0,R), Complex.exp (L*w)/(w*(instantonAction w)^(complexity g 1))) ∧
      ((2*k+1).factorial:ℂ) * WP.coeff F (2*k) =
        (2*(Real.pi:ℂ)*Complex.I) *
          ((2*(4:ℝ)^(-(k:ℤ))*oneBoundaryBracketModel g k:ℝ):ℂ) := by
  have hh : Odd (complexity g 1) := by
    refine ⟨g-1,?_⟩
    unfold complexity
    omega
  refine ⟨instantonRawContourAmplitude (complexity g 1),
    instantonRawContourAmplitude_analytic _,
    instantonRawContourAmplitude_eq_circle _ hh,?_⟩
  calc
    _ = (2*(Real.pi:ℂ)*Complex.I) *
        ((Real.Gamma (complexity g 1):ℂ) *
          residueAtZero (instantonIntegrand (complexity g 1) k)) := by
      rw [instantonRawContourAmplitude_coefficient _ _ _ (instanton_degree_identity g k hg hk)]
      ring
    _ = _ := by rw [instanton_residue_normalization g k hg hk]

theorem original_stationary_equation (g k : ℕ) (hg : 1 ≤ g)
    (t : ℝ) (ht : t ∈ Ioo 0 Real.pi) :
    deriv (instantonSaddleExponent g k) (t/(2*Real.pi)) = 0 ↔
      t^2*Real.sin t/(Real.sin t-t*Real.cos t) = (2*(k:ℝ)+1)/(2*(g:ℝ)-1) := by
  simpa only [densityTrig, trigDen] using instanton_stationary_iff_trig g k hg t ht

theorem action_three_remainders :
    ((fun Y => (xCritical-XR Y)/((criticalB/2)*(y₀-Y)^2)-1)
      =O[𝓝[<] y₀] (fun Y => y₀-Y)) ∧
    ((fun Y => Z Y/((2*Real.sqrt 3*criticalB/5)*(y₀-Y)^(5/2:ℝ))-1)
      =O[𝓝[<] y₀] (fun Y => y₀-Y)) ∧
    ((fun Y => Z Y/(((2:ℝ)^(9/4:ℝ)*Real.sqrt 3/(5*criticalB^(1/4:ℝ)))*
        (xCritical-XR Y)^(5/4:ℝ))-1)
      =O[𝓝[<] y₀] (fun Y => Real.sqrt (xCritical-XR Y))) := by
  simpa only [Real.rpow_eq_pow] using
    And.intro jt_critical_action.1 (And.intro jt_critical_action.2.1 jt_critical_action.2.2.1)

-- The same exponential correction survives multiplication by the remaining
-- expansion factor; there is no hidden replacement of that factor or g limit.
theorem replacement_with_common_factor (p : ℕ) (hp : 1 ≤ p) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ g : ℕ, 1 ≤ g → ∀ Y ∈ Ico (0:ℝ) y₀, y₀-Y ≤ ε → ∀ F : ℝ,
        ∃ e : ℝ, |e| ≤ C*(g:ℝ)*Real.sqrt (xCritical-XR Y) ∧
          markedModel g p Y*F = (jtCriticalMarkedModel g p Y*F)*Real.exp e := by
  obtain ⟨C,ε,hC,hε,h⟩ := jt_critical_action.2.2.2 p hp
  refine ⟨C,ε,hC,hε,?_⟩
  intro g hg Y hY hsmall F
  obtain ⟨e,he,heq⟩ := h g hg Y hY hsmall
  refine ⟨e,he,?_⟩
  rw [heq]
  ring

#print axioms all_lengths
#print axioms cusp_volume_nonzero
#print axioms growing_lengths
#print axioms string_at_negative_energy_nonzero
#print axioms genus_amplitude
#print axioms abel_literal
#print axioms critical_edge_with_endpoint
#print axioms actual_circle_limit
#print axioms nonzero_residue_probe
#print axioms contour_expression_coefficient
#print axioms original_stationary_equation
#print axioms action_three_remainders
#print axioms replacement_with_common_factor

end StatementExamples

open Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- Do not discard private, imported, or non-WP constant dependencies.
run_cmd do
  let env := (← getEnv).setExporting false
  let seeds := #[``WP.growing_boundary_factor, ``WP.Coefficients.instanton_correspondence,
    ``WP.JT.string_normalization, ``WP.JT.jt_abel_critical_edge,
    ``WP.Analysis.jt_critical_action,
    ``StatementExamples.contour_expression_coefficient]
  let mut todo := seeds
  let mut seen : NameSet := {}
  let mut roots : Array String := #[]
  let mut axioms : Array String := #[]
  let mut seedTypes : Array Json := #[]
  for n in seeds do
    let some ci := env.find? n | throwError "Missing seed {n}"
    let fmt ← Lean.Elab.Command.liftTermElabM <| Meta.ppExpr ci.type
    seedTypes := seedTypes.push <| Json.mkObj [
      ("name",toJson n.toString), ("type",toJson fmt.pretty)]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "Missing constant {n}"
    if ci matches .axiomInfo _ then axioms := axioms.push n.toString
    if ci.type.hasSorry || (ci.value? (allowOpaque := true)).any (·.hasSorry) then
      roots := roots.push n.toString
    todo := todo ++ ci.getUsedConstantsAsSet.toArray
  IO.FS.writeFile "_out/audit/statement-examples.json" <| Json.pretty <| Json.mkObj [
    ("visitedConstants",toJson seen.size), ("directSorry",toJson roots),
    ("axioms",toJson axioms), ("seedTypes",toJson seedTypes)]
  logInfo m!"Statement examples dependency closure: {seen.size} constants; roots {roots}; axioms {axioms}"
