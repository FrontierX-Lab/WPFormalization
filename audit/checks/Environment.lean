import WPFormalization.Statements
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
open Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def projectConstant (n : Name) : Bool :=
  n.toString.startsWith "WP." || n.toString.startsWith "_private.WPFormalization." || n.toString == "PartialEquiv.codomainSubtype" || n.toString == "PartialEquiv.codomainSubtype_coe" || n.toString == "PartialEquiv.codomainSubtype_continuousOn" || n.toString == "PartialEquiv.codomainSubtype_continuousOn_symm" || n.toString == "PartialEquiv.codomainSubtype_image" || n.toString == "PartialEquiv.continuousOn_symm_of_compact"

-- Direct named paper-goal premises are tracked independently of the conclusion.
-- These formerly open goals now have actual producers; the exact examples
-- below are kernel-checked again on every fresh export.
example (P : WP.PsiTheory) : WP.HigherOrder.UniformRecursiveRemainderTarget P :=
  WP.HigherOrder.canonical_uniform_recursive_remainders P
example (P : WP.PsiTheory) : WP.HigherOrder.CanonicalAdjacentCompatibility P :=
  WP.HigherOrder.canonical_adjacent_compatibility P
example (P : WP.PsiTheory) : WP.HigherOrder.KernelFiniteData.PolynomialDependenceTarget P :=
  WP.HigherOrder.KernelFiniteData.canonical_polynomial_dependence P
example (P : WP.PsiTheory) : WP.HigherOrder.KernelFiniteData.ProfileBoundaryPolynomialTarget P :=
  WP.HigherOrder.KernelFiniteData.canonical_profile_boundary_polynomial P
example (P : WP.PsiTheory) : WP.HigherOrder.UniformRecursiveExpansionsTarget P :=
  WP.uniform_recursive_expansions P
example (P : WP.PsiTheory) (J k : Nat) (hk : k ≤ J) :
    WP.HigherOrder.KernelFiniteData.FiniteDataStage P J k :=
  WP.HigherOrder.KernelFiniteData.canonical_finite_data_stage P J k hk
private partial def explicitPaperPremises (e : Expr) : Array Name :=
  match e with
  | .forallE _ domain body _ =>
    let here := domain.getUsedConstants.filter (fun n =>
      n.toString == "WP.HigherOrder.UniformRecursiveRemainderTarget" ||
      n.toString == "WP.HigherOrder.CanonicalAdjacentCompatibility" ||
      n.toString == "WP.HigherOrder.KernelFiniteData.PolynomialDependenceTarget" ||
      n.toString == "WP.HigherOrder.KernelFiniteData.ProfileBoundaryPolynomialTarget" ||
      n.toString == "WP.HigherOrder.UniformRecursiveExpansionsTarget")
    here ++ explicitPaperPremises body
  | .letE _ _ _ body _ => explicitPaperPremises body
  | _ => #[]

-- Record direct project edges, including generated/private implementation constants.
-- Python computes their closure; Lean independently supplies the transitive axiom set.
run_cmd do
  let env := (← getEnv).setExporting false
  let mut records : Array Json := #[]
  let all := env.constants.toList.filter (fun (n, _) => projectConstant n)
  for (n, info) in all do
    let refs := info.getUsedConstantsAsSet.toArray.filter projectConstant
    let axs ← collectAxioms n
    let interfaces := info.type.getUsedConstants.filter (fun k =>
      k.toString == "WP.PsiTheory" || k.toString.startsWith "WP.External.")
    records := records.push <| Json.mkObj [
      ("name", toJson n.toString),
      ("directSorry", toJson ((info.value? (allowOpaque := true)).any (·.hasSorry) || info.type.hasSorry)),
      ("axioms", toJson (axs.map Name.toString)),
      ("projectReferences", toJson (refs.map Name.toString)),
      ("typeInterfaces", toJson (interfaces.map Name.toString)),
      ("paperPremises", toJson ((explicitPaperPremises info.type).map Name.toString))]
  IO.FS.writeFile "_out/audit/environment.json" (Json.pretty (Json.mkObj [("sourceHash", toJson "ae8216d53b3bcf01aaa223cf17be80df9c7d2b995574ba5edaa853487742c702"), ("records", toJson records)]))
  logInfo m!"Exported {records.size} project constants, their direct proof gaps, interfaces, and transitive axioms."
