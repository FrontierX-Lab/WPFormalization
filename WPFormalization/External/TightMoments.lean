import WPFormalization.External.WeilPeterssonGeometry
import WPFormalization.Tight.ComplexMoments

/-! Classical tight volumes and the universal moment transform.

Source TIGHT-BZ: Budd--Zonneveld, arXiv:2307.04708 (11 July 2023),
Section 1.2 / Eq.(7)-(8), Eq.(21),(23), and Proposition 12 / Eq.(69)-(70),
with descendant generating series Eq.(65), external times Eq.(68), and the
classical dilaton resummation. Published J. Math. Phys. 65 (2024), 092302,
DOI 10.1063/5.0192711. The displayed finite moment polynomial is the
coefficientwise protected-insertion consequence of Proposition 12, not an
asymptotic statement from the paper being formalized.

Only Taylor coefficients for compactly supported nonnegative finite weights
are imported. No global real-series convergence or Y-dependent shifted
identity is a field. Every such specialization and convergence statement
must be proved locally. No concrete geometric realization is asserted.

Phase two must construct the simple cycles, capping maps and tight locus on
actual hyperbolic moduli, prove measurability, and formalize this pre-existing
Budd--Zonneveld transform. No new probabilistic/large-genus result is assumed.
-/
noncomputable section
universe u v
namespace WP.External
open MeasureTheory Set Filter
open scoped Topology

/-- Unoriented simple geometric cycles, modulo reparametrization, and their
free-homotopy class after filling precisely the k unprotected boundaries.
Boundary cycles are included; length-zero cusp boundaries use the standard
limit convention. Construction of these geometric objects is phase two. -/
structure ProtectedCycleGeometry {P:PsiTheory} (G:WeilPeterssonGeometry.{u,v} P) where
  SimpleCycle : ∀(g n:ℕ)(L:Fin n→ℝ),G.Moduli g n L→Type v
  length : ∀g n L X,SimpleCycle g n L X→ℝ
  length_nonneg : ∀g n L X γ,0≤length g n L X γ
  boundary : ∀g n L X,Fin n→SimpleCycle g n L X
  boundary_injective : ∀g n L X,Function.Injective (boundary g n L X)
  boundary_length : ∀g n L X i,length g n L X (boundary g n L X i)=L i
  CappedClass : ∀(g p k:ℕ)(L:Fin p→ℝ)(K:Fin k→ℝ),
    G.Moduli g (p+k) (Fin.append L K)→Type v
  cap : ∀g p k L K X,SimpleCycle g (p+k) (Fin.append L K) X→CappedClass g p k L K X
  nullClass : ∀g p k L K X,CappedClass g p k L K X
  free_boundary_null : ∀g p k L K X j,
    cap g p k L K X (boundary g (p+k) (Fin.append L K) X (Fin.natAdd p j))=
      nullClass g p k L K X

/-- BZ Section 1.2: each protected boundary is the unique simple cycle in
its capped free-homotopy class having length at most that boundary length. -/
def tightLocus {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
    (C:ProtectedCycleGeometry G) (g p k:ℕ) (L:Fin p→ℝ) (K:Fin k→ℝ):
    Set (G.Moduli g (p+k) (Fin.append L K)):=
  {X | ∀i:Fin p,∀γ:C.SimpleCycle g (p+k) (Fin.append L K) X,
    C.cap g p k L K X γ=
      C.cap g p k L K X (C.boundary g (p+k) (Fin.append L K) X (Fin.castAdd k i))→
    C.length g (p+k) (Fin.append L K) X γ≤L i→
      γ=C.boundary g (p+k) (Fin.append L K) X (Fin.castAdd k i)}

/-- The locus is defined by its geometric predicate. Measurability is the
classical open-locus fact in BZ Section 1.2, immediately following Eq.(7). -/
structure TightRegions {P:PsiTheory} (G:WeilPeterssonGeometry.{u,v} P) where
  cycles : ProtectedCycleGeometry G
  measurable_region : ∀g p k L K,MeasurableSet (tightLocus cycles g p k L K)

def TightRegions.region {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
    (T:TightRegions G) (g p k:ℕ) (L:Fin p→ℝ) (K:Fin k→ℝ):
    Set (G.Moduli g (p+k) (Fin.append L K)):=tightLocus T.cycles g p k L K

def tightVolume {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
    (T:TightRegions G) (g p k:ℕ) (L:Fin p→ℝ) (K:Fin k→ℝ):ℝ:=
  (G.wpMeasure g (p+k) (Fin.append L K) (T.region g p k L K)).toReal

def weightedTightCoefficient {P:PsiTheory} {G:WeilPeterssonGeometry.{u,v} P}
    (T:TightRegions G) (g p k:ℕ) (L:Fin p→ℝ)
    (μ:Measure ℝ) [IsFiniteMeasure μ]:ℝ:=
  (∫K:Fin k→ℝ,tightVolume T g p k L K ∂Measure.pi (fun _:Fin k=>μ))/(k.factorial:ℝ)

/-- Entire I0(L sqrt(2r)) kernel, written without a square-root branch. -/
def classicalI0Kernel (L:ℝ) (r:ℂ):ℂ:=
  ∑'j:ℕ,((L:ℂ)^2*r/2)^j/(j.factorial:ℂ)^2

def classicalWeightedKernel (μ:Measure ℝ) (r:ℂ):ℂ:=
  ∫L:ℝ,classicalI0Kernel L r ∂μ

/-- Budd--Zonneveld Eq.(21), expressed by the actual entire X function. -/
def classicalRootKernel (μ:Measure ℝ) (r t:ℂ):ℂ:=
  X ((2*Real.pi^2:ℝ)*r)/(2*Real.pi^2:ℝ)-t*classicalWeightedKernel μ r

def classicalMomentGerm (μ:Measure ℝ) (R:ℂ→ℂ) (j:ℕ) (t:ℂ):ℂ:=
  iteratedDeriv (j+1) (fun r=>classicalRootKernel μ r t) (R t)

/- Only formal/Taylor coefficients of the classical universal transform.
No global real generating-series equality or convergence is assumed.
The compact weight support makes every source coefficient integral finite. -/
@[blueprint "ext:tight-transform"]
structure BuddZonneveldTransform {P:PsiTheory} (G:WeilPeterssonGeometry.{u,v} P)
    (T:TightRegions G) where
  weighted_taylor : ∀(g p:ℕ),Stable g p→∀L:Fin p→ℝ,(∀i,0≤L i)→
    ∀(μ:Measure ℝ),∀[IsFiniteMeasure μ],
    (∃B:ℝ,0≤B ∧ μ (Icc (0:ℝ) B)ᶜ=0)→
    ∀(R:ℂ→ℂ),AnalyticAt ℂ R 0→R 0=0→
    (∀ᶠt:ℂ in 𝓝 0,classicalRootKernel μ (R t) t=0)→∀k:ℕ,
    weightedTightCoefficient T g p k L μ=
      (WP.coeff (fun t=>WP.TightMoments.complexMomentPolynomial P g p
        (fun j=>classicalMomentGerm μ R j t) L) k).re
end WP.External
