import WPFormalization.HigherOrder.Triangular
import WPFormalization.HigherOrder.ComplexSmallComponentBounds
/-! Concrete complex scalar extension of the exact fixed-path algorithm.
Coefficientwise total sums are defined, but no summability, holomorphy,
path independence or Gevrey estimate for the hierarchy is asserted here. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.HigherOrder.ComplexCanonical
open PowerSeries
abbrev Series := PowerSeries ℂ

def shiftVariable (c : ℂ) : Series := PowerSeries.X * (1-C c*PowerSeries.X)⁻¹

def complexityShift (c : ℂ) (f : Series) : Series := f.subst (shiftVariable c)

def setCoeff (f : Series) (k : ℕ) (x : ℂ) : Series :=
  PowerSeries.mk (fun j => if j = k then x else PowerSeries.coeff j f)

def coefficientSum (f : ℕ → Series) : Series :=
  PowerSeries.mk (fun k => ∑' l : ℕ, PowerSeries.coeff k (f l))

def kernelA (R : ℂ → ℂ) (z : ℂ) : ℂ := WP.Analysis.regularizedKernel H R z 1/3

@[simp] theorem shiftVariable_constant (c : ℂ) : constantCoeff (shiftVariable c) = 0 := by
  simp [shiftVariable]

@[simp] theorem complexityShift_constant (c : ℂ) (f : Series) :
    constantCoeff (complexityShift c f) = constantCoeff f := by
  exact PowerSeries.constantCoeff_subst_of_constantCoeff_zero (shiftVariable_constant c) f

@[simp] theorem setCoeff_other (f : Series) (k j : ℕ) (x : ℂ) (h : j ≠ k) :
    PowerSeries.coeff j (setCoeff f k x) = PowerSeries.coeff j f := by simp [setCoeff,h]

@[simp] theorem setCoeff_constant (f : Series) (k : ℕ) (x : ℂ) (h : k ≠ 0) :
    constantCoeff (setCoeff f k x) = constantCoeff f := by
  simpa only [← coeff_zero_eq_constantCoeff] using setCoeff_other f k 0 x (Ne.symm h)

/-- Formal profile, cusp scalar and genus scalar at one already constructed order. -/
structure HierarchyJet where
  profile : List ℕ → Series
  cusp : ℕ → Series
  genus : ℕ → Series

/-- All three constant coefficients in Eq.C.13 are 1. -/
def baseJet : HierarchyJet := ⟨fun _ => 1, fun _ => 1, fun _ => 1⟩

/-- The coefficient b_d=(1/3)[z^(d-1)]barH, valid also at the critical endpoint. -/
def bCoeff (R : ℂ → ℂ) (Y : ℂ) (d : ℕ) : ℂ :=
  WP.Analysis.complexDilatonCoefficient R d Y

/-- Bounded-component W_{j,q}(d), not an arbitrary auxiliary coefficient. -/
def smallW (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) (j : ℕ) (d : List ℕ) : ℂ :=
  WP.Analysis.complexSmallW P R j d Y

/-- Exact formal ratio in Eq.C.14; r_*=2j+s is the complexity loss. -/
def ratioSeries (R : ℂ → ℂ) (Y : ℂ) (F : HierarchyJet) (p j s : ℕ) : Series :=
  let r := 2*j+s
  (C (kernelA R Y)*PowerSeries.X)^r *
    (∏ a ∈ Finset.range r,
      complexityShift (r-a) (F.cusp (p-s+a)) * (1-C ((r-a : ℕ) : ℂ)*PowerSeries.X)⁻¹) *
    ∏ b ∈ Finset.range j, F.genus (p+2*b)

/-- Merger contribution in Eq.C.15 with a distinguished first marking. -/
def mergerSeries (R : ℂ → ℂ) (Y : ℂ) (F : HierarchyJet) (t : ℕ) (d : List ℕ) : Series :=
  C (kernelA R Y)*shiftVariable 1*complexityShift 1 (F.cusp d.length) *
    ∑ j ∈ Finset.range d.length, C (2*(d[j]! : ℂ)+1) *
      coefficientSum (fun l =>
        if 1 ≤ t+d[j]!+l then
          C (WP.Analysis.complexWeightCoeff R l Y) * complexityShift 1 (F.profile ((t+d[j]!+l-1) :: d.eraseIdx j))
        else 0)

/-- Nonseparating contribution in Eq.C.15. -/
def nonseparatingSeries (R : ℂ → ℂ) (Y : ℂ) (F : HierarchyJet) (t : ℕ) (d : List ℕ) : Series :=
  C (2*kernelA R Y)*shiftVariable 1*complexityShift 1 (F.cusp (d.length+2))*F.genus (d.length+1) *
    coefficientSum (fun l => C (WP.Analysis.complexWeightCoeff R l Y) *
      ∑ u ∈ Finset.range (t+l-1),
        complexityShift 1 (F.profile (u :: (t+l-2-u) :: d)))

/-- Separating contribution in Eq.C.16. Only losses 2≤2j+s≤K are retained.
The bounded component is oriented once, as in the paper; no extra factor 1/2. -/
def separatingSeries (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) (F : HierarchyJet)
    (K t : ℕ) (d : List ℕ) : Series :=
  ∑ j ∈ Finset.range (K+1), ∑ I ∈ (Finset.range d.length).powerset,
    if Stable j (I.card+1) ∧ 2 ≤ 2*j+I.card ∧ 2*j+I.card ≤ K then
      ratioSeries R Y F (d.length+1) j I.card *
        coefficientSum (fun l => C (WP.Analysis.complexWeightCoeff R l Y) *
          ∑ u ∈ Finset.range (t+l-1),
            C (smallW P R Y j (u :: selectedNat d I)) *
              complexityShift (2*j+I.card)
                (F.profile ((t+l-2-u) :: selectedNat d ((Finset.range d.length) \ I))))
    else 0

/-- The exact order-K adjacent increment prescribed by Eq.C.17. -/
def adjacentCoefficient (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) (F : HierarchyJet)
    (K i : ℕ) (d : List ℕ) : ℂ :=
  let t := d[i]!
  let tail := d.eraseIdx i
  show ℂ from -(PowerSeries.coeff K (mergerSeries R Y F t tail + nonseparatingSeries R Y F t tail +
    separatingSeries P R Y F K t tail))

/-- Integrate adjacent increments along the fixed path allowed in Eq.C.17. -/
def profileAtOrder (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) (F : HierarchyJet) (K : ℕ) (d : List ℕ) : ℂ :=
  ∑ i ∈ Finset.range d.length, ∑ t ∈ Finset.range d[i]!,
    adjacentCoefficient P R Y F K i (beforeCoordinate d i t)

/-- Dilaton rule Eq.C.17, with child complexity h+1, hence shift c=-1. -/
def cuspSeries (R : ℂ → ℂ) (Y : ℂ) (profiles : List ℕ → Series) (p : ℕ) : Series :=
  C (kernelA R Y)⁻¹ * coefficientSum (fun d =>
    C (bCoeff R Y (d+1))*complexityShift (-1) (profiles ((d+1) :: List.replicate p 0)))

/-- KdV rule Eq.C.18 at p≥2. Scalar ratios here use already computed lower orders. -/
def genusSeries (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) (F : HierarchyJet)
    (profiles : List ℕ → Series) (K p : ℕ) : Series :=
  profiles (1 :: List.replicate (p-1) 0) -
    C 3 * ∑ j ∈ Finset.range (K+1), ∑ s ∈ Finset.range (p-1),
      if Stable j (s+2) ∧ 1 ≤ 2*j+s ∧ 2*j+s ≤ K then
        C ((Nat.choose (p-2) s : ℂ) * smallW P R Y j (List.replicate (s+2) 0)) *
          ratioSeries R Y F p j s
      else 0

/-- Exact descent at unchanged parent complexity, including the h+1 shift. -/
def descendGenus (cusps : ℕ → Series) (next : Series) (p : ℕ) : Series :=
  complexityShift (-1) next * cusps (p+2) * (cusps p)⁻¹

/-- Construct the next coefficient in the prescribed triangular order. -/
def nextJet (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) (K : ℕ) (F : HierarchyJet) : HierarchyJet :=
  let profiles := fun d => setCoeff (F.profile d) K (profileAtOrder P R Y F K d)
  let cusps := fun p => setCoeff (F.cusp p) K (PowerSeries.coeff K (cuspSeries R Y profiles p))
  let highGenus := fun p => setCoeff (F.genus p) K (PowerSeries.coeff K (genusSeries P R Y F profiles K p))
  let genus₁ := setCoeff (F.genus 1) K (PowerSeries.coeff K (descendGenus cusps (highGenus 2) 1))
  let genus₀ := setCoeff (F.genus 0) K (PowerSeries.coeff K (descendGenus cusps genus₁ 0))
  ⟨profiles, cusps, fun p => if p = 0 then genus₀ else if p = 1 then genus₁ else highGenus p⟩

/-- This is a Nat recursion, not a fixed-point assumption or unspecified coefficient family. -/
def hierarchyJet (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) : ℕ → HierarchyJet
  | 0 => baseJet
  | k+1 => nextJet P R Y (k+1) (hierarchyJet P R Y k)

/-- Canonical coefficients obtained from the exact order at which each is constructed. -/
def profileCoefficient (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) (d : List ℕ) (k : ℕ) : ℂ :=
  PowerSeries.coeff k ((hierarchyJet P R Y k).profile d)
def cuspCoefficient (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) (p k : ℕ) : ℂ :=
  PowerSeries.coeff k ((hierarchyJet P R Y k).cusp p)
def genusCoefficient (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) (p k : ℕ) : ℂ :=
  PowerSeries.coeff k ((hierarchyJet P R Y k).genus p)

/- Formal series of Eq.C.13. No assertion about convergence of this series. -/
def formalProfile (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) (d : List ℕ) : Series :=
  PowerSeries.mk (profileCoefficient P R Y d)
def formalCusp (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) (p : ℕ) : Series :=
  PowerSeries.mk (cuspCoefficient P R Y p)
def formalGenus (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) (p : ℕ) : Series :=
  PowerSeries.mk (genusCoefficient P R Y p)

@[simp] theorem profileCoefficient_zero (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) (d : List ℕ) :
    profileCoefficient P R Y d 0 = 1 := by simp [profileCoefficient,hierarchyJet,baseJet]
@[simp] theorem cuspCoefficient_zero (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) (p : ℕ) :
    cuspCoefficient P R Y p 0 = 1 := by simp [cuspCoefficient,hierarchyJet,baseJet]
@[simp] theorem genusCoefficient_zero (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) (p : ℕ) :
    genusCoefficient P R Y p 0 = 1 := by simp [genusCoefficient,hierarchyJet,baseJet]

@[simp] theorem formalProfile_constant (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) (d : List ℕ) :
    constantCoeff (formalProfile P R Y d) = 1 := by
  simp [formalProfile]
@[simp] theorem formalCusp_constant (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) (p : ℕ) :
    constantCoeff (formalCusp P R Y p) = 1 := by
  simp [formalCusp]
@[simp] theorem formalGenus_constant (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) (p : ℕ) :
    constantCoeff (formalGenus P R Y p) = 1 := by
  simp [formalGenus]

/-- A later stage cannot change a coefficient that has already been constructed. -/
theorem hierarchy_profile_stable (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) (d : List ℕ)
    (n k : ℕ) (hk : k ≤ n) :
    PowerSeries.coeff k ((hierarchyJet P R Y n).profile d) = profileCoefficient P R Y d k := by
  induction n with
  | zero =>
      have hk0 : k=0 := by omega
      subst k
      rfl
  | succ n ih =>
      by_cases h : k = n+1
      · subst k; rfl
      · have hkn : k ≤ n := by omega
        change PowerSeries.coeff k
          (setCoeff ((hierarchyJet P R Y n).profile d) (n+1)
            (profileAtOrder P R Y (hierarchyJet P R Y n) (n+1) d)) = _
        rw [setCoeff_other _ _ _ _ h]
        exact ih hkn

/-- Every constructed jet retains the unit normalization of all three series. -/
theorem hierarchy_unit_constants (P : PsiTheory) (R : ℂ → ℂ) (Y : ℂ) (n : ℕ) :
    (∀ d, constantCoeff ((hierarchyJet P R Y n).profile d) = 1) ∧
    (∀ p, constantCoeff ((hierarchyJet P R Y n).cusp p) = 1) ∧
    (∀ p, constantCoeff ((hierarchyJet P R Y n).genus p) = 1) := by
  induction n with
  | zero => simp [hierarchyJet,baseJet]
  | succ n ih =>
      constructor
      · intro d
        simpa [hierarchyJet,nextJet] using ih.1 d
      constructor
      · intro p
        simpa [hierarchyJet,nextJet] using ih.2.1 p
      · intro p
        by_cases hp₀ : p = 0
        · subst p
          simpa [hierarchyJet,nextJet] using ih.2.2 0
        · by_cases hp₁ : p = 1
          · subst p
            simpa [hierarchyJet,nextJet] using ih.2.2 1
          · simpa [hierarchyJet,nextJet,hp₀,hp₁] using ih.2.2 p


abbrev ofRealSeries : WP.HigherOrder.Series →+* Series := PowerSeries.map Complex.ofRealHom

@[simp] lemma ofRealSeries_coeff (f : WP.HigherOrder.Series) (n : ℕ) :
    PowerSeries.coeff n (ofRealSeries f)=((PowerSeries.coeff n f:ℝ):ℂ) :=
  PowerSeries.coeff_map Complex.ofRealHom n f

@[simp] lemma ofRealSeries_C (x : ℝ) : ofRealSeries (C x)=C (x:ℂ) :=
  PowerSeries.map_C Complex.ofRealHom x

@[simp] lemma ofRealSeries_X : ofRealSeries PowerSeries.X=PowerSeries.X :=
  PowerSeries.map_X Complex.ofRealHom

@[simp] lemma ofRealSeries_inv (f : WP.HigherOrder.Series) :
    ofRealSeries (f⁻¹)=(ofRealSeries f)⁻¹ := by
  have hc : PowerSeries.constantCoeff (ofRealSeries f)=((PowerSeries.constantCoeff f:ℝ):ℂ) :=
    by simpa only [← coeff_zero_eq_constantCoeff] using ofRealSeries_coeff f 0
  by_cases h : PowerSeries.constantCoeff f=0
  · rw [(PowerSeries.inv_eq_zero).mpr h,map_zero,(PowerSeries.inv_eq_zero).mpr (by simpa [h] using hc)]
  · apply (PowerSeries.eq_inv_iff_mul_eq_one (by rw [hc];exact_mod_cast h)).mpr
    rw [← map_mul,PowerSeries.inv_mul_cancel f h,map_one]

@[simp] lemma ofRealSeries_shiftVariable (c : ℝ) :
    ofRealSeries (WP.HigherOrder.shiftVariable c)=shiftVariable (c:ℂ) := by
  simp [WP.HigherOrder.shiftVariable,shiftVariable]

@[simp] lemma ofRealSeries_complexityShift (c : ℝ) (f : WP.HigherOrder.Series) :
    ofRealSeries (WP.HigherOrder.complexityShift c f)=complexityShift (c:ℂ) (ofRealSeries f) := by
  have hs := PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero
    (WP.HigherOrder.shiftVariable_constant c)) (h:=Complex.ofRealHom) f
  change ofRealSeries (f.subst (WP.HigherOrder.shiftVariable c))=
    (ofRealSeries f).subst (ofRealSeries (WP.HigherOrder.shiftVariable c)) at hs
  rw [ofRealSeries_shiftVariable] at hs
  exact hs

@[simp] lemma ofRealSeries_setCoeff (f : WP.HigherOrder.Series) (k : ℕ) (x : ℝ) :
    ofRealSeries (WP.HigherOrder.setCoeff f k x)=setCoeff (ofRealSeries f) k (x:ℂ) := by
  ext j
  by_cases h : j=k <;> simp [WP.HigherOrder.setCoeff,setCoeff,h]

/-- This identity preserves the total-sum convention. It is not a convergence assertion. -/
@[simp] lemma ofRealSeries_coefficientSum (f : ℕ → WP.HigherOrder.Series) :
    ofRealSeries (WP.HigherOrder.coefficientSum f)=coefficientSum (fun l=>ofRealSeries (f l)) := by
  ext k
  simp only [ofRealSeries_coeff,WP.HigherOrder.coefficientSum_coeff,coefficientSum,
    PowerSeries.coeff_mk,Complex.ofReal_tsum]

def ofRealJet (F : WP.HigherOrder.HierarchyJet) : HierarchyJet :=
  ⟨fun d=>ofRealSeries (F.profile d),fun p=>ofRealSeries (F.cusp p),fun p=>ofRealSeries (F.genus p)⟩

section ScalarExtension
variable (P : PsiTheory) (R : ℂ → ℂ) (Y : ℝ)
variable (hA : kernelA R (Y:ℂ)=(A Y:ℂ))
variable (hw : ∀ l,WP.Analysis.complexWeightCoeff R l (Y:ℂ)=(weight Y l:ℂ))
variable (hb : ∀ d,bCoeff R (Y:ℂ) d=(WP.HigherOrder.bCoeff Y d:ℂ))
variable (hsmall : ∀ g d,smallW P R (Y:ℂ) g d=(WP.HigherOrder.smallW P Y g d:ℂ))

include hA in
lemma ratioSeries_ofReal (F : WP.HigherOrder.HierarchyJet) (p j s : ℕ) :
    ofRealSeries (WP.HigherOrder.ratioSeries Y F p j s)=ratioSeries R (Y:ℂ) (ofRealJet F) p j s := by
  simp [WP.HigherOrder.ratioSeries,ratioSeries,ofRealJet,hA]

include hA hw in
lemma mergerSeries_ofReal (F : WP.HigherOrder.HierarchyJet) (t : ℕ) (d : List ℕ) :
    ofRealSeries (WP.HigherOrder.mergerSeries Y F t d)=mergerSeries R (Y:ℂ) (ofRealJet F) t d := by
  simp [WP.HigherOrder.mergerSeries,mergerSeries,ofRealJet,hA,hw,apply_ite]

include hA hw in
lemma nonseparatingSeries_ofReal (F : WP.HigherOrder.HierarchyJet) (t : ℕ) (d : List ℕ) :
    ofRealSeries (WP.HigherOrder.nonseparatingSeries Y F t d)=nonseparatingSeries R (Y:ℂ) (ofRealJet F) t d := by
  simp [WP.HigherOrder.nonseparatingSeries,nonseparatingSeries,ofRealJet,hA,hw]

include hA hw hsmall in
lemma separatingSeries_ofReal (F : WP.HigherOrder.HierarchyJet) (K t : ℕ) (d : List ℕ) :
    ofRealSeries (WP.HigherOrder.separatingSeries P Y F K t d)=separatingSeries P R (Y:ℂ) (ofRealJet F) K t d := by
  simp [WP.HigherOrder.separatingSeries,separatingSeries,ratioSeries_ofReal R Y hA,ofRealJet,hw,hsmall,apply_ite]

include hA hw hsmall in
lemma adjacentCoefficient_ofReal (F : WP.HigherOrder.HierarchyJet) (K i : ℕ) (d : List ℕ) :
    ((WP.HigherOrder.adjacentCoefficient P Y F K i d:ℝ):ℂ)=adjacentCoefficient P R (Y:ℂ) (ofRealJet F) K i d := by
  unfold WP.HigherOrder.adjacentCoefficient adjacentCoefficient
  dsimp only
  rw [← mergerSeries_ofReal R Y hA hw,← nonseparatingSeries_ofReal R Y hA hw,
    ← separatingSeries_ofReal P R Y hA hw hsmall,← map_add,← map_add,ofRealSeries_coeff]
  simp only [Complex.ofReal_neg]

include hA hw hsmall in
lemma profileAtOrder_ofReal (F : WP.HigherOrder.HierarchyJet) (K : ℕ) (d : List ℕ) :
    ((WP.HigherOrder.profileAtOrder P Y F K d:ℝ):ℂ)=profileAtOrder P R (Y:ℂ) (ofRealJet F) K d := by
  simp [WP.HigherOrder.profileAtOrder,profileAtOrder,
    adjacentCoefficient_ofReal P R Y hA hw hsmall]

include hA hb in
lemma cuspSeries_ofReal (profiles : List ℕ → WP.HigherOrder.Series) (p : ℕ) :
    ofRealSeries (WP.HigherOrder.cuspSeries Y profiles p)=
      cuspSeries R (Y:ℂ) (fun d=>ofRealSeries (profiles d)) p := by
  simp [WP.HigherOrder.cuspSeries,cuspSeries,hA,hb]

include hA hsmall in
lemma genusSeries_ofReal (F : WP.HigherOrder.HierarchyJet) (profiles : List ℕ → WP.HigherOrder.Series) (K p : ℕ) :
    ofRealSeries (WP.HigherOrder.genusSeries P Y F profiles K p)=
      genusSeries P R (Y:ℂ) (ofRealJet F) (fun d=>ofRealSeries (profiles d)) K p := by
  simp [WP.HigherOrder.genusSeries,genusSeries,ratioSeries_ofReal R Y hA,hsmall,apply_ite]

lemma descendGenus_ofReal (cusps : ℕ → WP.HigherOrder.Series) (next : WP.HigherOrder.Series) (p : ℕ) :
    ofRealSeries (WP.HigherOrder.descendGenus cusps next p)=
      descendGenus (fun q=>ofRealSeries (cusps q)) (ofRealSeries next) p := by
  simp [WP.HigherOrder.descendGenus,descendGenus]

include hA hw hb hsmall in
lemma nextJet_ofReal (F : WP.HigherOrder.HierarchyJet) (K : ℕ) :
    ofRealJet (WP.HigherOrder.nextJet P Y K F)=nextJet P R (Y:ℂ) K (ofRealJet F) := by
  let rp := fun d=>WP.HigherOrder.setCoeff (F.profile d) K (WP.HigherOrder.profileAtOrder P Y F K d)
  let cp := fun d=>setCoeff ((ofRealJet F).profile d) K (profileAtOrder P R (Y:ℂ) (ofRealJet F) K d)
  have hp : (fun d=>ofRealSeries (rp d))=cp := by
    funext d
    simp only [rp,cp,ofRealSeries_setCoeff,profileAtOrder_ofReal P R Y hA hw hsmall,ofRealJet]
  let rc := fun p=>WP.HigherOrder.setCoeff (F.cusp p) K (PowerSeries.coeff K (WP.HigherOrder.cuspSeries Y rp p))
  let cc := fun p=>setCoeff ((ofRealJet F).cusp p) K (PowerSeries.coeff K (cuspSeries R (Y:ℂ) cp p))
  have hc : (fun p=>ofRealSeries (rc p))=cc := by
    funext p
    dsimp only [rc,cc]
    rw [ofRealSeries_setCoeff,←ofRealSeries_coeff,cuspSeries_ofReal R Y hA hb,hp]
    rfl
  let rg := fun p=>WP.HigherOrder.setCoeff (F.genus p) K (PowerSeries.coeff K (WP.HigherOrder.genusSeries P Y F rp K p))
  let cg := fun p=>setCoeff ((ofRealJet F).genus p) K (PowerSeries.coeff K (genusSeries P R (Y:ℂ) (ofRealJet F) cp K p))
  have hg : (fun p=>ofRealSeries (rg p))=cg := by
    funext p
    dsimp only [rg,cg]
    rw [ofRealSeries_setCoeff,←ofRealSeries_coeff,genusSeries_ofReal P R Y hA hsmall,hp]
    rfl
  let rg₁ := WP.HigherOrder.setCoeff (F.genus 1) K (PowerSeries.coeff K (WP.HigherOrder.descendGenus rc (rg 2) 1))
  let cg₁ := setCoeff ((ofRealJet F).genus 1) K (PowerSeries.coeff K (descendGenus cc (cg 2) 1))
  have hg₁ : ofRealSeries rg₁=cg₁ := by
    dsimp only [rg₁,cg₁]
    rw [ofRealSeries_setCoeff,←ofRealSeries_coeff,descendGenus_ofReal,hc]
    change setCoeff (ofRealSeries (F.genus 1)) K (PowerSeries.coeff K
      (descendGenus cc ((fun p=>ofRealSeries (rg p)) 2) 1))=_
    rw [hg]
    rfl
  let rg₀ := WP.HigherOrder.setCoeff (F.genus 0) K (PowerSeries.coeff K (WP.HigherOrder.descendGenus rc rg₁ 0))
  let cg₀ := setCoeff ((ofRealJet F).genus 0) K (PowerSeries.coeff K (descendGenus cc cg₁ 0))
  have hg₀ : ofRealSeries rg₀=cg₀ := by
    dsimp only [rg₀,cg₀]
    rw [ofRealSeries_setCoeff,←ofRealSeries_coeff,descendGenus_ofReal,hc,hg₁]
    rfl
  change (⟨fun d=>ofRealSeries (rp d),fun p=>ofRealSeries (rc p),
    fun p=>ofRealSeries (if p=0 then rg₀ else if p=1 then rg₁ else rg p)⟩ : HierarchyJet)=
      ⟨cp,cc,fun p=>if p=0 then cg₀ else if p=1 then cg₁ else cg p⟩
  rw [hp,hc]
  congr 1
  funext p
  by_cases h0 : p=0
  · simpa only [ite_eq_left h0] using hg₀
  · by_cases h1 : p=1
    · simpa only [ite_eq_right h0,ite_eq_left h1] using hg₁
    · simpa only [ite_eq_right h0,ite_eq_right h1] using congrFun hg p

include hA hw hb hsmall in
lemma hierarchyJet_ofReal (n : ℕ) :
    ofRealJet (WP.HigherOrder.hierarchyJet P Y n)=hierarchyJet P R (Y:ℂ) n := by
  induction n with
  | zero => simp [WP.HigherOrder.hierarchyJet,hierarchyJet,WP.HigherOrder.baseJet,baseJet,ofRealJet]
  | succ n ih =>
    rw [WP.HigherOrder.hierarchyJet,hierarchyJet,nextJet_ofReal P R Y hA hw hb hsmall,ih]

include hA hw hb hsmall in
lemma canonicalCoefficients_ofReal (k : ℕ) :
    (∀ d,profileCoefficient P R (Y:ℂ) d k=(WP.HigherOrder.profileCoefficient P Y d k:ℂ)) ∧
    (∀ p,cuspCoefficient P R (Y:ℂ) p k=(WP.HigherOrder.cuspCoefficient P Y p k:ℂ)) ∧
    (∀ p,genusCoefficient P R (Y:ℂ) p k=(WP.HigherOrder.genusCoefficient P Y p k:ℂ)) := by
  have hjet := (hierarchyJet_ofReal P R Y hA hw hb hsmall k).symm
  constructor
  · intro d
    simp only [profileCoefficient,hjet,ofRealJet,ofRealSeries_coeff,WP.HigherOrder.profileCoefficient]
  constructor
  · intro p
    simp only [cuspCoefficient,hjet,ofRealJet,ofRealSeries_coeff,WP.HigherOrder.cuspCoefficient]
  · intro p
    simp only [genusCoefficient,hjet,ofRealJet,ofRealSeries_coeff,WP.HigherOrder.genusCoefficient]

include hA hw hb hsmall in
lemma formalSeries_ofReal :
    (∀ d,formalProfile P R (Y:ℂ) d=ofRealSeries (WP.HigherOrder.formalProfile P Y d)) ∧
    (∀ p,formalCusp P R (Y:ℂ) p=ofRealSeries (WP.HigherOrder.formalCusp P Y p)) ∧
    (∀ p,formalGenus P R (Y:ℂ) p=ofRealSeries (WP.HigherOrder.formalGenus P Y p)) := by
  constructor
  · intro d
    ext k
    simpa only [formalProfile,WP.HigherOrder.formalProfile,PowerSeries.coeff_mk,ofRealSeries_coeff] using
      (canonicalCoefficients_ofReal P R Y hA hw hb hsmall k).1 d
  constructor
  · intro p
    ext k
    simpa only [formalCusp,WP.HigherOrder.formalCusp,PowerSeries.coeff_mk,ofRealSeries_coeff] using
      (canonicalCoefficients_ofReal P R Y hA hw hb hsmall k).2.1 p
  · intro p
    ext k
    simpa only [formalGenus,WP.HigherOrder.formalGenus,PowerSeries.coeff_mk,ofRealSeries_coeff] using
      (canonicalCoefficients_ofReal P R Y hA hw hb hsmall k).2.2 p

end ScalarExtension
open Set

lemma actual_kernel_inputs_restrict_closed (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R Ω) (hR0 : R (y₀:ℂ)=0)
    (hraw : ∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ))
    (hunit : ∀ z∈Ω,WP.Analysis.complexAUnit z≠0) (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) :
    kernelA R (Y:ℂ)=(A Y:ℂ) ∧
    (∀ l,WP.Analysis.complexWeightCoeff R l (Y:ℂ)=(weight Y l:ℂ)) ∧
    (∀ d,bCoeff R (Y:ℂ) d=(WP.HigherOrder.bCoeff Y d:ℂ)) ∧
    (∀ (P : PsiTheory) g d,smallW P R (Y:ℂ) g d=(WP.HigherOrder.smallW P Y g d:ℂ)) := by
  have hc := WP.Analysis.normalized_coefficients_holomorphic_on_common_domain Ω hΩ hcover R hR hR0 hraw hunit
  have hKr : ∀ n : ℕ,∀ y∈Icc (0:ℝ) y₀,WP.Analysis.regularizedKernelCoeff K R n (y:ℂ)=WP.coeff (barK y) n :=
    fun n y hy=>((hc n).2.2 y hy).1
  have hHr : ∀ n : ℕ,∀ y∈Icc (0:ℝ) y₀,WP.Analysis.regularizedKernelCoeff H R n (y:ℂ)=WP.coeff (barH y) n :=
    fun n y hy=>((hc n).2.2 y hy).2
  have hclosed := WP.Analysis.normalized_complex_kernels_restrict_closed Ω hΩ hcover R hR hR0 hraw hunit
  constructor
  · unfold kernelA
    rw [(hclosed Y hY 1).2]
    have hr : barH Y 1=((barH Y 1).re:ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using WP.Analysis.barH_one_im_zero Y
    rw [hr]
    simp only [A,Complex.ofReal_div,Complex.ofReal_ofNat]
  constructor
  · intro l
    exact WP.Analysis.complexWeightCoeff_restrict_closed R hKr l Y hY
  constructor
  · intro d
    unfold bCoeff
    rw [WP.Analysis.complexDilatonCoefficient_restrict_closed R hHr d Y hY]
    congr 1
    by_cases hd : d=0
    · subst d
      simp [WP.canonicalDilatonCoefficient,WP.HigherOrder.bCoeff]
    · simp [WP.canonicalDilatonCoefficient,WP.HigherOrder.bCoeff,hd,show 1≤d by omega]
  · intro P g d
    unfold smallW WP.Analysis.complexSmallW WP.HigherOrder.smallW
    rw [WP.Analysis.complexNormalized_restrict_closed P R hKr g d Y hY]
    push_cast
    rfl

lemma canonical_coefficients_restrict_closed (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R Ω) (hR0 : R (y₀:ℂ)=0)
    (hraw : ∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ))
    (hunit : ∀ z∈Ω,WP.Analysis.complexAUnit z≠0)
    (P : PsiTheory) (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) (k : ℕ) :
    (∀ d,profileCoefficient P R (Y:ℂ) d k=(WP.HigherOrder.profileCoefficient P Y d k:ℂ)) ∧
    (∀ p,cuspCoefficient P R (Y:ℂ) p k=(WP.HigherOrder.cuspCoefficient P Y p k:ℂ)) ∧
    (∀ p,genusCoefficient P R (Y:ℂ) p k=(WP.HigherOrder.genusCoefficient P Y p k:ℂ)) := by
  obtain ⟨hA,hw,hb,hs⟩ := actual_kernel_inputs_restrict_closed Ω hΩ hcover R hR hR0 hraw hunit Y hY
  exact canonicalCoefficients_ofReal P R Y hA hw hb (hs P) k

lemma canonical_formal_series_restrict_closed (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R Ω) (hR0 : R (y₀:ℂ)=0)
    (hraw : ∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ))
    (hunit : ∀ z∈Ω,WP.Analysis.complexAUnit z≠0)
    (P : PsiTheory) (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) :
    (∀ d,formalProfile P R (Y:ℂ) d=ofRealSeries (WP.HigherOrder.formalProfile P Y d)) ∧
    (∀ p,formalCusp P R (Y:ℂ) p=ofRealSeries (WP.HigherOrder.formalCusp P Y p)) ∧
    (∀ p,formalGenus P R (Y:ℂ) p=ofRealSeries (WP.HigherOrder.formalGenus P Y p)) := by
  obtain ⟨hA,hw,hb,hs⟩ := actual_kernel_inputs_restrict_closed Ω hΩ hcover R hR hR0 hraw hunit Y hY
  exact formalSeries_ofReal P R Y hA hw hb (hs P)

lemma kernelA_analyticOnNhd (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R Ω) (hR0 : R (y₀:ℂ)=0)
    (hraw : ∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ))
    (hunit : ∀ z∈Ω,WP.Analysis.complexAUnit z≠0) :
    AnalyticOnNhd ℂ (kernelA R) Ω := by
  have hj := WP.Analysis.normalized_kernel_jets_holomorphic_on_common_domain Ω hΩ hcover R hR hR0 hraw hunit
  intro z hz
  have hh := ((hj 0 1).2.1 z hz).div_const (c:=(3:ℂ))
  have he : (fun w=>WP.Analysis.regularizedKernel H R w 1/3)=kernelA R := rfl
  simp only [WP.Analysis.regularizedKernelJet,ite_true] at hh
  rw [he] at hh
  exact hh

lemma exists_convex_kernelA_uniform_control (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hcover : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R Ω) (hR0 : R (y₀:ℂ)=0)
    (hraw : ∀ Y∈Ico (0:ℝ) y₀,R (Y:ℂ)=(r Y:ℂ))
    (hunit : ∀ z∈Ω,WP.Analysis.complexAUnit z≠0) :
    ∃ (V : Set ℂ) (M : ℝ),IsOpen V ∧ Convex ℝ V ∧
      (∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈V) ∧ V⊆Ω ∧ 0<M ∧
      AnalyticOnNhd ℂ (kernelA R) V ∧
      ∀ z∈closure V,kernelA R z≠0 ∧ ‖kernelA R z‖≤M ∧ ‖(kernelA R z)⁻¹‖≤M := by
  have hA := kernelA_analyticOnNhd Ω hΩ hcover R hR hR0 hraw hunit
  let S : Set ℂ := Complex.ofReal '' Icc (0:ℝ) y₀
  have hS : IsCompact S := isCompact_Icc.image Complex.continuous_ofReal
  have hSU : S⊆Ω := by rintro z ⟨Y,hY,rfl⟩;exact hcover Y hY
  have hAc : ∀ z∈Ω,∀ w : ℂ,ContinuousAt (fun p : ℂ × ℂ=>kernelA R p.1) (z,w) :=
    fun z hz w=>by
      simpa only [Function.comp_def] using (hA z hz).continuousAt.comp continuous_fst.continuousAt
  have hzero : ∀ z∈S,∀ w∈({0}:Set ℂ),kernelA R z≠0 := by
    rintro z ⟨Y,hY,rfl⟩ w hw
    rw [(actual_kernel_inputs_restrict_closed Ω hΩ hcover R hR hR0 hraw hunit Y hY).1]
    have hpos : 0<A Y := div_pos (WP.Analysis.barH_one_re_pos Y hY) (by norm_num)
    exact_mod_cast hpos.ne'
  obtain ⟨W,hW,hSW,hWC,hWΩ,M,hM,hbound⟩ :=
    WP.Analysis.compact_nonzero_parameter_uniform_bound Ω S {0} hΩ hS isCompact_singleton
      (singleton_nonempty 0) hSU (fun z _=>kernelA R z) (fun z _=>kernelA R z) hAc hAc hzero
  have hcoverW : ∀ Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈W := fun Y hY=>hSW ⟨Y,hY,rfl⟩
  obtain ⟨V,hV,hVc,hcoverV,hVW⟩ := WP.Analysis.exists_convex_physical_neighborhood W hW hcoverW
  have hVΩ : V⊆Ω := hVW.trans (subset_closure.trans hWΩ)
  refine ⟨V,M,hV,hVc,hcoverV,hVΩ,hM,hA.mono hVΩ,?_⟩
  intro z hz
  have hb := hbound z (closure_mono hVW hz) 0 (mem_singleton 0)
  exact ⟨hb.1,hb.2.2,hb.2.1⟩

end WP.HigherOrder.ComplexCanonical
