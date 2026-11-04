# Paper targets and formal statements

This table lists every registered paper target: 92 results and derivations (including all 57 numbered theorems, lemmas, propositions, and corollaries), plus 36 definitions.
Each entry gives the paper statement, its Lean declarations, and their source locations. See [Classical results](CLASSICAL_RESULTS.md) for the premises of conditional results and [Remaining infrastructure](INFRASTRUCTURE.md) for the outstanding work.

Lean excerpts reproduce the source declarations or definitions, omitting theorem proof bodies. Namespaces, implicit parameters, and notation come from the linked module.
Click a declaration name to read its full source.

## Additional definitions and representations

<a id="target-def:stable"></a>

### Stable pairs and degree conventions

**Paper statement** (PDF p. 3):

Genus and cusp/boundary counts are nonnegative integers with $2g-2+n>0$. For a degree tuple of length n set $h=2g-2+n$, $N=3g-3+n$, $D=\sum_i d_i$, $m=N-D$. Negative-degree, wrong-dimension and unstable recursion factors vanish; the stated genus-zero initial derivatives are kept separate.

**Lean declarations** (defined):

- [WP.Stable](../WPFormalization/Statements/Basic.lean#L16)
- [WP.complexity](../WPFormalization/Statements/Basic.lean#L25)
- [WP.dimension](../WPFormalization/Statements/Basic.lean#L31)
- [WP.totalDegree](../WPFormalization/Statements/Basic.lean#L37)
- [WP.deficit](../WPFormalization/Statements/Basic.lean#L43)

<details>
<summary>View formal statements</summary>

[WP.Stable](../WPFormalization/Statements/Basic.lean#L16):

```lean
def Stable (g n : ℕ) : Prop := 2 < 2 * g + n
```

[WP.complexity](../WPFormalization/Statements/Basic.lean#L25):

```lean
def complexity (g n : ℕ) : ℕ := 2 * g + n - 2
```

[WP.dimension](../WPFormalization/Statements/Basic.lean#L31):

```lean
def dimension (g n : ℕ) : ℕ := 3 * g + n - 3
```

[WP.totalDegree](../WPFormalization/Statements/Basic.lean#L37):

```lean
def totalDegree (d : List ℕ) : ℕ := d.sum
```

[WP.deficit](../WPFormalization/Statements/Basic.lean#L43):

```lean
def deficit (g : ℕ) (d : List ℕ) : ℕ := dimension g d.length - d.sum
```

</details>

<a id="target-def:wp-volume"></a>

### Geometric Weil--Petersson volume

**Paper statement** (PDF p. 3):

For a stable pair and nonnegative labeled boundary lengths, use the orbifold convention $V_{g,n}(L)=\frac1{(3g-3+n)!}\int_{\mathcal M_{g,n}(L)}\omega_{WP}^{3g-3+n}$ and $V_{g,n}=V_{g,n}(0,\ldots,0)$. A zero-length boundary is a cusp. These are geometric volumes, not definitions by a scalar recurrence.

**Lean declarations** (defined under classical premises):

- [WP.External.WeilPeterssonGeometry](../WPFormalization/External/WeilPeterssonGeometry.lean#L25)
- [WP.External.wpVolume](../WPFormalization/External/WeilPeterssonGeometry.lean#L41)

<details>
<summary>View formal statements</summary>

[WP.External.WeilPeterssonGeometry](../WPFormalization/External/WeilPeterssonGeometry.lean#L25):

```lean
structure WeilPeterssonGeometry (P : PsiTheory) extends IntersectionRealization.{u} P where
  Moduli : (g n : ℕ) → (Fin n → ℝ) → Type v
  [measurable : ∀ g n L, MeasurableSpace (Moduli g n L)]
  wpMeasure : ∀ g n L, Measure (Moduli g n L)
  finite_volume : ∀ (g n : ℕ) (L : Fin n → ℝ), Stable g n →
    (∀ i, 0 ≤ L i) → wpMeasure g n L Set.univ ≠ ⊤
  volume_polynomial : ∀ (g n : ℕ) (L : Fin n → ℝ), Stable g n → (∀ i, 0 ≤ L i) →
    (wpMeasure g n L Set.univ).toReal =
      ∑ d ∈ degreeTuples g n, geometricBracket (classes g n) d *
        ∏ i, L i^(2*d i)/((4 : ℝ)^(d i)*(2*d i+1).factorial)
```

[WP.External.wpVolume](../WPFormalization/External/WeilPeterssonGeometry.lean#L41):

```lean
def wpVolume {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (g n : ℕ) (L : Fin n → ℝ) : ℝ := (G.wpMeasure g n L Set.univ).toReal
```

</details>

<a id="target-def:intersections"></a>

### Geometric intersection classes and brackets

**Paper statement** (PDF p. 19):

On the Deligne–Mumford compactification, $\psi_i$ is the cotangent class and $\kappa_1$ is the logarithmic Mumford class. For stable (g,n), nonnegative degrees and $m=3g-3+n-|\mathbf d|\ge0$, define $[\tau_{d_1}\cdots\tau_{d_n}]_{g,n}=\prod_i(2d_i+1)!!\,4^{|\mathbf d|}(2\pi^2)^m\int_{\overline{\mathcal M}_{g,n}}\kappa_1^m\prod_i\psi_i^{d_i}/m!$. Angle brackets are the unweighted pure psi integrals. The geometric identification $[\omega_{WP}]=2\pi^2\kappa_1$ is an external theorem, not a definition.

**Lean declarations** (defined under classical premises):

- [WP.External.DMClasses](../WPFormalization/External/IntersectionTheory.lean#L21)
- [WP.External.mixedIntegral](../WPFormalization/External/IntersectionTheory.lean#L37)
- [WP.External.geometricBracket](../WPFormalization/External/IntersectionTheory.lean#L41)

<details>
<summary>View formal statements</summary>

[WP.External.DMClasses](../WPFormalization/External/IntersectionTheory.lean#L21):

```lean
structure DMClasses (g n : ℕ) where
  Carrier : Type u
  [ring : CommRing Carrier]
  [algebra : Algebra ℝ Carrier]
  psi : Fin n → Carrier
  kappa₁ : Carrier
  wpClass : Carrier
  integral : Carrier →ₗ[ℝ] ℝ
  wolpert : wpClass = (2*Real.pi^2) • kappa₁
  dimension_vanish : ∀ (m : ℕ) (d : Fin n → ℕ),
    m + ∑ i, d i ≠ dimension g n →
    integral (kappa₁^m * ∏ i, psi i^(d i)) = 0
```

[WP.External.mixedIntegral](../WPFormalization/External/IntersectionTheory.lean#L37):

```lean
def mixedIntegral {g n : ℕ} (D : DMClasses.{u} g n) (m : ℕ) (d : Fin n → ℕ) : ℝ :=
  D.integral (D.kappa₁^m * ∏ i, D.psi i^(d i))
```

[WP.External.geometricBracket](../WPFormalization/External/IntersectionTheory.lean#L41):

```lean
def geometricBracket {g n : ℕ} (D : DMClasses.{u} g n) (d : Fin n → ℕ) : ℝ :=
  if Stable g n ∧ ∑ i, d i ≤ dimension g n then
    let m := dimension g n - ∑ i, d i
    (∏ i, (oddFactorial (d i) : ℝ)) * (4 : ℝ)^(∑ i, d i) *
      (2*Real.pi^2)^m * (mixedIntegral D m d / m.factorial)
  else 0
```

</details>

<a id="target-def:bessel"></a>

### Genus-zero analytic function and inverse branch

**Paper statement** (PDF p. 4):

Define the entire function $X(y)=\sum_{j\ge0}(-1)^jy^{j+1}/(j!(j+1)!)=\sqrt y J_1(2\sqrt y)$ and $a=X^{\prime}$. Let $y_0=j_{0,1}^2/4$ be its first positive derivative zero, $x_c=X(y_0)$, and let Y(x) denote the inverse branch taking $[0,x_c)$ to $[0,y_0)$. Kernel properties establish that this inverse and the stationary root are well defined.

**Lean declarations** (defined):

- [WP.X](../WPFormalization/Statements/Basic.lean#L58)
- [WP.XR](../WPFormalization/Statements/Basic.lean#L64)
- [WP.a](../WPFormalization/Statements/Basic.lean#L70)
- [WP.y₀](../WPFormalization/Statements/Basic.lean#L77)
- [WP.xCritical](../WPFormalization/Statements/Basic.lean#L83)
- [WP.inverseY](../WPFormalization/Statements/Basic.lean#L89)
- [WP.bessel_branches](../WPFormalization/Analysis/BesselBranches.lean#L61)
- [WP.besselJ₀](../WPFormalization/Statements/Basic.lean#L224)
- [WP.besselJ₁](../WPFormalization/Statements/Basic.lean#L230)
- [WP.firstJ₀Zero](../WPFormalization/Statements/Basic.lean#L237)
- [WP.bessel_dictionary](../WPFormalization/Analysis/BesselDictionary.lean#L104)

<details>
<summary>View formal statements</summary>

[WP.X](../WPFormalization/Statements/Basic.lean#L58):

```lean
def X (z : ℂ) : ℂ := ∑' j : ℕ, (-1 : ℂ)^j * z^(j+1) / (j.factorial * (j+1).factorial)
```

[WP.XR](../WPFormalization/Statements/Basic.lean#L64):

```lean
def XR (y : ℝ) : ℝ := (X y).re
```

[WP.a](../WPFormalization/Statements/Basic.lean#L70):

```lean
def a (y : ℝ) : ℝ := (deriv X y).re
```

[WP.y₀](../WPFormalization/Statements/Basic.lean#L77):

```lean
def y₀ : ℝ := sInf {y : ℝ | 0 < y ∧ deriv X y = 0}
```

[WP.xCritical](../WPFormalization/Statements/Basic.lean#L83):

```lean
def xCritical : ℝ := XR y₀
```

[WP.inverseY](../WPFormalization/Statements/Basic.lean#L89):

```lean
def inverseY (x : ℝ) : ℝ := sInf {y : ℝ | y ≤ y₀ ∧ XR y = x}
```

[WP.bessel_branches](../WPFormalization/Analysis/BesselBranches.lean#L61):

```lean
theorem bessel_branches :
    Differentiable ℂ X ∧ 0 < y₀ ∧ y₀ < 3/2 ∧ deriv X y₀ = 0 ∧
    (∀ y ∈ Ico 0 y₀, 0 < a y) ∧
    (∀ x ∈ Ico 0 xCritical, inverseY x ∈ Ico 0 y₀ ∧ XR (inverseY x) = x)
```

[WP.besselJ₀](../WPFormalization/Statements/Basic.lean#L224):

```lean
def besselJ₀ (z : ℂ) : ℂ := ∑' j : ℕ, (-1 : ℂ)^j*(z/2)^(2*j)/(j.factorial : ℂ)^2
```

[WP.besselJ₁](../WPFormalization/Statements/Basic.lean#L230):

```lean
def besselJ₁ (z : ℂ) : ℂ := ∑' j : ℕ, (-1 : ℂ)^j*(z/2)^(2*j+1)/
  ((j.factorial : ℂ)*(j+1).factorial)
```

[WP.firstJ₀Zero](../WPFormalization/Statements/Basic.lean#L237):

```lean
def firstJ₀Zero : ℝ := sInf {t : ℝ | 0 < t ∧ besselJ₀ t = 0}
```

[WP.bessel_dictionary](../WPFormalization/Analysis/BesselDictionary.lean#L104):

```lean
theorem bessel_dictionary (z : ℂ) :
    X z = Complex.sqrt z*besselJ₁ (2*Complex.sqrt z) ∧
    deriv X z = besselJ₀ (2*Complex.sqrt z) ∧ y₀ = firstJ₀Zero^2/4
```

</details>

## Introduction and main results

<a id="target-eq:intro-Phi"></a>

### Paper 1.1: Normalized cusp generating function

**Paper statement** (PDF p. 4):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\Phi_g(x)=\sum_{n\ge0}\frac{V_{g,n}}{(2\pi^2)^{3g-3+n}}\,\frac{x^n}{n!},
$$

**Lean declarations** (defined under classical premises):

- [WP.Phi](../WPFormalization/Statements/Volumes.lean#L25)
- [WP.volumeModel](../WPFormalization/Statements/Volumes.lean#L17)

<details>
<summary>View formal statements</summary>

[WP.Phi](../WPFormalization/Statements/Volumes.lean#L25):

```lean
def Phi (P : PsiTheory) (g : ℕ) (x : ℂ) : ℂ :=
  ∑' n : ℕ, (volumeModel P g n : ℂ) / (2*Real.pi^2 : ℂ)^(dimension g n) * x^n/n.factorial
```

[WP.volumeModel](../WPFormalization/Statements/Volumes.lean#L17):

```lean
def volumeModel (P : PsiTheory) (g n : ℕ) : ℝ := mixedBracket P g (List.replicate n 0)
```

</details>

<a id="target-eq:SP1"></a>

### Paper 1.2: Stationary root T

**Paper statement** (PDF p. 4):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\int_Y^T\frac{X'(v)}{\sqrt{T-v}}\,\mathrm{d}v=0.
$$

**Lean declarations** (defined):

- [WP.T](../WPFormalization/Statements/ParameterDefinitions.lean#L22)
- [WP.stationaryIntegral](../WPFormalization/Statements/ParameterDefinitions.lean#L14)
- [WP.stationary_root](../WPFormalization/Statements/Parameter.lean#L21)

<details>
<summary>View formal statements</summary>

[WP.T](../WPFormalization/Statements/ParameterDefinitions.lean#L22):

```lean
def T (Y : ℝ) : ℝ := if Y = y₀ then y₀ else sInf {t : ℝ | y₀ < t ∧ stationaryIntegral Y t = 0}
```

[WP.stationaryIntegral](../WPFormalization/Statements/ParameterDefinitions.lean#L14):

```lean
def stationaryIntegral (Y T : ℝ) : ℝ := ∫ v in Y..T, a v / Real.sqrt (T-v)
```

[WP.stationary_root](../WPFormalization/Statements/Parameter.lean#L21):

```lean
theorem stationary_root (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    T Y ∈ Set.Ioc y₀ (Real.pi^2/4) ∧ stationaryIntegral Y (T Y) = 0 ∧
    (∀ t ∈ Set.Ioc y₀ (Real.pi^2/4), stationaryIntegral Y t = 0 → t = T Y) ∧
    r Y = 2*Delta Y
```

</details>

<a id="target-eq:SP2"></a>

### Paper 1.3: Action and cusp density

**Paper statement** (PDF p. 4):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
I(Y)=\int_Y^{T(Y)} X'(v)\sqrt{T(Y)-v}\,\mathrm{d}v,
 \qquad
 \lambda(Y)=\frac{2X(Y)\sqrt{\Delta(Y)}}{I(Y)}.
$$

**Lean declarations** (defined):

- [WP.Delta](../WPFormalization/Statements/ParameterDefinitions.lean#L28)
- [WP.action](../WPFormalization/Statements/ParameterDefinitions.lean#L35)
- [WP.density](../WPFormalization/Statements/ParameterDefinitions.lean#L41)

<details>
<summary>View formal statements</summary>

[WP.Delta](../WPFormalization/Statements/ParameterDefinitions.lean#L28):

```lean
def Delta (Y : ℝ) : ℝ := T Y - Y
```

[WP.action](../WPFormalization/Statements/ParameterDefinitions.lean#L35):

```lean
def action (Y : ℝ) : ℝ := ∫ v in Y..T Y, a v * Real.sqrt (T Y-v)
```

[WP.density](../WPFormalization/Statements/ParameterDefinitions.lean#L41):

```lean
def density (Y : ℝ) : ℝ := 2*XR Y*Real.sqrt (Delta Y)/action Y
```

</details>

<a id="target-eq:intro-leading"></a>

### Paper 1.5: Explicit absolute-volume model

**Paper statement** (PDF p. 5):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\widehat V_{g,n}=\frac{(2\pi^2)^{3g-3+n}\,\Gamma(h)}{\pi\,4^g\sqrt{\pi h}}\,
 \frac{\varpi(Y)}{(\sqrt2\,I(Y))^{h}}
 \left(\frac{k}{\mathrm e x}\right)^{k}
 \sqrt{\frac{k}{h\,x\Psi'(x)}},
$$

**Lean declarations** (defined):

- [WP.leadingVolume](../WPFormalization/Statements/Volumes.lean#L36)

<details>
<summary>View formal statements</summary>

[WP.leadingVolume](../WPFormalization/Statements/Volumes.lean#L36):

```lean
def leadingVolume (g n : ℕ) : ℝ :=
  if n = 0 then
    Real.Gamma (2*(g : ℝ)-2)*(4*Real.pi^2)^(2*g-3)/Real.sqrt (Real.pi*g)
  else
    let h : ℝ := 2*(g : ℝ)-1
    let k : ℕ := n-1
    let Y := densityY (2*k/h)
    let x := XR Y
    (2*Real.pi^2)^(dimension g n)*Real.Gamma h /
      (Real.pi*4^g*Real.sqrt (Real.pi*h)) * varpi Y / (Real.sqrt 2*action Y)^(2*g-1) *
      (if k = 0 then 1 else ((k : ℝ)/(Real.exp 1*x))^k*Real.sqrt (k/(h*euler Psi x)))
```

</details>

<a id="target-eq:intro-varpi"></a>

### Paper 1.6: Absolute prefactor varpi

**Paper statement** (PDF p. 5):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\varpi(Y)^2=\frac{I(Y)}{\Delta(Y)^{3/2}}
 \left(\int_0^1(1-s^2)\,\frac{X(v)}{v}\,\mathrm ds\right)^{-1},
 \qquad v=T(Y)-\Delta(Y)s^2;
$$

**Lean declarations** (defined):

- [WP.varpi](../WPFormalization/Statements/Parameter.lean#L101)
- [WP.Xdiv](../WPFormalization/Statements/Parameter.lean#L94)

<details>
<summary>View formal statements</summary>

[WP.varpi](../WPFormalization/Statements/Parameter.lean#L101):

```lean
def varpi (Y : ℝ) : ℝ := Real.sqrt
  (action Y / Real.rpow (Delta Y) (3/2 : ℝ) /
    (∫ s : ℝ in (0)..1, (1-s^2)*Xdiv (T Y - Delta Y*s^2)))
```

[WP.Xdiv](../WPFormalization/Statements/Parameter.lean#L94):

```lean
def Xdiv (v : ℝ) : ℝ := if v = 0 then 1 else XR v / v
```

</details>

<a id="target-thm:intro-absolute"></a>

### Paper 1.1: Uniform absolute expansion

**Paper statement** (PDF p. 5):

There are constants $C,B,c,g_0>0$ such that, for every $g\ge g_0$ and every integer $0\le K\le c\sqrt{2g-1}$,



$$
\sup_{n\ge0}\left|\frac{V_{g,n}}{\widehat V_{g,n}}
       -\sum_{j=0}^K\frac{A_j(g,n)}{(2g-1)^j}\right|
 \le\frac{CB^{K+1}((K+1)!)^2}{(2g-1)^{K+1}},
$$



 and the coefficients satisfy $|A_j(g,n)|\le CB^j(j!)^2$ for all $g\ge g_0$ and $n\ge0$. In particular,



$$
\sup_{n\ge0}\left|\frac{V_{g,n}}{\widehat V_{g,n}}-1\right|=O(g^{-1}).
$$



 Taking $K$ to be a sufficiently small fixed multiple of $\sqrt g$, rounded down to an integer, gives relative error $O(\mathrm{e}^{-a\sqrt g})$ for some $a>0$, uniformly in $n$.

**Lean declarations** (proved under classical premises):

- [WP.HigherOrder.intro_absolute](../WPFormalization/HigherOrder/Targets.lean#L14)
- [WP.HigherOrder.unmarked_first_exact](../WPFormalization/HigherOrder/UnmarkedFirstExact.lean#L27)

<details>
<summary>View formal statements</summary>

[WP.HigherOrder.intro_absolute](../WPFormalization/HigherOrder/Targets.lean#L14):

```lean
theorem intro_absolute (P : PsiTheory) (G : External.WeilPeterssonGeometry P) :
    ∃ C B c : ℝ, 0 < C ∧ 0 < B ∧ 0 < c ∧ ∃ g₀ : ℕ, 0 < g₀ ∧
      (∀ (g : ℕ), g₀ ≤ g → ∀ (K : ℕ),
        (K : ℝ) ≤ c*Real.sqrt (2*(g : ℝ)-1) → ∀ n : ℕ,
        |External.cuspVolume G g n/leadingVolume g n -
          ∑ j ∈ Finset.range (K+1), absoluteCoefficient P j g n/(2*(g : ℝ)-1)^j| ≤
          C*B^(K+1)*((K+1).factorial : ℝ)^2/(2*(g : ℝ)-1)^(K+1)) ∧
      (∀ (g : ℕ), g₀ ≤ g → ∀ j n : ℕ,
        |absoluteCoefficient P j g n| ≤ C*B^j*(j.factorial : ℝ)^2) ∧
      (∃ C' : ℝ, 0 < C' ∧ ∀ (g : ℕ), g₀ ≤ g → ∀ n : ℕ,
        |External.cuspVolume G g n/leadingVolume g n-1| ≤ C'/(g : ℝ)) ∧
      (∃ c' a C' : ℝ, 0 < c' ∧ c' ≤ c ∧ 0 < a ∧ 0 < C' ∧
        ∀ (g : ℕ), g₀ ≤ g → ∀ n : ℕ,
          |External.cuspVolume G g n/leadingVolume g n -
            ∑ j ∈ Finset.range (⌊c'*Real.sqrt (2*(g : ℝ)-1)⌋₊+1),
              absoluteCoefficient P j g n/(2*(g : ℝ)-1)^j| ≤
                C'*Real.exp (-a*Real.sqrt (2*(g : ℝ)-1)))
```

[WP.HigherOrder.unmarked_first_exact](../WPFormalization/HigherOrder/UnmarkedFirstExact.lean#L27):

```lean
theorem unmarked_first_exact (P : PsiTheory) :
    unmarkedCoefficient P 1 = 7/6 - 17/(3*Real.pi^2)
```

</details>

<a id="target-cor:constant"></a>

### Paper 1.2: Zograf's constant

**Paper statement** (PDF p. 6):

For every fixed $n\ge0$, as $g\to\infty$,



$$
V_{g,n}=\frac{(2g-3+n)!\,(4\pi^2)^{2g-3+n}}{\sqrt{\pi g}}
 \bigl(1+O_n(g^{-1})\bigr).
$$

**Lean declarations** (proved under classical premises):

- [WP.zograf_constant](../WPFormalization/Statements/ZografConstant.lean#L13)

<details>
<summary>View formal statements</summary>

[WP.zograf_constant](../WPFormalization/Statements/ZografConstant.lean#L13):

```lean
theorem zograf_constant (P : PsiTheory) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀,
      |volumeModel P g n /
        ((2*g+n-3).factorial*(4*Real.pi^2)^(2*g+n-3)/Real.sqrt (Real.pi*g))-1| ≤ C/g
```

</details>

<a id="target-eq:SP3"></a>

### Paper 1.7: Volume-ratio profiles

**Paper statement** (PDF p. 7):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\mathcal B(\lambda(Y))=\frac{\pi^2}{4\Delta(Y)},\qquad
 \mathcal C(\lambda(Y))=\frac{\lambda(Y)\pi^2}{X(Y)}.
$$

**Lean declarations** (defined):

- [WP.profileB](../WPFormalization/Statements/ParameterDefinitions.lean#L53)
- [WP.profileC](../WPFormalization/Statements/ParameterDefinitions.lean#L59)

<details>
<summary>View formal statements</summary>

[WP.profileB](../WPFormalization/Statements/ParameterDefinitions.lean#L53):

```lean
def profileB (l : ℝ) : ℝ := Real.pi^2 / (4*Delta (densityY l))
```

[WP.profileC](../WPFormalization/Statements/ParameterDefinitions.lean#L59):

```lean
def profileC (l : ℝ) : ℝ := if l = 0 then 4*Real.pi^2 else l*Real.pi^2 / XR (densityY l)
```

</details>

<a id="target-thm:volume"></a>

### Paper 1.3: Uniform volume ratios

**Paper statement** (PDF p. 7):

There are constants $C_0,g_0>0$ such that, for every $g\ge g_0$,



$$
\sup_{n\ge0}\left|\frac{B_{g,n}}{\mathcal B(n/g)}-1\right|\le\frac{C_0}{g},
 \qquad
 \sup_{n\ge0}\left|\frac{C_{g,n}}{\mathcal C(n/g)}-1\right|\le\frac{C_0}{g},
$$



 and



$$
\sup_{n\ge1}|D_{g,n}-1|\le\frac{C_0}{g}.
$$



 In particular, along every path $n/g\to\infty$ with $g\to\infty$,



$$
B_{g,n}\sim\frac{\pi^2}{3\sqrt5\,j_{0,1}}\sqrt{n/g},\qquad
 C_{g,n}\sim\frac{\pi^2}{x_c}\frac ng.
$$

**Lean declarations** (proved under classical premises):

- [WP.volume_ratios](../WPFormalization/Statements/VolumeRatios.lean#L12)

<details>
<summary>View formal statements</summary>

[WP.volume_ratios](../WPFormalization/Statements/VolumeRatios.lean#L12):

```lean
theorem volume_ratios (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀,
      (∀ n : ℕ,
        |(volumeModel P g n/volumeModel P (g-1) (n+2))/profileB ((n : ℝ)/g)-1| ≤ C/g ∧
        |(volumeModel P g (n+1)/(2*g*volumeModel P g n))/profileC ((n : ℝ)/g)-1| ≤ C/g) ∧
      (∀ n : ℕ, 1 ≤ n →
        |volumeModel P g n^2/(volumeModel P g (n-1)*volumeModel P g (n+1))-1| ≤ C/g)
```

</details>

<a id="target-thm:coefficient"></a>

### Paper 1.4: All adjacent degrees

**Paper statement** (PDF p. 8):

For $0\le k<N$, let $t_{g,k}\in(0,\pi)$ be determined by



$$
\frac{2k+1}{2g-1}
 =\frac{t_{g,k}^{2}\sin t_{g,k}}
 {\sin t_{g,k}-t_{g,k}\cos t_{g,k}}.
$$



 Then



$$
\sup_{0\le k<3g-2}
 \left|\frac{a_{g,k}/a_{g,k+1}}{4\pi^2/t_{g,k}^{2}}-1\right|
 =O(g^{-1/8}).
$$



 In particular, $a_{g,k}/a_{g,k+1}\to4$ for every $k=o(g)$, and, with $m=N-k\ge1$,



$$
\frac{a_{g,N-m}}{a_{g,N-m+1}}
 \sim\frac{4\pi^2g}{5m}\qquad\text{if }m=o(g).
$$

**Lean declarations** (proved under classical premises):

- [WP.adjacent_limit](../WPFormalization/Statements/AdjacentLimit.lean#L13)
- [WP.quantitative_adjacent](../WPFormalization/Statements/QuantitativeAdjacent.lean#L13)
- [WP.adjacent_endpoint_limits](../WPFormalization/Statements/AdjacentEndpointLimits.lean#L14)

<details>
<summary>View formal statements</summary>

[WP.adjacent_limit](../WPFormalization/Statements/AdjacentLimit.lean#L13):

```lean
theorem adjacent_limit (P : PsiTheory) :
    ∀ ε : ℝ, 0 < ε → ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ k : ℕ, k < 3*g-2 →
      adjacentError P g k ≤ ε
```

[WP.quantitative_adjacent](../WPFormalization/Statements/QuantitativeAdjacent.lean#L13):

```lean
theorem quantitative_adjacent (P : PsiTheory) :
    (∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ k : ℕ, k < 3*g-2 →
      adjacentError P g k ≤ C*Real.rpow g (-1/8 : ℝ)) ∧
    (∀ ε ∈ Set.Ioo (0 : ℝ) 3, ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀,
      ∀ k : ℕ, ε*g ≤ k → k < 3*g-2 → adjacentError P g k ≤ C*Real.rpow g (-1/4 : ℝ))
```

[WP.adjacent_endpoint_limits](../WPFormalization/Statements/AdjacentEndpointLimits.lean#L14):

```lean
theorem adjacent_endpoint_limits (P : PsiTheory) :
    (∀ ks : ℕ → ℕ,
      (∀ᶠ g in atTop, ks g < 3*g-2) →
      Tendsto (fun g : ℕ => (ks g : ℝ)/g) atTop (𝓝 0) →
      Tendsto (fun g => boundaryA P g (ks g)/boundaryA P g (ks g+1)) atTop (𝓝 4)) ∧
    (∀ ms : ℕ → ℕ,
      (∀ᶠ g in atTop, 1 ≤ ms g ∧ ms g ≤ 3*g-2) →
      Tendsto (fun g : ℕ => (ms g : ℝ)/g) atTop (𝓝 0) →
      Tendsto (fun g =>
        (boundaryA P g (3*g-2-ms g)/boundaryA P g (3*g-2-ms g+1)) /
          (4*Real.pi^2*g/(5*ms g))) atTop (𝓝 1))
```

</details>

<a id="target-eq:WC1"></a>

### Paper 1.8: Full diagonal chain rate profile

**Paper statement** (PDF p. 8):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
F(t)=\int_0^t\log\frac{4\Delta(Y(u))}{\pi^2}\,\mathrm{d}u
 \quad(0\le t<1),\qquad F(1)=-2\log(2x_c).
$$

**Lean declarations** (defined):

- [WP.chainProfile](../WPFormalization/Statements/ChainDefinitions.lean#L13)

<details>
<summary>View formal statements</summary>

[WP.chainProfile](../WPFormalization/Statements/ChainDefinitions.lean#L13):

```lean
def chainProfile (t : ℝ) : ℝ :=
  if t = 1 then -2*Real.log (2*xCritical) else
    ∫ u in (0 : ℝ)..t, Real.log (4*Delta (densityY (2*u/(1-u)))/Real.pi^2)
```

</details>

<a id="target-thm:chain"></a>

### Paper 1.5: A logarithmic rate for the full chain

**Paper statement** (PDF p. 8):

Uniformly over stable $(g,n)$ with $2g+n\to\infty$,



$$
\log\frac{V_{g,n}}{(2g+n-3)!(4\pi^2)^{2g+n-3}}
 =\frac{2g+n}{2}F\!\left(\frac n{2g+n}\right)+o(2g+n).
$$



 Consequently,



$$
\sup_{0\le j\le G}
 \left|\frac1G\log\frac{V_{G-j,2j}}{V_{G,0}}-F(j/G)\right|\to0.
$$

**Lean declarations** (proved under classical premises):

- [WP.diagonal_chain](../WPFormalization/Statements/Boundary.lean#L70)

<details>
<summary>View formal statements</summary>

[WP.diagonal_chain](../WPFormalization/Statements/Boundary.lean#L70):

```lean
theorem diagonal_chain (P : PsiTheory) :
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g n : ℕ, Stable g n → N ≤ 2*g+n →
      |Real.log (normalizedVolume P g n) - ((2*(g : ℝ)+n)/2)*
        chainProfile ((n : ℝ)/(2*g+n))| ≤ ε*(2*g+n)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ G₀ : ℕ, ∀ G ≥ G₀, 2 ≤ G → ∀ j : ℕ, j ≤ G →
      |Real.log (volumeModel P (G-j) (2*j)/volumeModel P G 0)/G-
        chainProfile ((j : ℝ)/G)| ≤ ε)
```

</details>

<a id="target-cor:spectral"></a>

### Paper 1.6: Vanishing spectral gap

**Paper statement** (PDF p. 9):

Suppose that $g\to\infty$ and that the integer cusp counts satisfy $n(g)/\sqrt g\to\infty$. Then, for every $\varepsilon>0$,



$$
\mathbb P^{\mathrm{WP}}_{g,n(g)}
 \{X:\Delta_X\text{ has an eigenvalue in }(0,\varepsilon)\}\longrightarrow1.
$$

**Lean declarations** (proved under classical premises):

- [WP.Spectral.vanishing_spectral_gap](../WPFormalization/Spectral/VanishingGap.lean#L80)

<details>
<summary>View formal statements</summary>

[WP.Spectral.vanishing_spectral_gap](../WPFormalization/Spectral/VanishingGap.lean#L80):

```lean
theorem vanishing_spectral_gap (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P)
    (H : HyperbolicCurveGeometry.{u,v,w} G) (S : SpectralGeometry H)
    (SW : ShenWuPantsBound H) (n : ℕ → ℕ)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop atTop) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun g => (wpProbability G g (n g)).real
        {X | ∃ ℓ, S.positiveEigenvalue X 1 = some ℓ ∧ ℓ < ε}) atTop (𝓝 1)
```

</details>

## Kernels and the parameter

<a id="target-eq:P1"></a>

### Paper 2.1: Positive-recursion kernels

**Paper statement** (PDF p. 16):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\begin{aligned}
 K_Y(z)&=\int_0^1X'\bigl(Y+\tfrac z2(1-s^2)\bigr)\,\mathrm{d}s
       =\sum_{\ell\ge0}\frac{X^{(\ell+1)}(Y)}{(2\ell+1)!!}z^\ell,\\
 H_Y(z)&=3\int_0^1s^2X'\bigl(Y+\tfrac z2(1-s^2)\bigr)\,\mathrm{d}s
       =\sum_{\ell\ge0}\frac{3X^{(\ell+1)}(Y)}{(2\ell+3)!!}z^\ell.
 \end{aligned}
$$

**Lean declarations** (defined):

- [WP.K](../WPFormalization/Statements/Kernels.lean#L21)
- [WP.H](../WPFormalization/Statements/Kernels.lean#L28)
- [WP.kernel_series](../WPFormalization/Statements/Kernels.lean#L80)

<details>
<summary>View formal statements</summary>

[WP.K](../WPFormalization/Statements/Kernels.lean#L21):

```lean
def K (Y : ℂ) (z : ℂ) : ℂ :=
  ∫ s : ℝ in (0)..1, deriv X (Y + z / 2 * (1 - (s : ℂ)^2))
```

[WP.H](../WPFormalization/Statements/Kernels.lean#L28):

```lean
def H (Y : ℂ) (z : ℂ) : ℂ :=
  3 * ∫ s : ℝ in (0)..1, (s : ℂ)^2 * deriv X (Y + z / 2 * (1 - (s : ℂ)^2))
```

[WP.kernel_series](../WPFormalization/Statements/Kernels.lean#L80):

```lean
theorem kernel_series (Y z : ℂ) :
    HasSum (fun l : ℕ => iteratedDeriv (l+1) X Y / oddFactorial l * z^l) (K Y z) ∧
    HasSum (fun l : ℕ => 3 * iteratedDeriv (l+1) X Y / oddFactorial (l+1) * z^l) (H Y z)
```

</details>

<a id="target-eq:P2"></a>

### Paper 2.2: Kernel differential identity

**Paper statement** (PDF p. 16):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
K_Y=H_Y+\tfrac23z\partial_zH_Y.
$$

**Lean declarations** (proved):

- [WP.kernel_differential](../WPFormalization/Statements/Kernels.lean#L104)

<details>
<summary>View formal statements</summary>

[WP.kernel_differential](../WPFormalization/Statements/Kernels.lean#L104):

```lean
theorem kernel_differential (Y z : ℂ) :
    K Y z = H Y z + 2/3 * z * deriv (H Y) z
```

</details>

<a id="target-lem:kernel-zeros"></a>

### Paper 2.1: Real zeros

**Paper statement** (PDF p. 16):

On $[0,\pi^2/4]$, $X(y)>0$ for $y>0$, $X''<0$, and $X'''>0$. Moreover $y_0<3/2$; in particular $X(Y)\le Y<3/2$ for $0\le Y\le y_0$. All zeros of $a(y)$ are positive real; in particular $a$ has no zeros in $|y|<y_0$. For $0\le Y<y_0$, every zero of $K_Y$ is positive and simple, and



$$
K_Y(z)=a(Y)\prod_{j\ge1}(1-z/r_j(Y)),
 \qquad 0<r_1(Y)<r_2(Y)<\cdots.
$$

**Lean declarations** (proved under classical premises):

- [WP.kernel_zeros](../WPFormalization/Analysis/KernelZeros.lean#L16)

<details>
<summary>View formal statements</summary>

[WP.kernel_zeros](../WPFormalization/Analysis/KernelZeros.lean#L16):

```lean
theorem kernel_zeros :
    (∀ y : ℝ, y ∈ Set.Ioc 0 (Real.pi^2/4) → 0 < XR y) ∧
    (∀ y : ℝ, y ∈ Set.Icc 0 (Real.pi^2/4) →
      (iteratedDeriv 2 X y).re < 0 ∧ 0 < (iteratedDeriv 3 X y).re) ∧
    y₀ < 3/2 ∧
    (∀ Y ∈ Set.Icc 0 y₀, XR Y ≤ Y) ∧
    (∀ z : ℂ, deriv X z = 0 → z.im = 0 ∧ 0 < z.re) ∧
    (∀ Y ∈ Set.Ico 0 y₀, ∃ roots : ℕ → ℝ,
      StrictMono roots ∧ (∀ j, 0 < roots j) ∧ roots 0 = r Y ∧
      (∀ z : ℂ, K Y z = 0 ↔ ∃ j, z = (roots j : ℂ)) ∧
      (∀ j, deriv (K Y) (roots j) ≠ 0) ∧
      (∀ z : ℂ, HasProd (fun j => 1 - z / (roots j : ℂ)) (K Y z / a Y)))
```

</details>

<a id="target-lem:kernel-positivity"></a>

### Paper 2.2: Coefficient positivity

**Paper statement** (PDF p. 17):

For $0\le Y<y_0$,



$$
\log\frac{a(Y)}{H_Y(z)}=\sum_{m\ge1}t_m(Y)z^m,
 \qquad t_m^{(q)}(0)\ge0\quad(m\ge1,q\ge0),\quad t_m(0)>0,
$$



 where each $t_m$ is analytic on $|Y|<y_0$ and its Taylor series at zero converges to $t_m(Y)$ there. Consequently $H_Y^{-h}$ has strictly positive Taylor coefficients for every real $h>0$, and $-H_Y'/H_Y$ has nonnegative coefficients. Moreover every Taylor coefficient in $Y$ of



$$
\widehat\vartheta_\ell(Y):=a(Y)[z^\ell]K_Y(z)^{-1}
$$



 is nonnegative, and the same holds for $a^{-1}$ and for $\vartheta_\ell=[z^\ell]K_Y^{-1}$.

**Lean declarations** (proved under classical premises):

- [WP.logKernelCoeff](../WPFormalization/Statements/Kernels.lean#L138)
- [WP.kernel_positivity](../WPFormalization/Analysis/KernelPositivity.lean#L15)
- [WP.log_kernel_series](../WPFormalization/Statements/Kernels.lean#L482)

<details>
<summary>View formal statements</summary>

[WP.logKernelCoeff](../WPFormalization/Statements/Kernels.lean#L138):

```lean
def logKernelCoeff (m : ℕ) (Y : ℂ) : ℂ :=
  coeff (fun z => Complex.log (deriv X Y / H Y z)) m
```

[WP.kernel_positivity](../WPFormalization/Analysis/KernelPositivity.lean#L15):

```lean
theorem kernel_positivity :
    (∀ m : ℕ, 0 < m →
      (∀ Y : ℂ, ‖Y‖ < y₀ → AnalyticAt ℂ (logKernelCoeff m) Y) ∧
      (∀ q, 0 ≤ (iteratedDeriv q (logKernelCoeff m) 0).re) ∧
      0 < (logKernelCoeff m 0).re ∧
      (∀ Y : ℂ, ‖Y‖ < y₀ →
        HasSum (fun q => coeff (logKernelCoeff m) q * Y^q) (logKernelCoeff m Y))) ∧
    (∀ Y ∈ Set.Ico 0 y₀, ∀ h : ℝ, 0 < h → ∀ m,
      0 < realCoeff (fun z => Complex.exp (-(h : ℂ) * Complex.log (H Y z))) m) ∧
    (∀ Y ∈ Set.Ico 0 y₀, ∀ m, 0 ≤ realCoeff (fun z => -deriv (H Y) z / H Y z) m) ∧
    (∀ l q : ℕ,
      0 ≤ realCoeff (fun Y => deriv X Y * coeff (fun z => (K Y z)⁻¹) l) q ∧
      0 ≤ realCoeff (fun Y => coeff (fun z => (K Y z)⁻¹) l) q) ∧
    (∀ q, 0 ≤ realCoeff (fun Y => (deriv X Y)⁻¹) q)
```

[WP.log_kernel_series](../WPFormalization/Statements/Kernels.lean#L482):

```lean
theorem log_kernel_series (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, ‖z‖ < ρ →
      HasSum (fun m : ℕ => logKernelCoeff (m+1) Y*z^(m+1))
        (Complex.log ((a Y : ℂ)/H Y z))
```

</details>

<a id="target-eq:P9"></a>

### Paper 2.5: Compact normalized kernels

**Paper statement** (PDF p. 17):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\bar K_Y(w)=K_Y(rw)/a(Y),\qquad
 \bar H_Y(w)=H_Y(rw)/a(Y),\qquad
 A(Y)=\bar H_Y(1)/3.
$$

**Lean declarations** (defined):

- [WP.barK](../WPFormalization/Statements/Kernels.lean#L339)
- [WP.barH](../WPFormalization/Statements/Kernels.lean#L346)
- [WP.A](../WPFormalization/Statements/Kernels.lean#L353)

<details>
<summary>View formal statements</summary>

[WP.barK](../WPFormalization/Statements/Kernels.lean#L339):

```lean
def barK (Y : ℝ) (w : ℂ) : ℂ :=
  if Y = y₀ then 1 - w else K Y ((r Y : ℂ) * w) / a Y
```

[WP.barH](../WPFormalization/Statements/Kernels.lean#L346):

```lean
def barH (Y : ℝ) (w : ℂ) : ℂ :=
  if Y = y₀ then 1 - 3/5 * w else H Y ((r Y : ℂ) * w) / a Y
```

[WP.A](../WPFormalization/Statements/Kernels.lean#L353):

```lean
def A (Y : ℝ) : ℝ := (barH Y 1).re / 3
```

</details>

<a id="target-eq:P10"></a>

### Paper 2.6: Critical kernel limits

**Paper statement** (PDF p. 17):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
r(Y)\sim3a(Y)/b,\qquad
 \bar K_Y(w)\longrightarrow1-w,\qquad
 \bar H_Y(w)\longrightarrow1-3w/5.
$$

**Lean declarations** (proved):

- [WP.critical_kernel_limits](../WPFormalization/Analysis/CriticalKernelLimits.lean#L197)

<details>
<summary>View formal statements</summary>

[WP.critical_kernel_limits](../WPFormalization/Analysis/CriticalKernelLimits.lean#L197):

```lean
theorem critical_kernel_limits :
    Tendsto (fun Y => r Y / (3*a Y / (-(iteratedDeriv 2 X y₀).re))) (𝓝[<] y₀) (𝓝 1) ∧
    (∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ Y in 𝓝[<] y₀, ∀ w : ℂ, ‖w‖ ≤ R →
        ‖barK Y w - (1-w)‖ ≤ ε ∧ ‖barH Y w - (1-3/5*w)‖ ≤ ε)
```

</details>

<a id="target-eq:P11"></a>

### Paper 2.7: Uniform kernel moments

**Paper statement** (PDF p. 17):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
1=\theta_0\le\theta_1\le\cdots\le C,
 \quad \theta_\ell=[w^\ell]\bar K_Y(w)^{-1},
 \quad w_\ell:=\theta_\ell-\theta_{\ell-1}\ge0,
 \quad\sup_Y\sum_{\ell\ge0}(1+\ell)^q w_\ell<\infty.
$$

**Lean declarations** (proved under classical premises):

- [WP.theta](../WPFormalization/Statements/Kernels.lean#L359)
- [WP.weight](../WPFormalization/Statements/Kernels.lean#L401)
- [WP.uniform_kernel_moments](../WPFormalization/Analysis/UniformKernelMoments.lean#L14)

<details>
<summary>View formal statements</summary>

[WP.theta](../WPFormalization/Statements/Kernels.lean#L359):

```lean
def theta (Y : ℝ) (l : ℕ) : ℝ := realCoeff (fun w => (barK Y w)⁻¹) l
```

[WP.weight](../WPFormalization/Statements/Kernels.lean#L401):

```lean
def weight (Y : ℝ) (l : ℕ) : ℝ := theta Y l - if l = 0 then 0 else theta Y (l-1)
```

[WP.uniform_kernel_moments](../WPFormalization/Analysis/UniformKernelMoments.lean#L14):

```lean
theorem uniform_kernel_moments :
    (∃ C : ℝ, ∀ Y ∈ Set.Icc 0 y₀,
      theta Y 0 = 1 ∧ Monotone (theta Y) ∧ ∀ l, theta Y l ≤ C ∧ 0 ≤ weight Y l) ∧
    (∀ q : ℕ, ∃ C : ℝ, ∀ Y ∈ Set.Icc 0 y₀,
      Summable (fun l : ℕ => (1+(l : ℝ))^q * weight Y l) ∧
      ∑' l : ℕ, (1+(l : ℝ))^q * weight Y l ≤ C)
```

</details>

<a id="target-eq:P12"></a>

### Paper 2.8: Harmonic probability law

**Paper statement** (PDF p. 17):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
P_Y(w)=\frac{\bar H_Y(1)}{\bar H_Y(w)}
$$

**Lean declarations** (defined under classical premises):

- [WP.harmonicPGF](../WPFormalization/Statements/Kernels.lean#L459)
- [WP.harmonicMass](../WPFormalization/Statements/Kernels.lean#L465)
- [WP.harmonicVariance](../WPFormalization/Statements/Kernels.lean#L471)
- [WP.harmonic_law](../WPFormalization/Analysis/HarmonicLaw.lean#L13)

<details>
<summary>View formal statements</summary>

[WP.harmonicPGF](../WPFormalization/Statements/Kernels.lean#L459):

```lean
def harmonicPGF (Y : ℝ) (w : ℂ) : ℂ := barH Y 1 / barH Y w
```

[WP.harmonicMass](../WPFormalization/Statements/Kernels.lean#L465):

```lean
def harmonicMass (Y : ℝ) (m : ℕ) : ℝ := realCoeff (harmonicPGF Y) m
```

[WP.harmonicVariance](../WPFormalization/Statements/Kernels.lean#L471):

```lean
def harmonicVariance (Y : ℝ) : ℝ :=
  ∑' m : ℕ, ((m : ℝ)-3/2)^2 * harmonicMass Y m
```

[WP.harmonic_law](../WPFormalization/Analysis/HarmonicLaw.lean#L13):

```lean
theorem harmonic_law :
    (∀ Y ∈ Set.Icc 0 y₀,
      (∀ m, 0 ≤ harmonicMass Y m) ∧ HasSum (harmonicMass Y) 1 ∧
      HasSum (fun m : ℕ => (m : ℝ) * harmonicMass Y m) (3/2)) ∧
    (∃ c C t : ℝ, 0 < c ∧ 0 < C ∧ 0 < t ∧ ∀ Y ∈ Set.Icc 0 y₀,
      c ≤ harmonicMass Y 0 ∧ c ≤ harmonicMass Y 1 ∧
      c ≤ harmonicVariance Y ∧ harmonicVariance Y ≤ C ∧
      Summable (fun m : ℕ => Real.exp (t*m) * harmonicMass Y m) ∧
      ∑' m : ℕ, Real.exp (t*m) * harmonicMass Y m ≤ C) ∧
    harmonicVariance y₀ = 15/4
```

</details>

<a id="target-eq:P13"></a>

### Paper 2.9: Uniform harmonic local limit

**Paper statement** (PDF p. 18):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\Pr(S_h=m)=\frac1{\sqrt{2\pi h\sigma_Y^2}}
     \exp\!\left(-\frac{(m-3h/2)^2}{2h\sigma_Y^2}\right)
       +o(h^{-1/2}).
$$

**Lean declarations** (proved under classical premises):

- [WP.harmonic_local_limit](../WPFormalization/Analysis/HarmonicLocalLimit.lean#L66)

<details>
<summary>View formal statements</summary>

[WP.harmonic_local_limit](../WPFormalization/Analysis/HarmonicLocalLimit.lean#L66):

```lean
theorem harmonic_local_limit (L : ℝ) (hL : 0 ≤ L) :
    ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℕ, ∀ h ≥ h₀, 0 < h →
    ∀ Y ∈ Set.Icc 0 y₀, ∀ m : ℕ, |(m : ℝ)-3*(h : ℝ)/2| ≤ L*Real.sqrt h →
      |harmonicSumMass Y h m -
        Real.exp (-((m : ℝ)-3*(h : ℝ)/2)^2/(2*h*harmonicVariance Y)) /
          Real.sqrt (2*Real.pi*h*harmonicVariance Y)| ≤ ε / Real.sqrt h
```

</details>

<a id="target-lem:parameter"></a>

### Paper 3.1: The parameter

**Paper statement** (PDF p. 18):

1. The root $T(Y)$ of [1.2](#target-eq:SP1) exists, is unique and depends analytically on $Y\in[0,y_0)$. One has $T(0)=\pi^2/4$, $-1\le T'<0$, $T''>0$, and $T\to y_0$ as $Y\to y_0$. Moreover $I>0$.

2. Put


$$
J(Y)=\int_0^1X(T-\Delta s^2)\,\mathrm{d}s
     =X(Y)+\frac{I(Y)}{\sqrt\Delta},
 \qquad
 \beta(Y)=\frac{X(Y)}{J(Y)}=
           \frac{\lambda(Y)}{2+\lambda(Y)}.
$$


    Then $\beta'>0$, and $\lambda$ is an analytic strictly increasing bijection from $[0,y_0)$ onto $[0,\infty)$. At $Y=0$, $\Delta=T=\pi^2/4$, $I(0)=\pi/4$, $J(0)=1/2$, and $\lambda(Y)=4Y+O(Y^2)$.

3. Put $\delta=y_0-Y$ and $b=-X''(y_0)=x_c/y_0>0$. As $\delta\to0$,


$$
\Delta=\frac32\delta+O(\delta^2),\qquad
 I(Y)=\frac{8b}{45}\Delta^{5/2}(1+O(\Delta)),
$$





$$
\lambda\sim\frac{45x_c}{4b}\Delta^{-2}
       =\frac{45j_{0,1}^2}{16}\Delta^{-2},
$$


    and consequently


$$
\mathcal B(\lambda)\sim
 \frac{\pi^2}{3\sqrt5\,j_{0,1}}\sqrt\lambda,\qquad
 \mathcal C(\lambda)\sim\frac{\pi^2}{x_c}\lambda.
$$


    Also $\Delta\asymp\sqrt{1-\beta}$.

4. The function $\Psi$ is analytic and strictly increasing for $0<x<x_c$. With $\varepsilon=1-x/x_c$,


$$
\begin{array}{ll}
 x\downarrow0:&
 \Psi=2x+O(x^2),\quad\mathscr D\Psi=2x+O(x^2),\quad
 \mathscr D^2\Psi=2x+O(x^2),\\[1mm]
 x\uparrow x_c:&
 \displaystyle\Psi=\frac5{4\varepsilon}(1+O(\sqrt\varepsilon)),\quad
 \mathscr D\Psi=\frac5{4\varepsilon^2}(1+O(\sqrt\varepsilon)),\quad
 \mathscr D^2\Psi=O(\varepsilon^{-3}).
 \end{array}
$$


    These expansions arise from convergent analytic expansions in $x$ or $\sqrt\varepsilon$. In particular $\Psi^2/(\mathscr D\Psi)$ has finite endpoint limits $0$ and $5/4$, and is bounded on the full interval.

**Lean declarations** (proved):

- [WP.parameter_regular](../WPFormalization/Statements/Parameter.lean#L33)
- [WP.parameter_critical](../WPFormalization/Statements/Parameter.lean#L52)
- [WP.parameter_cusp_weight](../WPFormalization/Statements/Parameter.lean#L73)
- [WP.parameter_analytic_expansions](../WPFormalization/Statements/Parameter.lean#L156)

<details>
<summary>View formal statements</summary>

[WP.parameter_regular](../WPFormalization/Statements/Parameter.lean#L33):

```lean
theorem parameter_regular :
    (∀ Y ∈ Set.Ico 0 y₀,
      AnalyticAt ℝ T Y ∧ -1 ≤ deriv T Y ∧ deriv T Y < 0 ∧
      0 < iteratedDeriv 2 T Y ∧ 0 < action Y ∧
      J Y = XR Y + action Y / Real.sqrt (Delta Y) ∧
      beta Y = density Y / (2+density Y) ∧ 0 < deriv beta Y ∧ AnalyticAt ℝ density Y) ∧
    StrictMonoOn density (Set.Ico 0 y₀) ∧
    Set.BijOn density (Set.Ico 0 y₀) (Set.Ici 0) ∧
    T 0 = Real.pi^2/4 ∧ action 0 = Real.pi/4 ∧ J 0 = 1/2 ∧
    Tendsto T (𝓝[<] y₀) (𝓝 y₀) ∧
    (fun Y => density Y - 4*Y) =O[𝓝[>] (0 : ℝ)] (fun Y => Y^2)
```

[WP.parameter_critical](../WPFormalization/Statements/Parameter.lean#L52):

```lean
theorem parameter_critical :
    let b := -(iteratedDeriv 2 X y₀).re
    0 < b ∧ b = xCritical/y₀ ∧
    (fun Y => Delta Y - 3/2*(y₀-Y)) =O[𝓝[<] y₀] (fun Y => (y₀-Y)^2) ∧
    (fun Y => action Y / (8*b/45 * Real.rpow (Delta Y) (5/2 : ℝ)) - 1)
      =O[𝓝[<] y₀] Delta ∧
    Tendsto (fun Y => density Y / (45*xCritical/(4*b) * (Delta Y)⁻¹^2))
      (𝓝[<] y₀) (𝓝 1) ∧
    Tendsto (fun l => profileB l /
      (Real.pi^2/(3*Real.sqrt 5*(2*Real.sqrt y₀))*Real.sqrt l)) atTop (𝓝 1) ∧
    Tendsto (fun l => profileC l / (Real.pi^2/xCritical*l)) atTop (𝓝 1) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ Y in 𝓝[<] y₀,
      c*Real.sqrt (1-beta Y) ≤ Delta Y ∧ Delta Y ≤ C*Real.sqrt (1-beta Y))
```

[WP.parameter_cusp_weight](../WPFormalization/Statements/Parameter.lean#L73):

```lean
theorem parameter_cusp_weight :
    (∀ x ∈ Set.Ioo 0 xCritical, AnalyticAt ℝ Psi x) ∧
    StrictMonoOn Psi (Set.Ioo 0 xCritical) ∧
    (∀ j ∈ Finset.range 3,
      (fun x => (euler^[j]) Psi x - 2*x) =O[𝓝[>] (0 : ℝ)] (fun x => x^2)) ∧
    (fun x => Psi x / (5/(4*(1-x/xCritical))) - 1)
      =O[𝓝[<] xCritical] (fun x => Real.sqrt (1-x/xCritical)) ∧
    (fun x => euler Psi x / (5/(4*(1-x/xCritical)^2)) - 1)
      =O[𝓝[<] xCritical] (fun x => Real.sqrt (1-x/xCritical)) ∧
    (euler (euler Psi)) =O[𝓝[<] xCritical] (fun x => (1-x/xCritical)⁻¹^3) ∧
    Tendsto (fun x => Psi x^2 / euler Psi x) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun x => Psi x^2 / euler Psi x) (𝓝[<] xCritical) (𝓝 (5/4)) ∧
    (∃ C : ℝ, ∀ x ∈ Set.Ioo 0 xCritical, |Psi x^2 / euler Psi x| ≤ C)
```

[WP.parameter_analytic_expansions](../WPFormalization/Statements/Parameter.lean#L156):

```lean
theorem parameter_analytic_expansions :
    AnalyticAt ℝ Psi 0 ∧ AnalyticAt ℝ (euler Psi) 0 ∧ AnalyticAt ℝ (euler (euler Psi)) 0 ∧
    ∃ δ : ℝ, 0 < δ ∧ ∃ f₀ f₁ f₂ : ℝ → ℝ,
      AnalyticAt ℝ f₀ 0 ∧ AnalyticAt ℝ f₁ 0 ∧ AnalyticAt ℝ f₂ 0 ∧
      f₀ 0 = 5/4 ∧ f₁ 0 = 5/4 ∧ ∀ t ∈ Set.Ioo 0 δ,
        Psi (xCritical*(1-t^2))*t^2 = f₀ t ∧
        euler Psi (xCritical*(1-t^2))*t^4 = f₁ t ∧
        euler (euler Psi) (xCritical*(1-t^2))*t^6 = f₂ t
```

</details>

## Amplitude functions

<a id="target-eq:H2"></a>

### Paper 4.1: Normalized kernels and recursion coefficients

**Paper statement** (PDF p. 19):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\bar H_Y(z)=\frac{H_Y(r_Yz)}a,\qquad
\bar K_Y(z)=\frac{K_Y(r_Yz)}a
      =\bar H_Y(z)+\frac23z\bar H_Y'(z),\qquad
\theta_\ell(Y)=[z^\ell]\bar K_Y(z)^{-1}.
$$

**Lean declarations** (defined):

- [WP.normalized_kernel_identity](../WPFormalization/Statements/Kernels.lean#L409)
- [WP.theta](../WPFormalization/Statements/Kernels.lean#L359)

<details>
<summary>View formal statements</summary>

[WP.normalized_kernel_identity](../WPFormalization/Statements/Kernels.lean#L409):

```lean
theorem normalized_kernel_identity (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (z : ℂ) :
    barK Y z = barH Y z + 2/3*z*deriv (barH Y) z
```

[WP.theta](../WPFormalization/Statements/Kernels.lean#L359):

```lean
def theta (Y : ℝ) (l : ℕ) : ℝ := realCoeff (fun w => (barK Y w)⁻¹) l
```

</details>

<a id="target-eq:H3"></a>

### Paper 4.2: Critical normalized kernels

**Paper statement** (PDF p. 19):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\bar H_{y_0}(z)=1-\frac35z,\qquad \bar K_{y_0}(z)=1-z,\qquad
\theta_\ell(y_0)=1.
$$

**Lean declarations** (defined):

- [WP.critical_kernels](../WPFormalization/Statements/Kernels.lean#L434)

<details>
<summary>View formal statements</summary>

[WP.critical_kernels](../WPFormalization/Statements/Kernels.lean#L434):

```lean
theorem critical_kernels :
    (∀ w, barK y₀ w = 1 - w ∧ barH y₀ w = 1 - 3/5*w) ∧
    (∀ l, theta y₀ l = 1)
```

</details>

<a id="target-eq:H4"></a>

### Paper 4.3: Pure psi normalization

**Paper statement** (PDF p. 19):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
C_g(\mathbf e)=
\frac{4^g\prod_i(2e_i+1)!!}
 {3^{\,2g-2+q}\Gamma(2g-2+q)}
\left\langle\prod_{i=1}^q\tau_{e_i}\right\rangle_g,
\qquad \sum_i e_i=3g-3+q.
$$

**Lean declarations** (defined under classical premises):

- [WP.pureC](../WPFormalization/Statements/IntersectionInterface.lean#L59)

<details>
<summary>View formal statements</summary>

[WP.pureC](../WPFormalization/Statements/IntersectionInterface.lean#L59):

```lean
def pureC (P : PsiTheory) (g : ℕ) (d : List ℕ) : ℝ :=
  (4 : ℝ)^g * (d.map (fun k => (oddFactorial k : ℝ))).prod /
    (3^(complexity g d.length) * Real.Gamma (complexity g d.length)) * pure P g d
```

</details>

<a id="target-eq:H5"></a>

### Paper 4.4: Mixed kappa to psi transform

**Paper statement** (PDF p. 20):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\frac{[\tau_{d_1}\cdots\tau_{d_n}]_{g,n}}
 {4^D(2\pi^2)^m}
=\prod_i(2d_i+1)!!
\sum_{\substack{\ell_k\ge0,\ k\ge2\\
                 \sum_{k\ge2}(k-1)\ell_k=m}}
\left\langle\tau_{\mathbf d}\prod_{k\ge2}\tau_k^{\ell_k}\right\rangle_g
\prod_{k\ge2}\frac{((-1)^k/(k-1)!)^{\ell_k}}{\ell_k!}.
$$

**Lean declarations** (proved under classical premises):

- [WP.mixed_transform](../WPFormalization/Statements/IntersectionInterface.lean#L230)

<details>
<summary>View formal statements</summary>

[WP.mixed_transform](../WPFormalization/Statements/IntersectionInterface.lean#L230):

```lean
theorem mixed_transform (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hst : Stable g d.length) (hd : d.sum ≤ dimension g d.length) :
    mixedBracket P g d / ((4 : ℝ)^d.sum*(2*Real.pi^2)^(deficit g d)) =
      (d.map (fun k => (oddFactorial k : ℝ))).prod *
      ∑ l ∈ backgrounds (deficit g d), pure P g (d ++ backgroundDegrees l) *
        ∏ i : Fin (deficit g d),
          (((-1 : ℝ)^(i.val+2)/(i.val+1).factorial)^(l i))/(l i).factorial
```

</details>

<a id="target-eq:H6"></a>

### Paper 4.5: Shifted amplitudes

**Paper statement** (PDF p. 20):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
U^Y_{g,n}(\mathbf d)=\prod_i(2d_i+1)!!
\sum_{\substack{\ell_k\ge0,\ k\ge2\\
                 \sum(k-1)\ell_k=m}}
\left\langle\tau_{\mathbf d}\prod_{k\ge2}\tau_k^{\ell_k}\right\rangle_g
\frac{\prod_{k\ge2}(-X^{(k)}(Y))^{\ell_k}/\ell_k!}
 {a^{h+\sum\ell_k}}.
$$

**Lean declarations** (defined under classical premises):

- [WP.shifted](../WPFormalization/Statements/IntersectionInterface.lean#L86)
- [WP.backgrounds](../WPFormalization/Statements/IntersectionInterface.lean#L69)
- [WP.backgroundDegrees](../WPFormalization/Statements/IntersectionInterface.lean#L77)

<details>
<summary>View formal statements</summary>

[WP.shifted](../WPFormalization/Statements/IntersectionInterface.lean#L86):

```lean
def shifted (P : PsiTheory) (g : ℕ) (d : List ℕ) (Y : ℝ) : ℝ :=
  if Stable g d.length ∧ d.sum ≤ dimension g d.length then
    (d.map (fun k => (oddFactorial k : ℝ))).prod *
    ∑ l ∈ backgrounds (deficit g d),
      pure P g (d ++ backgroundDegrees l) *
      (∏ i : Fin (deficit g d),
        (-(iteratedDeriv (i.val+2) X Y).re)^(l i)/(l i).factorial) /
      a Y ^ (complexity g d.length + ∑ i, l i)
  else 0
```

[WP.backgrounds](../WPFormalization/Statements/IntersectionInterface.lean#L69):

```lean
def backgrounds (m : ℕ) : Finset (Fin m → ℕ) :=
  (Finset.univ.image (fun l : Fin m → Fin (m+1) => fun i => (l i).val)).filter
    (fun l => ∑ i : Fin m, (i.val+1)*l i = m)
```

[WP.backgroundDegrees](../WPFormalization/Statements/IntersectionInterface.lean#L77):

```lean
def backgroundDegrees {m : ℕ} (l : Fin m → ℕ) : List ℕ :=
  (List.finRange m).flatMap (fun i => List.replicate (l i) (i.val+2))
```

</details>

<a id="target-eq:H7"></a>

### Paper 4.6: Normalized shifted amplitudes

**Paper statement** (PDF p. 20):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\mathcal U_{g,n}(\mathbf d;Y)=a^h r_Y^m U^Y_{g,n}(\mathbf d).
$$

**Lean declarations** (defined under classical premises):

- [WP.normalized](../WPFormalization/Statements/IntersectionInterface.lean#L108)

<details>
<summary>View formal statements</summary>

[WP.normalized](../WPFormalization/Statements/IntersectionInterface.lean#L108):

```lean
def normalized (P : PsiTheory) (g : ℕ) (d : List ℕ) (Y : ℝ) : ℝ :=
  if Y = y₀ then
    if Stable g d.length ∧ d.sum ≤ dimension g d.length then
      (3 : ℝ)^(deficit g d) *
        (d.map (fun k => (oddFactorial k : ℝ))).prod *
        pure P g (d ++ List.replicate (deficit g d) 2) / (deficit g d).factorial
    else 0
  else a Y^(complexity g d.length) * r Y^(deficit g d) * shifted P g d Y
```

</details>

<a id="target-eq:H8"></a>

### Paper 4.7: String-flow identification with geometric volumes

**Paper statement** (PDF p. 20):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
U^Y_{g,n}(0^n)=\Phi_g^{(n)}(x),\qquad
\Phi_g(x)=\sum_{n\ge0}\frac{V_{g,n}}{(2\pi^2)^{3g-3+n}}\frac{x^n}{n!},
$$

**Lean declarations** (proved under classical premises):

- [WP.string_flow](../WPFormalization/Statements/StringFlow.lean#L13)

<details>
<summary>View formal statements</summary>

[WP.string_flow](../WPFormalization/Statements/StringFlow.lean#L13):

```lean
theorem string_flow (P : PsiTheory) (g n : ℕ) (hst : Stable g n)
    (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    shifted P g (List.replicate n 0) Y = markedF P g n (XR Y)
```

</details>

<a id="target-eq:H9"></a>

### Paper 4.8: Exact positive geometric recursion

**Paper statement** (PDF p. 21):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\begin{aligned}
\mathcal U_{g,n}(\mathbf d)={}&
\sum_{j=2}^n(2d_j+1)\sum_{\ell=0}^m\theta_\ell
 \mathcal U_{g,n-1}(d_1+d_j+\ell-1,\mathbf d_{\widehat{1,j}})\\
&+\frac12\sum_{\ell=0}^m\theta_\ell
 \sum_{u+v=d_1+\ell-2}
 \mathcal U_{g-1,n+1}(u,v,\mathbf d_{\widehat1})\\
&+\frac12\sum_{\ell=0}^m\theta_\ell
 \sum_{u+v=d_1+\ell-2}
 \sum_{\substack{g_1+g_2=g\\I\sqcup J=\{2,\ldots,n\}}}
 \mathcal U_{g_1,|I|+1}(u,\mathbf d_I)
 \mathcal U_{g_2,|J|+1}(v,\mathbf d_J).
\end{aligned}
$$

**Lean declarations** (proved under classical premises):

- [WP.positive_recursion](../WPFormalization/Statements/Comparison.lean#L145)
- [WP.positiveRHS](../WPFormalization/Statements/Comparison.lean#L21)

<details>
<summary>View formal statements</summary>

[WP.positive_recursion](../WPFormalization/Statements/Comparison.lean#L145):

```lean
theorem positive_recursion (P : PsiTheory) (g pivot : ℕ) (d : List ℕ) (Y : ℝ)
    (hh : 2 ≤ complexity g (d.length+1))
    (hd : (pivot :: d).sum ≤ dimension g (d.length+1)) (hY : Y ∈ Set.Icc 0 y₀) :
    normalized P g (pivot :: d) Y = positiveRHS P g pivot d Y
```

[WP.positiveRHS](../WPFormalization/Statements/Comparison.lean#L21):

```lean
def positiveRHS (P : PsiTheory) (g pivot : ℕ) (d : List ℕ) (Y : ℝ) : ℝ :=
  let m := deficit g (pivot :: d)
  (∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1) *
    ∑ l ∈ Finset.range (m+1), theta Y l * normInt P g
      (((pivot : ℤ)+d[j]!+l-1) :: ((d.eraseIdx j).map Int.ofNat)) Y) +
  (if g = 0 then 0 else (1/2 : ℝ) * ∑ l ∈ Finset.range (m+1), theta Y l *
    ∑ u ∈ Finset.range (pivot+l-1), normInt P (g-1)
      ((u : ℤ) :: ((pivot : ℤ)+l-2-u) :: d.map Int.ofNat) Y) +
  (1/2 : ℝ) * ∑ l ∈ Finset.range (m+1), theta Y l *
    ∑ u ∈ Finset.range (pivot+l-1), ∑ g₁ ∈ Finset.range (g+1),
      ∑ I ∈ (Finset.range d.length).powerset,
        normInt P g₁ ((u : ℤ) :: selected (d.map Int.ofNat) I) Y *
        normInt P (g-g₁) (((pivot : ℤ)+l-2-u) ::
          selected (d.map Int.ofNat) ((Finset.range d.length) \ I)) Y
```

</details>

<a id="target-eq:H10"></a>

### Paper 4.9: Initial amplitudes

**Paper statement** (PDF p. 22):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\mathcal U_{0,3}(0,0,0)=1,\qquad
\mathcal U_{1,1}(1)=\frac18,\qquad
\mathcal U_{1,1}(0)=\frac{\theta_1}{8}.
$$

**Lean declarations** (proved under classical premises):

- [WP.initial_amplitudes](../WPFormalization/Statements/IntersectionInterface.lean#L210)

<details>
<summary>View formal statements</summary>

[WP.initial_amplitudes](../WPFormalization/Statements/IntersectionInterface.lean#L210):

```lean
theorem initial_amplitudes (P : PsiTheory) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) :
    normalized P 0 [0,0,0] Y = 1 ∧ normalized P 1 [1] Y = 1/8 ∧
    normalized P 1 [0] Y = theta Y 1/8
```

</details>

<a id="target-eq:H12"></a>

### Paper 4.11: Harmonic comparison model

**Paper statement** (PDF p. 22):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
A_m(h)=[z^m]\bar H(z)^{-h},\qquad
\mathcal M_{g,n}(\mathbf d)=3^h\Gamma(h)4^{-g}A_m(h),\qquad
R=\mathcal U/\mathcal M.
$$

**Lean declarations** (defined under classical premises):

- [WP.harmonicCoeff](../WPFormalization/Statements/IntersectionInterface.lean#L123)
- [WP.model](../WPFormalization/Statements/IntersectionInterface.lean#L130)
- [WP.ratio](../WPFormalization/Statements/IntersectionInterface.lean#L138)

<details>
<summary>View formal statements</summary>

[WP.harmonicCoeff](../WPFormalization/Statements/IntersectionInterface.lean#L123):

```lean
def harmonicCoeff (Y : ℝ) (h m : ℕ) : ℝ :=
  realCoeff (fun z => (barH Y z)⁻¹^h) m
```

[WP.model](../WPFormalization/Statements/IntersectionInterface.lean#L130):

```lean
def model (g : ℕ) (d : List ℕ) (Y : ℝ) : ℝ :=
  (3 : ℝ)^(complexity g d.length) * Real.Gamma (complexity g d.length) /
    4^g * harmonicCoeff Y (complexity g d.length) (deficit g d)
```

[WP.ratio](../WPFormalization/Statements/IntersectionInterface.lean#L138):

```lean
def ratio (P : PsiTheory) (g : ℕ) (d : List ℕ) (Y : ℝ) : ℝ :=
  normalized P g d Y / model g d Y
```

</details>

<a id="target-eq:H13"></a>

### Paper 4.12: Linear mass identity

**Paper statement** (PDF p. 22):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\sum_{\ell=0}^m q_\ell
\left(1-\frac{2(m-\ell)}{3(h-1)}\right)=1.
$$

**Lean declarations** (proved under classical premises):

- [WP.mass_identity](../WPFormalization/Statements/Comparison.lean#L172)
- [WP.linearQ](../WPFormalization/Statements/Comparison.lean#L157)

<details>
<summary>View formal statements</summary>

[WP.mass_identity](../WPFormalization/Statements/Comparison.lean#L172):

```lean
theorem mass_identity (Y : ℝ) (h m : ℕ) (hh : 2 ≤ h) (hY : Y ∈ Set.Icc 0 y₀) :
    ∑ l ∈ Finset.range (m+1), linearQ Y h m l *
      (1 - 2*((m : ℝ)-l)/(3*((h : ℝ)-1))) = 1
```

[WP.linearQ](../WPFormalization/Statements/Comparison.lean#L157):

```lean
def linearQ (Y : ℝ) (h m l : ℕ) : ℝ :=
  theta Y l * harmonicCoeff Y (h-1) (m-l) / harmonicCoeff Y h m
```

</details>

<a id="target-eq:H14"></a>

### Paper 4.13: All-zero mass defect

**Paper statement** (PDF p. 23):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
s=1+\frac{3-n}{3(h-1)}
       \frac{A_m(h-1)}{A_m(h)}.
$$

**Lean declarations** (proved under classical premises):

- [WP.zero_mass_defect](../WPFormalization/Statements/Comparison.lean#L194)
- [WP.zeroLinearMass](../WPFormalization/Statements/Comparison.lean#L183)

<details>
<summary>View formal statements</summary>

[WP.zero_mass_defect](../WPFormalization/Statements/Comparison.lean#L194):

```lean
theorem zero_mass_defect (Y : ℝ) (g n : ℕ) (hg : 2 ≤ g) (hn : 1 ≤ n)
    (hY : Y ∈ Set.Icc 0 y₀) :
    zeroLinearMass Y g n = 1 + (3-(n : ℝ))/(3*((complexity g n : ℝ)-1)) *
      harmonicCoeff Y (complexity g n-1) (dimension g n) /
        harmonicCoeff Y (complexity g n) (dimension g n)
```

[WP.zeroLinearMass](../WPFormalization/Statements/Comparison.lean#L183):

```lean
def zeroLinearMass (Y : ℝ) (g n : ℕ) : ℝ :=
  let h := complexity g n
  let m := dimension g n
  (∑ l ∈ Finset.range (m+1), linearQ Y h m l *
    (((n : ℝ)-1)*(if 1 ≤ l then 1 else 0) + 2*(l-1 : ℕ)) / (3*((h : ℝ)-1)))
```

</details>

<a id="target-eq:H22"></a>

### Paper 4.21: Uniform linear coefficient mass bounds

**Paper statement** (PDF p. 23):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
S_0\le C\sqrt h,\qquad S_0\le Ch/L\quad(L\ge6).
$$

**Lean declarations** (proved under classical premises):

- [WP.linear_mass_bounds](../WPFormalization/Analysis/LinearMassBounds.lean#L176)
- [WP.linearS₀](../WPFormalization/Statements/Comparison.lean#L164)

<details>
<summary>View formal statements</summary>

[WP.linear_mass_bounds](../WPFormalization/Analysis/LinearMassBounds.lean#L176):

```lean
theorem linear_mass_bounds : ∃ C : ℝ, 0 < C ∧
    ∀ g : ℕ, ∀ d : List ℕ, 2 ≤ complexity g d.length → 1 ≤ d.length →
    d.sum ≤ dimension g d.length → ∀ Y ∈ Set.Icc 0 y₀,
      linearS₀ Y (complexity g d.length) (deficit g d) ≤ C*Real.sqrt (complexity g d.length) ∧
      (6 ≤ 2*d.sum+d.length →
        linearS₀ Y (complexity g d.length) (deficit g d) ≤
          C*(complexity g d.length)/(2*(d.sum : ℝ)+d.length))
```

[WP.linearS₀](../WPFormalization/Statements/Comparison.lean#L164):

```lean
def linearS₀ (Y : ℝ) (h m : ℕ) : ℝ := ∑ l ∈ Finset.range (m+1), linearQ Y h m l
```

</details>

## Comparison estimates

<a id="target-prop:harmonic"></a>

### Paper 5.1: Uniform harmonic comparison

**Paper statement** (PDF p. 24):

For every fixed $n\ge1$, there is a constant $C_n$ such that



$$
-C_n\log^2(h+1)\le
 \log\frac{\mathcal U_{g,n}(\mathbf d;Y)}
 {3^h\Gamma(h)4^{-g}[z^m]\bar H_Y(z)^{-h}}
 \le C_n\sqrt h
$$



 for every stable pair $(g,n)$, every $\mathbf d\in\mathbb Z_{\ge0}^n$ with $|\mathbf d|\le3g-3+n$, and every $Y\in[0,y_0]$. Here $h=2g-2+n$ and $m=3g-3+n-|\mathbf d|$.

**Lean declarations** (proved under classical premises):

- [WP.harmonic_comparison](../WPFormalization/Statements/HarmonicComparison.lean#L12)

<details>
<summary>View formal statements</summary>

[WP.harmonic_comparison](../WPFormalization/Statements/HarmonicComparison.lean#L12):

```lean
theorem harmonic_comparison (P : PsiTheory) (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, ∀ d : List ℕ, d.length = n → Stable g n →
    d.sum ≤ dimension g n → ∀ Y ∈ Set.Icc 0 y₀,
      -C*(Real.log (complexity g n+1))^2 ≤ Real.log (ratio P g d Y) ∧
      Real.log (ratio P g d Y) ≤ C*Real.sqrt (complexity g n)
```

</details>

<a id="target-lem:terminal"></a>

### Paper 5.2: Terminal bounds

**Paper statement** (PDF p. 24):

There are constants $c_\psi,C_\psi,c,C>0$ with the following properties.

1. For every pure $\psi$ tuple $\mathbf e$ with $Z_0$ zero entries, $c_\psi(2/3)^{Z_0}\le C_g(\mathbf e)\le C_\psi2^{Z_0}$, in the normalization [4.3](#target-eq:H4).

2. At every terminal state, $R\ge c\,\mathrm e^{-CZ_0}$.

3. At every state, $R\le\mathrm e^{Ch}$.

**Lean declarations** (proved under classical premises):

- [WP.terminal_bounds](../WPFormalization/Statements/TerminalBounds.lean#L14)
- [WP.pureC_zero_bounds](../WPFormalization/Intersection/PureZeroBounds.lean#L228)
- [WP.terminal_ratio_lower](../WPFormalization/Intersection/TerminalLower.lean#L81)

<details>
<summary>View formal statements</summary>

[WP.terminal_bounds](../WPFormalization/Statements/TerminalBounds.lean#L14):

```lean
theorem terminal_bounds (P : PsiTheory) :
    ∃ cψ Cψ c C : ℝ, 0 < cψ ∧ 0 < Cψ ∧ 0 < c ∧ 0 < C ∧
    (∀ g : ℕ, ∀ d : List ℕ, Stable g d.length → d.sum = dimension g d.length →
      cψ*(2/3 : ℝ)^(zeros d) ≤ pureC P g d ∧ pureC P g d ≤ Cψ*2^(zeros d)) ∧
    (∀ g : ℕ, ∀ d : List ℕ, 1 ≤ d.length → Stable g d.length →
      d.sum ≤ dimension g d.length → ∀ Y ∈ Set.Icc 0 y₀,
        (Terminal g d → c*Real.exp (-C*zeros d) ≤ ratio P g d Y) ∧
        ratio P g d Y ≤ Real.exp (C*complexity g d.length))
```

[WP.pureC_zero_bounds](../WPFormalization/Intersection/PureZeroBounds.lean#L228):

```lean
lemma pureC_zero_bounds (P:PsiTheory)(g:ℕ)(d:List ℕ)(hs:Stable g d.length)
    (hdim:d.sum=dimension g d.length):
    (1/6:ℝ)*(2/3:ℝ)^(d.count 0)≤ pureC P g d ∧
      pureC P g d≤(2:ℝ)^(d.count 0)
```

[WP.terminal_ratio_lower](../WPFormalization/Intersection/TerminalLower.lean#L81):

```lean
lemma terminal_ratio_lower (P:PsiTheory):∃c C:ℝ,0<c ∧0<C ∧∀g:ℕ,∀d:List ℕ,
    1≤d.length→Stable g d.length→d.sum≤dimension g d.length→∀Y∈Icc (0:ℝ) y₀,
      (deficit g d=0 ∨g≤1)→c*Real.exp (-C*(d.count 0))≤ratio P g d Y
```

</details>

<a id="target-lem:lower"></a>

### Paper 5.3: Lower bound

**Paper statement** (PDF p. 25):

There are constants $c,C>0$ such that, at every state,



$$
R\ge c\exp\{-C(Z_0+\log(h+1))\log(h+1)\}.
$$

**Lean declarations** (proved under classical premises):

- [WP.comparison_lower](../WPFormalization/Statements/LowerComparison.lean#L12)

<details>
<summary>View formal statements</summary>

[WP.comparison_lower](../WPFormalization/Statements/LowerComparison.lean#L12):

```lean
theorem comparison_lower (P : PsiTheory) : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ g : ℕ, ∀ d : List ℕ, 1 ≤ d.length → Stable g d.length →
    d.sum ≤ dimension g d.length → ∀ Y ∈ Set.Icc 0 y₀,
      c*Real.exp (-C*(zeros d+Real.log (complexity g d.length+1))*
        Real.log (complexity g d.length+1)) ≤ ratio P g d Y
```

</details>

<a id="target-eq:H30"></a>

### Paper 5.8: Clipped inactive weight

**Paper statement** (PDF p. 26):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\phi(\iota)=\prod_{j=1}^\iota\max(1,c_*\sqrt j),\qquad
\mathcal W(\mathbf d)=4^{Z_0}\phi(\iota).
$$

**Lean declarations** (defined):

- [WP.clippedWeight](../WPFormalization/Statements/Comparison.lean#L267)
- [WP.zeros](../WPFormalization/Statements/Comparison.lean#L254)
- [WP.inactive](../WPFormalization/Statements/Comparison.lean#L260)

<details>
<summary>View formal statements</summary>

[WP.clippedWeight](../WPFormalization/Statements/Comparison.lean#L267):

```lean
def clippedWeight (c : ℝ) (d : List ℕ) : ℝ :=
  (4 : ℝ)^(zeros d) * ∏ j ∈ Finset.range (inactive d), max 1 (c*Real.sqrt (j+1))
```

[WP.zeros](../WPFormalization/Statements/Comparison.lean#L254):

```lean
def zeros (d : List ℕ) : ℕ := (d.filter (fun k => k = 0)).length
```

[WP.inactive](../WPFormalization/Statements/Comparison.lean#L260):

```lean
def inactive (d : List ℕ) : ℕ := (d.filter (fun k => k ≤ 1)).length
```

</details>

<a id="target-lem:weighted-linear"></a>

### Paper 5.4: Weighted linear terms

**Paper statement** (PDF p. 27):

If $c_*$ is sufficiently small, then at every nonterminal state



$$
\sum_{\rm linear}p_{\rm child}
\frac{\mathcal W_{\rm child}}{\mathcal W}
\le1+CS_0/h\le1+Ch^{-1/2}.
$$

**Lean declarations** (proved under classical premises):

- [WP.weighted_linear_bound](../WPFormalization/Statements/Weighted.lean#L15)
- [WP.weightedLinear](../WPFormalization/Weighted/Definitions.lean#L28)
- [WP.PivotChoice](../WPFormalization/Weighted/Definitions.lean#L20)

<details>
<summary>View formal statements</summary>

[WP.weighted_linear_bound](../WPFormalization/Statements/Weighted.lean#L15):

```lean
theorem weighted_linear_bound : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c ∈ Set.Ioc 0 c₀,
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ g pivot : ℕ, ∀ d : List ℕ,
      PivotChoice pivot d → ¬ Terminal g (pivot :: d) →
      (pivot :: d).sum ≤ dimension g (d.length+1) → ∀ Y ∈ Set.Icc 0 y₀,
        weightedLinear c Y g pivot d ≤
          1+C₁*linearS₀ Y (complexity g (d.length+1)) (deficit g (pivot :: d))/complexity g (d.length+1) ∧
        1+C₁*linearS₀ Y (complexity g (d.length+1)) (deficit g (pivot :: d))/complexity g (d.length+1) ≤
          1+C₂/Real.sqrt (complexity g (d.length+1))
```

[WP.weightedLinear](../WPFormalization/Weighted/Definitions.lean#L28):

```lean
def weightedLinear (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) : ℝ :=
  let parent := pivot :: d
  let m := deficit g parent
  let factor := fun g' ds => validModel g' ds Y/model g parent Y *
    signedWeight c ds/clippedWeight c parent
  (∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1) *
    ∑ l ∈ Finset.range (m+1), theta Y l * factor g
      (((pivot : ℤ)+d[j]!+l-1) :: (d.eraseIdx j).map Int.ofNat)) +
  (if g = 0 then 0 else (1/2 : ℝ) * ∑ l ∈ Finset.range (m+1), theta Y l *
    ∑ u ∈ Finset.range (pivot+l-1), factor (g-1)
      ((u : ℤ) :: ((pivot : ℤ)+l-2-u) :: d.map Int.ofNat))
```

[WP.PivotChoice](../WPFormalization/Weighted/Definitions.lean#L20):

```lean
def PivotChoice (pivot : ℕ) (d : List ℕ) : Prop :=
  2 ≤ pivot ∨ (pivot = 1 ∧ ∀ k ∈ d, k ≤ 1) ∨ (pivot = 0 ∧ ∀ k ∈ d, k = 0)
```

</details>

<a id="target-lem:weighted-separating"></a>

### Paper 5.5: Weighted separating terms

**Paper statement** (PDF p. 27):

Let $\eta=1/12$. At every nonterminal state,



$$
\sum_{\rm separating}\frac{\theta_\ell}{2}\,
 \frac{\mathcal M_1\mathcal M_2}{\mathcal M}\,
 \frac{\mathcal W_1\mathcal W_2}{\mathcal W}\,
 \mathrm e^{\eta\min(h_1,h_2)}
 \le CS_0h^{-3/2}(1+\iota)\le Ch^{-1/2},
$$



 where the sum runs over all separating terms of [4.8](#target-eq:H9).

**Lean declarations** (proved under classical premises):

- [WP.weighted_separating_bound](../WPFormalization/Statements/Weighted.lean#L31)
- [WP.weightedSeparating](../WPFormalization/Weighted/Definitions.lean#L45)

<details>
<summary>View formal statements</summary>

[WP.weighted_separating_bound](../WPFormalization/Statements/Weighted.lean#L31):

```lean
theorem weighted_separating_bound : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c ∈ Set.Ioc 0 c₀,
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ g pivot : ℕ, ∀ d : List ℕ,
      PivotChoice pivot d → ¬ Terminal g (pivot :: d) →
      (pivot :: d).sum ≤ dimension g (d.length+1) → ∀ Y ∈ Set.Icc 0 y₀,
        weightedSeparating c Y g pivot d ≤
          C₁*linearS₀ Y (complexity g (d.length+1)) (deficit g (pivot :: d))*
            (1+inactive (pivot :: d))/Real.rpow (complexity g (d.length+1)) (3/2 : ℝ) ∧
        C₁*linearS₀ Y (complexity g (d.length+1)) (deficit g (pivot :: d))*
            (1+inactive (pivot :: d))/Real.rpow (complexity g (d.length+1)) (3/2 : ℝ) ≤
          C₂/Real.sqrt (complexity g (d.length+1))
```

[WP.weightedSeparating](../WPFormalization/Weighted/Definitions.lean#L45):

```lean
def weightedSeparating (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) : ℝ :=
  let parent := pivot :: d
  let m := deficit g parent
  (1/2 : ℝ) * ∑ l ∈ Finset.range (m+1), theta Y l *
    ∑ u ∈ Finset.range (pivot+l-1), ∑ g₁ ∈ Finset.range (g+1),
      ∑ I ∈ (Finset.range d.length).powerset,
        let d₁ := (u : ℤ) :: selected (d.map Int.ofNat) I
        let d₂ := ((pivot : ℤ)+l-2-u) :: selected (d.map Int.ofNat) ((Finset.range d.length) \ I)
        validModel g₁ d₁ Y*validModel (g-g₁) d₂ Y/model g parent Y *
          signedWeight c d₁*signedWeight c d₂/clippedWeight c parent *
          Real.exp ((1/12 : ℝ)*min (complexity g₁ d₁.length) (complexity (g-g₁) d₂.length))
```

</details>

<a id="target-lem:upper"></a>

### Paper 5.6: Upper bound

**Paper statement** (PDF p. 29):

There is a constant $C$ such that $R\le C\mathcal W\mathrm e^{C\sqrt h}$ at every state.

**Lean declarations** (proved under classical premises):

- [WP.comparison_upper](../WPFormalization/Statements/UpperComparison.lean#L12)

<details>
<summary>View formal statements</summary>

[WP.comparison_upper](../WPFormalization/Statements/UpperComparison.lean#L12):

```lean
theorem comparison_upper (P : PsiTheory) : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ c ∈ Set.Ioc 0 c₀, ∃ C : ℝ, 0 < C ∧
      ∀ g : ℕ, ∀ d : List ℕ, 1 ≤ d.length → Stable g d.length →
      d.sum ≤ dimension g d.length → ∀ Y ∈ Set.Icc 0 y₀,
        ratio P g d Y ≤ C*clippedWeight c d*Real.exp (C*Real.sqrt (complexity g d.length))
```

</details>

## Marked ratios

<a id="target-eq:TL9"></a>

### Paper 6.1: Marked profiles

**Paper statement** (PDF p. 31):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\overline U_{g,p}(\mathbf d)=a^h r^m U_{g,p}(\mathbf d),
 \qquad W_{g,p}=4^g\overline U_{g,p}(\mathbf0),
 \qquad c_{g,p}(\mathbf d)=
 \frac{\overline U_{g,p}(\mathbf d)}{\overline U_{g,p}(\mathbf0)}.
$$

**Lean declarations** (defined under classical premises):

- [WP.W](../WPFormalization/Statements/Marked.lean#L20)
- [WP.profile](../WPFormalization/Statements/Marked.lean#L27)

<details>
<summary>View formal statements</summary>

[WP.W](../WPFormalization/Statements/Marked.lean#L20):

```lean
def W (P : PsiTheory) (g p : ℕ) (Y : ℝ) : ℝ :=
  (4 : ℝ)^g * normalized P g (List.replicate p 0) Y
```

[WP.profile](../WPFormalization/Statements/Marked.lean#L27):

```lean
def profile (P : PsiTheory) (g : ℕ) (d : List ℕ) (Y : ℝ) : ℝ :=
  normalized P g d Y / normalized P g (List.replicate d.length 0) Y
```

</details>

<a id="target-eq:TL12"></a>

### Paper 6.4: Shifted dilaton identity

**Paper statement** (PDF p. 31):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
h\overline U_{g,p}(\mathbf0)=
 \sum_{d\ge1}b_d(Y)\overline U_{g,p+1}(d,0^p),
 \qquad
 b_d(Y)=\frac{X^{(d)}(Y)r^{d-1}}{a(2d+1)!!}
 =\frac13[z^{d-1}]\bar H_Y(z).
$$

**Lean declarations** (proved under classical premises):

- [WP.shifted_dilaton](../WPFormalization/Statements/Marked.lean#L43)
- [WP.dilaton_coefficient](../WPFormalization/Statements/Marked.lean#L55)
- [WP.dilatonCoeff](../WPFormalization/Statements/Marked.lean#L35)

<details>
<summary>View formal statements</summary>

[WP.shifted_dilaton](../WPFormalization/Statements/Marked.lean#L43):

```lean
theorem shifted_dilaton (P : PsiTheory) (g p : ℕ) (hst : Stable g p)
    (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    (complexity g p : ℝ) * normalized P g (List.replicate p 0) Y =
      ∑ d ∈ Finset.range (dimension g (p+1)+1),
        if 1 ≤ d then dilatonCoeff Y d * normalized P g (d :: List.replicate p 0) Y else 0
```

[WP.dilaton_coefficient](../WPFormalization/Statements/Marked.lean#L55):

```lean
theorem dilaton_coefficient (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) (d : ℕ) (hd : 1 ≤ d) :
    dilatonCoeff Y d = realCoeff (barH Y) (d-1)/3
```

[WP.dilatonCoeff](../WPFormalization/Statements/Marked.lean#L35):

```lean
def dilatonCoeff (Y : ℝ) (d : ℕ) : ℝ :=
  (iteratedDeriv d X Y).re * r Y^(d-1) / (a Y * oddFactorial d)
```

</details>

<a id="target-eq:TL14"></a>

### Paper 6.6: Shifted KdV identity

**Paper statement** (PDF p. 31):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\overline U_{g,p}(1,0^{p-1})
 =\frac14\overline U_{g-1,p+2}(\mathbf0)
 +\frac32\sum_{j=0}^g\sum_{s=0}^{p-2}\binom{p-2}s
 \overline U_{j,s+2}(\mathbf0)
 \overline U_{g-j,p-s}(\mathbf0).
$$

**Lean declarations** (proved under classical premises):

- [WP.shifted_kdv](../WPFormalization/Statements/Marked.lean#L69)

<details>
<summary>View formal statements</summary>

[WP.shifted_kdv](../WPFormalization/Statements/Marked.lean#L69):

```lean
theorem shifted_kdv (P : PsiTheory) (g p : ℕ) (hg : 1 ≤ g) (hp : 2 ≤ p)
    (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) :
    normalized P g (1 :: List.replicate (p-1) 0) Y =
      normalized P (g-1) (List.replicate (p+2) 0) Y / 4 +
      3/2 * ∑ j ∈ Finset.range (g+1), ∑ s ∈ Finset.range (p-1),
        (Nat.choose (p-2) s : ℝ) * normalized P j (List.replicate (s+2) 0) Y *
          normalized P (g-j) (List.replicate (p-s) 0) Y
```

</details>

<a id="target-lem:monotone"></a>

### Paper 6.1: Monotonicity in the degrees

**Paper statement** (PDF p. 32):

For every stable $(g,p)$, every degree tuple $\mathbf d$, every $i$ and every $Y\in[0,y_0]$,



$$
\overline U_{g,p}(\mathbf d)\ge
 \overline U_{g,p}(\mathbf d+\mathbf e_i),
 \qquad 0\le c_{g,p}(\mathbf d)\le1.
$$



 Amplitudes outside the dimension range are zero.

**Lean declarations** (proved under classical premises):

- [WP.profile_monotone](../WPFormalization/Statements/Marked.lean#L84)

<details>
<summary>View formal statements</summary>

[WP.profile_monotone](../WPFormalization/Statements/Marked.lean#L84):

```lean
theorem profile_monotone (P : PsiTheory) (g : ℕ) (d : List ℕ) (hst : Stable g d.length)
    (i : ℕ) (hi : i < d.length) (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) :
    normalized P g (d.set i (d[i]!+1)) Y ≤ normalized P g d Y ∧
    0 ≤ profile P g d Y ∧ profile P g d Y ≤ 1
```

</details>

<a id="target-eq:TL19"></a>

### Paper 6.11: Separating convolution estimates

**Paper statement** (PDF p. 32):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
S_{g,p}=O_p(g^{-2}),\qquad T_{g,p}=O_p(g^{-1}),
$$

**Lean declarations** (proved under classical premises):

- [WP.separating_estimates](../WPFormalization/Statements/MarkedSeparating.lean#L12)
- [WP.separatingS](../WPFormalization/Statements/Marked.lean#L95)
- [WP.separatingT](../WPFormalization/Statements/Marked.lean#L103)
- [WP.separating_S_all_markings](../WPFormalization/Statements/MarkedExtensions.lean#L30)
- [WP.separating_T_two_markings](../WPFormalization/Statements/MarkedExtensions.lean#L36)

<details>
<summary>View formal statements</summary>

[WP.separating_estimates](../WPFormalization/Statements/MarkedSeparating.lean#L12):

```lean
theorem separating_estimates (P : PsiTheory) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Icc 0 y₀,
      |separatingS P g p Y| ≤ C/(g : ℝ)^2 ∧ |separatingT P g p Y| ≤ C/g
```

[WP.separatingS](../WPFormalization/Statements/Marked.lean#L95):

```lean
def separatingS (P : PsiTheory) (g p : ℕ) (Y : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (g+1), ∑ s ∈ Finset.range p,
    (Nat.choose (p-1) s : ℝ) * W P j (s+1) Y * W P (g-j) (p-s) Y) / W P g p Y
```

[WP.separatingT](../WPFormalization/Statements/Marked.lean#L103):

```lean
def separatingT (P : PsiTheory) (g p : ℕ) (Y : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (g+1), ∑ s ∈ Finset.range (p-1),
    (Nat.choose (p-2) s : ℝ) * W P j (s+2) Y * W P (g-j) (p-s) Y) / W P g p Y
```

[WP.separating_S_all_markings](../WPFormalization/Statements/MarkedExtensions.lean#L30):

```lean
theorem separating_S_all_markings (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Icc 0 y₀,
      |separatingS P g p Y| ≤ C/(complexity g p : ℝ)^2
```

[WP.separating_T_two_markings](../WPFormalization/Statements/MarkedExtensions.lean#L36):

```lean
theorem separating_T_two_markings (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Icc 0 y₀,
      |separatingT P g 2 Y| ≤ C/(g : ℝ)^2
```

</details>

<a id="target-eq:TL23"></a>

### Paper 6.15: Quadratic profile estimate with at least two markings

**Paper statement** (PDF p. 33):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
0\le1-c_{g,p}(\mathbf d)
 \le C_p\frac{|\mathbf d|(|\mathbf d|+1)}g,
 \qquad p\ge2.
$$

**Lean declarations** (proved under classical premises):

- [WP.quadratic_profile](../WPFormalization/Statements/QuadraticProfile.lean#L12)
- [WP.quadratic_profile_all_markings](../WPFormalization/Statements/MarkedExtensions.lean#L11)

<details>
<summary>View formal statements</summary>

[WP.quadratic_profile](../WPFormalization/Statements/QuadraticProfile.lean#L12):

```lean
theorem quadratic_profile (P : PsiTheory) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, 1 ≤ g → ∀ d : List ℕ, d.length = p →
    ∀ Y ∈ Set.Icc 0 y₀, 0 ≤ 1-profile P g d Y ∧
      1-profile P g d Y ≤ C*(d.sum : ℝ)*(d.sum+1)/g
```

[WP.quadratic_profile_all_markings](../WPFormalization/Statements/MarkedExtensions.lean#L11):

```lean
theorem quadratic_profile_all_markings (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, 1 ≤ g → ∀ d : List ℕ, d.length = p →
    ∀ Y ∈ Set.Icc 0 y₀, 0 ≤ 1-profile P g d Y ∧
      1-profile P g d Y ≤ C*(d.sum : ℝ)*(d.sum+1)/g
```

</details>

<a id="target-eq:TL24"></a>

### Paper 6.16: Two-sided marked cusp ratio

**Paper statement** (PDF p. 33):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
(2g-2+p)\frac{W_{g,p}}{W_{g,p+1}}
 =A(Y)+O_p(g^{-1}),\qquad p\ge1.
$$

**Lean declarations** (proved under classical premises):

- [WP.marked_cusp](../WPFormalization/Statements/MarkedCusp.lean#L12)
- [WP.marked_cusp_all](../WPFormalization/Statements/MarkedExtensions.lean#L18)

<details>
<summary>View formal statements</summary>

[WP.marked_cusp](../WPFormalization/Statements/MarkedCusp.lean#L12):

```lean
theorem marked_cusp (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Icc 0 y₀,
      |(complexity g p : ℝ)*W P g p Y/W P g (p+1) Y - A Y| ≤ C/g
```

[WP.marked_cusp_all](../WPFormalization/Statements/MarkedExtensions.lean#L18):

```lean
theorem marked_cusp_all (P : PsiTheory) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Icc 0 y₀,
      |(complexity g p : ℝ)*W P g p Y/W P g (p+1) Y - A Y| ≤ C/g
```

</details>

<a id="target-eq:TL27"></a>

### Paper 6.19: Marked genus exchange

**Paper statement** (PDF p. 34):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\frac{W_{g-1,p+2}}{W_{g,p}}=1+O_p(g^{-1}),\qquad p\ge2.
$$

**Lean declarations** (proved under classical premises):

- [WP.marked_genus](../WPFormalization/Statements/MarkedGenus.lean#L12)
- [WP.marked_genus_all](../WPFormalization/Statements/MarkedExtensions.lean#L24)

<details>
<summary>View formal statements</summary>

[WP.marked_genus](../WPFormalization/Statements/MarkedGenus.lean#L12):

```lean
theorem marked_genus (P : PsiTheory) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Icc 0 y₀,
      |W P (g-1) (p+2) Y / W P g p Y - 1| ≤ C/g
```

[WP.marked_genus_all](../WPFormalization/Statements/MarkedExtensions.lean#L24):

```lean
theorem marked_genus_all (P : PsiTheory) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Icc 0 y₀,
      |W P (g-1) (p+2) Y / W P g p Y - 1| ≤ C/g
```

</details>

<a id="target-prop:marked-ratios"></a>

### Paper 6.2: Marked cusp and genus ratios

**Paper statement** (PDF p. 34):

For every fixed $p\ge1$, uniformly for $0\le Y<y_0$ and $x=X(Y)$, the cusp ratio of $\Phi_g^{(p)}$ satisfies 6.20 and the genus ratio satisfies 6.21, with $\Psi(x)=\lambda(Y)/2$. The genus ratio holds also at $p=0$.

**Lean declarations** (proved under classical premises):

- [WP.marked_ratios](../WPFormalization/Statements/MarkedRatios.lean#L14)

<details>
<summary>View formal statements</summary>

[WP.marked_ratios](../WPFormalization/Statements/MarkedRatios.lean#L14):

```lean
theorem marked_ratios (P : PsiTheory) :
    (∀ p : ℕ, 1 ≤ p → ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀,
      ∀ Y ∈ Set.Ico 0 y₀,
        |XR Y*markedF P g (p+1) (XR Y)/markedF P g p (XR Y) -
          (complexity g p : ℝ)*Psi (XR Y)| ≤ C*Psi (XR Y)) ∧
    (∀ p : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Ico 0 y₀,
      |markedF P (g-1) (p+2) (XR Y)/(4*r Y*markedF P g p (XR Y))-1| ≤ C/g)
```

</details>

## The leading term

<a id="target-eq:PF1"></a>

### Paper 7.1: Kernel moments and action

**Paper statement** (PDF p. 35):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\Theta=\sum_{\ell\ge0}w_\ell=-\frac1{\bar K'(1)},\qquad
 M_1=\sum_{\ell\ge0}\ell w_\ell=\frac{\bar K''(1)}{2\bar K'(1)^2},\qquad
 \mathcal Z=Aar^{3/2}=\sqrt2 I.
$$

**Lean declarations** (defined under classical premises):

- [WP.Theta](../WPFormalization/Statements/Marked.lean#L113)
- [WP.moment₁](../WPFormalization/Statements/Marked.lean#L119)
- [WP.Z](../WPFormalization/Statements/Marked.lean#L125)
- [WP.kernel_action_moments](../WPFormalization/Statements/Marked.lean#L132)

<details>
<summary>View formal statements</summary>

[WP.Theta](../WPFormalization/Statements/Marked.lean#L113):

```lean
def Theta (Y : ℝ) : ℝ := ∑' l : ℕ, weight Y l
```

[WP.moment₁](../WPFormalization/Statements/Marked.lean#L119):

```lean
def moment₁ (Y : ℝ) : ℝ := ∑' l : ℕ, (l : ℝ)*weight Y l
```

[WP.Z](../WPFormalization/Statements/Marked.lean#L125):

```lean
def Z (Y : ℝ) : ℝ := A Y*a Y*Real.rpow (r Y) (3/2 : ℝ)
```

[WP.kernel_action_moments](../WPFormalization/Statements/Marked.lean#L132):

```lean
theorem kernel_action_moments (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    Theta Y = -1/(deriv (barK Y) 1).re ∧
    moment₁ Y = (iteratedDeriv 2 (barK Y) 1).re/(2*(deriv (barK Y) 1).re^2) ∧
    Z Y = Real.sqrt 2*action Y
```

</details>

<a id="target-eq:PF3"></a>

### Paper 7.3: Marked leading model

**Paper statement** (PDF p. 35):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\mathcal J_{g,p}(Y)=
 \frac{\Gamma(h)4^{-g}}{\sqrt{\pi h}}
 \mathcal Z(Y)^{-h}r(Y)^{p/2}\sqrt{A(Y)\Theta(Y)}.
$$

**Lean declarations** (defined):

- [WP.markedModel](../WPFormalization/Statements/Marked.lean#L148)

<details>
<summary>View formal statements</summary>

[WP.markedModel](../WPFormalization/Statements/Marked.lean#L148):

```lean
def markedModel (g p : ℕ) (Y : ℝ) : ℝ :=
  Real.Gamma (complexity g p) * (4 : ℝ)⁻¹^g / Real.sqrt (Real.pi*complexity g p) *
    (Z Y)⁻¹^(complexity g p) * Real.rpow (r Y) ((p : ℝ)/2) * Real.sqrt (A Y*Theta Y)
```

</details>

<a id="target-prop:prefactor"></a>

### Paper 7.1: Absolute marked prefactor

**Paper statement** (PDF p. 35):

For each fixed $p\ge1$, uniformly for $0\le Y<y_0$,



$$
\Phi_g^{(p)}(X(Y))=
 \frac{\mathcal J_{g,p}(Y)}{\pi}
 \left(1+O_p\!\left(\frac{\log(g+1)}g\right)\right).
$$

**Lean declarations** (proved under classical premises):

- [WP.absolute_prefactor](../WPFormalization/Statements/AbsolutePrefactor.lean#L13)

<details>
<summary>View formal statements</summary>

[WP.absolute_prefactor](../WPFormalization/Statements/AbsolutePrefactor.lean#L13):

```lean
theorem absolute_prefactor (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Ico 0 y₀,
      |Real.pi*markedF P g p (XR Y)/markedModel g p Y-1| ≤ C*Real.log (g+1)/g
```

</details>

<a id="target-lem:first-degree"></a>

### Paper 7.2: First degree correction

**Paper statement** (PDF p. 35):

For each fixed $p\ge1$, uniformly for $Y\in[0,y_0]$ and for degree tuples with $D\le h^{1/4}$,



$$
\begin{aligned}
 c_{g,p}(\mathbf d)&=1-\frac{\delta_p(\mathbf d)}h
       +O_p\!\left(\frac{(D+1)^4}{h^2}\right),\\
 \delta_p(\mathbf d)&=A\left\{
 \Theta\bigl(D^2+(p-4)D\bigr)+2M_1D+
 \frac{q(q+5-2p)}2\right\}.
 \end{aligned}
$$

**Lean declarations** (proved under classical premises):

- [WP.first_degree](../WPFormalization/Statements/FirstDegree.lean#L13)
- [WP.degreeCorrection](../WPFormalization/Statements/Marked.lean#L158)
- [WP.first_degree_all_degrees](../WPFormalization/Statements/FirstDegree.lean#L22)

<details>
<summary>View formal statements</summary>

[WP.first_degree](../WPFormalization/Statements/FirstDegree.lean#L13):

```lean
theorem first_degree (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ d : List ℕ, d.length = p →
    (d.sum : ℝ) ≤ Real.rpow (complexity g p) (1/4 : ℝ) →
    ∀ Y ∈ Set.Icc 0 y₀,
      |profile P g d Y - (1-degreeCorrection d Y/complexity g p)| ≤
        C*(d.sum+1 : ℝ)^4/(complexity g p : ℝ)^2
```

[WP.degreeCorrection](../WPFormalization/Statements/Marked.lean#L158):

```lean
def degreeCorrection (d : List ℕ) (Y : ℝ) : ℝ :=
  let D : ℝ := d.sum
  let p : ℝ := d.length
  let q : ℝ := (d.filter (fun k => 0 < k)).length
  A Y*(Theta Y*(D^2+(p-4)*D)+2*moment₁ Y*D+q*(q+5-2*p)/2)
```

[WP.first_degree_all_degrees](../WPFormalization/Statements/FirstDegree.lean#L22):

```lean
theorem first_degree_all_degrees (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ d : List ℕ, d.length = p →
    ∀ Y ∈ Set.Icc 0 y₀,
      |profile P g d Y - (1-degreeCorrection d Y/complexity g p)| ≤
        C*(d.sum+1 : ℝ)^4/(complexity g p : ℝ)^2
```

</details>

<a id="target-eq:PF8"></a>

### Paper 7.8: Transport differential equation

**Paper statement** (PDF p. 36):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\frac{\mathrm{d}}{\mathrm{d}Y}\log\Phi_g^{(p)}(X(Y))
 =\frac{h+\beta_p+O_p(h^{-1})}{A r}.
$$

**Lean declarations** (proved under classical premises):

- [WP.transport_equation](../WPFormalization/Statements/TransportEquation.lean#L12)
- [WP.transportBeta](../WPFormalization/Statements/Volumes.lean#L54)

<details>
<summary>View formal statements</summary>

[WP.transport_equation](../WPFormalization/Statements/TransportEquation.lean#L12):

```lean
theorem transport_equation (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Ico 0 y₀,
      |A Y*r Y*deriv (fun t => Real.log (markedF P g p (XR t))) Y -
        ((complexity g p : ℝ)+transportBeta p Y)| ≤ C/complexity g p
```

[WP.transportBeta](../WPFormalization/Statements/Volumes.lean#L54):

```lean
def transportBeta (p : ℕ) (Y : ℝ) : ℝ :=
  A Y*((7-2*(p : ℝ))/4*Theta Y-moment₁ Y+2-p)-1/2
```

</details>

<a id="target-eq:PF12"></a>

### Paper 7.13: Endpoint string reduction and pure psi asymptotic

**Paper statement** (PDF p. 37):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
C_g(0^p,2^m)=
 \prod_{i=0}^{p-1}
 \frac{5(m-i)}{3(2g-3+p+m-2i)}\ C_g(2^{3g-3})
 =\frac1\pi+O_p(g^{-1}).
$$

**Lean declarations** (proved under classical premises):

- [WP.endpoint_string](../WPFormalization/Statements/Marked.lean#L170)
- [WP.endpoint_pure_limit](../WPFormalization/Statements/Marked.lean#L185)

<details>
<summary>View formal statements</summary>

[WP.endpoint_string](../WPFormalization/Statements/Marked.lean#L170):

```lean
theorem endpoint_string (P : PsiTheory) (g p : ℕ) (hg : 2 ≤ g) :
    let m := dimension g p
    pureC P g (List.replicate p 0 ++ List.replicate m 2) =
      (∏ i ∈ Finset.range p, 5*((m : ℝ)-i) /
        (3*(2*(g : ℝ)-3+p+m-2*i))) * pureC P g (List.replicate (3*g-3) 2)
```

[WP.endpoint_pure_limit](../WPFormalization/Statements/Marked.lean#L185):

```lean
theorem endpoint_pure_limit (P : PsiTheory) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀,
      |pureC P g (List.replicate p 0 ++ List.replicate (dimension g p) 2)-1/Real.pi| ≤ C/g
```

</details>

<a id="target-eq:PF13"></a>

### Paper 7.14: Endpoint harmonic ratio equals pure psi normalization

**Paper statement** (PDF p. 37):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\frac{\overline U_{g,p}(0^p;y_0)}
      {\mathcal M_{g,p}(0^p;y_0)}=C_g(0^p,2^m).
$$

**Lean declarations** (proved under classical premises):

- [WP.endpoint_ratio](../WPFormalization/Statements/Marked.lean#L195)

<details>
<summary>View formal statements</summary>

[WP.endpoint_ratio](../WPFormalization/Statements/Marked.lean#L195):

```lean
theorem endpoint_ratio (P : PsiTheory) (g p : ℕ) (hg : 2 ≤ g) :
    ratio P g (List.replicate p 0) y₀ =
      pureC P g (List.replicate p 0 ++ List.replicate (dimension g p) 2)
```

</details>

<a id="target-eq:boundary-factor"></a>

### Paper 7.19: All-length quantitative boundary factor and growing-length Kimura asymptotic

**Paper statement** (PDF p. 38):

Stage-one implementation: the linked theorem proves the quantitative estimate for all nonnegative lengths and the growing-length Kimura consequence. It uses the actual WP-volume dictionary and the previously registered classical Gamma input.

For completeness, we derive the boundary-length consequence stated in the introduction. Fix $n\ge1$, put $x_i=L_i/2$, and set $S(x)=\sinh(x)/x$, with $S(0)=1$. At $Y=0$, the normalization [6.1](#target-eq:TL9) gives $c_{g,n}(\mathbf d)=[\tau_{d_1}\cdots\tau_{d_n}]_{g,n}/V_{g,n}$. Thus the volume polynomial, extended by zero outside its degree range, is



$$
\frac{V_{g,n}(\mathbf L)}{V_{g,n}}
 =\sum_{\mathbf d\ge0}c_{g,n}(\mathbf d)
   \prod_{i=1}^n\frac{x_i^{2d_i}}{(2d_i+1)!}.
$$



 Divide by $\prod_i S(x_i)$ and regard the product weights as the law of independent nonnegative integers $d_i$. The identity $\sum_{d\ge0}(2d)(2d+1)x^{2d}/(2d+1)!=x^2S(x)$ gives $\mathbb E[d_i(d_i+1)]\le x_i^2/2$. Since $D(D+1)\le n\sum_i d_i(d_i+1)$, where $D=\sum_i d_i$, [6.15](#target-eq:TL23), including its one-marking case, yields



$$
0\le 1-\frac{V_{g,n}(\mathbf L)}{V_{g,n}\prod_i S(L_i/2)}
 \le \frac{C_n}{g}\sum_{i=1}^n L_i^2.
$$



 For $L_i=o(\sqrt g)$ the right side tends to zero. Corollary [1.2](#target-cor:constant) and Stirling’s formula then give the asserted asymptotic formula.

**Lean declarations** (proved under classical premises):

- [WP.growing_boundary_factor](../WPFormalization/Volumes/GrowingBoundaryTheorem.lean#L18)

<details>
<summary>View formal statements</summary>

[WP.growing_boundary_factor](../WPFormalization/Volumes/GrowingBoundaryTheorem.lean#L18):

```lean
theorem growing_boundary_factor (P : PsiTheory)
    (G : External.WeilPeterssonGeometry.{u,v} P) (n : ℕ) (hn : 1 ≤ n) :
    (∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, 1 ≤ g → ∀ L : Fin n → ℝ,
      (∀ i, 0 ≤ L i) →
      0 ≤ 1-External.wpVolume G g n L /
        (External.cuspVolume G g n *
          ∏ i, (if L i=0 then 1 else Real.sinh (L i/2)/(L i/2))) ∧
      1-External.wpVolume G g n L /
        (External.cuspVolume G g n *
          ∏ i, (if L i=0 then 1 else Real.sinh (L i/2)/(L i/2))) ≤
        C/g * ∑ i, (L i)^2) ∧
    (∀ L : ℕ → Fin n → ℝ, (∀ g i, 0 ≤ L g i) →
      (∀ i, Tendsto (fun g : ℕ => L g i/Real.sqrt g) atTop (𝓝 0)) →
      Tendsto (fun g : ℕ => External.wpVolume G g n (L g) /
        (External.cuspVolume G g n *
          ∏ i, (if L g i=0 then 1 else Real.sinh (L g i/2)/(L g i/2))))
        atTop (𝓝 1) ∧
      Tendsto (fun g : ℕ => External.wpVolume G g n (L g) /
        (Real.sqrt (2/Real.pi)*(4*Real.pi^2)^(2*g+n-3)*
          Real.Gamma (2*(g:ℝ)+n-5/2) *
          ∏ i, (if L g i=0 then 1 else Real.sinh (L g i/2)/(L g i/2))))
        atTop (𝓝 1))
```

</details>

## Higher-order corrections

<a id="target-eq:ST13"></a>

### Paper 8.1: First marked correction coefficient

**Paper statement** (PDF p. 38):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
t_p=\frac{-2p^2+12p-11}{20},\qquad
 \mathcal L_p(Y)=t_p-\int_Y^{y_0}\frac{\gamma_p(v)}{A(v)r(v)}\,\mathrm{d}v.
$$

**Lean declarations** (defined):

- [WP.HigherOrder.firstEndpointConstant](../WPFormalization/HigherOrder/SecondProfile.lean#L135)
- [WP.HigherOrder.firstMarkedCorrection](../WPFormalization/HigherOrder/SecondProfile.lean#L139)

<details>
<summary>View formal statements</summary>

[WP.HigherOrder.firstEndpointConstant](../WPFormalization/HigherOrder/SecondProfile.lean#L135):

```lean
def firstEndpointConstant (p : ℕ) : ℝ := (-2*(p : ℝ)^2+12*p-11)/20
```

[WP.HigherOrder.firstMarkedCorrection](../WPFormalization/HigherOrder/SecondProfile.lean#L139):

```lean
def firstMarkedCorrection (p : ℕ) (Y : ℝ) : ℝ :=
  firstEndpointConstant p - ∫ v in Y..y₀, transportGamma p v/(A v*r v)
```

</details>

<a id="target-thm:first-correction"></a>

### Paper 8.1: Uniform marked first correction

**Paper statement** (PDF p. 38):

For every fixed $p\ge1$, uniformly for $0\le Y<y_0$,



$$
\Phi_g^{(p)}(X(Y))=\frac{\mathcal J_{g,p}(Y)}\pi
 \left\{1+\frac{\mathcal L_p(Y)}h+
            O_p\!\left(\frac{\log(g+1)}{g^2}\right)\right\}.
$$



 In particular the leading relative error is $O_p(g^{-1})$.

**Lean declarations** (proved under classical premises):

- [WP.HigherOrder.first_correction](../WPFormalization/Statements/FirstCorrection.lean#L9)

<details>
<summary>View formal statements</summary>

[WP.HigherOrder.first_correction](../WPFormalization/Statements/FirstCorrection.lean#L9):

```lean
theorem first_correction (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Ico 0 y₀,
      |Real.pi*markedF P g p (XR Y)/markedModel g p Y -
        (1+firstMarkedCorrection p Y/(complexity g p : ℝ))| ≤
      C*Real.log (g+1)/(g : ℝ)^2
```

</details>

<a id="target-thm:full-expansion"></a>

### Paper 8.2: Complete uniform marked expansion

**Paper statement** (PDF p. 39):

For each fixed $p\ge1$ there are $C_p,\mathfrak B_p,c_p,h_p>0$ such that, for $h=2g-2+p\ge h_p$ and $0\le K\le c_p\sqrt h$,



$$
\sup_{0\le Y<y_0}\left|
 \frac{\pi\Phi_g^{(p)}(X(Y))}{\mathcal J_{g,p}(Y)}
       -\sum_{j=0}^K\frac{\mathcal L_{p,j}(Y)}{h^j}\right|
 \le\frac{C_p\mathfrak B_p^{K+1}((K+1)!)^2}{h^{K+1}},
 \qquad \mathcal L_{p,0}=1.
$$



 The coefficients are specified by the finite rules and integrals of Appendix C, and have the Gevrey-2 norms stated above on one complex neighborhood of $[0,y_0]$. The same real error holds for the logarithm with coefficients $a_{p,j}$. A sufficiently small square-root truncation has error $O_p(\mathrm{e}^{-a_p\sqrt h})$; no convergence of the infinite series is required.

**Lean declarations** (proved under classical premises):

- [WP.HigherOrder.full_expansion](../WPFormalization/HigherOrder/CanonicalExpansionStatement.lean#L14)

<details>
<summary>View formal statements</summary>

[WP.HigherOrder.full_expansion](../WPFormalization/HigherOrder/CanonicalExpansionStatement.lean#L14):

```lean
theorem full_expansion (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C B c h₀ : ℝ, 0 < C ∧ 0 < B ∧ 0 < c ∧ 0 < h₀ ∧
      GevreyExtensionPair (logarithmicMarkedCoefficient P p) (markedCoefficient P p) C B ∧
      (∀ (g K : ℕ), h₀ ≤ (complexity g p : ℝ) →
        (K : ℝ) ≤ c*Real.sqrt (complexity g p) → ∀ Y ∈ Set.Ico 0 y₀,
        |Real.pi*markedF P g p (XR Y)/markedModel g p Y -
          ∑ j ∈ Finset.range (K+1), markedCoefficient P p j Y/(complexity g p : ℝ)^j| ≤
            C*B^(K+1)*((K+1).factorial : ℝ)^2/(complexity g p : ℝ)^(K+1)) ∧
      (∀ (g K : ℕ), h₀ ≤ (complexity g p : ℝ) →
        (K : ℝ) ≤ c*Real.sqrt (complexity g p) → ∀ Y ∈ Set.Ico 0 y₀,
        |Real.log (Real.pi*markedF P g p (XR Y)/markedModel g p Y) -
          ∑ j ∈ Finset.range (K+1), logarithmicMarkedCoefficient P p j Y/
            (complexity g p : ℝ)^j| ≤
            C*B^(K+1)*((K+1).factorial : ℝ)^2/(complexity g p : ℝ)^(K+1)) ∧
      (∃ c' a C' h₁ : ℝ, 0 < c' ∧ c' ≤ c ∧ 0 < a ∧ 0 < C' ∧ 0 < h₁ ∧
        ∀ g : ℕ, h₁ ≤ (complexity g p : ℝ) → ∀ Y ∈ Set.Ico 0 y₀,
          |Real.pi*markedF P g p (XR Y)/markedModel g p Y -
            ∑ j ∈ Finset.range (⌊c'*Real.sqrt (complexity g p)⌋₊+1),
              markedCoefficient P p j Y/(complexity g p : ℝ)^j| ≤
                C'*Real.exp (-a*Real.sqrt (complexity g p)))
```

</details>

## Coefficient extraction

<a id="target-lem:convolution"></a>

### Paper 9.1: Positive convolution factor

**Paper statement** (PDF p. 40):

For each stable marked pair $(g,p)$ with $p\ge1$, the marked generating function has the exact factorization



$$
\Phi_g^{(p)}(x)=V(x)^h R_{g,p}(x),\qquad
 V(x)=Y'(x)=1/a(Y(x)),\qquad h=2g-2+p,
$$



 where $R_{g,p}$ has nonnegative Taylor coefficients and converges for $0\le x<x_c$.

**Lean declarations** (proved under classical premises):

- [WP.positive_convolution](../WPFormalization/Statements/Boundary.lean#L38)
- [WP.convolutionR](../WPFormalization/Statements/ConvolutionDefinitions.lean#L18)
- [WP.universalV](../WPFormalization/Statements/ConvolutionDefinitions.lean#L11)

<details>
<summary>View formal statements</summary>

[WP.positive_convolution](../WPFormalization/Statements/Boundary.lean#L38):

```lean
theorem positive_convolution (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p) (hst : Stable g p) :
    (∀ x ∈ Set.Ico 0 xCritical, universalV P x = ((a (inverseY x))⁻¹ : ℝ) ∧
      iteratedDeriv p (Phi P g) x =
        universalV P x^(complexity g p)*convolutionR P g p x) ∧
    (∀ j, 0 ≤ realCoeff (convolutionR P g p) j) ∧
    (∀ z : ℂ, ‖z‖ < xCritical →
      HasSum (fun j => coeff (convolutionR P g p) j*z^j) (convolutionR P g p z))
```

[WP.convolutionR](../WPFormalization/Statements/ConvolutionDefinitions.lean#L18):

```lean
def convolutionR (P : PsiTheory) (g p : ℕ) (z : ℂ) : ℂ :=
  iteratedDeriv p (Phi P g) z / universalV P z^(complexity g p)
```

[WP.universalV](../WPFormalization/Statements/ConvolutionDefinitions.lean#L11):

```lean
def universalV (P : PsiTheory) (z : ℂ) : ℂ := iteratedDeriv 3 (Phi P 0) z
```

</details>

<a id="target-eq:TL37"></a>

### Paper 9.4: Cusp-count law and model center and variance

**Paper statement** (PDF p. 41):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\mathbb P_x(N=k)=\frac{[z^k]F(z)x^k}{F(x)},\qquad
 \mu=h\Psi(x),\qquad \sigma^2=h\mathscr D\Psi(x).
$$

**Lean declarations** (defined under classical premises):

- [WP.cuspMass](../WPFormalization/Statements/Volumes.lean#L99)

<details>
<summary>View formal statements</summary>

[WP.cuspMass](../WPFormalization/Statements/Volumes.lean#L99):

```lean
def cuspMass (P : PsiTheory) (g p k : ℕ) (x : ℝ) : ℝ :=
  realCoeff (iteratedDeriv p (Phi P g)) k * x^k / markedF P g p x
```

</details>

<a id="target-prop:local-limit"></a>

### Paper 9.2: Uniform local limit theorem

**Paper statement** (PDF p. 41):

Fix $p\ge1$ and use the notation [9.4](#target-eq:TL37). Along every sequence with $h\to\infty$, $\mu\to\infty$ and $x\in(0,x_c)$,



$$
\mathbb P_x(N=k)=\frac{1+o(1)}{\sqrt{2\pi}\sigma}
 \mathrm{e}^{-u^2/2}\qquad\text{whenever }(k-\mu)/\sigma\longrightarrow u.
$$



 No relation between $h$ and the distance from $x$ to $x_c$ is required.

**Lean declarations** (proved under classical premises):

- [WP.cusp_local_limit](../WPFormalization/Statements/CuspLocalLimit.lean#L13)

<details>
<summary>View formal statements</summary>

[WP.cusp_local_limit](../WPFormalization/Statements/CuspLocalLimit.lean#L13):

```lean
theorem cusp_local_limit (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (gs : ℕ → ℕ) (xs : ℕ → ℝ) (ks : ℕ → ℕ) (u : ℝ)
    (hg : Tendsto gs atTop atTop) (hx : ∀ j, xs j ∈ Set.Ioo 0 xCritical)
    (hmu : Tendsto (fun j => complexity (gs j) p*Psi (xs j)) atTop atTop)
    (hu : Tendsto (fun j => ((ks j : ℝ)-complexity (gs j) p*Psi (xs j)) /
      Real.sqrt (complexity (gs j) p*euler Psi (xs j))) atTop (𝓝 u)) :
    Tendsto (fun j => Real.sqrt (complexity (gs j) p*euler Psi (xs j))*
      cuspMass P (gs j) p (ks j) (xs j)) atTop
      (𝓝 (Real.exp (-u^2/2)/Real.sqrt (2*Real.pi)))
```

</details>

<a id="target-lem:point-mass"></a>

### Paper 9.3: Uniform point-mass bound

**Paper statement** (PDF p. 43):

For every $c_0>0$ there is a constant $C$ with the following property. Let $x\in(0,x_c)$, let $h,h'$ be positive integers with $h'\ge\max(16,c_0h)$, and let $G(z)=V(z)^{h'}R(z)$, where $R$ has nonnegative Taylor coefficients, converges for $|z|<x_c$ and satisfies $R(x)>0$. Then, with $\sigma^2=h\mathscr D\Psi(x)$,



$$
\sup_{j\ge0}\frac{[z^j]G(z)\,x^j}{G(x)}\le\frac C\sigma.
$$

**Lean declarations** (proved under classical premises):

- [WP.point_mass_bound](../WPFormalization/Statements/Boundary.lean#L53)

<details>
<summary>View formal statements</summary>

[WP.point_mass_bound](../WPFormalization/Statements/Boundary.lean#L53):

```lean
theorem point_mass_bound (P : PsiTheory) (c₀ : ℝ) (hc : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ h h' : ℕ, 1 ≤ h → 16 ≤ h' → c₀*h ≤ h' →
    ∀ x ∈ Set.Ioo 0 xCritical, ∀ R : ℂ → ℂ,
      AnalyticOnNhd ℂ R (Metric.ball 0 xCritical) →
      (∀ j, 0 ≤ realCoeff R j ∧ (coeff R j).im = 0) → 0 < (R x).re → (R x).im = 0 →
      (∀ z : ℂ, ‖z‖ < xCritical → HasSum (fun j => coeff R j*z^j) (R z)) →
      ∀ j : ℕ,
        realCoeff (fun z => universalV P z^h'*R z) j*x^j /
          (universalV P x^h'*R x).re ≤ C/Real.sqrt (h*euler Psi x)
```

</details>

<a id="target-eq:boundary-profile"></a>

### Paper 9.23: Boundary insertion interpolation factor

**Paper statement** (PDF p. 7):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\mathfrak b_Y(L)=\int_0^1
 I_0\!\left(\frac L\pi\sqrt{T(Y)-\Delta(Y)s^2}\right)\,\mathrm ds,
$$

**Lean declarations** (defined):

- [WP.boundaryFactor](../WPFormalization/Statements/Parameter.lean#L111)
- [WP.boundary_factor_endpoints](../WPFormalization/Statements/Parameter.lean#L119)

<details>
<summary>View formal statements</summary>

[WP.boundaryFactor](../WPFormalization/Statements/Parameter.lean#L111):

```lean
def boundaryFactor (Y L : ℝ) : ℝ :=
  ∫ s : ℝ in (0)..1, (I₀ (L/Real.pi*Real.sqrt (T Y-Delta Y*s^2))).re
```

[WP.boundary_factor_endpoints](../WPFormalization/Statements/Parameter.lean#L119):

```lean
theorem boundary_factor_endpoints (L : ℝ) :
    boundaryFactor 0 L = (if L = 0 then 1 else Real.sinh (L/2)/(L/2)) ∧
    boundaryFactor y₀ L = (I₀ (Real.sqrt y₀*L/Real.pi)).re
```

</details>

<a id="target-prop:bounded-boundaries"></a>

### Paper 9.4: Boundary lengths at arbitrary cusp density

**Paper statement** (PDF p. 44):

Fix an integer $p\ge1$ and $L_0<\infty$. As $g\to\infty$,



$$
\sup_{\substack{n\ge p\\\mathbf L\in[0,L_0]^p}}
 \left|
 \frac{V_{g,n}(L_1,\ldots,L_p,0^{n-p})}
 {V_{g,n}\prod_{i=1}^p\mathfrak b_{Y_{n/g}}(L_i)}-1
 \right|\longrightarrow0.
$$



 The endpoint factors are



$$
\mathfrak b_0(L)=\frac{\sinh(L/2)}{L/2},\qquad
 \mathfrak b_{y_0}(L)=I_0\!\left(\frac{j_{0,1}L}{2\pi}\right),
$$



 with value one at $L=0$.

**Lean declarations** (proved under classical premises):

- [WP.bounded_boundaries](../WPFormalization/Statements/Boundary.lean#L23)
- [WP.boundaryVolumeModel](../WPFormalization/Statements/BoundaryDefinitions.lean#L17)

<details>
<summary>View formal statements</summary>

[WP.bounded_boundaries](../WPFormalization/Statements/Boundary.lean#L23):

```lean
theorem bounded_boundaries (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) (L₀ : ℝ) (hL : 0 ≤ L₀) :
    ∀ ε : ℝ, 0 < ε → ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ n : ℕ, p ≤ n →
      ∀ L : Fin n → ℝ, (∀ i, 0 ≤ L i) → (∀ i, L i ≤ L₀) →
      (∀ i, p ≤ i.val → L i = 0) →
        |boundaryVolumeModel P g n L /
          (volumeModel P g n * ∏ i : Fin n,
            boundaryFactor (densityY ((n : ℝ)/g)) (L i))-1| ≤ ε
```

[WP.boundaryVolumeModel](../WPFormalization/Statements/BoundaryDefinitions.lean#L17):

```lean
def boundaryVolumeModel (P : PsiTheory) (g n : ℕ) (L : Fin n → ℝ) : ℝ :=
  ∑ d ∈ degreeTuples g n, mixedBracket P g (List.ofFn d) *
    ∏ i, L i^(2*d i)/((4 : ℝ)^(d i)*(2*d i+1).factorial)
```

</details>

## Sharp coefficient extraction

<a id="target-eq:CE1"></a>

### Paper 10.1: Extraction action and amplitude

**Paper statement** (PDF p. 46):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\mathcal J_{g,p}(x)=\mathcal J_{g,p}(0)\mathrm{e}^{hS(x)}B_p(x),\qquad
 S=\log\frac{\mathcal Z(0)}{\mathcal Z(Y(x))},\qquad
 B_p=\frac{r^{p/2}\sqrt{A\Theta}}{r(0)^{p/2}\sqrt{A(0)\Theta(0)}}.
$$

**Lean declarations** (defined under classical premises):

- [WP.extractionS](../WPFormalization/Statements/Volumes.lean#L63)
- [WP.extractionB](../WPFormalization/Statements/Volumes.lean#L69)
- [WP.extraction_factorization](../WPFormalization/Statements/ExtractionFactorization.lean#L12)

<details>
<summary>View formal statements</summary>

[WP.extractionS](../WPFormalization/Statements/Volumes.lean#L63):

```lean
def extractionS (x : ℝ) : ℝ := Real.log (Z 0 / Z (inverseY x))
```

[WP.extractionB](../WPFormalization/Statements/Volumes.lean#L69):

```lean
def extractionB (p : ℕ) (x : ℝ) : ℝ :=
  let Y := inverseY x
  Real.rpow (r Y) ((p : ℝ)/2)*Real.sqrt (A Y*Theta Y) /
    (Real.rpow (r 0) ((p : ℝ)/2)*Real.sqrt (A 0*Theta 0))
```

[WP.extraction_factorization](../WPFormalization/Statements/ExtractionFactorization.lean#L12):

```lean
theorem extraction_factorization (g p : ℕ) (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) :
    markedModel g p Y = markedModel g p 0 *
      Real.exp (complexity g p*extractionS (XR Y))*extractionB p (XR Y)
```

</details>

<a id="target-thm:sharp-extraction"></a>

### Paper 10.1: Uniform Poisson-corrected extraction

**Paper statement** (PDF p. 47):

For fixed $p\ge1$, uniformly over integers $k\ge0$,



$$
[z^k]F_h(z)=\frac{\mathcal J_{g,p}(x)}\pi x^{-k}\mathfrak p_k
       \sqrt{\frac{k}{h\mathscr D\Psi(x)}}\,(1+O_p(h^{-1})).
$$



 At $k=0$ take $x=0$ and interpret both $k$-dependent factors by continuity as one.

**Lean declarations** (proved under classical premises):

- [WP.sharp_extraction](../WPFormalization/Statements/SharpExtraction.lean#L12)

<details>
<summary>View formal statements</summary>

[WP.sharp_extraction](../WPFormalization/Statements/SharpExtraction.lean#L12):

```lean
theorem sharp_extraction (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ k : ℕ,
      |realCoeff (iteratedDeriv p (Phi P g)) k / extractionQ g p k-1| ≤ C/complexity g p
```

</details>

<a id="target-eq:CG1"></a>

### Paper 10.3: Poisson corrected normalization

**Paper statement** (PDF p. 47):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\mathcal Q_{g,p,k}=
 \frac{\mathcal J_{g,p}(x)}\pi x^{-k}\mathfrak p_k
                   \sqrt{\frac{k}{hv}}.
$$

**Lean declarations** (defined):

- [WP.extractionQ](../WPFormalization/Statements/Volumes.lean#L86)
- [WP.poissonCenter](../WPFormalization/Statements/Volumes.lean#L79)

<details>
<summary>View formal statements</summary>

[WP.extractionQ](../WPFormalization/Statements/Volumes.lean#L86):

```lean
def extractionQ (g p k : ℕ) : ℝ :=
  let h := complexity g p
  let Y := densityY (2*(k : ℝ)/h)
  let x := XR Y
  markedModel g p Y / Real.pi *
    (if k = 0 then 1 else x⁻¹^k*poissonCenter k*Real.sqrt ((k : ℝ)/(h*euler Psi x)))
```

[WP.poissonCenter](../WPFormalization/Statements/Volumes.lean#L79):

```lean
def poissonCenter (k : ℕ) : ℝ := Real.exp (-(k : ℝ)) * (k : ℝ)^k/k.factorial
```

</details>

<a id="target-eq:CG3"></a>

### Paper 10.5: Extracted correction coefficients

**Paper statement** (PDF p. 48):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\mathcal A_{p,j}(Y)=[\tau^{2j}]
       \frac{\mathcal N_p(\tau,X(Y))}
            {\displaystyle\sum_{i\ge0}s_i\Psi(X(Y))^{-i}\tau^{2i}}.
$$

**Lean declarations** (defined under classical premises):

- [WP.HigherOrder.extractionNumerator](../WPFormalization/HigherOrder/Extraction.lean#L54)
- [WP.HigherOrder.extractionDenominator](../WPFormalization/HigherOrder/Extraction.lean#L92)
- [WP.HigherOrder.rawExtractedCoefficient](../WPFormalization/HigherOrder/Extraction.lean#L101)
- [WP.HigherOrder.extractedCoefficient](../WPFormalization/HigherOrder/Extraction.lean#L127)
- [WP.HigherOrder.criticalExtractedCoefficient](../WPFormalization/HigherOrder/Extraction.lean#L112)

<details>
<summary>View formal statements</summary>

[WP.HigherOrder.extractionNumerator](../WPFormalization/HigherOrder/Extraction.lean#L54):

```lean
def extractionNumerator (P : PsiTheory) (p : ℕ) (x : ℝ) : Series :=
  PowerSeries.mk (fun n => gaussianFunctional
    (∑ j ∈ Finset.range (n+1), extractionExpPolynomial p x j * markedTaylorPolynomial P p x (n-j)))
```

[WP.HigherOrder.extractionDenominator](../WPFormalization/HigherOrder/Extraction.lean#L92):

```lean
def extractionDenominator (x : ℝ) : Series := PowerSeries.mk (fun n =>
  if Even n then PowerSeries.coeff (n/2) poissonStirlingSeries * (Psi x)⁻¹^(n/2) else 0)
```

[WP.HigherOrder.rawExtractedCoefficient](../WPFormalization/HigherOrder/Extraction.lean#L101):

```lean
def rawExtractedCoefficient (P : PsiTheory) (p j : ℕ) (Y : ℝ) : ℝ :=
  PowerSeries.coeff (2*j) (extractionNumerator P p (XR Y)*(extractionDenominator (XR Y))⁻¹)
```

[WP.HigherOrder.extractedCoefficient](../WPFormalization/HigherOrder/Extraction.lean#L127):

```lean
def extractedCoefficient (P : PsiTheory) (p j : ℕ) (Y : ℝ) : ℝ :=
  if Y = 0 then markedCoefficient P p j 0 else
    if Y = y₀ then criticalExtractedCoefficient P p j else rawExtractedCoefficient P p j Y
```

[WP.HigherOrder.criticalExtractedCoefficient](../WPFormalization/HigherOrder/Extraction.lean#L112):

```lean
def criticalExtractedCoefficient (P : PsiTheory) (p j : ℕ) : ℝ :=
  limUnder (𝓝[<] y₀) (rawExtractedCoefficient P p j)
```

</details>

<a id="target-thm:canonical-expansion"></a>

### Paper 10.2: Uniform expansion at a prescribed cusp count

**Paper statement** (PDF p. 48):

For every fixed $p\ge1$ there are constants $C_p,\mathfrak B_p,c_p,h_p>0$ such that, for $h=2g-2+p\ge h_p$, every integer $k\ge0$ and $0\le K\le c_p\sqrt h$,



$$
\left|\frac{[z^k]\Phi_g^{(p)}}{\mathcal Q_{g,p,k}}
       -\sum_{j=0}^K\frac{\mathcal A_{p,j}(Y)}{h^j}\right|
 \le\frac{C_p\mathfrak B_p^{K+1}((K+1)!)^2}{h^{K+1}},
 \qquad h\Psi(X(Y))=k,
$$



 where $\mathcal A_{p,0}=1$. The coefficients are analytic on one complex neighborhood $\Omega_p$ of $[0,y_0]$, with $\|\mathcal A_{p,j}\|_{\Omega_p}\le C_p\mathfrak B_p^j(j!)^2$, and $\mathcal A_{p,j}(0)=\mathcal L_{p,j}(0)$. For a sufficiently small fixed $c'_p>0$, truncation at $K=\lfloor c'_p\sqrt h\rfloor$ has relative error $O_p(\mathrm{e}^{-a_p\sqrt h})$, uniformly in $k$, for some $a_p>0$. The marking count is fixed. The infinite series need not converge.

**Lean declarations** (proved under classical premises):

- [WP.HigherOrder.canonical_expansion](../WPFormalization/HigherOrder/CanonicalExtractionStatement.lean#L11)

<details>
<summary>View formal statements</summary>

[WP.HigherOrder.canonical_expansion](../WPFormalization/HigherOrder/CanonicalExtractionStatement.lean#L11):

```lean
theorem canonical_expansion (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C B c h₀ : ℝ, 0 < C ∧ 0 < B ∧ 0 < c ∧ 0 < h₀ ∧
      GevreyExtension (extractedCoefficient P p) C B ∧
      (∀ j, ContinuousOn (extractedCoefficient P p j) (Set.Icc 0 y₀)) ∧
      (∀ j, extractedCoefficient P p j y₀ = criticalExtractedCoefficient P p j) ∧
      (∀ (g k K : ℕ), h₀ ≤ (complexity g p : ℝ) →
        (K : ℝ) ≤ c*Real.sqrt (complexity g p) →
        let Y := densityY (2*(k : ℝ)/(complexity g p : ℝ))
        |realCoeff (iteratedDeriv p (Phi P g)) k / extractionQ g p k -
          ∑ j ∈ Finset.range (K+1), extractedCoefficient P p j Y/
            (complexity g p : ℝ)^j| ≤
          C*B^(K+1)*((K+1).factorial : ℝ)^2/(complexity g p : ℝ)^(K+1)) ∧
      (∃ c' a C' h₁ : ℝ, 0 < c' ∧ c' ≤ c ∧ 0 < a ∧ 0 < C' ∧ 0 < h₁ ∧
        ∀ (g k : ℕ), h₁ ≤ (complexity g p : ℝ) →
          let Y := densityY (2*(k : ℝ)/(complexity g p : ℝ))
          |realCoeff (iteratedDeriv p (Phi P g)) k / extractionQ g p k -
            ∑ j ∈ Finset.range (⌊c'*Real.sqrt (complexity g p)⌋₊+1),
              extractedCoefficient P p j Y/(complexity g p : ℝ)^j| ≤
                C'*Real.exp (-a*Real.sqrt (complexity g p)))
```

</details>

## Absolute expansions

<a id="target-thm:absolute"></a>

### Paper 11.1: The leading term

**Paper statement** (PDF p. 48):

There is a constant $C>0$ such that, for all sufficiently large $g$,



$$
\sup_{n\ge0}\left|\frac{V_{g,n}}{\widehat V_{g,n}}-1\right|
       \le\frac Cg.
$$



 The order $g^{-1}$ is sharp for the leading model 11.1:



$$
\liminf_{g\to\infty}g\sup_{n\ge0}
       \left|\frac{V_{g,n}}{\widehat V_{g,n}}-1\right|
       \ge\frac7{12}-\frac{17}{6\pi^2}>0.
$$

**Lean declarations** (proved under classical premises):

- [WP.absolute_volume](../WPFormalization/Statements/AbsoluteVolume.lean#L12)

<details>
<summary>View formal statements</summary>

[WP.absolute_volume](../WPFormalization/Statements/AbsoluteVolume.lean#L12):

```lean
theorem absolute_volume (P : PsiTheory) :
    (∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ n : ℕ,
      |volumeModel P g n/leadingVolume g n-1| ≤ C/g) ∧
    (7/12-17/(6*Real.pi^2) ≤ Filter.liminf
      (fun g : ℕ => (g : ℝ)*⨆ n : ℕ, |volumeModel P g n/leadingVolume g n-1|) atTop) ∧
    0 < 7/12-17/(6*Real.pi^2)
```

</details>

<a id="target-eq:AV6"></a>

### Paper 11.6: Exact unmarked dilaton reduction

**Paper statement** (PDF p. 50):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
V_{g,0}=\frac{V_{g,1}\mathsf C_0(h-1;0)}{4\pi^2(h-1)},\qquad
 \frac{\widehat V_{g,1}}{4\pi^2(h-1)\widehat V_{g,0}}
       =\sqrt{1+\frac1h}.
$$

**Lean declarations** (proved under classical premises):

- [WP.unmarked_reduction](../WPFormalization/Statements/UnmarkedReduction.lean#L13)

<details>
<summary>View formal statements</summary>

[WP.unmarked_reduction](../WPFormalization/Statements/UnmarkedReduction.lean#L13):

```lean
theorem unmarked_reduction (P : PsiTheory) (g : ℕ) (hg : 2 ≤ g) :
    volumeModel P g 0 = volumeModel P g 1 *
      ((complexity g 0 : ℝ)/A 0*W P g 0 0/W P g 1 0)/(4*Real.pi^2*(2*(g : ℝ)-2)) ∧
    leadingVolume g 1/(4*Real.pi^2*(2*(g : ℝ)-2)*leadingVolume g 0) =
      Real.sqrt (1+1/(2*(g : ℝ)-1))
```

</details>

<a id="target-eq:AV7"></a>

### Paper 11.7: Unmarked correction coefficients

**Paper statement** (PDF p. 50):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
1+\sum_{j\ge1}a_{0,j}t^j
 =(1+t)^{1/2}\mathsf C_0\!\left(\frac t{1-t};0\right)
       \left(1+\sum_{j\ge1}\mathcal L_{1,j}(0)t^j\right).
$$

**Lean declarations** (defined under classical premises):

- [WP.HigherOrder.canonicalUnmarkedSeries](../WPFormalization/HigherOrder/Endpoint.lean#L42)
- [WP.HigherOrder.unmarkedCoefficient](../WPFormalization/HigherOrder/Endpoint.lean#L46)
- [WP.HigherOrder.absoluteCoefficient](../WPFormalization/HigherOrder/Extraction.lean#L140)

<details>
<summary>View formal statements</summary>

[WP.HigherOrder.canonicalUnmarkedSeries](../WPFormalization/HigherOrder/Endpoint.lean#L42):

```lean
def canonicalUnmarkedSeries (P : PsiTheory) : Series :=
  unmarkedProduct (formalCusp P 0 0) (PowerSeries.mk (fun j => markedCoefficient P 1 j 0))
```

[WP.HigherOrder.unmarkedCoefficient](../WPFormalization/HigherOrder/Endpoint.lean#L46):

```lean
def unmarkedCoefficient (P : PsiTheory) (j : ℕ) : ℝ :=
  PowerSeries.coeff j (canonicalUnmarkedSeries P)
```

[WP.HigherOrder.absoluteCoefficient](../WPFormalization/HigherOrder/Extraction.lean#L140):

```lean
def absoluteCoefficient (P : PsiTheory) (j g n : ℕ) : ℝ :=
  if n = 0 then unmarkedCoefficient P j else
    extractedCoefficient P 1 j (densityY (2*((n-1 : ℕ) : ℝ)/(2*(g : ℝ)-1)))
```

</details>

## Coefficient estimates

<a id="target-eq:C1"></a>

### Paper 13.1: Exact-density trigonometric saddle

**Paper statement** (PDF p. 52):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\alpha_{g,k}:=\frac{2k+1}{2g-1}
 =\frac{t_{g,k}^{2}\sin t_{g,k}}
        {\sin t_{g,k}-t_{g,k}\cos t_{g,k}}.
$$

**Lean declarations** (defined):

- [WP.trigSaddle](../WPFormalization/Statements/Parameter.lean#L136)
- [WP.trigDensity](../WPFormalization/Statements/Parameter.lean#L130)
- [WP.trig_saddle_spec](../WPFormalization/Statements/Parameter.lean#L143)

<details>
<summary>View formal statements</summary>

[WP.trigSaddle](../WPFormalization/Statements/Parameter.lean#L136):

```lean
def trigSaddle (g k : ℕ) : ℝ := sInf {t : ℝ | t ∈ Set.Ioo 0 Real.pi ∧
  trigDensity t = (2*(k : ℝ)+1)/(2*(g : ℝ)-1)}
```

[WP.trigDensity](../WPFormalization/Statements/Parameter.lean#L130):

```lean
def trigDensity (t : ℝ) : ℝ := t^2*Real.sin t / (Real.sin t-t*Real.cos t)
```

[WP.trig_saddle_spec](../WPFormalization/Statements/Parameter.lean#L143):

```lean
theorem trig_saddle_spec (g k : ℕ) (hg : 1 ≤ g) (hk : k < 3*g-2) :
    trigSaddle g k ∈ Set.Ioo 0 Real.pi ∧
    trigDensity (trigSaddle g k) = (2*(k : ℝ)+1)/(2*(g : ℝ)-1) ∧
    (∀ t ∈ Set.Ioo 0 Real.pi, trigDensity t = (2*(k : ℝ)+1)/(2*(g : ℝ)-1) →
      t = trigSaddle g k)
```

</details>

<a id="target-eq:C7"></a>

### Paper 13.7: Log concavity of unnormalized mixed intersections

**Paper statement** (PDF p. 53):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
J_k^2\ge J_{k-1}J_{k+1},\qquad 1\le k<N.
$$

**Lean declarations** (proved under classical premises):

- [WP.mixed_log_concavity](../WPFormalization/Statements/MixedLogConcavity.lean#L12)
- [WP.mixedJ](../WPFormalization/Statements/Coefficients.lean#L27)

<details>
<summary>View formal statements</summary>

[WP.mixed_log_concavity](../WPFormalization/Statements/MixedLogConcavity.lean#L12):

```lean
theorem mixed_log_concavity (P : PsiTheory) (g k : ℕ) (hg : 1 ≤ g)
    (hk : 1 ≤ k) (ht : k < 3*g-2) :
    mixedJ P g (k-1)*mixedJ P g (k+1) ≤ mixedJ P g k^2
```

[WP.mixedJ](../WPFormalization/Statements/Coefficients.lean#L27):

```lean
def mixedJ (P : PsiTheory) (g k : ℕ) : ℝ :=
  bracketB P g k * (3*g-2-k).factorial /
    ((oddFactorial k : ℝ)*4^k*(2*Real.pi^2)^(3*g-2-k))
```

</details>

<a id="target-eq:C8"></a>

### Paper 13.8: Absolute bracket differences

**Paper statement** (PDF p. 53):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
c_0=1,\qquad 0\le c_k-c_{k+1}\le C\frac{k+1}{g},
  \qquad 0\le k<N.
$$

**Lean declarations** (proved under classical premises):

- [WP.bracket_differences](../WPFormalization/Statements/BracketDifferences.lean#L10)

<details>
<summary>View formal statements</summary>

[WP.bracket_differences](../WPFormalization/Statements/BracketDifferences.lean#L10):

```lean
theorem bracket_differences (P : PsiTheory) : ∃ C : ℝ, 0 < C ∧
    ∀ g : ℕ, 1 ≤ g →
      bracketB P g 0/volumeModel P g 1 = 1 ∧
      ∀ k : ℕ, k < 3*g-2 →
        0 ≤ bracketB P g k/volumeModel P g 1-bracketB P g (k+1)/volumeModel P g 1 ∧
        bracketB P g k/volumeModel P g 1-bracketB P g (k+1)/volumeModel P g 1 ≤
          C*(k+1)/g
```

</details>

<a id="target-eq:C18"></a>

### Paper 13.18: Exact top adjacent coefficient anchor

**Paper statement** (PDF p. 55):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
q_{N-1}=\frac{12g^2-12g+5}{5},
 \qquad
 \frac{a_{g,N-1}}{a_{g,N}}
 =\frac{2\pi^2(12g^2-12g+5)}{5(6g-3)}.
$$

**Lean declarations** (proved under classical premises):

- [WP.top_anchor](../WPFormalization/Statements/TopAnchor.lean#L10)
- [WP.boundaryA](../WPFormalization/Statements/Coefficients.lean#L21)

<details>
<summary>View formal statements</summary>

[WP.top_anchor](../WPFormalization/Statements/TopAnchor.lean#L10):

```lean
theorem top_anchor (P : PsiTheory) (g : ℕ) (hg : 1 ≤ g) :
    mixedJ P g (3*g-3)/mixedJ P g (3*g-2) = (12*(g : ℝ)^2-12*g+5)/5 ∧
    boundaryA P g (3*g-3)/boundaryA P g (3*g-2) =
      2*Real.pi^2*(12*(g : ℝ)^2-12*g+5)/(5*(6*(g : ℝ)-3))
```

[WP.boundaryA](../WPFormalization/Statements/Coefficients.lean#L21):

```lean
def boundaryA (P : PsiTheory) (g k : ℕ) : ℝ := bracketB P g k / (4 : ℝ)^k
```

</details>

<a id="target-eq:C23"></a>

### Paper 13.23: Bottom-degree logarithmic bound

**Paper statement** (PDF p. 55):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
0\le\log\frac{V_{g,1}}{b_{g,k}}
 \le C\log^2(g+1)+C\frac{(k+1)^2}{g}.
$$

**Lean declarations** (proved under classical premises):

- [WP.bottom_log_bound](../WPFormalization/Statements/BottomLogBound.lean#L12)
- [WP.bracketB](../WPFormalization/Statements/Coefficients.lean#L15)

<details>
<summary>View formal statements</summary>

[WP.bottom_log_bound](../WPFormalization/Statements/BottomLogBound.lean#L12):

```lean
theorem bottom_log_bound (P : PsiTheory) : ∃ C : ℝ, 0 < C ∧
    ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ k : ℕ, k ≤ 3*g-2 →
      0 ≤ Real.log (volumeModel P g 1/bracketB P g k) ∧
      Real.log (volumeModel P g 1/bracketB P g k) ≤
        C*(Real.log (g+1))^2+C*(k+1 : ℝ)^2/g
```

[WP.bracketB](../WPFormalization/Statements/Coefficients.lean#L15):

```lean
def bracketB (P : PsiTheory) (g k : ℕ) : ℝ := mixedBracket P g [k]
```

</details>

## Instanton-related expansions

<a id="target-eq:instanton-correspondence"></a>

### Paper Section 13.7 exact action, residue normalization and stationary equation: Ordinary WP instanton action, residue and saddle dictionary

**Paper statement** (PDF pp. 56, 57):

Stage-one implementation: the complete mathematical deduction has a Lean producer linked below. The physical interpretation cited here is background; the local identities and remainder estimates are proved from the defined mathematical functions, without a new physical-model assumption.

The denominator $H$ in 13.4 is the normalized ordinary Weil–Petersson instanton action. To see the correspondence, choose the positive sign convention



$$
A_{\rm inst}(w)=\frac{\sin(2\pi w)-2\pi w\cos(2\pi w)}{4\pi^3}
     =\frac23 w^3 H(2\pi^2w^2).
$$



 With $x=w^2$, this is the effective potential of \[25\] equation (3.15), whose values at its stationary points are the instanton actions. The ordinary-volume polynomial prediction in \[28\] Section 3.3 and the one-boundary term in \[45\] equation (4.22) contain, up to an overall factor independent of the coefficient degree, the contour expression



$$
\frac{\Gamma(h)}{L}\oint
       \frac{\mathrm{e}^{Lw}}{w A_{\rm inst}(w)^h}\,\mathrm{d}w,\qquad h=2g-1.
$$



 The coefficient of $L^{2k}$, multiplied by $(2k+1)!$, is proportional to



$$
\Gamma(h)\operatorname*{Res}_{w=0} w^{2k}A_{\rm inst}(w)^{-h}\,\mathrm{d}w.
$$



 Since $3h-2k-1=2m$, expansion at zero gives the exact identity



$$
\Gamma(h)\operatorname*{Res}_{w=0} w^{2k}A_{\rm inst}(w)^{-h}\,\mathrm{d}w
 =\Gamma(h)(3/2)^h(2\pi^2)^m \widetilde A_m(h)
 =2\,4^{-k}M_{g,k}.
$$



 Thus the model for the coefficients $a_{g,k}$ has precisely the normalization $4^{-k}M_{g,k}$, up to the degree-independent overall factor in the prediction. Moreover, the exponent in the $\mathrm{d}w/w$ representation has its stationary point at



$$
\frac{2k+1}{h}=\frac{wA_{\rm inst}'(w)}{A_{\rm inst}(w)}
 =\frac{t^2\sin t}{\sin t-t\cos t},\qquad t=2\pi w.
$$



 Thus both the comparison model and the saddle equation already appear in the instanton calculus. The estimates 13.5 and the concavity argument above justify the asymptotic formula for adjacent ratios of the true mixed intersection numbers, including both endpoint regimes; that proof does not use the contour expression.

**Lean declarations** (proved):

- [WP.Coefficients.instanton_correspondence](../WPFormalization/Coefficients/InstantonCorrespondence.lean#L67)
- [WP.Analysis.instanton_contour_coefficient_dictionary](../WPFormalization/Analysis/WPInstantonContour.lean#L222)

<details>
<summary>View formal statements</summary>

[WP.Coefficients.instanton_correspondence](../WPFormalization/Coefficients/InstantonCorrespondence.lean#L67):

```lean
theorem instanton_correspondence :
    Differentiable ℂ instantonAction ∧
    (∀ w : ℂ, instantonAction w =
      (2/3 : ℂ) * w^3 * H 0 (2 * (Real.pi : ℂ)^2 * w^2)) ∧
    (∀ g k : ℕ, 1 ≤ g → k ≤ 3*g-2 →
      ((Real.Gamma (complexity g 1) : ℂ) *
          residueAtZero (instantonIntegrand (complexity g 1) k) =
        (Real.Gamma (complexity g 1) * (3/2 : ℝ)^(complexity g 1) *
          (2*Real.pi^2)^(3*g-2-k) * unscaledCoeff (complexity g 1) (3*g-2-k) : ℝ)) ∧
      ((Real.Gamma (complexity g 1) : ℂ) *
          residueAtZero (instantonIntegrand (complexity g 1) k) =
        (2 * (4 : ℝ)^(-(k : ℤ)) * oneBoundaryBracketModel g k : ℝ))) ∧
    (∀ w : ℂ, instantonAction w ≠ 0 →
      w * deriv instantonAction w / instantonAction w =
        (2 * Real.pi * w)^2 * Complex.sin (2 * Real.pi * w) /
          (Complex.sin (2 * Real.pi * w) -
            2 * Real.pi * w * Complex.cos (2 * Real.pi * w))) ∧
    (∀ g k : ℕ, 1 ≤ g → k < 3*g-2 → ∀ t ∈ Ioo 0 Real.pi,
      deriv (instantonSaddleExponent g k) (t / (2 * Real.pi)) = 0 ↔
        t = trigSaddle g k)
```

[WP.Analysis.instanton_contour_coefficient_dictionary](../WPFormalization/Analysis/WPInstantonContour.lean#L222):

```lean
theorem instanton_contour_coefficient_dictionary (g : ℕ) (hg : 1 ≤ g) :
    AnalyticAt ℂ (instantonRawContourAmplitude (complexity g 1)) 0 ∧
    (∃ ε : ℝ, 0 < ε ∧ ∀ R ∈ Ioo (0 : ℝ) ε, ∀ L : ℂ, L ≠ 0 →
      instantonRawContourAmplitude (complexity g 1) L =
        (Real.Gamma (complexity g 1) : ℂ)/L *
          ∮ w in C(0,R), Complex.exp (L*w)/(w*(instantonAction w)^(complexity g 1))) ∧
    (∀ k : ℕ, k ≤ 3*g-2 →
      ((2*k+1).factorial : ℂ) * WP.coeff (instantonContourAmplitude (complexity g 1)) (2*k) =
        (Real.Gamma (complexity g 1) : ℂ) *
          residueAtZero (instantonIntegrand (complexity g 1) k)) ∧
    (∀ k : ℕ, k ≤ 3*g-2 →
      ((2*k+1).factorial : ℂ) * WP.coeff (instantonRawContourAmplitude (complexity g 1)) (2*k) =
        (2*(Real.pi : ℂ)*Complex.I) * (Real.Gamma (complexity g 1) : ℂ) *
          residueAtZero (instantonIntegrand (complexity g 1) k))
```

</details>

## Geometric applications

<a id="target-eq:PS1"></a>

### Paper 14.1: Short-pants length scale

**Paper statement** (PDF p. 57):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
q_g=\frac{n(n-1)}{8g\mathcal C(n/g)}.
$$

**Lean declarations** (defined):

- [WP.pantsScale](../WPFormalization/Statements/Intensities.lean#L15)

<details>
<summary>View formal statements</summary>

[WP.pantsScale](../WPFormalization/Statements/Intensities.lean#L15):

```lean
def pantsScale (g n : ℕ) : ℝ := (n : ℝ)*(n-1)/(8*g*profileC ((n : ℝ)/g))
```

</details>

<a id="target-thm:pants-poisson"></a>

### Paper 14.1: Short-curve processes and the systole

**Paper statement** (PDF p. 58):

Scope from Section 14.2: integer cusp counts, genus tending to infinity, and $n/\sqrt g\to\infty$. All further hypotheses in the statement apply as written.

(i) Curves cutting off two cusps. The random locally finite counting measures



$$
\sum_{\gamma\in\mathcal P_2(X)}
       \delta_{\sqrt{q_g}\ell_\gamma}
 \ \Longrightarrow\ \operatorname{PPP}(2t\,\mathrm{d}t)
 \quad\hbox{on }[0,\infty)
$$



 converge in distribution for the vague topology. Thus counts in finitely many disjoint bounded intervals $[a_i,b_i]$ converge jointly to independent Poisson variables with means $b_i^2-a_i^2$. If $\ell_{\min}^{(2)}$ is the shortest length in $\mathcal P_2(X)$, with value infinity when this set is empty, then



$$
\mathbb P^{\mathrm{WP}}_{g,n}
 \{\sqrt{q_g}\ell_{\min}^{(2)}>t\}\longrightarrow \mathrm{e}^{-t^2}
 \qquad(t\ge0).
$$



 (ii) All planar cusp types. Let $\mathcal P_k(X)$ consist of simple geodesics whose genus-zero side contains exactly $k$ cusps. If $n/g\to\lambda\in[0,\infty]$, put $x_\lambda=X(Y_\lambda)$, where $\lambda(Y_\lambda)=\lambda$, with $x_0=0$ and $x_\infty=x_c$. Define



$$
w_k(x)=\frac{2V_{0,k+1}}{k!}
             \left(\frac{x}{2\pi^2}\right)^{k-2},\qquad
 W(x)=\sum_{k\ge2}w_k(x)=\frac{2\Phi_0'(x)}{x^2}.
$$



 Here $w_2(0)=W(0)=1$, $w_k(0)=0$ for $k>2$, and $W(x_c)<\infty$. Then



$$
\sum_{k\ge2}\ \sum_{\gamma\in\mathcal P_k(X)}
       \delta_{(\sqrt{q_g}\ell_\gamma,k)}
 \ \Longrightarrow\
 \operatorname{PPP}\!\left(2t\,\mathrm{d}t\otimes
                    \sum_{k\ge2}w_k(x_\lambda)\delta_k\right).
$$



 Convergence is for the vague topology on the product with the discrete type space. The projection to lengths also converges, to $\operatorname{PPP}(2W(x_\lambda)t\,\mathrm{d}t)$.

(iii) Primitive geodesics and the systole. This is also the limit of the process of all unoriented primitive closed geodesics, at the same rescaling. Writing $\operatorname{sys}(X)$ for the shortest closed geodesic length, we have



$$
\mathbb P^{\mathrm{WP}}_{g,n}
 \{\sqrt{q_g}\operatorname{sys}(X)>t\}
 \longrightarrow \mathrm{e}^{-W(x_\lambda)t^2}\qquad(t\ge0).
$$



 With probability tending to one every systolic curve is planar separating. Select one by any measurable tie rule, and let $K_g$ be its planar-side cusp count, with value zero if it is not planar. Then $\bigl(\sqrt{q_g}\operatorname{sys}(X),K_g\bigr)$ converges jointly to a pair $(Z,K)$ with



$$
\begin{aligned}
 \mathbb P\{Z\in \mathrm{d}t,K=k\}
 &=2t\,w_k(x_\lambda)\mathrm{e}^{-W(x_\lambda)t^2}\,\mathrm{d}t,\\
 \mathbb P\{K=k\}&=\frac{w_k(x_\lambda)}{W(x_\lambda)}
 \qquad(t>0,\ k\ge2).
 \end{aligned}
$$

**Lean declarations** (proved under classical premises):

- [WP.RandomGeometry.pants_poisson_theorem](../WPFormalization/RandomGeometry/PantsPoissonTheorem.lean#L56)

<details>
<summary>View formal statements</summary>

[WP.RandomGeometry.pants_poisson_theorem](../WPFormalization/RandomGeometry/PantsPoissonTheorem.lean#L56):

```lean
theorem pants_poisson_theorem (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop) : PantsPoissonConclusion H n
```

</details>

<a id="target-eq:PS3"></a>

### Paper 14.6: Ordered pants factorial moments

**Paper statement** (PDF p. 59):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\mathbb E\!\sum_{\substack{\gamma_1,\ldots,\gamma_r\in\mathcal P_2(X)\\
                            \text{distinct}}}
       \prod_{j=1}^r\mathbf1_{\ell_{\gamma_j}\in I_j}
 =\frac{(n)_{2r}}{2^r V_{g,n}}
    \int_{I_1\times\cdots\times I_r}
       V_{g,n-r}(x_1,\ldots,x_r,0^{n-2r})
       \prod_{j=1}^r x_j\,\mathrm{d}x_j.
$$

**Lean declarations** (proved under classical premises):

- [WP.RandomGeometry.pants_ordered_window_moments](../WPFormalization/RandomGeometry/PantsOrderedMoments.lean#L58)

<details>
<summary>View formal statements</summary>

[WP.RandomGeometry.pants_ordered_window_moments](../WPFormalization/RandomGeometry/PantsOrderedMoments.lean#L58):

```lean
theorem pants_ordered_window_moments (hg : 2 ≤ g) (hn : 2*r ≤ n)
    (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (I : Fin r → Set ℝ) (hI : ∀i, MeasurableSet (I i)) (hsub : ∀i, I i ⊆ Set.Icc 0 L) :
    (∫X : G.Moduli g n (fun _ => 0), (pantsWindowCount H X L I : ℝ) ∂wpProbability G g n) =
      ((n.descFactorial (2*r) : ℝ)/((2:ℝ)^r*cuspVolume G g n))*
        pantsGeometricWindowIntegral G g (n-r) r (show r ≤ n-r by omega) I
```

</details>

<a id="target-prop:pants-concentration"></a>

### Paper 14.2: Many short pants

**Paper statement** (PDF p. 62):

Scope from Section 14.2: integer cusp counts, genus tending to infinity, and $n/\sqrt g\to\infty$. All further hypotheses in the statement apply as written.

If $L=L_g\to0$ and $q_gL_g^2\to\infty$, then



$$
\frac{N_{L_g}}{q_gL_g^2}\longrightarrow1
 \quad\hbox{in probability}.
$$



 Consequently, for each fixed $\varepsilon\in(0,1)$, with probability tending to one there are at least $\lfloor(1-\varepsilon)q_gL_g^2\rfloor-1$ positive discrete eigenvalues in $(0,6L_g]$, counted with multiplicity.

**Lean declarations** (proved under classical premises):

- [WP.RandomGeometry.short_pants_concentration](../WPFormalization/Spectral/PantsConsequences.lean#L69)

<details>
<summary>View formal statements</summary>

[WP.RandomGeometry.short_pants_concentration](../WPFormalization/Spectral/PantsConsequences.lean#L69):

```lean
theorem short_pants_concentration (P : PsiTheory)
    (G : WeilPeterssonGeometry.{u,v} P) (H : HyperbolicCurveGeometry.{u,v,w} G)
    (T : MulticurveTopology.{u,v,w,z} G H) (C : CollarGeometry G H T)
    (MI : MirzakhaniIntegration G H T) (S : SpectralGeometry H)
    (n : ℕ → ℕ)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop atTop)
    (L : ℕ → ℝ) (hLp : ∀ᶠ g in atTop, 0 < L g) (hL : Tendsto L atTop (𝓝 0))
    (hscale : Tendsto (fun g => pantsScale g (n g) * L g ^ 2) atTop atTop) :
    (∀ η : ℝ, 0 < η → Tendsto (fun g => (wpProbability G g (n g)).real
      {X | η ≤ |(H.pantsCount X (L g) : ℝ) /
        (pantsScale g (n g) * L g ^ 2) - 1|}) atTop (𝓝 0)) ∧
    ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      Tendsto (fun g => (wpProbability G g (n g)).real
        {X | ∃ ℓ, S.positiveEigenvalue X
            (Nat.floor ((1 - ε) * (pantsScale g (n g) * L g ^ 2)) - 1) = some ℓ ∧
          ℓ ≤ 6 * L g}) atTop (𝓝 1)
```

</details>

<a id="target-cor:many-spectrum"></a>

### Paper 14.3: A growing number of small eigenvalues

**Paper statement** (PDF p. 62):

Suppose $g\to\infty$ and $n/\sqrt g\to\infty$. If $j=j(g)\to\infty$ and $j=o(q_g)$, then



$$
\mathbb P^{\mathrm{WP}}_{g,n}
 \{\lambda_j(X)\text{ exists and }\lambda_j(X)\le12\sqrt{j/q_g}\}
 \longrightarrow1,
$$



 where positive discrete eigenvalues are ordered with multiplicity.

**Lean declarations** (proved under classical premises):

- [WP.Spectral.many_small_eigenvalues](../WPFormalization/Spectral/ManyEigenvalues.lean#L13)

<details>
<summary>View formal statements</summary>

[WP.Spectral.many_small_eigenvalues](../WPFormalization/Spectral/ManyEigenvalues.lean#L13):

```lean
theorem many_small_eigenvalues (P : PsiTheory)
    (G : WeilPeterssonGeometry.{u,v} P) (H : HyperbolicCurveGeometry.{u,v,w} G)
    (T : MulticurveTopology.{u,v,w,z} G H) (C : CollarGeometry G H T)
    (MI : MirzakhaniIntegration G H T) (S : SpectralGeometry H)
    (n j : ℕ → ℕ)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop atTop)
    (hj : Tendsto j atTop atTop)
    (hsmall : Tendsto (fun g => (j g : ℝ) / pantsScale g (n g)) atTop (𝓝 0)) :
    Tendsto (fun g => (wpProbability G g (n g)).real
      {X | ∃ ℓ, S.positiveEigenvalue X (j g) = some ℓ ∧
        ℓ ≤ 12 * Real.sqrt ((j g : ℝ) / pantsScale g (n g))}) atTop (𝓝 1)
```

</details>

<a id="target-eq:tight-scale"></a>

### Paper 14.17: Tight length scale and limiting intensity

**Paper statement** (PDF p. 63):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\alpha(\lambda)=\frac{\sqrt{2r(Y_\lambda)}}\pi,
 \qquad \nu(\mathrm dt)=\frac{\cosh t-1}{t}\,\mathrm dt.
$$

**Lean declarations** (defined):

- [WP.tightScale](../WPFormalization/Statements/Intensities.lean#L22)
- [WP.tightIntensityDensity](../WPFormalization/Statements/Intensities.lean#L29)
- [WP.tightIntensity](../WPFormalization/Statements/Intensities.lean#L36)

<details>
<summary>View formal statements</summary>

[WP.tightScale](../WPFormalization/Statements/Intensities.lean#L22):

```lean
def tightScale (l : ℝ) : ℝ := Real.sqrt (2*r (densityY l))/Real.pi
```

[WP.tightIntensityDensity](../WPFormalization/Statements/Intensities.lean#L29):

```lean
def tightIntensityDensity (t : ℝ) : ℝ := (Real.cosh t-1)/t
```

[WP.tightIntensity](../WPFormalization/Statements/Intensities.lean#L36):

```lean
def tightIntensity : Measure ℝ :=
  (volume.restrict (Set.Ici 0)).withDensity (fun t => ENNReal.ofReal (tightIntensityDensity t))
```

</details>

<a id="target-thm:tight-spectrum"></a>

### Paper 14.4: Tight lengths at arbitrary cusp density

**Paper statement** (PDF p. 63):

Let $n=n(g)\ge0$ be any integer sequence, and let $X$ have law $\mathbb P^{\mathrm{WP}}_{g,n}$. As $g\to\infty$, the point process



$$
\sum_{\substack{\gamma\text{ primitive, unoriented}\\
                  \gamma\text{ tight on }X}}
 \delta_{\alpha(n/g)\ell_X(\gamma)}
 \ \Longrightarrow\ \operatorname{PPP}(\nu)
$$



 converges in distribution for the vague topology on $[0,\infty)$. For every fixed $L<\infty$, with probability tending to one all the curves counted in $[0,L]$ are simple, pairwise disjoint, and have connected complement after filling the cusps.

**Lean declarations** (proved under classical premises):

- [WP.Tight.tight_length_spectrum](../WPFormalization/Tight/TightSpectrum.lean#L57)

<details>
<summary>View formal statements</summary>

[WP.Tight.tight_length_spectrum](../WPFormalization/Tight/TightSpectrum.lean#L57):

```lean
theorem tight_length_spectrum
    (T : TightRegions G) (BZ : BuddZonneveldTransform G T)
    (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (MI : BuddLionsTightIntegration G T H Q A) (D : BuddLionsTightGeometry G T H Q A)
    (BM : ∀g n,(hg : 2≤g)→TightGeodesicBorelModel G T H Q g n hg)
    (n : ℕ→ℕ) :
    ∃QL : ProbabilityMeasure (PointMeasure ℝ≥0),
      IsPoissonPointProcessLaw ℝ≥0 nonseparatingLengthIntensity QL ∧
      LawConverges (fun g=>wpProbability G g (n g))
        (fun g=>actualScaledTightPointMeasure Q g (n g)) QL (fun ξ=>ξ) ∧
      ∀B : ℝ,0≤B→Tendsto (fun g=>wpProbability G g (n g)
        {X | actualTightPrefixGood Q A g (n g) B X}) atTop (𝓝 1)
```

</details>

<a id="target-cor:tight-boltzmann"></a>

### Paper 14.5: Arbitrary subcritical cusp weights

**Paper statement** (PDF p. 63):

For any sequence $0\le\mu_g<\mu_{\rm cr}$, put



$$
a_g=\frac{\sqrt{2r(Y(2\pi^2\mu_g))}}\pi.
$$



 Under $\mathbb P^{\mathrm{WP}}_{g,\mu_g}$, the primitive tight lengths multiplied by $a_g$ converge to $\operatorname{PPP}(\nu)$. In particular, if $\mu_g\to\mu<\mu_{\rm cr}$, the unscaled lengths have limiting intensity $(\cosh(a_\mu t)-1)\,\mathrm dt/t$, where $a_\mu=\sqrt{2r(Y(2\pi^2\mu))}/\pi$. If $\mu_g\to\mu_{\rm cr}$, no condition on the speed of convergence is required.

**Lean declarations** (proved under classical premises):

- [WP.BoltzmannWp.tight_boltzmann](../WPFormalization/RandomGeometry/BoltzmannWpMixtureConsequences.lean#L49)

<details>
<summary>View formal statements</summary>

[WP.BoltzmannWp.tight_boltzmann](../WPFormalization/RandomGeometry/BoltzmannWpMixtureConsequences.lean#L49):

```lean
theorem tight_boltzmann
    (T:TightRegions G) (BZ:BuddZonneveldTransform G T)
    (Q:TightGeodesicGeometry G T H) (A:TightMulticurveTopology.{u,v,w,z} G T H Q)
    (MI:BuddLionsTightIntegration G T H Q A) (D:BuddLionsTightGeometry G T H Q A)
    (BM:∀g n,(hg:2≤g)→TightGeodesicBorelModel G T H Q g n hg)
    (μs:ℕ→ℝ) (hμs:∀g,μs g∈Ico (0:ℝ) muCritical) :
    (∃QL:ProbabilityMeasure (PointMeasure ℝ≥0),
      IsPoissonPointProcessLaw ℝ≥0 nonseparatingLengthIntensity QL ∧
      LawConverges (fun g=>wpMixture G g (parameter (μs g)))
        (fun g=>physicalPointMeasure Q g (μs g) (hμs g)) QL (fun ξ=>ξ)) ∧
    (∀μ:ℝ,∀hμ:μ∈Ico (0:ℝ) muCritical,Tendsto μs atTop (𝓝 μ)→
      letI := dilatedTightIntensity_locallyFinite (physicalScale μ) (physicalScale_pos μ hμ)
      ∃QL:ProbabilityMeasure (PointMeasure ℝ≥0),
        IsPoissonPointProcessLaw ℝ≥0 (dilatedTightIntensity (physicalScale μ)) QL ∧
        LawConverges (fun g=>wpMixture G g (parameter (μs g)))
          (fun g=>actualLengthPointMeasure Q g 1 (by norm_num)) QL (fun ξ=>ξ))
```

</details>

<a id="target-eq:cluster-intensities"></a>

### Paper 14.19: Critical primitive cluster intensities

**Paper statement** (PDF p. 64):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\mu_c(\mathrm ds)=\frac{c^2}{8\pi^2}\sinh(s/2)\,\mathrm ds,
 \qquad \nu(\mathrm dt)=\frac{\cosh t-1}{t}\,\mathrm dt.
$$

**Lean declarations** (defined):

- [WP.criticalIntensityDensity](../WPFormalization/Statements/Intensities.lean#L43)
- [WP.criticalIntensity](../WPFormalization/Statements/Intensities.lean#L49)
- [WP.tightIntensity](../WPFormalization/Statements/Intensities.lean#L36)

<details>
<summary>View formal statements</summary>

[WP.criticalIntensityDensity](../WPFormalization/Statements/Intensities.lean#L43):

```lean
def criticalIntensityDensity (c s : ℝ) : ℝ := c^2/(8*Real.pi^2)*Real.sinh (s/2)
```

[WP.criticalIntensity](../WPFormalization/Statements/Intensities.lean#L49):

```lean
def criticalIntensity (c : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ici 0)).withDensity (fun s => ENNReal.ofReal (criticalIntensityDensity c s))
```

[WP.tightIntensity](../WPFormalization/Statements/Intensities.lean#L36):

```lean
def tightIntensity : Measure ℝ :=
  (volume.restrict (Set.Ici 0)).withDensity (fun t => ENNReal.ofReal (tightIntensityDensity t))
```

</details>

<a id="target-thm:critical-cluster"></a>

### Paper 14.6: Critical primitive length spectrum

**Paper statement** (PDF p. 64):

Suppose $g\to\infty$ and $n/\sqrt g\to c\in(0,\infty)$, and let $X$ have law $\mathbb P^{\mathrm{WP}}_{g,n}$. Then



$$
\sum_{\substack{\gamma\text{ primitive}\\\text{unoriented on }X}}
       \delta_{\ell_X(\gamma)}
 \ \Longrightarrow\ \Xi_c:=\mathcal N+\sum_{s\in\mathcal Q_c}K_s,
$$



 as locally finite counting measures on $[0,\infty)$ with the vague topology. Here $\mathcal N$ and $\mathcal Q_c$ are independent Poisson point processes of intensities $\nu$ and $\mu_c$. In particular, for every nonnegative continuous compactly supported function $f$,



$$
\mathbb E\mathrm e^{-\langle f,\Xi_c\rangle}
 =\exp\left\{-\int(1-\mathrm e^{-f(t)})\,\nu(\mathrm dt)
 -\int(1-\mathrm e^{-\langle f,K_s\rangle})\,\mu_c(\mathrm ds)\right\}.
$$

**Lean declarations** (proved under classical premises):

- [WP.Critical.PantsCluster.critical_primitive_length_spectrum](../WPFormalization/Critical/CriticalPrimitiveLengthSpectrum.lean#L29)

<details>
<summary>View formal statements</summary>

[WP.Critical.PantsCluster.critical_primitive_length_spectrum](../WPFormalization/Critical/CriticalPrimitiveLengthSpectrum.lean#L29):

```lean
theorem critical_primitive_length_spectrum
    (Cuts:ActualCutRealizationData A T AC.complete_domain)
    (SC:∀g n (X:G.Moduli g n (fun _=>0)),SegmentClassics (A.model g n X))
    (SP:∀g n (X:G.Moduli g n (fun _=>0)),
      SupportingPieceClassics (A.model g n X) (AC.complete_domain g n X))
    (FG:FiniteGraphFundamentalGroupClassics.{u})
    (C:WP.External.FiniteCyclicIntervalGeometry.Classics)
    (LS:∀g n (X:G.Moduli g n (fun _=>0)),
      LoopStraighteningClassics (A.model g n X) (AC.complete_domain g n X))
    (M:∀g n r (X:G.Moduli g n (fun _=>0)) L (hL:0<L)
      (γ:ShortIntersectingSimpleTuple T X r L),
      TupleRecordingCompanions A AC X γ.val γ.property.1 γ.property.2.1
        (SC g n X) L hL γ.property.2.2.1 (SP g n X) C)
    (J:PlanarJordanClassics) (PC:PlanarRegionClassics)
    (BC:∀g n {k}(o:T.Orbit g n k)(X:G.Moduli g n (fun _=>0))
      (κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      PrimitiveBoundaryClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (BLS:∀g n {k}(o:T.Orbit g n k)(X:G.Moduli g n (fun _=>0))
      (κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      BorderedLoopStraighteningClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (PP:∀g n {k}(o:T.Orbit g n k)(X:G.Moduli g n (fun _=>0))
      (κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      BorderedPeripheralClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (S : SingleCurvePieceClassics A)
    (SCut : SingleCurveCutCompanionData Cuts S)
    (HF : FullSingleCurveFillingClassics A AC.complete_domain S)
    (F : Family.{u,w}) (D : DeformationClassics F) (U : UniquenessClassics F)
    (FB : ∀ s, PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (FL : ∀ s, BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (FP : ∀ s, BorderedPeripheralClassics (F.model s) (F.boundary s))
    (FS : ∀ s, BorderedSingleCurveBoundaryClassics (F.model s) (F.boundary s))
    (MI : MirzakhaniIntegration G H T) (RG : MulticurveRestrictionGeometry G H T)
    (B : WP.External.CompactBorelVaguePairing)
    (CM : WP.External.AlmostSureContinuousMapping.{0,0,v,0})
    (I : WP.External.TwoColorPoissonRestrictionIndependence)
    (LC : WP.External.PointMeasureLaplaceConvergence.{v,0})
    (c : ℝ) (hc : 0 < c) (n : ℕ → ℕ)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c)) :
    CriticalPhysicalClusterLimit H F D FB FL J PC FP FS n c
```

</details>

<a id="target-eq:cluster-overdispersion"></a>

### Paper 14.22: Critical cluster finite moments, variance excess and non-Poisson consequence

**Paper statement** (PDF pp. 64, 65):

Equation 14.22 and its subsequent deduction — finite moments and non-Poisson critical clusters.

This is a paper-new deduction, not a separately numbered lemma in the original paper. The conditional Lean proof uses the canonical pants spectrum and the same independent Poisson product law as Theorem 14.6. Classical inputs are Campbell’s formulas and Rivin’s figure-eight formula; the count bounds, variance excess and strict non-Poisson deduction are proved locally.

The limit is not Poisson. If $m_L(s)=K_s([0,L])$, then Lemma [G.2](#target-lem:primitive-count) and the support restriction $s\le2L$ give finite moments and



$$
\operatorname{Var}\Xi_c([0,L])-\mathbb E\Xi_c([0,L])
 =\int m_L(s)(m_L(s)-1)\,\mu_c(\mathrm ds).
$$



 Besides its waist, $P_s$ contains the primitive figure-eight around its two cusps, of length $2\operatorname{arccosh}(2+\cosh(s/2))$ by \[76\] Theorem 1.3. For $L>2\operatorname{arccosh}3$, both lengths lie below $L$ on an interval of positive $\mu_c$-measure. The right side of 14.22 is therefore strictly positive. The theorem identifies these correlations in the limit; no convergence of the full-spectrum second moments is asserted.

**Lean declarations** (proved under classical premises):

- [WP.Critical.PantsCluster.critical_cluster_overdispersion](../WPFormalization/Critical/ClusterOverdispersion.lean#L19)

<details>
<summary>View formal statements</summary>

[WP.Critical.PantsCluster.critical_cluster_overdispersion](../WPFormalization/Critical/ClusterOverdispersion.lean#L19):

```lean
theorem critical_cluster_overdispersion
    (F : Family.{u, v}) (D : DeformationClassics F)
    (BC : ∀ s, PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (LS : ∀ s, BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : ∀ s, BorderedPeripheralClassics (F.model s) (F.boundary s))
    (SC : ∀ s, BorderedSingleCurveBoundaryClassics (F.model s) (F.boundary s))
    (C : PoissonIntegralMoments) (R : FigureEightClassics F)
    (c : ℝ) (hc : 0 < c) (QN QP : ProbabilityMeasure (PointMeasure ℝ≥0))
    (hN : IsPoissonPointProcessLaw ℝ≥0 nonseparatingLengthIntensity QN)
    (hP : IsPoissonPointProcessLaw ℝ≥0 (criticalPantsLengthIntensity c) QP) :
    ClusterOverdispersionConclusion F c
      (canonicalClusterSuperpositionLaw F D BC LS J PC PP SC QN QP)
```

</details>

## Conclusion

<a id="target-eq:jt-string-normalization"></a>

### Paper Section 15.1 string substitution and defect generating-function normalization: JT defect string equation and generating-function normalization

**Paper statement** (PDF p. 65):

Stage-one implementation: the complete mathematical deduction has a Lean producer linked below. The physical interpretation cited here is background; the local identities and remainder estimates are proved from the defined mathematical functions, without a new physical-model assumption.

Saad, Shenker and Stanford related the genus expansion of Jackiw–Teitelboim (JT) gravity to a matrix integral, with Weil–Petersson volumes as its geometric input \[77\]. The parameter $Y$ describes a spectral edge in its defect deformation, introduced by Maxfield–Turiaci and by Witten \[59\]; \[82\]. We record the normalization to relate the uniform estimates to that model. A defect of opening angle $2\pi\alpha$ is a cusp at $\alpha=0$ \[22\] Section 2. Let $\lambda_{\mathrm{def}}$ be its weight, distinct from the cusp density $\lambda=n/g$, and use the convention $2\gamma=1$ of Maxfield–Turiaci \[59\]. Their string equation at $\alpha=0$ and its branch connected to the undeformed edge are



$$
\frac{\sqrt{E_0}}{2\pi}I_1(2\pi\sqrt{E_0})
       +\lambda_{\mathrm{def}}=0,\qquad
 E_0=-\frac{Y}{\pi^2},\qquad x=2\pi^2\lambda_{\mathrm{def}}.
$$



 The Bessel expressions are interpreted by their entire power series. Substitution gives exactly $X(Y)=x$. Moreover, the definition [4.7](#target-eq:H8) gives, for $g\ge2$,



$$
\sum_{n\ge0}V_{g,n}\frac{\lambda_{\mathrm{def}}^n}{n!}
       =(2\pi^2)^{3g-3}\Phi_g(x).
$$



 Thus a fixed cusp count is a coefficient of the defect-weighted amplitude, whereas $Y$ parametrizes its spectral edge.

**Lean declarations** (proved under classical premises):

- [WP.JT.string_normalization](../WPFormalization/JT/StringStatement.lean#L14)

<details>
<summary>View formal statements</summary>

[WP.JT.string_normalization](../WPFormalization/JT/StringStatement.lean#L14):

```lean
theorem string_normalization (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P) :
    (∀ Y lambdaDef : ℝ,
      stringBesselEnergy (edgeEnergy Y)+lambdaDef=0 ↔ XR Y=2*Real.pi^2*lambdaDef) ∧
    (∀ lambdaDef : ℝ, 0 ≤ lambdaDef → 2*Real.pi^2*lambdaDef ≤ xCritical →
      inverseY (2*Real.pi^2*lambdaDef) ∈ Icc 0 y₀ ∧
      stringBesselEnergy (edgeEnergy (inverseY (2*Real.pi^2*lambdaDef)))+lambdaDef=0 ∧
      ∀ Y ∈ Icc 0 y₀, stringBesselEnergy (edgeEnergy Y)+lambdaDef=0 →
        Y=inverseY (2*Real.pi^2*lambdaDef)) ∧
    edgeEnergy (inverseY 0)=0 ∧
    (∀ g : ℕ, 2 ≤ g → ∀ lambdaDef : ℝ, |2*Real.pi^2*lambdaDef| < xCritical →
      HasSum (fun n : ℕ => cuspVolume G g n*lambdaDef^n/(n.factorial : ℝ))
        ((2*Real.pi^2)^(3*g-3)*(Phi P g (2*Real.pi^2*lambdaDef)).re))
```

</details>

<a id="target-eq:jt-abel-critical-edge"></a>

### Paper Section 15.1 Abel-to-kernel equality and cubic critical density: JT Abel kernel dictionary, undeformed density and cubic critical edge

**Paper statement** (PDF pp. 65, 66):

Stage-one implementation: the complete mathematical deduction has a Lean producer linked below. The physical interpretation cited here is background; the local identities and remainder estimates are proved from the defined mathematical functions, without a new physical-model assumption.

The genus-zero density, with its overall topological factor removed, can be written using our kernel. Specializing the Abel integral in \[59\] equation (3.50) to $\alpha=0$ gives



$$
\rho_0(E)=\frac1{4\pi}\int_{E_0}^{E}
        \frac{I_0(2\pi\sqrt u)}{\sqrt{E-u}}\,\mathrm du
   =\frac{\sqrt q}{2\pi}K_Y(-2\pi^2q),\qquad q=E-E_0\ge0.
$$



 For the second equality set $u=E_0+q(1-s^2)$ and use [2.1](#target-eq:P1). At $Y=0$ this is the JT density $\sinh(2\pi\sqrt E)/(4\pi^2)$. At $Y=y_0$, put $b=-X''(y_0)>0$. Since $a(y_0)=0$, expansion of $K_{y_0}$ gives



$$
\rho_0(E_0+q)=\frac{\pi b}{3}q^{3/2}+O(q^{5/2}).
$$



 The square-root edge has become a cubic critical edge, the local geometry associated with the $(2,3)$ critical point. This identifies the physical meaning of the same endpoint at which the normalized intersection recursion reduces to pure $\psi$ intersections.

**Lean declarations** (proved):

- [WP.JT.jt_abel_critical_edge](../WPFormalization/JT/Abel.lean#L43)

<details>
<summary>View formal statements</summary>

[WP.JT.jt_abel_critical_edge](../WPFormalization/JT/Abel.lean#L43):

```lean
theorem jt_abel_critical_edge : AbelDensityConclusion
```

</details>

<a id="target-eq:jt-critical-action"></a>

### Paper Section 15.1 critical action in delta and spectral-gap coordinates: JT critical action constants and relative error in both coordinates

**Paper statement** (PDF p. 66):

Stage-one implementation: the complete mathematical deduction has a Lean producer linked below. The physical interpretation cited here is background; the local identities and remainder estimates are proved from the defined mathematical functions, without a new physical-model assumption.

The exponent in the large-genus action agrees with this critical geometry. With $\delta=y_0-Y$, the endpoint expansions of Section 3 give



$$
x_c-x=\frac b2\delta^2(1+O(\delta)),\qquad
 \mathcal Z=\frac{2\sqrt3\,b}{5}\delta^{5/2}(1+O(\delta))
       =\frac{2^{9/4}\sqrt3}{5b^{1/4}}
          (x_c-x)^{5/4}\bigl(1+O(\sqrt{x_c-x})\bigr).
$$



 The marked expansion in Theorem [8.2](#target-thm:full-expansion) uses the full action $\mathcal Z(Y)$ and remains uniform as $Y$ approaches $y_0$. Replacing the action by its leading critical power would instead introduce a multiplicative factor $\exp(O(g\sqrt{x_c-x}))$ for fixed marking count. That replacement is not uniform in an arbitrary joint limit. In formal genus counting, the corresponding balance is between the string coupling $\hbar$ and $(x_c-x)^{5/4}$; the genus index $g$ is not the inverse string coupling. A double-scaled sum over all genera requires a separate summation prescription and estimates beyond the large-genus coefficient asymptotics proved here.

**Lean declarations** (proved under classical premises):

- [WP.Analysis.jt_critical_action](../WPFormalization/Analysis/JTCriticalReplacement.lean#L82)

<details>
<summary>View formal statements</summary>

[WP.Analysis.jt_critical_action](../WPFormalization/Analysis/JTCriticalReplacement.lean#L82):

```lean
theorem jt_critical_action :
    ((fun Y => (xCritical-XR Y)/((criticalB/2)*(y₀-Y)^2)-1)
      =O[𝓝[<] y₀] (fun Y => y₀-Y)) ∧
    ((fun Y => Z Y/((2*Real.sqrt 3*criticalB/5)*Real.rpow (y₀-Y) (5/2:ℝ))-1)
      =O[𝓝[<] y₀] (fun Y => y₀-Y)) ∧
    ((fun Y => Z Y/((Real.rpow 2 (9/4:ℝ)*Real.sqrt 3/
        (5*Real.rpow criticalB (1/4:ℝ)))*Real.rpow (xCritical-XR Y) (5/4:ℝ))-1)
      =O[𝓝[<] y₀] (fun Y => Real.sqrt (xCritical-XR Y))) ∧
    (∀ p : ℕ, 1 ≤ p → ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ g : ℕ, 1 ≤ g → ∀ Y ∈ Ico (0:ℝ) y₀, y₀-Y ≤ ε →
        ∃ e : ℝ, |e| ≤ C*(g:ℝ)*Real.sqrt (xCritical-XR Y) ∧
          markedModel g p Y = jtCriticalMarkedModel g p Y*Real.exp e)
```

</details>

## Appendix B: Basic estimates

<a id="target-lem:primitive-bounds"></a>

### Paper B.1: lem:primitive-bounds

**Paper statement** (PDF p. 69):

For $g\ge1$ and positive integers $d_1,\ldots,d_n$ with $\sum d_i=3g-3+n$, the normalization in [4.3](#target-eq:H4) satisfies



$$
\frac16\le C_g(d_1,\ldots,d_n)\le1.
$$

**Lean declarations** (proved under classical premises):

- [WP.primitive_bounds](../WPFormalization/Statements/PrimitiveBounds.lean#L12)

<details>
<summary>View formal statements</summary>

[WP.primitive_bounds](../WPFormalization/Statements/PrimitiveBounds.lean#L12):

```lean
theorem primitive_bounds (P : PsiTheory) (g : ℕ) (d : List ℕ) (hg : 1 ≤ g)
    (hn : 1 ≤ d.length) (hd : ∀ k ∈ d, 0 < k) (hdim : d.sum = dimension g d.length) :
    1/6 ≤ pureC P g d ∧ pureC P g d ≤ 1
```

</details>

## Appendix C: The marked expansion

<a id="target-lem:second-profile"></a>

### Paper C.1: Second profile correction

**Paper statement** (PDF p. 72):

For fixed $p\ge1$, uniformly in $Y$ and $D\le h^{1/8}$,



$$
c_{g,p}(\mathbf d)=1-\frac{\delta_p(\mathbf d)}h
       +\frac{e_p(\mathbf d)}{h^2}
       +O_p\!\left(\frac{(D+1)^6}{h^3}\right).
$$



 The function $e_p$ is independent of the chosen path.

**Lean declarations** (proved under classical premises):

- [WP.HigherOrder.secondIncrement](../WPFormalization/HigherOrder/SecondProfile.lean#L21)
- [WP.HigherOrder.secondProfile](../WPFormalization/HigherOrder/SecondProfile.lean#L38)
- [WP.second_profile](../WPFormalization/Statements/SecondProfile.lean#L10)
- [WP.second_profile_all_degrees](../WPFormalization/Statements/SecondProfile.lean#L20)
- [WP.second_profile_adjacent](../WPFormalization/Statements/SecondProfile.lean#L29)
- [WP.HigherOrder.second_profile_path_independent](../WPFormalization/Statements/SecondProfile.lean#L39)

<details>
<summary>View formal statements</summary>

[WP.HigherOrder.secondIncrement](../WPFormalization/HigherOrder/SecondProfile.lean#L21):

```lean
def secondIncrement (Y : ℝ) (i : ℕ) (d : List ℕ) : ℝ :=
  let p := d.length
  let t := d[i]!
  let tail := d.eraseIdx i
  let z := zeros tail
  A Y * (∑ j ∈ Finset.range tail.length, (2*(tail[j]! : ℝ)+1) *
    ∑' l : ℕ, if 1 ≤ t+tail[j]!+l then
      weight Y l*(1-transportBeta (p-1) Y-
        degreeCorrection ((t+tail[j]!+l-1) :: tail.eraseIdx j) Y) else 0) +
  2*A Y * (∑' l : ℕ, if 2 ≤ t+l then weight Y l *
    ∑ u ∈ Finset.range (t+l-1),
      (1-transportBeta (p+1) Y-alpha p Y-degreeCorrection (u :: (t+l-2-u) :: tail) Y)
    else 0) +
  (A Y)^2*((Nat.choose z 2+theta Y 1/2)*tailWeight Y (2-t)+tailWeight Y (3-t)/2)
```

[WP.HigherOrder.secondProfile](../WPFormalization/HigherOrder/SecondProfile.lean#L38):

```lean
def secondProfile (Y : ℝ) (d : List ℕ) : ℝ :=
  -(∑ i ∈ Finset.range d.length, ∑ t ∈ Finset.range d[i]!,
    secondIncrement Y i (beforeCoordinate d i t))
```

[WP.second_profile](../WPFormalization/Statements/SecondProfile.lean#L10):

```lean
theorem second_profile (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ d : List ℕ, d.length = p →
      (d.sum : ℝ) ≤ Real.rpow (complexity g p : ℝ) (1/8 : ℝ) →
      ∀ Y ∈ Set.Icc 0 y₀,
        |profile P g d Y - (1-degreeCorrection d Y/(complexity g p : ℝ)+
          HigherOrder.secondProfile Y d/(complexity g p : ℝ)^2)| ≤
          C*((d.sum : ℝ)+1)^6/(complexity g p : ℝ)^3
```

[WP.second_profile_all_degrees](../WPFormalization/Statements/SecondProfile.lean#L20):

```lean
theorem second_profile_all_degrees (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ d : List ℕ, d.length = p →
      ∀ Y ∈ Set.Icc 0 y₀,
        |profile P g d Y - (1-degreeCorrection d Y/(complexity g p : ℝ)+
          HigherOrder.secondProfile Y d/(complexity g p : ℝ)^2)| ≤
          C*((d.sum : ℝ)+1)^6/(complexity g p : ℝ)^3
```

[WP.second_profile_adjacent](../WPFormalization/Statements/SecondProfile.lean#L29):

```lean
theorem second_profile_adjacent (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (d : List ℕ) (hd : d.length = p)
    (i : ℕ) (hi : i < d.length) :
    HigherOrder.secondProfile Y (HigherOrder.raiseDegree d i)-HigherOrder.secondProfile Y d =
      -HigherOrder.secondIncrement Y i d
```

[WP.HigherOrder.second_profile_path_independent](../WPFormalization/Statements/SecondProfile.lean#L39):

```lean
theorem second_profile_path_independent (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (v w : ℕ → List ℕ) (i j : ℕ → ℕ) (n m : ℕ)
    (hvlen : ∀ s < n, (v s).length = p) (hwlen : ∀ s < m, (w s).length = p)
    (hi : ∀ s < n, i s < (v s).length) (hj : ∀ s < m, j s < (w s).length)
    (hv : ∀ s < n, v (s+1) = raiseDegree (v s) (i s))
    (hw : ∀ s < m, w (s+1) = raiseDegree (w s) (j s))
    (hstart : v 0 = w 0) (hend : v n = w m) :
    (∑ s ∈ Finset.range n, secondIncrement Y (i s) (v s)) =
      ∑ s ∈ Finset.range m, secondIncrement Y (j s) (w s)
```

</details>

<a id="target-eq:FE1"></a>

### Paper C.13: Triangular formal coefficient system

**Paper statement** (PDF p. 76):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\mathsf P_p(\mathbf d;t)=\sum_{j\ge0}e_{p,j}(\mathbf d)t^j,
 \quad \mathsf C_p(h)=\frac hA\frac{W_{g,p}}{W_{g,p+1}},
 \quad \mathsf G_p(h)=\frac{W_{g-1,p+2}}{W_{g,p}}.
$$

**Lean declarations** (defined under classical premises):

- [WP.HigherOrder.formalProfile](../WPFormalization/HigherOrder/Triangular.lean#L135)
- [WP.HigherOrder.formalCusp](../WPFormalization/HigherOrder/Triangular.lean#L138)
- [WP.HigherOrder.formalGenus](../WPFormalization/HigherOrder/Triangular.lean#L141)
- [WP.cuspCorrection](../WPFormalization/Statements/Coefficients.lean#L61)
- [WP.genusCorrection](../WPFormalization/Statements/Coefficients.lean#L68)

<details>
<summary>View formal statements</summary>

[WP.HigherOrder.formalProfile](../WPFormalization/HigherOrder/Triangular.lean#L135):

```lean
def formalProfile (P : PsiTheory) (Y : ℝ) (d : List ℕ) : Series :=
  PowerSeries.mk (profileCoefficient P Y d)
```

[WP.HigherOrder.formalCusp](../WPFormalization/HigherOrder/Triangular.lean#L138):

```lean
def formalCusp (P : PsiTheory) (Y : ℝ) (p : ℕ) : Series :=
  PowerSeries.mk (cuspCoefficient P Y p)
```

[WP.HigherOrder.formalGenus](../WPFormalization/HigherOrder/Triangular.lean#L141):

```lean
def formalGenus (P : PsiTheory) (Y : ℝ) (p : ℕ) : Series :=
  PowerSeries.mk (genusCoefficient P Y p)
```

[WP.cuspCorrection](../WPFormalization/Statements/Coefficients.lean#L61):

```lean
def cuspCorrection (P : PsiTheory) (g p : ℕ) (Y : ℝ) : ℝ :=
  (complexity g p : ℝ)/A Y*W P g p Y/W P g (p+1) Y
```

[WP.genusCorrection](../WPFormalization/Statements/Coefficients.lean#L68):

```lean
def genusCorrection (P : PsiTheory) (g p : ℕ) (Y : ℝ) : ℝ :=
  if g=0 then 0 else W P (g-1) (p+2) Y/W P g p Y
```

</details>

<a id="target-lem:majorant"></a>

### Paper C.2: Analytic majorants

**Paper statement** (PDF p. 77):

Let $\Phi=(\Phi_1,\ldots,\Phi_m)$ be power series in $(t,v_1,\ldots,v_m)$ with nonnegative coefficients, convergent near the origin, such that $\Phi(0,0)=0$ and the matrix $\partial_v\Phi(0,0)$ is strictly lower triangular. Then $U=\Phi(t,U)$ has a unique formal solution with $U(0)=0$. Its coefficients are nonnegative, and it converges near $t=0$. Let $e_{i,j}\in[0,\infty]$, for $1\le i\le m$ and $j\ge1$, and put $E_i=\sum_{j\ge1}e_{i,j}t^j$. If $e_{i,j}\le[t^j]\Phi_i(t,E)$ for all $i,j$, then $e_{i,j}\le[t^j]U_i$. In particular every $e_{i,j}$ is finite, and $e_{i,j}\le C\rho^{-j}$ with $C,\rho>0$ depending only on $\Phi$.

**Lean declarations** (proved under classical premises):

- [WP.analytic_majorant](../WPFormalization/Statements/Majorant.lean#L14)
- [WP.formalFixedPoint](../WPFormalization/HigherOrder/MajorantDefinitions.lean#L43)
- [WP.substitutionCoeff](../WPFormalization/HigherOrder/MajorantDefinitions.lean#L18)
- [WP.positiveLift](../WPFormalization/HigherOrder/MajorantDefinitions.lean#L32)

<details>
<summary>View formal statements</summary>

[WP.analytic_majorant](../WPFormalization/Statements/Majorant.lean#L14):

```lean
theorem analytic_majorant (m : ℕ) (Φ : Fin m → MvPowerSeries (Option (Fin m)) ℝ)
    (hpos : ∀ i α, 0 ≤ MvPowerSeries.coeff α (Φ i))
    (hzero : ∀ i, MvPowerSeries.coeff 0 (Φ i) = 0)
    (htriangular : ∀ i l : Fin m, i.val ≤ l.val →
      MvPowerSeries.coeff (Finsupp.single (some l) 1) (Φ i) = 0)
    (hconv : ∃ r : ℝ, 0 < r ∧ ∀ i,
      Summable (fun α : Option (Fin m) →₀ ℕ => MvPowerSeries.coeff α (Φ i)*r^(multiDegree α))) :
    ∃ U : Fin m → PowerSeries ℝ,
      zeroConstant U ∧ formalFixedPoint Φ U ∧
      (∀ V : Fin m → PowerSeries ℝ, zeroConstant V → formalFixedPoint Φ V → V = U) ∧
      (∀ i j, 0 ≤ PowerSeries.coeff j (U i)) ∧
      (∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧
        (∀ i j, PowerSeries.coeff j (U i) ≤ C*ρ⁻¹^j) ∧
        (∀ i t, |t| < ρ → Summable (fun j => PowerSeries.coeff j (U i)*t^j)) ∧
        ∀ e : Fin m → ℕ → ℝ≥0∞,
          (∀ i, e i 0 = 0) →
          (∀ i j, 1 ≤ j → e i j ≤
            substitutionCoeff (positiveLift (Φ i)) (fun l => PowerSeries.mk (e l)) j) →
          ∀ i j, 1 ≤ j → e i j ≤ ENNReal.ofReal (PowerSeries.coeff j (U i)) ∧
            e i j ≠ ⊤ ∧ e i j ≤ ENNReal.ofReal (C*ρ⁻¹^j))
```

[WP.formalFixedPoint](../WPFormalization/HigherOrder/MajorantDefinitions.lean#L43):

```lean
def formalFixedPoint {m : ℕ} (Φ : Fin m → MvPowerSeries (Option (Fin m)) ℝ)
    (U : Fin m → PowerSeries ℝ) : Prop :=
  ∀ i j, PowerSeries.coeff j (U i) = substitutionCoeff (Φ i) U j
```

[WP.substitutionCoeff](../WPFormalization/HigherOrder/MajorantDefinitions.lean#L18):

```lean
def substitutionCoeff {R : Type*} [CommSemiring R] {m : ℕ}
    (Φ : MvPowerSeries (Option (Fin m)) R) (E : Fin m → PowerSeries R) (j : ℕ) : R :=
  ∑ α : Option (Fin m) → Fin (j+1),
    if (∑ s, (α s).val) ≤ j then
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (fun s => (α s).val)) Φ *
        PowerSeries.coeff j ((PowerSeries.X : PowerSeries R)^((α none).val) *
          ∏ i : Fin m, E i^((α (some i)).val))
    else 0
```

[WP.positiveLift](../WPFormalization/HigherOrder/MajorantDefinitions.lean#L32):

```lean
def positiveLift {m : ℕ} (Φ : MvPowerSeries (Option (Fin m)) ℝ) :
    MvPowerSeries (Option (Fin m)) ℝ≥0∞ := fun α => ENNReal.ofReal (MvPowerSeries.coeff α Φ)
```

</details>

<a id="target-prop:hierarchy"></a>

### Paper C.3: Uniform recursive expansions

**Paper statement** (PDF p. 77):

There are $C,B,M>0$ and one complex neighborhood $\Omega$ of $[0,y_0]$ such that the preceding rules determine path-independent holomorphic coefficients with



$$
\|e_{p,j}(\mathbf d)\|_\Omega\le CB^j(D+p+Mj)^{2j},\qquad
 \|\mathsf C_{p,j}\|_\Omega+\|\mathsf G_{p,j}\|_\Omega
       \le CB^j(p+Mj)^{2j}.
$$



 For every stable state $p\ge1$, $h=2g-2+p\ge1$, every $L\ge1$, and every nonnegative degree tuple, uniformly for $0\le Y\le y_0$,



$$
\begin{aligned}
 \left|c_{g,p}(\mathbf d)-\sum_{j<L}e_{p,j}(\mathbf d)h^{-j}\right|
       &\le CB^L(D+p+ML)^{2L}h^{-L},\\
 \left|\mathsf C_p(h)-\sum_{j<L}\mathsf C_{p,j}h^{-j}\right|
 +\left|\mathsf G_p(h)-\sum_{j<L}\mathsf G_{p,j}h^{-j}\right|
       &\le CB^L(p+ML)^{2L}h^{-L}.
 \end{aligned}
$$



 Here $D=\sum d_i$, $\mathsf C_{p,j}=[t^j]\mathsf C_p(t)$ and $\mathsf G_{p,j}=[t^j]\mathsf G_p(t)$; invalid-degree profiles and invalid genus numerators are zero. For fixed $p,j$, the rules use finitely many kernel moments, low kernel coefficients and exact bounded-complexity amplitudes.

**Lean declarations** (proved under classical premises):

- [WP.uniform_recursive_expansions](../WPFormalization/Statements/RecursiveExpansions.lean#L13)

<details>
<summary>View formal statements</summary>

[WP.uniform_recursive_expansions](../WPFormalization/Statements/RecursiveExpansions.lean#L13):

```lean
theorem uniform_recursive_expansions (P : PsiTheory) :
    HigherOrder.UniformRecursiveExpansionsTarget P
```

</details>

<a id="target-lem:coefficient-bounds"></a>

### Paper C.4: Coefficient bounds

**Paper statement** (PDF p. 79):

The rules C.15–C.18 determine coefficients $e_{p,j}(\mathbf d)$, $\mathsf C_{p,j}$ and $\mathsf G_{p,j}$ that are holomorphic on $\Omega$, and there are $C,B_0$ such that, on $\Omega$, for all $p\ge1$, all degree tuples and all $j\ge0$,



$$
|e_{p,j}(\mathbf d)|\le CB_0^{\,j}S_j^{2j},\qquad
 |\mathsf C_{p,j}|+|\mathsf G_{p,j}|\le CB_0^{\,j}S_j^{2j},
$$



 with the weights C.22.

**Lean declarations** (proved under classical premises):

- [WP.coefficient_bounds](../WPFormalization/Statements/CoefficientBounds.lean#L13)

<details>
<summary>View formal statements</summary>

[WP.coefficient_bounds](../WPFormalization/Statements/CoefficientBounds.lean#L13):

```lean
theorem coefficient_bounds (P : PsiTheory) :
    HigherOrder.ComplexCanonical.CanonicalCoefficientBoundsTarget P
```

</details>

<a id="target-lem:tails"></a>

### Paper C.5: Tails over topological types

**Paper statement** (PDF p. 81):

Fix $M_0>0$. There are $C_{M_0},B_{M_0}$ such that, for all sufficiently large $h$ and all $1\le p\le M_0\sqrt h$,



$$
\begin{aligned}
 S_{g,p}^{[L]}&\le C_{M_0}\left(\frac{B_{M_0}(p+L)}h\right)^L,
                  &&2\le L\le\sqrt h,\\
 T_{g,p}^{[L]}&\le C_{M_0}\left(\frac{B_{M_0}(p+L)}h\right)^L,
                  &&1\le L\le\sqrt h,
 \end{aligned}
$$



 the second bound being used only for $p\ge2$. The ranges of $L$ start at the stability minima two and one respectively.

**Lean declarations** (proved under classical premises):

- [WP.separatingSTail](../WPFormalization/Statements/TopologyTails.lean#L11)
- [WP.separatingTTail](../WPFormalization/Statements/TopologyTails.lean#L16)
- [WP.topology_tails](../WPFormalization/Statements/TopologyTails.lean#L30)

<details>
<summary>View formal statements</summary>

[WP.separatingSTail](../WPFormalization/Statements/TopologyTails.lean#L11):

```lean
def separatingSTail (P : PsiTheory) (g p L : ℕ) (Y : ℝ) : ℝ :=
  markedSplitLossTail P g p 1 L Y
```

[WP.separatingTTail](../WPFormalization/Statements/TopologyTails.lean#L16):

```lean
def separatingTTail (P : PsiTheory) (g p L : ℕ) (Y : ℝ) : ℝ :=
  markedSplitLossTail P g p 2 L Y
```

[WP.topology_tails](../WPFormalization/Statements/TopologyTails.lean#L30):

```lean
theorem topology_tails (P : PsiTheory) (M₀ : ℝ) (hM₀ : 0 < M₀) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∃ H : ℕ,
      (∀ g p : ℕ, 1 ≤ p → H ≤ complexity g p →
        (p : ℝ) ≤ M₀*Real.sqrt (complexity g p : ℝ) →
        ∀ L : ℕ, 2 ≤ L → (L : ℝ) ≤ Real.sqrt (complexity g p : ℝ) →
        ∀ Y ∈ Set.Icc 0 y₀,
          separatingSTail P g p L Y ≤ C*(B*((p : ℝ)+L)/(complexity g p : ℝ))^L) ∧
      (∀ g p : ℕ, 2 ≤ p → H ≤ complexity g p →
        (p : ℝ) ≤ M₀*Real.sqrt (complexity g p : ℝ) →
        ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ Real.sqrt (complexity g p : ℝ) →
        ∀ Y ∈ Set.Icc 0 y₀,
          separatingTTail P g p L Y ≤ C*(B*((p : ℝ)+L)/(complexity g p : ℝ))^L)
```

</details>

<a id="target-lem:first-order"></a>

### Paper C.6: First-order estimates

**Paper statement** (PDF p. 81):

Fix $M_0>0$. For all sufficiently large $h$, all $1\le p\le M_0\sqrt h$ and all degree tuples,



$$
0\le1-c_{g,p}(\mathbf d)
 \le\min\{1,C_{M_0}D(D+p+1)/h\},\qquad
 |\mathsf C_p(h)-1|+|\mathsf G_p(h)-1|\le C_{M_0}(p+1)/h.
$$

**Lean declarations** (proved under classical premises):

- [WP.growing_marking_first_order](../WPFormalization/Statements/GrowingMarkingFirstOrder.lean#L8)
- [WP.cuspCorrection](../WPFormalization/Statements/Coefficients.lean#L61)
- [WP.genusCorrection](../WPFormalization/Statements/Coefficients.lean#L68)

<details>
<summary>View formal statements</summary>

[WP.growing_marking_first_order](../WPFormalization/Statements/GrowingMarkingFirstOrder.lean#L8):

```lean
theorem growing_marking_first_order (P : PsiTheory) (M₀ : ℝ) (hM : 0 < M₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ h₀ : ℕ, ∀ g p : ℕ, 1 ≤ p →
    h₀ ≤ complexity g p → (p : ℝ) ≤ M₀*Real.sqrt (complexity g p) →
    ∀ Y ∈ Set.Icc 0 y₀,
      (∀ d : List ℕ, d.length = p →
        0 ≤ 1-profile P g d Y ∧ 1-profile P g d Y ≤
          min 1 (C*(d.sum : ℝ)*(d.sum+p+1)/complexity g p)) ∧
      |cuspCorrection P g p Y-1|+|genusCorrection P g p Y-1| ≤ C*(p+1)/complexity g p
```

[WP.cuspCorrection](../WPFormalization/Statements/Coefficients.lean#L61):

```lean
def cuspCorrection (P : PsiTheory) (g p : ℕ) (Y : ℝ) : ℝ :=
  (complexity g p : ℝ)/A Y*W P g p Y/W P g (p+1) Y
```

[WP.genusCorrection](../WPFormalization/Statements/Coefficients.lean#L68):

```lean
def genusCorrection (P : PsiTheory) (g p : ℕ) (Y : ℝ) : ℝ :=
  if g=0 then 0 else W P (g-1) (p+2) Y/W P g p Y
```

</details>

<a id="target-eq:FE14"></a>

### Paper C.37: Quantitative endpoint normalization

**Paper statement** (PDF p. 86):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\begin{aligned}
 E_{g,p}&=Z_g\,\frac{\Gamma(h_0+3/2)}{\Gamma(h_0)h_0^{3/2}}
             \frac{R_p(h_0)}{1+4/(5h_0)},\\
 R_p(h_0)&=\sqrt{1+p/h_0}\prod_{i=0}^{p-1}
                       \frac{1+4i/(5h_0)}{1+i/h_0}.
 \end{aligned}
$$

**Lean declarations** (proved under classical premises):

- [WP.HigherOrder.exactEndpoint](../WPFormalization/HigherOrder/PureEndpoint.lean#L173)
- [WP.HigherOrder.endpointInsertionFactor](../WPFormalization/HigherOrder/PureEndpoint.lean#L403)
- [WP.HigherOrder.exactEndpoint_formula](../WPFormalization/HigherOrder/PureEndpoint.lean#L444)

<details>
<summary>View formal statements</summary>

[WP.HigherOrder.exactEndpoint](../WPFormalization/HigherOrder/PureEndpoint.lean#L173):

```lean
def exactEndpoint (P : PsiTheory) (g p : ℕ) : ℝ :=
  Real.pi*normalized P g (List.replicate p 0) y₀ /
    (Real.Gamma (complexity g p)/(4:ℝ)^g*(15/2:ℝ)^(complexity g p)*
      Real.sqrt ((2/15:ℝ)/(Real.pi*(complexity g p))))
```

[WP.HigherOrder.endpointInsertionFactor](../WPFormalization/HigherOrder/PureEndpoint.lean#L403):

```lean
def endpointInsertionFactor (h : ℝ) (p : ℕ) : ℝ :=
  Real.sqrt (1+(p:ℝ)/h)*
    ∏ i ∈ Finset.range p, (1+4*(i:ℝ)/(5*h))/(1+(i:ℝ)/h)
```

[WP.HigherOrder.exactEndpoint_formula](../WPFormalization/HigherOrder/PureEndpoint.lean#L444):

```lean
lemma exactEndpoint_formula (P : PsiTheory) (g p : ℕ) (hg : 2 ≤ g) :
    exactEndpoint P g p = External.normalizedZeroInstanton g *
      (Real.Gamma (((2*g-2:ℕ):ℝ)+3/2) /
        (Real.Gamma ((2*g-2:ℕ):ℝ)*Real.rpow ((2*g-2:ℕ):ℝ) (3/2))) *
      endpointInsertionFactor ((2*g-2:ℕ):ℝ) p /(1+4/(5*((2*g-2:ℕ):ℝ)))
```

</details>

## Appendix D: Coefficient extraction

<a id="target-prop:quantitative-local"></a>

### Paper D.1: prop:quantitative-local

**Paper statement** (PDF p. 88):

Fix $p\ge1$, and use $h,\mu,\sigma$ from [9.4](#target-eq:TL37). There are constants $C_p,\kappa_p>0$ such that, with $M=\min(h,\mu)$,



$$
\sup_{k\in\mathbb Z}
 \left|\sigma\mathbb P_x(N=k)-
 \frac{\mathrm{e}^{-(k-\mu)^2/(2\sigma^2)}}{\sqrt{2\pi}}\right|
 \le C_p M^{-\kappa_p},
$$



 whenever $M$ is sufficiently large, uniformly for $0<x<x_c$.

**Lean declarations** (proved under classical premises):

- [WP.quantitative_cusp_local](../WPFormalization/Statements/QuantitativeCuspLocal.lean#L13)

<details>
<summary>View formal statements</summary>

[WP.quantitative_cusp_local](../WPFormalization/Statements/QuantitativeCuspLocal.lean#L13):

```lean
theorem quantitative_cusp_local (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C κ M₀ : ℝ, 0 < C ∧ 0 < κ ∧ 0 < M₀ ∧
    ∀ g : ℕ, ∀ x ∈ Set.Ioo 0 xCritical,
      let h : ℝ := complexity g p
      let μ := h*Psi x
      let σ := Real.sqrt (h*euler Psi x)
      M₀ ≤ min h μ → ∀ k : ℤ,
        |σ*(if 0 ≤ k then cuspMass P g p k.toNat x else 0) -
          Real.exp (-((k : ℝ)-μ)^2/(2*σ^2))/Real.sqrt (2*Real.pi)| ≤
          C*Real.rpow (min h μ) (-κ)
```

</details>

<a id="target-lem:local-comparison"></a>

### Paper D.2: Local comparison

**Paper statement** (PDF p. 90):

There are a fixed order $K_c$ and a constant $C_0$ such that, uniformly for $M\ge C_0\log h$,



$$
\sigma\mathbb P_x(N=k)=\frac1{2\pi}\int_{-T}^{T}\mathcal L_{h,[K_c]}(it)\,\mathrm dt
 +O(h^{-2}),\qquad T^2=A_0\log h.
$$

**Lean declarations** (proved under classical premises):

- [WP.HigherOrder.local_comparison](../WPFormalization/HigherOrder/LocalComparison.lean#L188)

<details>
<summary>View formal statements</summary>

[WP.HigherOrder.local_comparison](../WPFormalization/HigherOrder/LocalComparison.lean#L188):

```lean
theorem local_comparison (P:PsiTheory)(p:ℕ)(hp:1≤p):
    ∃Kc:ℕ,∃A₀ C₀ C H:ℝ,0<A₀ ∧ 0<C₀ ∧ 0<C ∧ 0<H ∧
      ∀g k:ℕ,H≤(complexity g p:ℝ)→∀x∈Ioo (0:ℝ) xCritical,
        (k:ℝ)=(complexity g p:ℝ)*Psi x→
        C₀*Real.log (complexity g p:ℝ)≤ min (complexity g p:ℝ) (k:ℝ)→
        let T:=Real.sqrt (A₀*Real.log (complexity g p:ℝ))
        T^2=A₀*Real.log (complexity g p:ℝ) ∧
        ∃M:ℂ→ℂ,IsLocalFiniteMarkedModel P g p k Kc x (16*T) M ∧
          ‖((Real.sqrt ((complexity g p:ℝ)*euler Psi x)*cuspMass P g p k x:ℝ):ℂ)-
            ((2*Real.pi:ℝ):ℂ)⁻¹*(∫t:ℝ in Icc (-T) T,M (Complex.I*(t:ℂ)))‖≤
              C/(complexity g p:ℝ)^2
```

</details>

<a id="target-lem:large-indices"></a>

### Paper D.3: Large indices

**Paper statement** (PDF p. 90):

The estimate 10.2 holds uniformly for integers $k\ge h^{1/4}$.

**Lean declarations** (proved under classical premises):

- [WP.HigherOrder.extraction_large_indices](../WPFormalization/HigherOrder/ExtractionIndexRanges.lean#L26)

<details>
<summary>View formal statements</summary>

[WP.HigherOrder.extraction_large_indices](../WPFormalization/HigherOrder/ExtractionIndexRanges.lean#L26):

```lean
theorem extraction_large_indices (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧
      ∀ g k : ℕ, H ≤ (complexity g p : ℝ) →
        (complexity g p : ℝ) ^ (1 / 4 : ℝ) ≤ (k : ℝ) →
        |realCoeff (iteratedDeriv p (Phi P g)) k / extractionQ g p k - 1| ≤
          C / (complexity g p : ℝ)
```

</details>

<a id="target-lem:small-indices"></a>

### Paper D.4: Small indices

**Paper statement** (PDF p. 91):

The estimate 10.2 holds uniformly for integers $0\le k\le h^{1/4}$.

**Lean declarations** (proved under classical premises):

- [WP.HigherOrder.extraction_small_indices](../WPFormalization/HigherOrder/ExtractionIndexRanges.lean#L38)

<details>
<summary>View formal statements</summary>

[WP.HigherOrder.extraction_small_indices](../WPFormalization/HigherOrder/ExtractionIndexRanges.lean#L38):

```lean
theorem extraction_small_indices (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧
      ∀ g k : ℕ, H ≤ (complexity g p : ℝ) →
        (k : ℝ) ≤ (complexity g p : ℝ) ^ (1 / 4 : ℝ) →
        |realCoeff (iteratedDeriv p (Phi P g)) k / extractionQ g p k - 1| ≤
          C / (complexity g p : ℝ)
```

</details>

<a id="target-lem:phase-change"></a>

### Paper D.5: Analytic phase change

**Paper statement** (PDF p. 92):

Let $S$ be analytic near zero with $S(0)=0$ and $S'(0)=s>0$, and let $x=x(\nu)$ be the solution of $xS'(x)=\nu$ near zero, so that $x=\nu/s+O(\nu^2)$. There is a jointly analytic map $z=Z(u,\nu)$ on a fixed polydisk, with $Z(0,\nu)=0$, such that



$$
S(z)-\nu\log z=u-\nu\log u+\mathcal H(\nu),\qquad
 \mathcal H(\nu)=S(x)-\nu+\nu\log(\nu/x),\qquad Z(\nu,\nu)=x.
$$



 If $H$ is analytic near zero and $f(u,\nu)=H(Z(u,\nu))\,uZ_u(u,\nu)/Z(u,\nu)$, then $f$ is jointly analytic, including at $u=0$, and for all sufficiently small $\nu=k/h$,



$$
[z^k]\mathrm{e}^{hS(z)}H(z)
       =\mathrm{e}^{h\mathcal H(\nu)}[u^k]\mathrm{e}^{hu}f(u,\nu).
$$

**Lean declarations** (proved):

- [WP.analytic_phase_change](../WPFormalization/Statements/Poisson.lean#L40)
- [WP.phaseAmplitude](../WPFormalization/Statements/PhaseChangeDefinitions.lean#L19)
- [WP.phaseQuotient](../WPFormalization/Statements/PhaseChangeDefinitions.lean#L11)

<details>
<summary>View formal statements</summary>

[WP.analytic_phase_change](../WPFormalization/Statements/Poisson.lean#L40):

```lean
theorem analytic_phase_change (S : ℂ → ℂ) (hS : AnalyticAt ℂ S 0) (hzero : S 0 = 0)
    (hsreal : (deriv S 0).im = 0) (hspos : 0 < (deriv S 0).re) :
    ∃ R : ℝ, 0 < R ∧ ∃ x Q : ℂ → ℂ, ∃ Z : ℂ × ℂ → ℂ,
      AnalyticOnNhd ℂ x (Metric.ball 0 R) ∧
      AnalyticOnNhd ℂ Q (Metric.ball 0 R) ∧
      AnalyticOnNhd ℂ Z (Metric.ball 0 R ×ˢ Metric.ball 0 R) ∧
      x 0 = 0 ∧ deriv x 0 = (deriv S 0)⁻¹ ∧ Q 0 = deriv S 0 ∧
      (∀ ν : ℂ, ‖ν‖ < R → x ν*deriv S (x ν) = ν ∧
        (ν ≠ 0 → Q ν = ν/x ν) ∧ Z (0,ν) = 0 ∧ Z (ν,ν) = x ν) ∧
      (∀ u ν : ℂ, ‖u‖ < R → ‖ν‖ < R →
        phaseQuotient Z u ν ≠ 0 ∧
        S (Z (u,ν))-u-ν*Complex.log (phaseQuotient Z u ν) =
          S (x ν)-ν+ν*Complex.log (Q ν)) ∧
      (∀ H : ℂ → ℂ, AnalyticAt ℂ H 0 → ∃ δ : ℝ, 0 < δ ∧
        AnalyticOnNhd ℂ (phaseAmplitude Z H) (Metric.ball 0 δ ×ˢ Metric.ball 0 δ) ∧
        ∀ h k : ℕ, 1 ≤ h → (k : ℝ)/h < δ →
          let ν : ℂ := (k : ℂ)/h
          coeff (fun z => Complex.exp (h*S z)*H z) k =
            Complex.exp (h*(S (x ν)-ν+ν*Complex.log (Q ν))) *
              coeff (fun u => Complex.exp (h*u)*phaseAmplitude Z H (u,ν)) k)
```

[WP.phaseAmplitude](../WPFormalization/Statements/PhaseChangeDefinitions.lean#L19):

```lean
def phaseAmplitude (Z : ℂ × ℂ → ℂ) (H : ℂ → ℂ) (z : ℂ × ℂ) : ℂ :=
  H (Z z) * deriv (fun u => Z (u,z.2)) z.1 / phaseQuotient Z z.1 z.2
```

[WP.phaseQuotient](../WPFormalization/Statements/PhaseChangeDefinitions.lean#L11):

```lean
def phaseQuotient (Z : ℂ × ℂ → ℂ) (u ν : ℂ) : ℂ :=
  if u = 0 then deriv (fun w => Z (w,ν)) 0 else Z (u,ν)/u
```

</details>

<a id="target-lem:poisson-central"></a>

### Paper D.6: Poisson central expansion

**Paper statement** (PDF p. 93):

Let $f(u,\nu)$ be jointly analytic and bounded by one on a fixed polydisk. There are $\nu_0,C>0$ such that, uniformly for $0\le\nu=k/h\le\nu_0$ and $0\le K\le h/2$,



$$
\begin{aligned}
 \mathscr P_{h,k}f&=\sum_{j=0}^Kh^{-j}\mathscr T_j[f](\nu)
       +O\!\left(C^{K+1}(K+1)!h^{-K-1}\right),\\
 \mathscr T_0[f]&=f(\nu,\nu),\qquad
 \mathscr T_j[f]=\sum_{m=j+1}^{2j}
 t_{m,j}\nu^{m-j}\frac{\partial_u^mf(\nu,\nu)}{m!}\quad(j\ge1).
 \end{aligned}
$$



 Moreover $\|\mathscr T_j[f]\|\le C^{j+1}j!$ on a smaller complex disk in $\nu$, each $\mathscr T_j[f]$ with $j\ge1$ vanishes at $\nu=0$, and $|\mathscr P_{h,k}f|\le C$.

**Lean declarations** (proved):

- [WP.poisson_central_expansion](../WPFormalization/Statements/Poisson.lean#L19)
- [WP.poissonOperator](../WPFormalization/Statements/PoissonDefinitions.lean#L20)
- [WP.poissonCorrection](../WPFormalization/Statements/PoissonDefinitions.lean#L28)
- [WP.centralCoefficient](../WPFormalization/Statements/PoissonDefinitions.lean#L12)

<details>
<summary>View formal statements</summary>

[WP.poisson_central_expansion](../WPFormalization/Statements/Poisson.lean#L19):

```lean
theorem poisson_central_expansion (R : ℝ) (hR : 0 < R) (f : ℂ × ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 R ×ˢ Metric.ball 0 R))
    (hbound : ∀ z ∈ Metric.ball (0 : ℂ) R ×ˢ Metric.ball (0 : ℂ) R, ‖f z‖ ≤ 1) :
    ∃ ν₀ ρ C : ℝ, 0 < ν₀ ∧ 0 < ρ ∧ 0 < C ∧
      (∀ h k K : ℕ, 1 ≤ h → (k : ℝ)/h ≤ ν₀ → 2*K ≤ h →
        ‖poissonOperator f h k -
          ∑ j ∈ Finset.range (K+1), (h : ℂ)⁻¹^j * poissonCorrection f j ((k : ℂ)/h)‖ ≤
          C^(K+1)*(K+1).factorial/(h : ℝ)^(K+1)) ∧
      (∀ j : ℕ, AnalyticOnNhd ℂ (poissonCorrection f j) (Metric.ball 0 ρ) ∧
        ∀ ν : ℂ, ‖ν‖ < ρ → ‖poissonCorrection f j ν‖ ≤ C^(j+1)*j.factorial) ∧
      (∀ j : ℕ, 1 ≤ j → poissonCorrection f j 0 = 0) ∧
      (∀ h k : ℕ, 1 ≤ h → (k : ℝ)/h ≤ ν₀ → ‖poissonOperator f h k‖ ≤ C)
```

[WP.poissonOperator](../WPFormalization/Statements/PoissonDefinitions.lean#L20):

```lean
def poissonOperator (f : ℂ × ℂ → ℂ) (h k : ℕ) : ℂ :=
  (k.factorial : ℂ)/(h : ℂ)^k * coeff (fun u => Complex.exp (h*u)*f (u,(k : ℂ)/h)) k
```

[WP.poissonCorrection](../WPFormalization/Statements/PoissonDefinitions.lean#L28):

```lean
def poissonCorrection (f : ℂ × ℂ → ℂ) (j : ℕ) (ν : ℂ) : ℂ :=
  if j = 0 then f (ν,ν) else
    ∑ m ∈ Finset.Icc (j+1) (2*j), centralCoefficient m j * ν^(m-j) *
      iteratedDeriv m (fun u => f (u,ν)) ν / m.factorial
```

[WP.centralCoefficient](../WPFormalization/Statements/PoissonDefinitions.lean#L12):

```lean
def centralCoefficient (m j : ℕ) : ℂ :=
  (m.factorial : ℂ) * coeff (fun t => (Complex.log (1+t)-t)^(m-j)) m / (m-j).factorial
```

</details>

<a id="target-eq:CG12"></a>

### Paper D.24: Explicit first extracted correction

**Paper statement** (PDF p. 97):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\begin{aligned}
 \mathcal A_{p,1}={}&\mathcal L_{p,1}
 -\frac{\mathscr D^2b+(\mathscr Db)^2}{2v}
 +\frac{(\mathscr Db)\mathscr D^2\Psi}{2v^2}
 +\frac{\mathscr D^3\Psi}{8v^2}
 -\frac{5(\mathscr D^2\Psi)^2}{24v^3}+\frac1{12\Psi},
 \qquad b=\log B_p.
 \end{aligned}
$$

**Lean declarations** (proved under classical premises):

- [WP.HigherOrder.first_extracted_correction](../WPFormalization/HigherOrder/FirstExtractedCorrection.lean#L111)

<details>
<summary>View formal statements</summary>

[WP.HigherOrder.first_extracted_correction](../WPFormalization/HigherOrder/FirstExtractedCorrection.lean#L111):

```lean
theorem first_extracted_correction (P : PsiTheory) (p : ℕ)
    (Y : ℝ) (hY : Y ∈ Set.Ioo (0:ℝ) y₀) :
    extractedCoefficient P p 1 Y = markedCoefficient P p 1 Y -
      (((euler^[2]) (fun t => Real.log (extractionB p t))) (XR Y) +
        ((euler (fun t => Real.log (extractionB p t))) (XR Y))^2) /
          (2 * euler Psi (XR Y)) +
      (euler (fun t => Real.log (extractionB p t))) (XR Y) * ((euler^[2]) Psi) (XR Y) /
          (2 * (euler Psi (XR Y))^2) +
      ((euler^[3]) Psi) (XR Y) / (8 * (euler Psi (XR Y))^2) -
      5 * (((euler^[2]) Psi) (XR Y))^2 / (24 * (euler Psi (XR Y))^3) +
      1/(12*Psi (XR Y))
```

</details>

<a id="target-eq:CG13"></a>

### Paper D.25: Critical value of first correction

**Paper statement** (PDF p. 48):

With the variables and hypotheses of the surrounding section, the mathematical statement is:





$$
\mathcal A_{p,1}(y_0)=-\frac{p^2}{8}+\frac p2-\frac{37}{60}.
$$

**Lean declarations** (proved under classical premises):

- [WP.HigherOrder.first_extracted_correction_critical](../WPFormalization/HigherOrder/FirstExtractedCritical.lean#L57)

<details>
<summary>View formal statements</summary>

[WP.HigherOrder.first_extracted_correction_critical](../WPFormalization/HigherOrder/FirstExtractedCritical.lean#L57):

```lean
theorem first_extracted_correction_critical (P:PsiTheory) (p:ℕ) :
    extractedCoefficient P p 1 y₀ = -(p:ℝ)^2/8+p/2-37/60
```

</details>

## Appendix E: The rate for adjacent degrees

<a id="target-thm:quantitative-coefficient"></a>

### Paper E.1: Quantitative adjacent ratios

**Paper statement** (PDF p. 97):

There is a constant $C$ such that, for all sufficiently large $g$,



$$
\sup_{0\le k<3g-2}
 \left|\frac{a_{g,k}/a_{g,k+1}}{4\pi^2/t_{g,k}^2}-1\right|
 \le Cg^{-1/8}.
$$



 For every fixed $\varepsilon\in(0,3)$ there is $C_\varepsilon$ such that



$$
\sup_{\varepsilon g\le k<3g-2}
 \left|\frac{a_{g,k}/a_{g,k+1}}{4\pi^2/t_{g,k}^2}-1\right|
 \le C_\varepsilon g^{-1/4}.
$$



 In the second supremum $k$ is an integer. Both bounds include bounded positive codimension from the top coefficient.

**Lean declarations** (proved under classical premises):

- [WP.quantitative_adjacent](../WPFormalization/Statements/QuantitativeAdjacent.lean#L13)

<details>
<summary>View formal statements</summary>

[WP.quantitative_adjacent](../WPFormalization/Statements/QuantitativeAdjacent.lean#L13):

```lean
theorem quantitative_adjacent (P : PsiTheory) :
    (∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ k : ℕ, k < 3*g-2 →
      adjacentError P g k ≤ C*Real.rpow g (-1/8 : ℝ)) ∧
    (∀ ε ∈ Set.Ioo (0 : ℝ) 3, ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀,
      ∀ k : ℕ, ε*g ≤ k → k < 3*g-2 → adjacentError P g k ≤ C*Real.rpow g (-1/4 : ℝ))
```

</details>

<a id="target-lem:uniform-saddle"></a>

### Paper E.2: Endpoint-uniform saddle estimate

**Paper statement** (PDF p. 98):

For integers $0\le m\le3h/2$, let $z=\zeta(m/h)$, interpreting the $m=0$ expressions by continuity. Then, uniformly in $m$,



$$
\log \widetilde A_m(h)=-h\log H(z)-m\log z+O(\log(h+1)).
$$

**Lean declarations** (proved under classical premises):

- [WP.uniform_saddle](../WPFormalization/Statements/UniformSaddle.lean#L11)
- [WP.unscaledCoeff](../WPFormalization/Statements/Coefficients.lean#L53)
- [WP.unscaledMean](../WPFormalization/Statements/Coefficients.lean#L41)
- [WP.saddleZeta](../WPFormalization/Statements/Coefficients.lean#L47)

<details>
<summary>View formal statements</summary>

[WP.uniform_saddle](../WPFormalization/Statements/UniformSaddle.lean#L11):

```lean
theorem uniform_saddle : ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 1 ≤ h → ∀ m : ℕ,
    2*m ≤ 3*h →
    |Real.log (unscaledCoeff h m) + (h : ℝ)*Real.log (H 0 (saddleZeta ((m : ℝ)/h))).re +
      (m : ℝ)*Real.log (saddleZeta ((m : ℝ)/h))| ≤ C*Real.log (h+1)
```

[WP.unscaledCoeff](../WPFormalization/Statements/Coefficients.lean#L53):

```lean
def unscaledCoeff (h m : ℕ) : ℝ := realCoeff (fun z => (H 0 z)⁻¹^h) m
```

[WP.unscaledMean](../WPFormalization/Statements/Coefficients.lean#L41):

```lean
def unscaledMean (z : ℝ) : ℝ := -z*(deriv (H 0) z).re/(H 0 z).re
```

[WP.saddleZeta](../WPFormalization/Statements/Coefficients.lean#L47):

```lean
def saddleZeta (u : ℝ) : ℝ := sInf {z : ℝ | z ∈ Set.Icc 0 (Real.pi^2/2) ∧ unscaledMean z = u}
```

</details>

<a id="target-lem:log-comparison"></a>

### Paper E.3: Logarithmic comparison up to the endpoints

**Paper statement** (PDF p. 98):

There is a constant $C$ such that



$$
\max_{0\le k\le N}|G_g(k)-g f(k/g)|\le C\sqrt g.
$$

**Lean declarations** (proved under classical premises):

- [WP.logarithmic_comparison](../WPFormalization/Statements/LogarithmicComparison.lean#L13)
- [WP.logComparisonG](../WPFormalization/Statements/Coefficients.lean#L95)
- [WP.logDegreeProfile](../WPFormalization/Statements/Coefficients.lean#L85)

<details>
<summary>View formal statements</summary>

[WP.logarithmic_comparison](../WPFormalization/Statements/LogarithmicComparison.lean#L13):

```lean
theorem logarithmic_comparison (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, 1 ≤ g → ∀ k : ℕ, k ≤ 3*g-2 →
      |logComparisonG P g k-(g : ℝ)*logDegreeProfile ((k : ℝ)/g)| ≤ C*Real.sqrt g
```

[WP.logComparisonG](../WPFormalization/Statements/Coefficients.lean#L95):

```lean
def logComparisonG (P : PsiTheory) (g k : ℕ) : ℝ :=
  Real.log (mixedJ P g k/(mixedJ P g (3*g-2)*(g : ℝ)^(2*(3*g-2-k))))
```

[WP.logDegreeProfile](../WPFormalization/Statements/Coefficients.lean#L85):

```lean
def logDegreeProfile (α : ℝ) : ℝ :=
  let z := saddleZeta ((3-α)/2)
  show ℝ from -2*Real.log (H 0 z).re-(3-α)*Real.log z+(3-α)*Real.log (3-α)+
    3*Real.log 6-α*Real.log (2*α)-2*(3-α)
```

</details>

## Appendix F: The tight length spectrum

<a id="target-lem:tight-gf"></a>

### Paper F.1: Tight generating functions

**Paper statement** (PDF p. 100):

Let $(g,p)$ be stable and $0\le Y<y_0$. The tight generating function is expressed through the shifted amplitudes by the exact identity



$$
\mathscr T_{g,p}(X(Y);\mathbf L)
 =\sum_{\mathbf d}U^Y_{g,p}(\mathbf d)
       \prod_{i=1}^p\frac{L_i^{2d_i}}{P^{d_i}(2d_i+1)!},
$$



 which fixes both the normalization and the meaning of the protected boundaries. Its ratio to the ordinary marked generating function satisfies



$$
\begin{aligned}
 1\le\frac{\mathscr T_{g,p}(X(Y);\mathbf L)}{F_{g,p}(X(Y))}
   &\le\prod_{i=1}^p S(\varrho(Y)L_i),\\
 \frac{\mathscr T_{g,p}(X(Y);\mathbf L)}{F_{g,p}(X(Y))}
   &=\prod_{i=1}^p S(\varrho(Y)L_i)
        \bigl(1+O_{p,B}(g^{-1})\bigr)
       \quad\text{if }\max_i\varrho(Y)L_i\le B,
 \end{aligned}
$$



 where the inequality holds at every stable genus. Finally, for each fixed physical length vector,



$$
\mathscr T_{g,p}(x;\mathbf L)=V(x)^{2g-2+p}R_{g,p,\mathbf L}(x),
 \qquad [x^j]R_{g,p,\mathbf L}(x)\ge0,
$$



 and the series converge for $0\le x<x_c$.

Lean coverage: the associated declarations prove the identity, bounds,
uniform relative error, and convergent positive factor for every stable
protected count, including p=0. The classical Budd--Zonneveld transform and
higher-kappa realization remain explicit inputs; their concrete geometric
instances have not been constructed.

**Lean declarations** (proved under classical premises):

- [WP.tightGeneratingFunction_identity](../WPFormalization/Tight/GeometricGeneratingFunctions.lean#L37)
- [WP.tightGeneratingFunction_allStable_bounds](../WPFormalization/Tight/AllStableGeneratingFunctions.lean#L81)
- [WP.tightGeneratingFunction_allStable_uniform_relative_error](../WPFormalization/Tight/AllStableGeneratingFunctions.lean#L91)
- [WP.tightGeneratingFunction_allStable_positive_factor](../WPFormalization/Tight/AllStableGeneratingFunctions.lean#L106)

<details>
<summary>View formal statements</summary>

[WP.tightGeneratingFunction_identity](../WPFormalization/Tight/GeometricGeneratingFunctions.lean#L37):

```lean
lemma tightGeneratingFunction_identity {P:PsiTheory} {G:WeilPeterssonGeometry P}
    (T:TightRegions G) (B:BuddZonneveldTransform G T)
    (g p:ℕ) (hs:Stable g p) (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀)
    (L:Fin p→ℝ) (hL:∀i,0≤L i):
    tightGeneratingFunction T g p L (XR Y)=tightShiftedPolynomial P g p Y L
```

[WP.tightGeneratingFunction_allStable_bounds](../WPFormalization/Tight/AllStableGeneratingFunctions.lean#L81):

```lean
lemma tightGeneratingFunction_allStable_bounds {P:PsiTheory} {G:WeilPeterssonGeometry P}
    (T:TightRegions G) (BZ:BuddZonneveldTransform G T) (C:HigherKappaRealization P)
    (g p:ℕ) (hs:Stable g p) (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀)
    (L:Fin p→ℝ) (hL:∀i,0≤L i):
    1≤tightGeneratingFunction T g p L (XR Y)/shifted P g (List.replicate p 0) Y ∧
    tightGeneratingFunction T g p L (XR Y)/shifted P g (List.replicate p 0) Y≤
      ∏i,boundaryFactor 0 (tightParameterScale Y*L i)
```

[WP.tightGeneratingFunction_allStable_uniform_relative_error](../WPFormalization/Tight/AllStableGeneratingFunctions.lean#L91):

```lean
lemma tightGeneratingFunction_allStable_uniform_relative_error
    {P:PsiTheory} {G:WeilPeterssonGeometry P} (T:TightRegions G)
    (BZ:BuddZonneveldTransform G T) (C:HigherKappaRealization P)
    (p:ℕ) (B:ℝ) (hB:0≤B):
    ∃K:ℝ,0<K ∧ ∀g:ℕ,1≤g→Stable g p→∀Y∈Ico (0:ℝ) y₀,∀L:Fin p→ℝ,
      (∀i,0≤L i)→(∀i,tightParameterScale Y*L i≤B)→
      |tightGeneratingFunction T g p L (XR Y)/
        (shifted P g (List.replicate p 0) Y*
          ∏i,boundaryFactor 0 (tightParameterScale Y*L i))-1|≤K/(g:ℝ)
```

[WP.tightGeneratingFunction_allStable_positive_factor](../WPFormalization/Tight/AllStableGeneratingFunctions.lean#L106):

```lean
lemma tightGeneratingFunction_allStable_positive_factor
    {P:PsiTheory} {G:WeilPeterssonGeometry P} (T:TightRegions G)
    (BZ:BuddZonneveldTransform G T) (C:HigherKappaRealization P)
    (g p:ℕ) (hs:Stable g p) (L:Fin p→ℝ) (hL:∀i,0≤L i)
    (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical):
    (tightGeneratingFunction T g p L x:ℂ)=
      universalV P (x:ℂ)^(complexity g p)*tightPositiveFactor C g p L (x:ℂ)
```

</details>

<a id="target-lem:tight-connected"></a>

### Paper F.2: Connected cut configurations

**Paper statement** (PDF p. 101):

Fix $k$ and a compact box of scaled lengths $\mathbf t\in[0,\infty)^{2k}$. With $x$ chosen as above, uniformly for $\mathbf t$ in the box,



$$
\frac{[z^n]\mathscr T_{g-k,2k}(z;\mathbf t/\alpha_x)}
      {[z^n]\Phi_g(z)}
 =(4r(Y))^k\prod_{i=1}^{2k}S(t_i/2)(1+o(1)).
$$



 Moreover $\alpha_x/\alpha(n/g)\to1$.

**Lean declarations** (proved under classical premises):

- [WP.TightConnected.tight_connected_original_saddle](../WPFormalization/Tight/ConnectedOriginal.lean#L20)
- [WP.TightConnected.tight_connected_original_scale](../WPFormalization/Tight/ConnectedOriginal.lean#L72)
- [WP.TightConnected.tight_connected_original_bounded](../WPFormalization/Tight/ConnectedOriginal.lean#L91)
- [WP.TightConnected.tight_connected_original_bounded_scale](../WPFormalization/Tight/ConnectedOriginal.lean#L102)
- [WP.TightConnected.tight_connected](../WPFormalization/Tight/ConnectedOriginal.lean#L110)

<details>
<summary>View formal statements</summary>

[WP.TightConnected.tight_connected_original_saddle](../WPFormalization/Tight/ConnectedOriginal.lean#L20):

```lean
theorem tight_connected_original_saddle (P:PsiTheory) (k:ℕ) (B:ℝ) (hB:0≤B)
    (gs ns:ℕ→ℕ) (hg:Tendsto gs atTop atTop) (hn:Tendsto ns atTop atTop)
    (ts:ℕ→Fin (2*k)→ℝ) (ht:∀j i,ts j i∈Icc (0:ℝ) B) :
    Tendsto (fun j=>connectedSaddleCoefficientRatio P k (gs j) (ns j) (ts j)) atTop (𝓝 1)
```

[WP.TightConnected.tight_connected_original_scale](../WPFormalization/Tight/ConnectedOriginal.lean#L72):

```lean
theorem tight_connected_original_scale (gs ns:ℕ→ℕ)
    (hg:Tendsto gs atTop atTop) (hn:Tendsto ns atTop atTop) :
    Tendsto (fun j=>tightParameterScale (inverseY (connectedSaddle (gs j) (ns j)))/
      tightScale ((ns j:ℝ)/(gs j:ℝ))) atTop (𝓝 1)
```

[WP.TightConnected.tight_connected_original_bounded](../WPFormalization/Tight/ConnectedOriginal.lean#L91):

```lean
theorem tight_connected_original_bounded (P:PsiTheory) (k n:ℕ)
    (c:ℝ) (hc:0<c) (B:ℝ) (hB:0≤B) (gs:ℕ→ℕ) (hg:Tendsto gs atTop atTop)
    (ts:ℕ→Fin (2*k)→ℝ) (ht:∀j i,ts j i∈Icc (0:ℝ) B) :
    Tendsto (fun j=>realCoeff (TightMoments.momentTightG P (gs j-k) (2*k)
      (fun i=>ts j i/tightParameterScale (inverseY (c/(complexity (gs j) 0:ℝ))))) n /
        (realCoeff (Phi P (gs j)) n*((4*r (inverseY (c/(complexity (gs j) 0:ℝ))))^k*
          ∏i,boundaryFactor 0 (ts j i)))) atTop (𝓝 1)
```

[WP.TightConnected.tight_connected_original_bounded_scale](../WPFormalization/Tight/ConnectedOriginal.lean#L102):

```lean
theorem tight_connected_original_bounded_scale (gs:ℕ→ℕ) (hg:Tendsto gs atTop atTop)
    (n:ℕ) (c:ℝ) (hc:0<c) :
    Tendsto (fun j=>tightParameterScale (inverseY (c/(complexity (gs j) 0:ℝ)))/
      tightScale ((n:ℝ)/(gs j:ℝ))) atTop (𝓝 1)
```

[WP.TightConnected.tight_connected](../WPFormalization/Tight/ConnectedOriginal.lean#L110):

```lean
theorem tight_connected (P:PsiTheory) (k:ℕ) (B:ℝ) (hB:0≤B) :
    ∀ε:ℝ,0<ε→∃G:ℕ,∀g≥G,∀n:ℕ,∀t:Fin (2*k)→ℝ,
      (∀i,t i∈Icc (0:ℝ) B)→|connectedDensityCoefficientRatio P k g n t-1|≤ε
```

</details>

<a id="target-lem:tight-separating"></a>

### Paper F.3: Separating configurations

**Paper statement** (PDF p. 101):

Fix $k$ and $L$. Uniformly in $n$, with lengths scaled by $\alpha_x$,



$$
\mathbb E^{\mathrm{WP}}_{g,n}
 \bigl[\text{ordered separating tight $k$-tuples with scaled
 lengths at most $L$}\bigr]=o(1),
$$



 where only simple, pairwise disjoint tuples are counted, and separating means that their union disconnects the filled surface.

**Lean declarations** (proved under classical premises):

- [WP.TightSeparating.actual_tight_separating_expectation_uniform](../WPFormalization/Tight/SeparatingActualExpectation.lean#L32)
- [WP.TightSeparating.actual_tight_separating_lintegral_uniform](../WPFormalization/Tight/SeparatingActualExpectation.lean#L67)

<details>
<summary>View formal statements</summary>

[WP.TightSeparating.actual_tight_separating_expectation_uniform](../WPFormalization/Tight/SeparatingActualExpectation.lean#L32):

```lean
theorem actual_tight_separating_expectation_uniform {P : PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} (T : TightRegions G)
    {H : HyperbolicCurveGeometry.{u,v,w} G} {Q : TightGeodesicGeometry G T H}
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (BZ : BuddZonneveldTransform G T) (I : BuddLionsTightIntegration G T H Q A)
    (k : ℕ) (L0 : ℝ) (hL0 : 0 ≤ L0) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g ≥ N, ∀ n : ℕ,
      Integrable (fun X => (actualTightSeparatingCount Q A k (L0/tightScale ((n : ℝ)/(g : ℝ))) X : ℝ))
        (wpProbability G g n) ∧
      (∫ X : G.Moduli g n (fun _ => 0),
        (actualTightSeparatingCount Q A k (L0/tightScale ((n : ℝ)/(g : ℝ))) X : ℝ)
        ∂wpProbability G g n) ≤ ε
```

[WP.TightSeparating.actual_tight_separating_lintegral_uniform](../WPFormalization/Tight/SeparatingActualExpectation.lean#L67):

```lean
theorem actual_tight_separating_lintegral_uniform {P : PsiTheory}
    {G : WeilPeterssonGeometry.{u,v} P} (T : TightRegions G)
    {H : HyperbolicCurveGeometry.{u,v,w} G} {Q : TightGeodesicGeometry G T H}
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (BZ : BuddZonneveldTransform G T) (I : BuddLionsTightIntegration G T H Q A)
    (k : ℕ) (L0 : ℝ) (hL0 : 0 ≤ L0) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g ≥ N, ∀ n : ℕ,
      (∫⁻ X : G.Moduli g n (fun _ => 0),
        (actualTightSeparatingCount Q A k (L0/tightScale ((n : ℝ)/(g : ℝ))) X : ℝ≥0∞)
        ∂wpProbability G g n) ≤ ENNReal.ofReal ε
```

</details>

## Appendix G: The critical length spectrum

<a id="target-lem:critical-cuts"></a>

### Paper G.1: Critical cut estimate

**Paper statement** (PDF p. 104):

Fix $k$ and a bound on the cut lengths. At $n/\sqrt g\to c>0$, the expected number of cut multicurves of the specified graph and vertex partition, summed over all admissible genera and cusp allocations, is $O(g^{1-w-v/2})$. If a specified $(0,1)$ component has at least three cusps, the bound gains a factor $g^{-1/2}$.

**Lean declarations** (proved under classical premises):

- [WP.Critical.critical_cut_estimate](../WPFormalization/Critical/CutActualEstimate.lean#L181)
- [WP.Critical.critical_cut_marked_estimate](../WPFormalization/Critical/CutActualEstimate.lean#L210)
- [WP.Critical.critical_cut_estimate_regime](../WPFormalization/Critical/CutCriticalRegime.lean#L28)
- [WP.Critical.critical_cut_marked_estimate_regime](../WPFormalization/Critical/CutCriticalRegime.lean#L45)
- [WP.Critical.critical_unordered_cut_estimate](../WPFormalization/Critical/CutUnorderedEstimate.lean#L12)
- [WP.Critical.critical_unordered_cut_marked_estimate](../WPFormalization/Critical/CutUnorderedEstimate.lean#L29)
- [WP.Critical.critical_unordered_cut_estimate_regime](../WPFormalization/Critical/CutUnorderedEstimate.lean#L46)
- [WP.Critical.critical_unordered_cut_marked_estimate_regime](../WPFormalization/Critical/CutUnorderedEstimate.lean#L63)
- [WP.Critical.critical_cut_expectation_regime](../WPFormalization/Critical/CutExpectationRegime.lean#L12)
- [WP.Critical.critical_cut_marked_expectation_regime](../WPFormalization/Critical/CutExpectationRegime.lean#L29)

<details>
<summary>View formal statements</summary>

[WP.Critical.critical_cut_estimate](../WPFormalization/Critical/CutActualEstimate.lean#L181):

```lean
theorem critical_cut_estimate {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (A L : ℝ) (hA : 0 < A) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∃ G₀ : ℕ, ∀ g ≥ G₀, ∀ n : ℕ,
      1 ≤ n → (n : ℝ) ≤ A*Real.sqrt g → ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, cutPartitionCount T S (g:=g) (n:=n) u v w L X ∂wpProbability G g n) ≤
        ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-(v:ℝ)/2))
```

[WP.Critical.critical_cut_marked_estimate](../WPFormalization/Critical/CutActualEstimate.lean#L210):

```lean
theorem critical_cut_marked_estimate {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (A L : ℝ) (hA : 0 < A) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∃ G₀ : ℕ, ∀ g ≥ G₀, ∀ n : ℕ,
      1 ≤ n → (n : ℝ) ≤ A*Real.sqrt g → ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, cutMarkedPartitionCount T S (g:=g) (n:=n) u v w L X ∂wpProbability G g n) ≤
        ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-((v:ℝ)+1)/2))
```

[WP.Critical.critical_cut_estimate_regime](../WPFormalization/Critical/CutCriticalRegime.lean#L28):

```lean
theorem critical_cut_estimate_regime {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (L : ℝ) (hL : 0 ≤ L)
    (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (nhds c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g : ℕ in atTop, ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, cutPartitionCount T S (g:=g) (n:=n g) u v w L X ∂wpProbability G g (n g)) ≤
        ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-(v:ℝ)/2))
```

[WP.Critical.critical_cut_marked_estimate_regime](../WPFormalization/Critical/CutCriticalRegime.lean#L45):

```lean
theorem critical_cut_marked_estimate_regime {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (L : ℝ) (hL : 0 ≤ L)
    (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (nhds c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g : ℕ in atTop, ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, cutMarkedPartitionCount T S (g:=g) (n:=n g) u v w L X ∂wpProbability G g (n g)) ≤
        ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-((v:ℝ)+1)/2))
```

[WP.Critical.critical_unordered_cut_estimate](../WPFormalization/Critical/CutUnorderedEstimate.lean#L12):

```lean
theorem critical_unordered_cut_estimate {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (A L : ℝ) (hA : 0 < A) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∃ G₀ : ℕ, ∀ g ≥ G₀, ∀ n : ℕ,
      1 ≤ n → (n : ℝ) ≤ A*Real.sqrt g → ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, unorderedCutCount T (partitionOrbits T S (g:=g) (n:=n) u v w) L X
        ∂wpProbability G g n) ≤ ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-(v:ℝ)/2))
```

[WP.Critical.critical_unordered_cut_marked_estimate](../WPFormalization/Critical/CutUnorderedEstimate.lean#L29):

```lean
theorem critical_unordered_cut_marked_estimate {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (A L : ℝ) (hA : 0 < A) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∃ G₀ : ℕ, ∀ g ≥ G₀, ∀ n : ℕ,
      1 ≤ n → (n : ℝ) ≤ A*Real.sqrt g → ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, unorderedCutCount T (markedPartitionOrbits T S (g:=g) (n:=n) u v w) L X
        ∂wpProbability G g n) ≤ ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-((v:ℝ)+1)/2))
```

[WP.Critical.critical_unordered_cut_estimate_regime](../WPFormalization/Critical/CutUnorderedEstimate.lean#L46):

```lean
theorem critical_unordered_cut_estimate_regime {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (L : ℝ) (hL : 0 ≤ L)
    (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (nhds c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g : ℕ in atTop, ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, unorderedCutCount T (partitionOrbits T S (g:=g) (n:=n g) u v w) L X
        ∂wpProbability G g (n g)) ≤ ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-(v:ℝ)/2))
```

[WP.Critical.critical_unordered_cut_marked_estimate_regime](../WPFormalization/Critical/CutUnorderedEstimate.lean#L63):

```lean
theorem critical_unordered_cut_marked_estimate_regime {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (L : ℝ) (hL : 0 ≤ L)
    (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (nhds c)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g : ℕ in atTop, ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, unorderedCutCount T (markedPartitionOrbits T S (g:=g) (n:=n g) u v w) L X
        ∂wpProbability G g (n g)) ≤ ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-((v:ℝ)+1)/2))
```

[WP.Critical.critical_cut_expectation_regime](../WPFormalization/Critical/CutExpectationRegime.lean#L12):

```lean
theorem critical_cut_expectation_regime {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (MC : MulticurveCountingMeasurability G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (L : ℝ) (hL : 0 ≤ L)
    (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (nhds c)) :
    (∀ (g : ℕ) (S : CutSkeleton k Q), Measurable
      (unorderedCutCount T (partitionOrbits T S (g:=g) (n:=n g) u v w) L)) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g : ℕ in atTop, ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, unorderedCutCount T (partitionOrbits T S (g:=g) (n:=n g) u v w) L X
        ∂wpProbability G g (n g)) ≤ ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-(v:ℝ)/2))
```

[WP.Critical.critical_cut_marked_expectation_regime](../WPFormalization/Critical/CutExpectationRegime.lean#L29):

```lean
theorem critical_cut_marked_expectation_regime {P : PsiTheory}
    (G : WeilPeterssonGeometry.{aa,bb} P) {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) (MI : MirzakhaniIntegration G H T)
    (MC : MulticurveCountingMeasurability G H T)
    (k Q u v w : ℕ) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (L : ℝ) (hL : 0 ≤ L)
    (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ)/Real.sqrt g) atTop (nhds c)) :
    (∀ (g : ℕ) (S : CutSkeleton k Q), Measurable
      (unorderedCutCount T (markedPartitionOrbits T S (g:=g) (n:=n g) u v w) L)) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ g : ℕ in atTop, ∀ S : CutSkeleton k Q, S.Connected →
      (∫⁻ X, unorderedCutCount T (markedPartitionOrbits T S (g:=g) (n:=n g) u v w) L X
        ∂wpProbability G g (n g)) ≤ ENNReal.ofReal (C*(g:ℝ)^(1-(w:ℝ)-((v:ℝ)+1)/2))
```

</details>

<a id="target-lem:primitive-count"></a>

### Paper G.2: Bounded primitive count

**Paper statement** (PDF p. 105):

For fixed $K,L$, a finite-area hyperbolic surface $S$ with geodesic boundary and $0<-\chi(S)\le K$ has at most $C(K,L)$ primitive unoriented geodesics of length at most $L$, uniformly in its metric.

**Lean declarations** (proved under classical premises):

- [WP.Critical.PrimitivePacking.bounded_primitive_count](../WPFormalization/Critical/PrimitiveCount.lean#L63)

<details>
<summary>View formal statements</summary>

[WP.Critical.PrimitivePacking.bounded_primitive_count](../WPFormalization/Critical/PrimitiveCount.lean#L63):

```lean
theorem bounded_primitive_count (K L : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ B : BorderedGeometry, ∀ D : DoublingClassics B,
      0<(B.negativeEuler:ℝ) → (B.negativeEuler:ℝ)≤K →
      ((B.curves.short L).card:ℝ)≤C
```

</details>

<a id="target-lem:critical-complex"></a>

### Paper G.3: Complex short configurations

**Paper statement** (PDF p. 105):

Fix $r$ and $L$. As $g\to\infty$ with $n/\sqrt g\to c\in(0,\infty)$,



$$
\mathbb E[\text{intersecting ordered simple $r$-tuples of lengths
 at most $L$}]=O_{r,L,c}(g^{-1/2}),
$$







$$
\mathbb E[\text{nonsimple primitive curves of length at most $L$
 not filling two-cusp pants}]=O_{L,c}(g^{-1/2}),
$$



 and the expected number of simple separating curves of length at most $L$ that are not waists of two-cusp pairs of pants tends to zero.

**Lean declarations** (proved under classical premises):

- [WP.Critical.complex_short_configurations](../WPFormalization/Critical/ComplexShortConfigurations.lean#L29)

<details>
<summary>View formal statements</summary>

[WP.Critical.complex_short_configurations](../WPFormalization/Critical/ComplexShortConfigurations.lean#L29):

```lean
theorem complex_short_configurations
    (Cuts:ActualCutRealizationData A T AC.complete_domain)
    (SC:∀g n (X:G.Moduli g n (fun _=>0)),SegmentClassics (A.model g n X))
    (SP:∀g n (X:G.Moduli g n (fun _=>0)),
      SupportingPieceClassics (A.model g n X) (AC.complete_domain g n X))
    (FG:FiniteGraphFundamentalGroupClassics.{u})
    (C:WP.External.FiniteCyclicIntervalGeometry.Classics)
    (LS:∀g n (X:G.Moduli g n (fun _=>0)),
      LoopStraighteningClassics (A.model g n X) (AC.complete_domain g n X))
    (M:∀g n r (X:G.Moduli g n (fun _=>0)) L (hL:0<L)
      (γ:ShortIntersectingSimpleTuple T X r L),
      TupleRecordingCompanions A AC X γ.val γ.property.1 γ.property.2.1
        (SC g n X) L hL γ.property.2.2.1 (SP g n X) C)
    (J:PlanarJordanClassics) (PC:PlanarRegionClassics)
    (BC:∀g n {k}(o:T.Orbit g n k)(X:G.Moduli g n (fun _=>0))
      (κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      PrimitiveBoundaryClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (BLS:∀g n {k}(o:T.Orbit g n k)(X:G.Moduli g n (fun _=>0))
      (κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      BorderedLoopStraighteningClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (PP:∀g n {k}(o:T.Orbit g n k)(X:G.Moduli g n (fun _=>0))
      (κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      BorderedPeripheralClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (S : SingleCurvePieceClassics A)
    (SCut : SingleCurveCutCompanionData Cuts S)
    (HF : FullSingleCurveFillingClassics A AC.complete_domain S)
    (MI : MirzakhaniIntegration G H T) (c : ℝ) (hc : 0 < c) :
    FullComplexShortConfigurationsConclusion A T c ∧
      ComplexShortConfigurationsConclusion A T S c
```

</details>

<a id="target-lem:critical-skeleton"></a>

### Paper G.4: Joint Poisson limit

**Paper statement** (PDF p. 106):

As $g\to\infty$ with $n/\sqrt g\to c\in(0,\infty)$,



$$
(\mathcal N_g,\mathcal Q_g)\Longrightarrow
 (\mathcal N,\mathcal Q_c)
$$



 jointly in the vague topology on $[0,\infty)$, where $\mathcal N$ and $\mathcal Q_c$ are independent Poisson point processes of intensities $\nu$ and $\mu_c$.

<a id="statement-mapping"></a>

**Lean declarations** (proved under classical premises):

- [WP.Critical.joint_nonseparating_pants_poisson_limit](../WPFormalization/Critical/JointPoissonLimitProducer.lean#L27)

<details>
<summary>View formal statements</summary>

[WP.Critical.joint_nonseparating_pants_poisson_limit](../WPFormalization/Critical/JointPoissonLimitProducer.lean#L27):

```lean
theorem joint_nonseparating_pants_poisson_limit
    (Cuts:ActualCutRealizationData A T AC.complete_domain)
    (SC:∀g n (X:G.Moduli g n (fun _=>0)),SegmentClassics (A.model g n X))
    (SP:∀g n (X:G.Moduli g n (fun _=>0)),
      SupportingPieceClassics (A.model g n X) (AC.complete_domain g n X))
    (FG:FiniteGraphFundamentalGroupClassics.{u})
    (C:WP.External.FiniteCyclicIntervalGeometry.Classics)
    (LS:∀g n (X:G.Moduli g n (fun _=>0)),
      LoopStraighteningClassics (A.model g n X) (AC.complete_domain g n X))
    (M:∀g n r (X:G.Moduli g n (fun _=>0)) L (hL:0<L)
      (γ:ShortIntersectingSimpleTuple T X r L),
      TupleRecordingCompanions A AC X γ.val γ.property.1 γ.property.2.1
        (SC g n X) L hL γ.property.2.2.1 (SP g n X) C)
    (J:PlanarJordanClassics) (PC:PlanarRegionClassics)
    (BC:∀g n {k}(o:T.Orbit g n k)(X:G.Moduli g n (fun _=>0))
      (κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      PrimitiveBoundaryClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (BLS:∀g n {k}(o:T.Orbit g n k)(X:G.Moduli g n (fun _=>0))
      (κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      BorderedLoopStraighteningClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (PP:∀g n {k}(o:T.Orbit g n k)(X:G.Moduli g n (fun _=>0))
      (κ:Fin k→H.Primitive g n X)(hκ:T.orbitMem o X κ)c,
      BorderedPeripheralClassics ((Cuts.cut o X κ hκ).piece c).model ((Cuts.cut o X κ hκ).piece c).boundary)
    (S : SingleCurvePieceClassics A)
    (SCut : SingleCurveCutCompanionData Cuts S)
    (HF : FullSingleCurveFillingClassics A AC.complete_domain S)
    (MI : MirzakhaniIntegration G H T) (RG : MulticurveRestrictionGeometry G H T)
    (I : WP.External.TwoColorPoissonRestrictionIndependence)
    (c : ℝ) (hc : 0 < c) (n : ℕ → ℕ)
    (hn : Tendsto (fun g : ℕ => (n g : ℝ) / Real.sqrt g) atTop (𝓝 c)) :
    CriticalJointPoissonLimit T n c
```

</details>
