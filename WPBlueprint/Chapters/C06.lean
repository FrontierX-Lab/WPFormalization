import WPFormalization.Statements
import WPBlueprint.Chapters.C05
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "07-leading-term" =>

# The leading term and its normalization

The marked ratios determine a differential equation for the leading term, but leave a multiplicative constant. The equation comes from the dilaton identity {bpref "eq:TL12"}[6.4], which expresses the $`Y`-derivative of $`\log\Phi_g^{(p)}` through the degree profiles $`c_{g,p+1}(d,0^p)`; to obtain it with error $`O(h^{-2})` we need the $`1/h` term of these profiles. We first compute this degree correction, then integrate it and determine the constant from pure $`\psi` intersections. The resulting estimate is Proposition {bpref "prop:prefactor"}[7.1]; its fixed-cusp specialization proves Corollary {bpref "cor:constant"}[1.2]. Matching at a point that approaches the critical endpoint polynomially in the genus keeps the integrated error uniform on the whole interval.

Write $`\bar K=\bar K_Y` and $`\bar H=\bar H_Y`, and introduce the kernel moments

:::definition "eq:PF1" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:P11, eq:SP2")
%%%
source := { document := "paper-v3", spans := #[{ page := "35", anchor := "eq:PF1", citation := "Equation 7.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 7.1 — Kernel moments and action.

In the setup and notation of this section, the paper defines or asserts:



$$`\Theta=\sum_{\ell\ge0}w_\ell=-\frac1{\bar K'(1)},\qquad
 M_1=\sum_{\ell\ge0}\ell w_\ell=\frac{\bar K''(1)}{2\bar K'(1)^2},\qquad
 \mathcal Z=Aar^{3/2}=\sqrt2 I.`


:::



Primes on $`\bar K,\bar H` mean differentiation in their argument; derivatives of parameter functions below are with respect to $`Y`. All the moments in {bpref "eq:PF1"}[7.1] are uniformly bounded on the closed normalized interval. The variance $`v_Y=\sigma_Y^2` of the law in {bpref "eq:P12"}[2.8], written $`\sigma_Y^2` in Section 2, satisfies 

$$`v_Y=\frac{15}{4}-\frac{\bar H''(1)}{\bar H(1)}=\frac1{2A\Theta}.`

 Indeed $`\bar H'(1)=-3\bar H(1)/2` and $`\bar K'(1)=-5\bar H(1)/2+2\bar H''(1)/3`.

For fixed $`p\ge1`, put $`h=2g-2+p` and define

:::definition "eq:PF3" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:PF1")
%%%
source := { document := "paper-v3", spans := #[{ page := "35", anchor := "eq:PF3", citation := "Equation 7.3", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 7.3 — Marked leading model.

In the setup and notation of this section, the paper defines or asserts:



$$`\mathcal J_{g,p}(Y)=
 \frac{\Gamma(h)4^{-g}}{\sqrt{\pi h}}
 \mathcal Z(Y)^{-h}r(Y)^{p/2}\sqrt{A(Y)\Theta(Y)}.`


:::



:::proposition "prop:prefactor" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:PF3")
%%%
source := { document := "paper-v3", spans := #[{ page := "35", anchor := "prop:prefactor", citation := "Proposition 7.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 7.1 — Absolute marked prefactor.

For each fixed $`p\ge1`, uniformly for $`0\le Y<y_0`, 

$$`\Phi_g^{(p)}(X(Y))=
 \frac{\mathcal J_{g,p}(Y)}{\pi}
 \left(1+O_p\!\left(\frac{\log(g+1)}g\right)\right).`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



## The first degree correction

We compute the first degree correction directly from the positive recursion. The remainder must be uniform in $`Y` and in a growing degree range, since an expansion at each fixed degree would not suffice in the dilaton sum. Set $`D=|\mathbf d|` and $`q=\#\{i:d_i>0\}`.

:::lemma_ "lem:first-degree" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:TL9, eq:PF1")
%%%
source := { document := "paper-v3", spans := #[{ page := "35", anchor := "lem:first-degree", citation := "Lemma 7.2", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma 7.2 — First degree correction.

For each fixed $`p\ge1`, uniformly for $`Y\in[0,y_0]` and for degree tuples with $`D\le h^{1/4}`, 

$$`\begin{aligned}
 c_{g,p}(\mathbf d)&=1-\frac{\delta_p(\mathbf d)}h
       +O_p\!\left(\frac{(D+1)^4}{h^2}\right),\\
 \delta_p(\mathbf d)&=A\left\{
 \Theta\bigl(D^2+(p-4)D\bigr)+2M_1D+
 \frac{q(q+5-2p)}2\right\}.
 \end{aligned}`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



:::proof "lem:first-degree" (uses := "eq:TL23, eq:TL24, eq:TL27, eq:H9")
Subtract the exact recursion {bpref "eq:H9"}[4.8] at pivot degree $`t=d_i` and $`t+1`, shifting the second kernel index. The difference has coefficients $`w_\ell`. By {bpref "eq:TL24"}[6.16] and {bpref "eq:TL27"}[6.19], its merging prefactor is $`A/h+O_p(h^{-2})`, and its nonseparating prefactor, including the factor $`1/2` and the genus normalization, is $`2A/h+O_p(h^{-2})`. For $`p=1` there is no merging term. All child degrees can be replaced by zero with error at most $`C_p(D+\ell+1)^2/h`, by {bpref "eq:TL23"}[6.15]. The coefficients and pair counts are $`O_p(D+\ell+1)`, so the moments of $`w_\ell` make the resulting error $`O_p((D+1)^3/h^2)`. The separating difference is $`O_p((D+1)/h^2)` by {bpref "eq:TL19"}[6.11]; at $`p=1` use 6.18. These bounds also cover dimension-invalid children through the zero convention in {bpref "eq:TL23"}[6.15].

Let $`z` count zeros among the other $`p-1` entries. A merger is admissible when $`t+d_j+\ell\ge1`; the nonseparating pair count is $`(t+\ell-1)_+`. Thus the leading adjacent difference is 

$$`\frac Ah\left\{\Theta(2D+p-3)+2M_1+(2-z)\mathbf1_{t=0}\right\}.`

 Here the zero-pivot term records both the missing zero-zero merger and the truncated pair count. Since the parent deficit is of order $`h` in the indicated degree range, extending the kernel sum to infinity costs $`O_p(h^{-2})`, using sufficiently high moments of $`w_\ell`. Summing increments from zero to $`\mathbf d` proves 7.5: the exceptional increments at the creation of successive positive entries are $`3-p,4-p,\ldots,q+2-p`. The sum of the remainders is bounded by $`C_p(D+1)^4/h^2`.
:::



For $`d>h^{1/4}` in the dilaton identity, use $`0\le c\le1`, the quadratic growth of $`\delta_p`, and sufficiently high uniform absolute moments of $`b_d`; moments of order twelve already bound the tail of $`1+d^2/h` by $`O_p(h^{-2})`. This justifies summing the expansion, although it gives no useful pointwise remainder at large degree.

## The differential equation for the leading term

The three signed dilaton moments are exact: 

$$`\sum b_d=A,\qquad \sum d b_d=-A/2,\qquad
 \sum d^2 b_d=\bar H''(1)/3-7A/2.`

 Apply 7.5 to $`(d,0^p)` in {bpref "eq:TL12"}[6.4]. Changing the child complexity $`h+1` to $`h` costs $`O_p(h^{-2})`. We obtain 

$$`h\frac{W_{g,p}}{W_{g,p+1}}
 =A\left(1-\frac{\beta_p}h+O_p(h^{-2})\right),\qquad
 \beta_p=A\left\{\frac{7-2p}{4}\Theta-M_1+2-p\right\}-\frac12.`

 This holds for each fixed $`p\ge0`: at $`p=0` its only profile input has one marking. Inverting and undoing the normalization gives

:::proposition "eq:PF8" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:PF3")
%%%
source := { document := "paper-v3", spans := #[{ page := "36", anchor := "eq:PF8", citation := "Equation 7.8", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 7.8 — Transport differential equation.

In the setup and notation of this section, the paper defines or asserts:



$$`\frac{\mathrm{d}}{\mathrm{d}Y}\log\Phi_g^{(p)}(X(Y))
 =\frac{h+\beta_p+O_p(h^{-1})}{A r}.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



The correction in {bpref "eq:PF8"}[7.8] has an explicit primitive. Differentiate $`K_Y(r)=0`, using $`\partial_YK=2\partial_zK+(K-a)/z`, to get 

$$`r'=-(\Theta+2),\qquad
 (\log\mathcal Z)'=-\frac1{Ar}.`

 The second identity also follows from $`I'=-a\sqrt\Delta`. Differentiating the root derivative and the corresponding equation for $`H` gives 

$$`\begin{aligned}
 (\log\Theta)'&=\frac{a'}a+
                  \frac{2\Theta+1-2M_1}{r},\\
 (\log A)'&=\frac{3\Theta/2+3-1/A}{r}-\frac{a'}a.
 \end{aligned}`

 For the first formula use $`\Theta=-a/(r\,\partial_zK_Y(r))` and $`\partial_Y\partial_zK_Y=2\partial_z^2K_Y+\partial_zK_Y/r+a/r^2` at the root $`z=r`. Equations 7.7 and 7.10 yield 

$$`\frac{\beta_p}{Ar}
 =\frac12(\log(A\Theta))'+\frac p2(\log r)',\qquad
 \left|\frac{\mathrm{d}}{\mathrm{d}Y}\log
 \frac{\Phi_g^{(p)}(X(Y))}{\mathcal J_{g,p}(Y)}\right|
 \le\frac{C_p}{h A r}.`

 Only exact identities have been differentiated here; the error term in {bpref "eq:PF8"}[7.8] will be integrated, never differentiated.

## Fixing the constant at the critical endpoint

Here we need the value at one pure-$`\psi` tuple, not only two-sided bounds. In the normalization {bpref "eq:H4"}[4.3], 

$$`C_g(2^{3g-3})=\frac1\pi+O(g^{-1}).`

 Indeed, the identity of Itzykson and Zuber \[43\] equation (6.10) expresses $`C_g(2^{3g-3})` through the coefficients of the formal power-series solution of Painlevé I. Their large-order asymptotics follow from the Stokes data of Joshi–Kitaev and Kapaev \[46\]; \[47\]; see \[27\] Section 2.3. Subsection C.9 proves a quantitative version, C.36, without using the present section. Estimate 7.12 is also the case $`\mathbf e=(2^{3g-3})` of the uniform theorem of Guo, Yang and Zagier \[32\] Theorem 1; no other case of that theorem is used. For $`m=3g-3+p`, string followed by dilaton gives the exact reduction

:::proposition "eq:PF12" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H7")
%%%
source := { document := "paper-v3", spans := #[{ page := "37", anchor := "eq:PF12", citation := "Equation 7.13", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 7.13 — Endpoint string reduction and pure psi asymptotic.

In the setup and notation of this section, the paper defines or asserts:



$$`C_g(0^p,2^m)=
 \prod_{i=0}^{p-1}
 \frac{5(m-i)}{3(2g-3+p+m-2i)}\ C_g(2^{3g-3})
 =\frac1\pi+O_p(g^{-1}).`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



Each string step chooses a degree-two marking with normalized coefficient $`5/[3(2g-3+p+m)]`; the resulting degree-one marking is removed by normalized dilaton with coefficient one. Since $`p` is fixed, the displayed finite product is $`1+O_p(g^{-1})`, and 7.12 gives the final equality.

At the endpoint, 5.2 gives exactly

:::proposition "eq:PF13" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H4, eq:H7, eq:H12")
%%%
source := { document := "paper-v3", spans := #[{ page := "37", anchor := "eq:PF13", citation := "Equation 7.14", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 7.14 — Endpoint harmonic ratio equals pure psi normalization.

In the setup and notation of this section, the paper defines or asserts:



$$`\frac{\overline U_{g,p}(0^p;y_0)}
      {\mathcal M_{g,p}(0^p;y_0)}=C_g(0^p,2^m).`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



Indeed the numerator is $`3^m\langle\tau_0^p\tau_2^m\rangle_g/m!` and the denominator is $`3^{h+m}\Gamma(h+m)/(4^g5^m m!)`.

We now show that the endpoint value persists on a short interval $`0\le y_0-Y\le h^{-2}`. The reason is that the amplitudes are polynomials with nonnegative coefficients in the kernel coefficients, and these are within a factor $`1+O(y_0-Y)` of their endpoint value one. Here $`\theta_\ell=[z^\ell]\bar K_Y(z)^{-1}` are the rescaled kernel coefficients. Put $`\delta=y_0-Y`. The normalized kernels are analytic in $`\delta` near zero on a common disk of radius greater than one. To see the removable parameter singularity, apply the implicit-function theorem to $`K_{y_0-\delta}(\delta\rho)/\delta` at $`(\delta,\rho)=(0,3)`; its $`\rho` derivative is nonzero. Division by the persistent root $`1-z` then gives $`\bar K_Y(z)/(1-z)=1+O(\delta)` on a smaller common disk. Together with coefficient positivity this proves 

$$`1\le\theta_\ell(Y)\le1+C\delta\quad\hbox{for all }\ell\ge0.`

 By the positive recursion, $`\overline U` is a polynomial with nonnegative coefficients in the variables $`\theta_\ell`, homogeneous of degree $`h`. At complexity one the bases have degree one, with $`\theta_0=1`; each recursion adds one factor, while child complexities sum to $`h-1`. Thus 

$$`1\le\frac{\overline U_{g,p}(0^p;Y)}
                {\overline U_{g,p}(0^p;y_0)}
 \le(1+C\delta)^h.`



Next we compare $`\mathcal J_{g,p}` with the harmonic model at all degrees zero, for every $`Y`. Here $`m=3g-3+p=3h/2-p/2`. Since $`\mathcal Z=Aar^{3/2}`, the powers of $`r` in $`a^hr^m\mathcal J_{g,p}` cancel exactly. On the other hand, {bpref "eq:H12"}[4.11] and 4.20 give $`\mathcal M_{g,p}(0^p;Y)=3^h\Gamma(h)4^{-g}(3A)^{-h}\Pr(S_h=m)`, and the central estimate 4.17 at displacement $`-p/2`, with variance $`v_Y=1/(2A\Theta)` from 7.2, gives $`\Pr(S_h=m)=\sqrt{A\Theta/(\pi h)}\,(1+O_p(h^{-1}))`. Hence 

$$`a^h r^m\mathcal J_{g,p}(Y)
 =\Gamma(h)4^{-g}A^{-h}\sqrt{\frac{A\Theta}{\pi h}}
 =\mathcal M_{g,p}(0^p;Y)(1+O_p(h^{-1})),`

 where the first equality is exact. Its ratio to its endpoint value is $`1+O_p(h\delta)` when $`0\le\delta\le h^{-2}`, by analyticity and uniform positivity of $`A,\Theta`. Hence {bpref "eq:PF12"}[7.13]–7.17 prove $`\Phi_g^{(p)}(X(Y))/\mathcal J_{g,p}(Y)=1/\pi+O_p(h^{-1})` throughout that interval.

:::proof "prop:prefactor" (uses := "lem:first-degree, eq:PF8, eq:PF12, eq:PF13, ext:painleve-leading")
Take $`Y_*=y_0-h^{-2}`. For $`Y\le Y_*` integrate 7.11: by 7.9, its error is at most 

$$`\frac{C_p}{h}\log\frac{\mathcal Z(Y)}{\mathcal Z(Y_*)}
 \le C_p\frac{\log h}{h},`

 since $`\mathcal Z(0)>0` and $`\mathcal Z(Y_*)\asymp h^{-5}`. The value at $`Y_*` was fixed above. Exponentiation gives 7.4 for $`Y\le Y_*`; the direct endpoint comparison gives the stronger $`O_p(h^{-1})` error for $`Y\ge Y_*`.
:::



At $`Y=0`, $`r=\pi^2/2`, $`A=1/\pi^2`, $`\Theta=2`, and $`\mathcal Z=\pi/(2\sqrt2)`. Taking $`p=1` in 7.4 gives 

$$`V_{g,1}=\frac{\Gamma(2g-1)(4\pi^2)^{2g-2}}{\sqrt{\pi g}}
 \left(1+O\!\left(\frac{\log(g+1)}g\right)\right).`



:::proof "cor:constant" (uses := "prop:prefactor, ext:fixed-cusps")
Comparing 7.18 with the expansion of Mirzakhani–Zograf \[66\] Theorem 1.2 and Remark 1.3 at $`n=1` identifies their universal constant as $`1/\sqrt\pi`. Since the constant does not depend on $`n`, their expansion then gives the asserted formula, with relative error $`O_n(g^{-1})`, for every fixed $`n\ge0`.
:::



:::lemma_ "eq:boundary-factor" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:TL9, eq:TL23, cor:constant")
%%%
source := { document := "paper-v3", spans := #[{ page := "38", anchor := "eq:boundary-factor", citation := "Equation 7.19 and growing-boundary Kimura consequence", pdf := some { path := "source/paper.pdf" } }] }
%%%

R35 implementation: the linked theorem proves the quantitative estimate for all nonnegative lengths and the growing-length Kimura consequence. It uses the actual WP-volume dictionary and the previously registered classical Gamma input.

For completeness, we derive the boundary-length consequence stated in the introduction. Fix $`n\ge1`, put $`x_i=L_i/2`, and set $`S(x)=\sinh(x)/x`, with $`S(0)=1`. At $`Y=0`, the normalization {bpref "eq:TL9"}[6.1] gives $`c_{g,n}(\mathbf d)=[\tau_{d_1}\cdots\tau_{d_n}]_{g,n}/V_{g,n}`. Thus the volume polynomial, extended by zero outside its degree range, is 

$$`\frac{V_{g,n}(\mathbf L)}{V_{g,n}}
 =\sum_{\mathbf d\ge0}c_{g,n}(\mathbf d)
   \prod_{i=1}^n\frac{x_i^{2d_i}}{(2d_i+1)!}.`

 Divide by $`\prod_i S(x_i)` and regard the product weights as the law of independent nonnegative integers $`d_i`. The identity $`\sum_{d\ge0}(2d)(2d+1)x^{2d}/(2d+1)!=x^2S(x)` gives $`\mathbb E[d_i(d_i+1)]\le x_i^2/2`. Since $`D(D+1)\le n\sum_i d_i(d_i+1)`, where $`D=\sum_i d_i`, {bpref "eq:TL23"}[6.15], including its one-marking case, yields 

$$`0\le 1-\frac{V_{g,n}(\mathbf L)}{V_{g,n}\prod_i S(L_i/2)}
 \le \frac{C_n}{g}\sum_{i=1}^n L_i^2.`

 For $`L_i=o(\sqrt g)` the right side tends to zero. Corollary {bpref "cor:constant"}[1.2] and Stirling’s formula then give the asserted asymptotic formula.


:::
