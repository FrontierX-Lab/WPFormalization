import WPFormalization.Statements
import WPBlueprint.Chapters.C04
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "06-marked-ratios" =>

# Ratios of marked generating functions

The comparison theorem controls logarithms, whereas the volume-ratio problem requires relative errors tending to zero. We obtain that stronger control here for generating functions with a fixed number of distinguished markings. The two ratios correspond to adding a cusp and to replacing one unit of genus by two cusps. Their errors are $`O(1/g)`, uniformly in the parameter. The passage to volumes with a prescribed cusp count will be made in Section 9.

The mechanism is simple. Positivity of the recursion implies that an amplitude decreases when one of its degrees is raised 6.7. The dilaton equation {bpref "eq:TL12"}[6.4] writes the cusp ratio as a weighted sum, over degrees $`d\ge1`, of the normalized amplitudes $`c_{g,p+1}(d,0^p)`. These weights can have either sign; their absolute moments are uniformly bounded by 6.5. The KdV equation {bpref "eq:TL14"}[6.6] writes the genus ratio through $`c_{g,p}(1,0^{p-1})` and separating terms. Both ratios are therefore within $`O(1/g)` of explicit functions of $`Y` once we know that $`c_{g,p}(\mathbf d)=1-O(|\mathbf d|^2/g)`. This last estimate, {bpref "eq:TL23"}[6.15], follows from the difference of the recursion at adjacent degrees; the coarse bounds of Section 5 are used only to show that the separating terms are small.

## Shifted amplitudes and normalization

Use $`p` for the number of distinguished markings, and keep $`n` for the number of cusps. Retain the kernels and shifted amplitudes of Sections 2 and 4; write $`U_{g,p}(\mathbf d;Y)=U^Y_{g,p}(\mathbf d)`, and suppress $`Y` when convenient. Put $`h=2g-2+p` and $`m=3g-3+p-|\mathbf d|`. Define

:::definition "eq:TL9" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:H7")
%%%
source := { document := "paper-v3", spans := #[{ page := "31", anchor := "eq:TL9", citation := "Equation 6.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 6.1 — Marked profiles.

In the setup and notation of this section, the paper defines or asserts:



$$`\overline U_{g,p}(\mathbf d)=a^h r^m U_{g,p}(\mathbf d),
 \qquad W_{g,p}=4^g\overline U_{g,p}(\mathbf0),
 \qquad c_{g,p}(\mathbf d)=
 \frac{\overline U_{g,p}(\mathbf d)}{\overline U_{g,p}(\mathbf0)}.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



Thus $`\overline U_{g,p}(\mathbf d)` is the normalized amplitude $`\mathcal U_{g,p}(\mathbf d;Y)` of {bpref "eq:H7"}[4.6]; the bar indicates that the markings are now the distinguished ones. The barred amplitudes obey the exact positive recursion {bpref "eq:H9"}[4.8].

We use two consequences of Sections 2–5.

1. The kernel bounds {bpref "eq:P11"}[2.7]: for each fixed $`k`, 
   $$`1=\theta_0\le\theta_1\le\cdots,
   \qquad w_\ell:=\theta_\ell-\theta_{\ell-1}\ge0,
   \quad\theta_{-1}=0,
   \quad\sup_Y\sum_{\ell\ge0}(1+\ell)^k w_\ell<\infty`
    Also $`A(Y)` is bounded above and away from zero; see Subsection 2.2.

2. Uniform harmonic comparison: for each fixed positive $`p`, 
   $$`\log W_{g,p}=
   \log\Gamma(2g-2+p)-(2g-2+p)\log A(Y)+o(g),`
    uniformly for $`0\le Y<y_0`. The corresponding crude bound $`W_{g,p}\le C_p^{g+1}(2g+p)!` holds uniformly, including bounded stable genera. Proposition {bpref "prop:harmonic"}[5.1], together with the central local limit 4.16 for the model, proves 6.3 without any input on volume ratios. Only its $`o(g)` error is needed below, and only for a positive number of markings.

## Dilaton and KdV identities

The shifted weighted dilaton identity is

:::proposition "eq:TL12" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:TL9")
%%%
source := { document := "paper-v3", spans := #[{ page := "31", anchor := "eq:TL12", citation := "Equation 6.4", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 6.4 — Shifted dilaton identity.

In the setup and notation of this section, the paper defines or asserts:



$$`h\overline U_{g,p}(\mathbf0)=
 \sum_{d\ge1}b_d(Y)\overline U_{g,p+1}(d,0^p),
 \qquad
 b_d(Y)=\frac{X^{(d)}(Y)r^{d-1}}{a(2d+1)!!}
 =\frac13[z^{d-1}]\bar H_Y(z).`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



It holds also at $`p=0`, $`g\ge2`. To track the shift, the background insertion of degree one contributes $`1-a`; moving it and the higher background insertions to the left leaves the coefficients $`X^{(d)}/(2d+1)!!`. The factor in {bpref "eq:TL9"}[6.1] then produces exactly $`r^{d-1}/a` in {bpref "eq:TL12"}[6.4]. The compact analytic family gives 

$$`\sum_{d\ge1}b_d=A(Y),\qquad
 \sup_Y\sum_{d\ge1}(1+d)^k|b_d(Y)|<\infty`

 for every fixed $`k`.

The genus ratio is governed instead by the KdV equation. Write $`F` for the Kontsevich–Witten free energy, with subscripts indicating differentiation with respect to the corresponding times. The integrated KdV identity $`F_{01}=F_{00}^2/2+F_{0000}/12`, differentiated $`p-2` times in the string variable, gives for $`p\ge2`

:::proposition "eq:TL14" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:TL9")
%%%
source := { document := "paper-v3", spans := #[{ page := "31", anchor := "eq:TL14", citation := "Equation 6.6", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 6.6 — Shifted KdV identity.

In the setup and notation of this section, the paper defines or asserts:



$$`\overline U_{g,p}(1,0^{p-1})
 =\frac14\overline U_{g-1,p+2}(\mathbf0)
 +\frac32\sum_{j=0}^g\sum_{s=0}^{p-2}\binom{p-2}s
 \overline U_{j,s+2}(\mathbf0)
 \overline U_{g-j,p-s}(\mathbf0).`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



The split is ordered. The factor three from the weighted degree-one insertion turns the original KdV coefficients into $`1/4` and $`3/2`. In {bpref "eq:TL14"}[6.6], every term has the same total powers of $`a` and $`r`: the two separating complexities sum to $`h`, and their deficits sum to $`3g-4+p`. Thus no omitted parameter factor is present.

The key consequence of positivity, used throughout this section, is the following monotonicity.

:::lemma_ "lem:monotone" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:TL9")
%%%
source := { document := "paper-v3", spans := #[{ page := "32", anchor := "lem:monotone", citation := "Lemma 6.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma 6.1 — Monotonicity in the degrees.

For every stable $`(g,p)`, every degree tuple $`\mathbf d`, every $`i` and every $`Y\in[0,y_0]`, 

$$`\overline U_{g,p}(\mathbf d)\ge
 \overline U_{g,p}(\mathbf d+\mathbf e_i),
 \qquad 0\le c_{g,p}(\mathbf d)\le1.`

 Amplitudes outside the dimension range are zero.

Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



:::proof "lem:monotone" (uses := "eq:H9, eq:P11")
We subtract the recursion at adjacent degrees. With $`\mathbf d'=(d_2,\ldots,d_p)` fixed, let $`\mathcal B_{\mathbf d'}(t)` denote the merging and contraction sums in {bpref "eq:H9"}[4.8], with the kernel weight removed and $`d_1+\ell=t`. These sums are nonnegative and vanish for $`t>3g-3+p-|\mathbf d'|` by dimension. If $`m=3g-3+p-|\mathbf d|\ge0`, shifting the kernel index gives 

$$`\begin{aligned}
 \overline U_{g,p}(\mathbf d)
   &=\sum_{\ell=0}^m\theta_\ell
                      \mathcal B_{\mathbf d'}(d_1+\ell),\\
 \overline U_{g,p}(\mathbf d+\mathbf e_1)
   &=\sum_{\ell=1}^m\theta_{\ell-1}
                      \mathcal B_{\mathbf d'}(d_1+\ell).
 \end{aligned}`

 Their difference is therefore $`\sum_{\ell=0}^m w_\ell\mathcal B_{\mathbf d'}(d_1+\ell)\ge0`, which proves 6.7 for $`i=1`, and by symmetry for every $`i`. This includes the dimension boundary by the zero convention. The difference identity is used for $`h\ge2`; the finite bases satisfy the inequality directly because $`\theta_1\ge\theta_0=1`.
:::



From {bpref "eq:TL12"}[6.4], 6.5, and 6.7, 

$$`\frac{W_{g,p}}{W_{g,p+1}}\le\frac C{2g-2+p}`

 in all stable cases used below, with a constant independent of $`p`: the absolute sum in 6.5 is uniform and the ratios in 6.7 are at most one. Finite stable bases are included in the constant. Multiplication of {bpref "eq:TL14"}[6.6] by $`4^g` and use of 6.7 give 

$$`W_{g-1,p+2}\le W_{g,p},\qquad p\ge2.`

 The factor $`4^g` in {bpref "eq:TL9"}[6.1] is essential: it converts the coefficient $`1/4` into the comparison constant one.

## Separating terms

The separating terms in the KdV identity {bpref "eq:TL14"}[6.6], and in the degree difference above, are controlled by the convolution sums $`S_{g,p}` and $`T_{g,p}` below. They are small for two reasons. Splitting off a component of bounded genus $`j` removes $`2j+s` units of complexity, and the cusp insertions cost a factor $`O(1/g)` each, by 6.8–6.9; and a split into two components of comparable genus is exponentially small by the binomial entropy in 6.13.

For fixed $`p\ge2`, define 

$$`S_{g,p}=\frac1{W_{g,p}}
 \sum_{j=0}^g\sum_{s=0}^{p-1}\binom{p-1}s
 W_{j,s+1}W_{g-j,p-s},`

 

$$`T_{g,p}=\frac1{W_{g,p}}
 \sum_{j=0}^g\sum_{s=0}^{p-2}\binom{p-2}s
 W_{j,s+2}W_{g-j,p-s}.`

 We claim, uniformly in $`Y`,

:::proposition "eq:TL19" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:TL9")
%%%
source := { document := "paper-v3", spans := #[{ page := "32", anchor := "eq:TL19", citation := "Equation 6.11", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 6.11 — Separating convolution estimates.

In the setup and notation of this section, the paper defines or asserts:



$$`S_{g,p}=O_p(g^{-2}),\qquad T_{g,p}=O_p(g^{-1}),`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



with the positive-genus portion of $`T` bounded by $`O_p(g^{-2})`. In particular $`T_{g,2}=O(g^{-2})` because its genus-zero terms are unstable.

By symmetry orient the smaller genus as $`j\le g/2`. For $`1\le j\le\varepsilon g`, insert $`2j` cusps into the larger-genus component using 6.8, apply 6.9 $`j` times, and insert the remaining $`s` cusps. This gives 

$$`\frac{W_{g-j,p-s}}{W_{g,p}}
 \le (C_p/g)^{2j+s}.`

 If $`p-s=1`, instead insert $`2j+1` cusps before raising the genus, so every genus-comparison step ends with at least two markings; afterward insert $`s-1` cusps. This is possible because $`p\ge2`, and the same exponent results. In the $`T` convolution both relevant marking counts are already at least two.

The crude bound following 6.3 makes the smaller-component contribution a fixed polynomial in $`j` times 

$$`(2j)!(C_p/g^2)^j g^{-s}.`

 Choose $`\varepsilon>0` small enough that successive factorial terms have a ratio bounded by a fixed number below one. Their positive-genus sum is $`O_p(g^{-2})`, also with any fixed polynomial in $`j`. For genus zero, stability gives $`s\ge2` in $`S` and $`s\ge1` in $`T`; direct use of 6.8 gives the respective orders.

For $`\varepsilon g\le j\le g/2`, apply 6.3 to both factors and the parent. The marking counts belong to a fixed finite set. The powers of $`A(Y)` cancel up to bounded exponents, and Stirling’s formula gives 

$$`\log\frac{W_{j,s+c}W_{g-j,p-s}}{W_{g,p}}
 \le-2g\mathsf H(j/g)+o(g),\qquad c\in\{1,2\},`

 where $`\mathsf H(t)=-t\log t-(1-t)\log(1-t)`. Its positive minimum on $`[\varepsilon,1/2]` makes the macroscopic sum exponentially small. This proves {bpref "eq:TL19"}[6.11]. Every use of 6.3 here has a positive fixed marking count.

## Cusp and genus ratios

For $`p\ge2`, the adjacent-degree difference obtained from {bpref "eq:H9"}[4.8] has a merging prefactor $`O_p(1/g)` by 6.8. Its nonseparating prefactor is bounded by 

$$`\frac{W_{g-1,p+1}}{W_{g,p}}
 \le\frac Cg\frac{W_{g-1,p+2}}{W_{g,p}}=O_p(g^{-1})`

 using 6.8–6.9. To see all three contributions, put $`D=|\mathbf d|`, $`\Omega_0=\sum_{\ell\ge0}w_\ell` and $`\Omega_1=\sum_{\ell\ge0}\ell w_\ell`. Bound each child amplitude by its zero-degree value in the difference identity above. Since there are at most $`d_1+\ell+1` new-degree pairs, it yields 

$$`\begin{aligned}
 c_{g,p}(\mathbf d)-c_{g,p}(\mathbf d+\mathbf e_1)
 \le{}&\Omega_0(2D+p-1)\frac{W_{g,p-1}}{W_{g,p}}\\
 &+\bigl((d_1+1)\Omega_0+\Omega_1\bigr)
   \left(2\frac{W_{g-1,p+1}}{W_{g,p}}+\frac12S_{g,p}\right).
 \end{aligned}`

 The factor $`2` in the nonseparating term includes the factor $`4` from the genus normalization of $`W`. The two kernel moments are uniformly bounded by 6.2. Equations 6.8, {bpref "eq:TL19"}[6.11] and 6.14 now give 

$$`0\le c_{g,p}(\mathbf d)-c_{g,p}(\mathbf d+\mathbf e_i)
 \le\frac{C_p(|\mathbf d|+1)}g.`

 Summing degree increments proves

:::proposition "eq:TL23" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:TL9")
%%%
source := { document := "paper-v3", spans := #[{ page := "33", anchor := "eq:TL23", citation := "Equation 6.15", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 6.15 — Quadratic profile estimate with at least two markings.

In the setup and notation of this section, the paper defines or asserts:



$$`0\le1-c_{g,p}(\mathbf d)
 \le C_p\frac{|\mathbf d|(|\mathbf d|+1)}g,
 \qquad p\ge2.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



When the right side exceeds one the bound is trivial. It also bounds the terms outside the dimension range when they are set to zero.

Substitute {bpref "eq:TL23"}[6.15] into {bpref "eq:TL12"}[6.4]. The errors sum absolutely by 6.5, giving

:::proposition "eq:TL24" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:TL9")
%%%
source := { document := "paper-v3", spans := #[{ page := "33", anchor := "eq:TL24", citation := "Equation 6.16", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 6.16 — Two-sided marked cusp ratio.

In the setup and notation of this section, the paper defines or asserts:



$$`(2g-2+p)\frac{W_{g,p}}{W_{g,p+1}}
 =A(Y)+O_p(g^{-1}),\qquad p\ge1.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



Since $`A` is uniformly positive, the error is relative $`O_p(1/g)`.

To recover the one-marking profile without circularity, first use 6.8 twice, 6.9 at parent marking count two, and the now two-sided ratio {bpref "eq:TL24"}[6.16] at marking count one: 

$$`\frac{W_{g-1,2}}{W_{g,1}}
 \le\frac C{g^2}\frac{W_{g-1,4}}{W_{g,2}}
 \frac{W_{g,2}}{W_{g,1}}=O(g^{-1}).`

 The separating terms at one marking have two positive genera. Equation 6.8, the inequality $`1/[j(g-j)]\le C/g`, and $`T_{g,2}=O(g^{-2})` give 

$$`\frac1{W_{g,1}}\sum_{j=1}^{g-1}W_{j,1}W_{g-j,1}
 \le\frac Cg\frac{W_{g,2}}{W_{g,1}}T_{g,2}=O(g^{-2}).`

 The same degree-difference argument now proves {bpref "eq:TL23"}[6.15] for $`p=1`. Thus {bpref "eq:TL24"}[6.16] holds also for $`p=0`.

Finally {bpref "eq:TL14"}[6.6], {bpref "eq:TL19"}[6.11], and {bpref "eq:TL23"}[6.15] yield

:::proposition "eq:TL27" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:TL9")
%%%
source := { document := "paper-v3", spans := #[{ page := "34", anchor := "eq:TL27", citation := "Equation 6.19", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 6.19 — Marked genus exchange.

In the setup and notation of this section, the paper defines or asserts:



$$`\frac{W_{g-1,p+2}}{W_{g,p}}=1+O_p(g^{-1}),\qquad p\ge2.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



For $`p=0,1`, add two markings in numerator and denominator and use {bpref "eq:TL24"}[6.16]; the two cusp products have the same complexity factors and cancel. Hence {bpref "eq:TL27"}[6.19] holds for every fixed $`p\ge0`.

We now return to volumes. Recall the cusp generating function $`\Phi_g` of {bpref "eq:intro-Phi"}[1.1] and the string-shift identity {bpref "eq:H8"}[4.7]: $`U_{g,p}(0^p;Y)=\Phi_g^{(p)}(x)` with $`x=X(Y)`, whenever the amplitude is stable. By {bpref "eq:TL9"}[6.1], $`W_{g,p}=4^ga^hr^m\Phi_g^{(p)}(x)` with $`m=3g-3+p`. Adding a marking raises both $`h` and $`m` by one, so 

$$`\frac{x\Phi_g^{(p+1)}(x)}{\Phi_g^{(p)}(x)}
 =\frac{x}{ar}\,\frac{W_{g,p+1}}{W_{g,p}}
 =\frac{hx}{A\,a\,r}\bigl(1+O_p(g^{-1})\bigr)`

 by {bpref "eq:TL24"}[6.16]. Replacing $`(g,p)` by $`(g-1,p+2)` leaves $`h` unchanged and lowers $`m` by one, so $`\Phi_{g-1}^{(p+2)}/\Phi_g^{(p)}=4r\,W_{g-1,p+2}/W_{g,p}`, and {bpref "eq:TL27"}[6.19] applies. This proves, for every fixed positive $`p`, 

$$`x\frac{(\Phi_g^{(p)})'(x)}{\Phi_g^{(p)}(x)}
 =h\Psi(x)+O_p(\Psi(x)),\qquad h=2g-2+p,`

 

$$`\frac{\Phi_{g-1}^{(p+2)}(x)}{\Phi_g^{(p)}(x)}
 =4r(Y)(1+O_p(g^{-1})),
 \qquad
 \Psi(x)=\frac{x}{A(Y)a(Y)r(Y)}.`

 The same genus ratio holds at $`p=0`. The estimates are uniform throughout $`0\le Y<y_0`; at $`x=0`, 6.20 is interpreted by continuity.

The scalar is exactly the stationary parameter: 

$$`H_Y(r)=\frac{3I(Y)}{2\Delta^{3/2}},\qquad
 A(Y)a(Y)r(Y)=\frac{I(Y)}{\sqrt\Delta},\qquad
 \Psi(x)=\lambda(Y)/2.`

 The first equality follows by substituting $`v=T-\Delta s^2` in $`I`, and the other two follow by direct substitution. We summarize the output of this section used in the extraction arguments.

:::proposition "prop:marked-ratios" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:TL9, eq:SP2")
%%%
source := { document := "paper-v3", spans := #[{ page := "34", anchor := "prop:marked-ratios", citation := "Proposition 6.2", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 6.2 — Marked cusp and genus ratios.

For every fixed $`p\ge1`, uniformly for $`0\le Y<y_0` and $`x=X(Y)`, the cusp ratio of $`\Phi_g^{(p)}` satisfies 6.20 and the genus ratio satisfies 6.21, with $`\Psi(x)=\lambda(Y)/2`. The genus ratio holds also at $`p=0`.

Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::


