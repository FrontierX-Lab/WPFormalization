import WPFormalization.Statements
import WPBlueprint.Chapters.C17
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "appC-marked-expansion" =>

# The marked expansion beyond the leading term

This appendix proves Theorems {bpref "thm:first-correction"}[8.1] and {bpref "thm:full-expansion"}[8.2]. Subsections C.1–C.3 compute one further term in the recursion. The coefficient to be integrated vanishes at the endpoint, so its primitive stays bounded. This gives both an $`O_p(g^{-1})` relative error for the leading term and its first explicit correction. The number $`p` of distinguished markings remains fixed. Subsections C.4 and C.9 then construct the full series and control its remainder as the truncation order grows.

## The second degree coefficient

We first extend the degree expansion 7.5 of the normalized profiles by one order (Lemma {bpref "lem:second-profile"}[C.1]). The argument is the adjacent-degree subtraction used for 7.5 in Section 7, now keeping the $`h^{-2}` terms of the prefactors and the two smallest separating configurations.

We retain $`\delta_p` and $`\beta_p` from 7.5 and 7.7. The kernel coefficients $`\theta_\ell` are those of {bpref "eq:H2"}[4.1]. Set

$$`\alpha_p=A\{(p-3)\Theta+2M_1+2p-3\},\qquad
 \mathcal T_j=\sum_{\ell\ge\max(0,j)}w_\ell.`

 For a pivot $`i`, put $`t=d_i` and let $`z` count zero entries among the other $`p-1` markings. Let $`\mathbf d^{ij,\ell}` be the merger child, with new degree $`t+d_j+\ell-1`, and let $`\mathbf d^{i;u,v}` be the nonseparating child with the pivot replaced by $`u,v`. Define

$$`\begin{aligned}
 B_{p,i}(\mathbf d)={}&
 A\sum_{j\ne i}(2d_j+1)
 \sum_{\ell\ge\max(0,1-t-d_j)}w_\ell
 [1-\beta_{p-1}-\delta_{p-1}(\mathbf d^{ij,\ell})]\\
 &+2A\sum_{\ell\ge\max(0,2-t)}w_\ell
 \sum_{\substack{u+v=t+\ell-2\\u,v\ge0}}
 [1-\beta_{p+1}-\alpha_p-\delta_{p+1}(\mathbf d^{i;u,v})]\\
 &+A^2\left\{\left[\binom z2+\frac{\theta_1}2\right]
                    \mathcal T_{2-t}+\frac12\mathcal T_{3-t}\right\}.
\end{aligned}`

 The first line is absent at $`p=1`. Starting at zero along a fixed coordinate-increment path, define $`e_p` by

$$`e_p(\mathbf0)=0,\qquad
 e_p(\mathbf d+\mathbf e_i)-e_p(\mathbf d)=-B_{p,i}(\mathbf d).`

 The formulas converge absolutely by 6.2; they give $`B_{p,i}=O_p((D+1)^3)` and $`e_p=O_p((D+1)^4)`.

:::lemma_ "lem:second-profile" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:TL9")
%%%
source := { document := "paper-v3", spans := #[{ page := "72", anchor := "lem:second-profile", citation := "Lemma C.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma C.1 — Second profile correction.

For fixed $`p\ge1`, uniformly in $`Y` and $`D\le h^{1/8}`,

$$`c_{g,p}(\mathbf d)=1-\frac{\delta_p(\mathbf d)}h
       +\frac{e_p(\mathbf d)}{h^2}
       +O_p\!\left(\frac{(D+1)^6}{h^3}\right).`

 The function $`e_p` is independent of the chosen path.

Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



:::proof "lem:second-profile" (uses := "lem:first-degree, eq:TL19, eq:H9")
We first need the linear term in the genus exchange. For $`p\ge2`, the two genus-zero three-marking contributions to 6.10 give $`T_{g,p}=2(p-2)A/h+O_p(h^{-2})`. Every other genus-zero term loses at least two cusp factors, and the positive-genus portion is $`O_p(h^{-2})` by {bpref "eq:TL19"}[6.11]. Thus {bpref "eq:TL14"}[6.6] and 7.5 imply

$$`\frac{W_{g-1,p+2}}{W_{g,p}}=1-\frac{\alpha_p}h+O_p(h^{-2}).`

 Indeed the coefficient is $`\delta_p(\mathbf e_1)+3(p-2)A=\alpha_p`. For $`p=0,1`, descend from $`p+1` using 7.7; the cusp ratio changes its first coefficient by $`\beta_{p+2}-\beta_p=-A(\Theta+2)`, while $`\alpha_{p+1}-\alpha_p=A(\Theta+2)`. Consequently the two adjacent-difference prefactors are

$$`\begin{aligned}
 \frac{W_{g,p-1}}{W_{g,p}}
 &=\frac Ah\left(1+\frac{1-\beta_{p-1}}h\right)+O_p(h^{-3}),\\
 2\frac{W_{g-1,p+1}}{W_{g,p}}
 &=\frac{2A}h\left(1+\frac{1-\beta_{p+1}-\alpha_p}h\right)
     +O_p(h^{-3}).
\end{aligned}`

 The first line is used only at $`p\ge2`. Both children have complexity $`h-1`, which accounts for the two constants $`+1`.

We next retain the leading separating terms of the adjacent difference. If the smaller component has genus $`j` and contains $`s` of the other external labels, the complementary component has complexity $`h-(2j+s)`. Stability forces $`2j+s\ge2`. Equality occurs only for $`(j,s)=(0,2)` and $`(1,0)`. The first component is a three-marked sphere, so its three degrees must be zero; it gives $`\binom z2\mathcal T_{2-t}`. The second is a one-marked torus, whose $`W` amplitudes are $`\theta_1/2` and $`1/2` at degrees zero and one. It gives $`(\theta_1/2)\mathcal T_{2-t}+(1/2)\mathcal T_{3-t}`. The two orientations cancel the factor $`1/2` in the recursion. In both cases the large all-zero component divided by the parent is $`A^2/h^2+O_p(h^{-3})`, by fixed iterations of 7.7 and C.5. Its degrees can be replaced by zero at cost $`O_p((D+\ell+1)^2/h)`.

After removing these two types the all-zero separating mass is $`O_p(h^{-3})`. To verify this sharper bound, repeat the proof of 6.12: the remaining genus-zero terms have $`s\ge3`, the remaining genus-one terms have $`s\ge1`, and $`j\ge2` starts at $`h^{-4}`. The same factorial-geometric series sums these bounds, with any fixed polynomial in $`j`; 6.13 handles the macroscopic splits. At $`p=1`, insert $`2j+1` cusps in the larger component before raising its genus to marking count two, then use $`W_{g,2}/W_{g,1}=O(g)`. This bounds its ratio by $`O((C/g)^{2j})`. After the two genus-one orientations are removed, the factorial series starts at $`j=2` and is $`O(h^{-4})`. This argument uses the marking-independent constant in 6.8. Pair counts and the moments of $`w_\ell` give an adjacent-difference error $`O_p((D+1)^3/h^3)` for the separating part.

Now substitute 7.5 and C.6 into the exact adjacent subtraction of {bpref "eq:H9"}[4.8]. The two retained separating types give the last line of C.2. The result is

$$`c(\mathbf d)-c(\mathbf d+\mathbf e_i)
 =\frac{\delta_p(\mathbf d+\mathbf e_i)-\delta_p(\mathbf d)}h
  +\frac{B_{p,i}(\mathbf d)}{h^2}
  +O_p((D+1)^5/h^3).`

 To justify the substitution, cut the kernel index $`\ell` at $`h^{1/8}`. Below this cutoff, child degrees are at most $`2h^{1/8}+O_p(1)`, inside the range of 7.5 for all sufficiently large $`h`. Its remainder, multiplied by the linear prefactor and degree count, is $`O_p((D+\ell+1)^5/h^3)`. Above the cutoff use $`0\le c\le1` and polynomial growth of the displayed coefficients. Since the uniform moments 6.2 of $`w_\ell` are finite to every order, these tails are $`O_p(h^{-3})`, even after summing at most $`D` increments. The dimension cutoff is farther away and is covered by the same argument. Summing increments proves C.4. For a fixed tuple, expansions along two paths must have the same $`h^{-2}` coefficient as $`g\to\infty`, proving path independence.
:::



Comparison with the fixed-cusp expansion. At $`Y=0` one has $`A=1/\pi^2`, $`\Theta=2` and $`M_1=3/2`, and the normalization {bpref "eq:TL9"}[6.1] gives $`W_{g,p}/W_{g,p+1}=4V_{g,p}/V_{g,p+1}` and $`W_{g-1,p+2}/W_{g,p}=V_{g-1,p+2}/V_{g,p}`. With $`h=2g-2+p`, equations 7.7 and C.5 become

$$`\frac{V_{g,p+1}}{8\pi^2gV_{g,p}}
 =1+\frac{(\frac12-\pi^{-2})p-\frac54+2\pi^{-2}}{g}+O_p(g^{-2}),
 \qquad
 \frac{V_{g-1,p+2}}{V_{g,p}}=1+\frac{3-2p}{\pi^2g}+O_p(g^{-2}),`

 and 7.5 gives, for fixed $`k\ge1`,

$$`\frac{[\tau_k\tau_0^{p-1}]_{g,p}}{V_{g,p}}
 =1-\frac{k^2+(p-\frac52)k-\frac p2+\frac32}{\pi^2g}+O_p(g^{-2}).`

 These are the first-order formulas of Mirzakhani and Zograf \[66\] Theorems 1.4 and 3.2(i), recovered here as the $`Y=0` case of the parameter-dependent coefficients.

## The coefficient in the differential equation

Inserting Lemma {bpref "lem:second-profile"}[C.1] into the dilaton identity gives the next coefficient $`\gamma_p` of the differential equation {bpref "eq:PF8"}[7.8]. We then evaluate it with finitely many kernel moments and check that it vanishes at the pure-$`\psi` endpoint.

Apply C.4 to the dilaton child of complexity $`h+1` and set

$$`E_p=\sum_{d\ge1}b_d e_{p+1}(d,0^p),\qquad
 \gamma_p=\beta_p^2-\beta_p-E_p/A.`

 The moments of $`b_d` justify this sum and yield

$$`\frac{\mathrm{d}}{\mathrm{d}Y}\log\Phi_g^{(p)}(X(Y))
 =\frac{h+\beta_p+\gamma_p/h+O_p(h^{-2})}{Ar}.`

 Indeed, replacing $`h+1` by $`h` in the child profile gives $`1-\delta/h+(\delta+e)/h^2`. Thus the dilaton ratio is $`A\{1-\beta_p/h+(\beta_p+E_p/A)/h^2+O_p(h^{-3})\}`, and inversion proves C.8. To justify the sum, truncate the dilaton degree at $`h^{1/8}`; the tail is bounded using $`1+d^2/h+d^4/h^2` and a sufficiently high absolute moment of $`b_d` from 6.5.

The coefficient in C.7 can be evaluated using finitely many kernel moments, as follows. Put $`P=p+1`, and write $`B_P(t)=B_{P,1}(t,0^{P-1})`. With $`k=t+\ell-1` and $`s=t+\ell-2`, C.2 becomes

$$`\begin{aligned}
 R_P(k)&=1-\beta_{P-1}
       -A\{\Theta(k^2+(P-5)k)+2M_1k+(4-P)\mathbf1_{k\ge1}\},\\
 S_P(s)&=(s+1)(1-\beta_{P+1}-\alpha_P)\\
 &\quad-A\{(s+1)(\Theta(s^2+(P-3)s)+2M_1s)
                   +(5-2P)s-1+\mathbf1_{s=0}\}.
\end{aligned}`

 Then

$$`\begin{aligned}
 B_P(t)={}&A(P-1)\sum_{\ell\ge\max(0,1-t)}w_\ell R_P(t+\ell-1)\\
 &+2A\sum_{\ell\ge\max(0,2-t)}w_\ell S_P(t+\ell-2)\\
 &+A^2\left\{\left[\binom{P-1}2+\frac{\theta_1}2\right]
                     \mathcal T_{2-t}+\frac12\mathcal T_{3-t}\right\}.
\end{aligned}`

 The zero-degree correction in $`S_P` follows by summing the $`q` term of $`\delta_{P+1}`: for $`s\ge1` the two endpoint pairs have $`q=1` and the $`s-1` interior pairs have $`q=2`.

For $`t\ge3`, remove both lower cutoffs, replace $`\mathbf1_{k\ge1}` by one, $`\mathbf1_{s=0}` by zero, and both tails by $`\Theta`. This gives a cubic polynomial $`B_\infty(t)=a_3t^3+a_2t^2+a_1t+a_0`. Its coefficients use only $`M_j=\sum\ell^jw_\ell`, $`0\le j\le3`. Put $`\Delta_j=B_P(j)-B_\infty(j)` for $`j=0,1,2`, and define

$$`\begin{aligned}
 \Sigma(d)&=\frac{a_3}4d^2(d-1)^2+
       \frac{a_2}6d(d-1)(2d-1)+\frac{a_1}2d(d-1)+a_0d,\\
 e_P(d,0^{P-1})&=-\Sigma(d)-\sum_{j=0}^2\Delta_j\mathbf1_{d\ge j+1}.
 \end{aligned}`

 The three exceptional values use the same moments and $`w_0,w_1,w_2`; there is no remaining infinite recursion. Set

$$`L_j=\frac13[(z\partial_z+1)^j\bar H_Y(z)]_{z=1}\quad(1\le j\le4),
 \qquad b_1=\frac13,\quad b_2=-\frac{\theta_1}5,`

 and

$$`\Sigma_b=\frac{a_3}4(L_4-2L_3+L_2)
   +\frac{a_2}6(2L_3-3L_2+L_1)
   +\frac{a_1}2(L_2-L_1)+a_0L_1.`

 Then the finite formula for C.7 is

$$`\gamma_p=\beta_p^2-\beta_p+
 \frac{\Sigma_b+\Delta_0A+\Delta_1(A-b_1)+\Delta_2(A-b_1-b_2)}A.`

 All ingredients extend analytically to $`Y=y_0`, by the removable normalized-kernel extension used in 7.15.

At that endpoint $`A=2/15`, $`\Theta=1`, $`M_j=0` for $`j\ge1`, $`w_0=\theta_1=1`, and $`\beta_p=-p/5`. Equation C.9 gives $`B_P(0)=0` and $`B_P(1)=A(P-1)(P+4)/5`. Only $`b_1=1/3` and $`b_2=-1/5` remain, so $`E_p/A=p(p+5)/25=\beta_p^2-\beta_p`. In particular,

$$`\gamma_p(y_0)=0,\qquad \gamma_p(Y)=O_p(y_0-Y),\qquad
 \gamma_p/(Ar)=O_p(1).`

 This agrees with an exact computation: string and dilaton at the pure-$`\psi` endpoint give $`W_{g,p+1}/W_{g,p}=3(h+m)=(15h-3p)/2`, so that $`A\,W_{g,p+1}/(hW_{g,p})=1-p/(5h)` exactly, with $`A=2/15`; there is no term of order $`h^{-2}`, and $`\gamma_p=0`.

## Critical matching to the next order

Recall $`t_p` and $`\mathcal L_p` from {bpref "eq:ST13"}[8.1]. By C.9–C.12, $`\mathcal L_p` is an explicit bounded function, given by finitely many kernel derivatives and a convergent one-dimensional integral.

:::proof "thm:first-correction" (uses := "lem:second-profile, eq:FE14")
The sharper critical input is $`C_g(2^{3g-3})=\pi^{-1}(1-2/(9g)+O(g^{-2}))`. It is derived in Subsection C.9, as the coefficient $`d_1=-2/9` in C.36, from the Itzykson–Zuber identity, the large-order relation of Garoufalidis–Its–Kapaev–Mariño and the first one-instanton coefficient $`v_1=-1/8`; that derivation is independent of the transport argument of Subsections C.1–C.3, and the value agrees with \[32\] equation (25). A leading estimate alone would not identify this correction. Expanding the finite product {bpref "eq:PF12"}[7.13] gives

$$`\pi C_g(0^p,2^m)=
 1+\frac{p(5-p)/15-4/9}{h}+O_p(h^{-2}).`

 The critical harmonic coefficient also has a first correction. Its summand law is geometric with mean $`3/2`, variance $`v=15/4`, third cumulant $`15`, and fourth cumulant $`705/8`. At displacement $`d=-p/2` from $`3h/2`, expansion of its exact negative-binomial coefficient by Stirling’s formula gives

$$`\frac{\mathcal M_{g,p}(0^p;y_0)}
 {\Gamma(h)4^{-g}A_*^{-h}/\sqrt{2\pi hv}}
 =1+\frac{-p^2/30+4p/15-19/180}{h}+O_p(h^{-2}),
 \qquad A_*=2/15.`

 For example the coefficient before substituting $`d=-p/2` is $`-d^2/(2v)-15d/(2v^2)+(705/8)/(8v^2)-5(15)^2/(24v^3)`. Combining these two expansions with {bpref "eq:PF13"}[7.14] proves

$$`\lim_{Y\uparrow y_0}
 \frac{\pi\Phi_g^{(p)}(X(Y))}{\mathcal J_{g,p}(Y)}
 =1+\frac{t_p}{h}+O_p(h^{-2}).`

 Take $`Y_*=y_0-h^{-3}`. The positive homogeneous-polynomial comparison 7.16 and the analytic normalized factor in 7.17 change this ratio by $`O_p(h(y_0-Y))=O_p(h^{-2})` for $`Y\ge Y_*`. Moreover $`\mathcal L_p(Y)=t_p+O_p(y_0-Y)` there. For $`Y\le Y_*`, subtract the exact logarithmic derivative of $`\mathcal J_{g,p}` in 7.11 from C.8, and integrate:

$$`\log\frac{\pi\Phi_g^{(p)}(X(Y))}{\mathcal J_{g,p}(Y)}
 =\frac{\mathcal L_p(Y)}h+
 O_p\!\left(h^{-2}+\frac1{h^2}
             \log\frac{\mathcal Z(Y)}{\mathcal Z(Y_*)}\right).`

 Here C.12 controls the terminal integral, and $`\mathcal Z(Y_*)\asymp h^{-15/2}`. The remainder is $`O_p(\log h/h^2)` uniformly. Boundedness of $`\mathcal L_p` permits exponentiation, proving 8.2 in both regions.
:::



## The formal hierarchy

We now construct the full series and control its remainder as the truncation order grows. These are still estimates for generating functions: the passage to a prescribed cusp count is made in Subsection 10.1 and Appendix D.

The recursion is triangular. Each new degree coefficient uses earlier cusp and genus coefficients; the dilaton and KdV equations then give the new cusp and genus coefficients. Proposition {bpref "prop:hierarchy"}[C.3] bounds the coefficients and the actual remainders. Matching at the pure-$`\psi` endpoint in Subsection C.9 completes the proof of Theorem {bpref "thm:full-expansion"}[8.2].

The proof makes the heuristic of Section 8 precise. It divides each order-$`j` coefficient by $`S_j^{2j}`, where $`S_j=D+p+Mj` is the weight described there. After this division, the coefficient rules become coefficientwise inequalities between power series with nonnegative coefficients, and an analytic majorant (Lemma {bpref "lem:majorant"}[C.2]) bounds the normalized coefficients by $`CB^j`. The true remainders are then controlled by a second, linear majorant system with the same normalization.

Use a formal variable $`t` for inverse complexity, and put

:::definition "eq:FE1" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:TL9")
%%%
source := { document := "paper-v3", spans := #[{ page := "76", anchor := "eq:FE1", citation := "Equation C.13", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition C.13 — Triangular formal coefficient system.

In the setup and notation of this section, the paper defines or asserts:



$$`\mathsf P_p(\mathbf d;t)=\sum_{j\ge0}e_{p,j}(\mathbf d)t^j,
 \quad \mathsf C_p(h)=\frac hA\frac{W_{g,p}}{W_{g,p+1}},
 \quad \mathsf G_p(h)=\frac{W_{g-1,p+2}}{W_{g,p}}.`


:::



The formal series for the last two quantities will also be denoted by $`\mathsf C_p(t),\mathsf G_p(t)`. Their constant terms, and $`e_{p,0}`, are one. Here $`e_{p,1}=-\delta_p` and $`e_{p,2}=e_p` from 7.5 and C.3. All series operations below are truncated at a fixed finite order; convergence of a formal series is never asserted. A complexity change from $`h` to $`h-c` means replacing $`t` by $`t/(1-ct)`.

For a bounded component of genus $`j` containing $`s` other external labels, set $`r_*=2j+s`. Thus $`r_*` is the decrease in complexity from the parent to the complementary component. Its all-zero ratio has the exact factorization

$$`\begin{aligned}
 \frac{W_{g-j,p-s}}{W_{g,p}}
 ={}&\prod_{a=0}^{r_*-1}
   \frac{A\mathsf C_{p-s+a}(h-r_*+a)}{h-r_*+a}
      \prod_{b=0}^{j-1}\mathsf G_{p+2b}(h),\\
 \mathsf R_{p;j,s}(t)
 ={}&(At)^{r_*}\prod_{a=0}^{r_*-1}
 \frac{\mathsf C_{p-s+a}(t/(1-(r_*-a)t))}{1-(r_*-a)t}
       \prod_{b=0}^{j-1}\mathsf G_{p+2b}(t).
\end{aligned}`

 The genus steps have unchanged complexity; the cusp steps remove $`r_*` markings at genus $`g-j`. All their marking counts are positive in the applications below. To obtain $`\mathsf R` through order $`t^K` requires scalar coefficients only through order $`K-r_*`.

The coefficients are computed as follows. Use the child tuples of C.2, and set $`\mathcal W_{j,q}(\mathbf d)=4^j\overline
U_{j,q}(\mathbf d)` for the exact bounded-complexity amplitudes. At each order $`K\ge1`, form

$$`\begin{aligned}
 \mathsf A_{p,i}={}&\frac{At}{1-t}\mathsf C_{p-1}\!\left(\frac t{1-t}\right)
 \sum_{j\ne i}(2d_j+1)
 \sum_{\ell\ge\max(0,1-d_i-d_j)}w_\ell
 \mathsf P_{p-1}\!\left(\mathbf d^{ij,\ell};\frac t{1-t}\right),\\
 \mathsf N_{p,i}={}&\frac{2At}{1-t}\mathsf C_{p+1}\!\left(\frac t{1-t}\right)
 \mathsf G_p(t)\sum_{\ell\ge\max(0,2-d_i)}w_\ell
 \sum_{u+v=d_i+\ell-2}\mathsf P_{p+1}\!\left(\mathbf d^{i;u,v};\frac t{1-t}\right).
\end{aligned}`

 Nonnegative node degrees are understood, and $`\mathsf A` is absent at $`p=1`. The retained separating contribution is

$$`\mathsf S_{p,i}=
 \sum_{\substack{j\ge0,\ I\subset\{1,\ldots,p\}\setminus\{i\}\\
        s=|I|,\ (j,s+1)\text{ stable}\\2\le2j+s\le K}}
 \mathsf R_{p;j,s}(t)\sum_{\ell\ge0}w_\ell
 \sum_{u+v=d_i+\ell-2}
 \mathcal W_{j,s+1}(u,\mathbf d_I)
 \mathsf P_{p-s}\!\left(v,\mathbf d_J;\frac t{1-(2j+s)t}\right),`

 where $`J` is the remaining set of labels. Only bounded $`j` occur; for large $`g` these orient the smaller component uniquely. The two orientations cancel the separating factor $`1/2`. Define

$$`\begin{aligned}
 e_{p,K}(\mathbf0)&=0,\\
 e_{p,K}(\mathbf d+\mathbf e_i)-e_{p,K}(\mathbf d)
   &=-[t^K](\mathsf A_{p,i}+\mathsf N_{p,i}+\mathsf S_{p,i}),\\
 \mathsf C_p(t)&=\frac1A\sum_{d\ge1}b_d
       \mathsf P_{p+1}\!\left(d,0^p;\frac t{1+t}\right).
 \end{aligned}`

 Finally, for $`p\ge2`, KdV gives

$$`\begin{aligned}
 \mathsf G_p(t)={}&\mathsf P_p(\mathbf e_1;t)
 -3\sum_{\substack{0\le s\le p-2,\ j\ge0\\
             (j,s+2)\text{ stable}\\1\le2j+s\le K}}
  \binom{p-2}s\mathcal W_{j,s+2}(\mathbf0)\mathsf R_{p;j,s}(t),\\
 \mathsf G_p(h)&=\mathsf G_{p+1}(h+1)
                   \mathsf C_{p+2}(h)/\mathsf C_p(h).
\end{aligned}`

 The last line descends from $`p=2` to $`p=1`, and optionally to $`p=0`. It is an exact identity; its shift $`h+1` must be retained.

The coefficient and remainder bounds below are obtained by comparing coefficientwise inequalities with an analytic system. We isolate the elementary principle used for this comparison.

:::lemma_ "lem:majorant" (parent := "paper_core") (tags := "paper-new") (priority := "high")
%%%
source := { document := "paper-v3", spans := #[{ page := "77", anchor := "lem:majorant", citation := "Lemma C.2", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma C.2 — Analytic majorants.

Let $`\Phi=(\Phi_1,\ldots,\Phi_m)` be power series in $`(t,v_1,\ldots,v_m)` with nonnegative coefficients, convergent near the origin, such that $`\Phi(0,0)=0` and the matrix $`\partial_v\Phi(0,0)` is strictly lower triangular. Then $`U=\Phi(t,U)` has a unique formal solution with $`U(0)=0`. Its coefficients are nonnegative, and it converges near $`t=0`. Let $`e_{i,j}\in[0,\infty]`, for $`1\le i\le m` and $`j\ge1`, and put $`E_i=\sum_{j\ge1}e_{i,j}t^j`. If $`e_{i,j}\le[t^j]\Phi_i(t,E)` for all $`i,j`, then $`e_{i,j}\le[t^j]U_i`. In particular every $`e_{i,j}` is finite, and $`e_{i,j}\le C\rho^{-j}` with $`C,\rho>0` depending only on $`\Phi`.
:::



:::proof "lem:majorant" (uses := "ext:complex-analysis")
Order the pairs $`(j,i)` lexicographically. Since $`E` has no constant term, $`[t^j]\Phi_i(t,E)` is a polynomial with nonnegative coefficients in the numbers $`e_{k,l}`. A monomial $`t^av^\beta` with $`a\ge1` or $`|\beta|\ge2` contributes only coefficients with $`l<j`, since each factor has order at least one. The remaining terms are $`\partial_{v_k}\Phi_i(0,0)\,e_{k,j}`, and they occur only for $`k<i`. Thus $`[t^j]\Phi_i(t,E)` involves only pairs preceding $`(j,i)`. The equations $`U=\Phi(t,U)` therefore determine the coefficients of $`U` recursively and uniquely, and these are nonnegative. The same induction and the monotonicity of polynomials with nonnegative coefficients give $`e_{i,j}\le[t^j]U_i`. The derivative of $`(t,v)\mapsto v-\Phi(t,v)` with respect to $`v` at the origin is $`I-\partial_v\Phi(0,0)`, which is invertible. The analytic implicit-function theorem gives a solution holomorphic near $`t=0` and vanishing at $`t=0`; its Taylor series is the formal solution. Cauchy’s estimate on a small circle gives the final bound.
:::



:::proposition "prop:hierarchy" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:FE1")
%%%
source := { document := "paper-v3", spans := #[{ page := "77", anchor := "prop:hierarchy", citation := "Proposition C.3", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition C.3 — Uniform recursive expansions.

There are $`C,B,M>0` and one complex neighborhood $`\Omega` of $`[0,y_0]` such that the preceding rules determine path-independent holomorphic coefficients with

$$`\|e_{p,j}(\mathbf d)\|_\Omega\le CB^j(D+p+Mj)^{2j},\qquad
 \|\mathsf C_{p,j}\|_\Omega+\|\mathsf G_{p,j}\|_\Omega
       \le CB^j(p+Mj)^{2j}.`

 For every stable state $`p\ge1`, $`h=2g-2+p\ge1`, every $`L\ge1`, and every nonnegative degree tuple, uniformly for $`0\le Y\le y_0`,

$$`\begin{aligned}
 \left|c_{g,p}(\mathbf d)-\sum_{j<L}e_{p,j}(\mathbf d)h^{-j}\right|
       &\le CB^L(D+p+ML)^{2L}h^{-L},\\
 \left|\mathsf C_p(h)-\sum_{j<L}\mathsf C_{p,j}h^{-j}\right|
 +\left|\mathsf G_p(h)-\sum_{j<L}\mathsf G_{p,j}h^{-j}\right|
       &\le CB^L(p+ML)^{2L}h^{-L}.
 \end{aligned}`

 Here $`D=\sum d_i`, $`\mathsf C_{p,j}=[t^j]\mathsf C_p(t)` and $`\mathsf G_{p,j}=[t^j]\mathsf G_p(t)`; invalid-degree profiles and invalid genus numerators are zero. For fixed $`p,j`, the rules use finitely many kernel moments, low kernel coefficients and exact bounded-complexity amplitudes.
:::



The proof of Proposition {bpref "prop:hierarchy"}[C.3] occupies Subsections C.5–C.8. At each order the construction runs in the sequence profile, cusp ratio, genus ratio at $`p\ge2`, and descent to $`p=1`; every profile on the right of C.15–C.16 has smaller order, and the dilaton and KdV rules use the current profile only after it has been constructed. Subsection C.5 fixes the analytic neighborhood and the weights $`S_j` and records four elementary bounds. Lemma {bpref "lem:coefficient-bounds"}[C.4] bounds the formal coefficients, uniformly in the order, by a system of analytic majorants; this is the first assertion of the proposition. Lemmas {bpref "lem:tails"}[C.5] and {bpref "lem:first-order"}[C.6] control the omitted topological types and give first-order estimates for the true quantities. Finally, Subsection C.8 proves the remainder bounds C.19 by induction on the order, using a linear majorant system for the normalized errors.

## Weights and elementary bounds

Shrink one complex neighborhood $`\Omega` of $`[0,y_0]` so that the normalized kernels $`\bar K_Y,\bar H_Y` and their nonvanishing quotients from Section 2 are holomorphic and bounded on a common disk $`|w|\le1+2\eta`, $`\eta>0`, for every $`Y\in\Omega`, and so that $`A(Y)` is bounded above and away from zero on $`\Omega`. Since $`\sum_\ell w_\ell w^\ell=(1-w)/\bar K_Y(w)` and $`b_d=\frac13[w^{d-1}]\bar H_Y(w)`, Cauchy’s estimate on the circle $`|w|=1+\eta` gives constants $`C_0` and $`\rho=1+\eta>1` with

$$`|w_\ell(Y)|\le C_0\rho^{-\ell},\qquad |b_d(Y)|\le C_0\rho^{-d}
 \qquad(Y\in\Omega,\ \ell,d\ge0).`

 The absolute-series argument in the proof of Lemma {bpref "lem:terminal"}[5.2](iii) also works on $`\Omega`: the background majorant $`B_Y` of Section 5.1 has a uniformly bounded germ, so one small radius $`z_*` makes $`B_Y(z_*)\le1/2` for all $`Y\in\Omega`. A stable component of complexity $`r` has at most $`r+2` markings and deficit $`m\le3r/2`, so the primitive bound of Lemma {bpref "lem:terminal"}[5.2](i) and this majorant give

$$`|\mathcal W_{j,q}(\mathbf d)|\le C_0^{\,r}\,\Gamma(r)\qquad(r=2j-2+q\ge1),`

 uniformly in the markings, the degrees and $`Y\in\Omega`; enlarging $`C_0` covers the components of complexity one.

Fix an integer $`M\ge2` with $`\mathrm{e}^{2/M}<\rho`. For a profile at a state with $`p` markings and degree sum $`D`, and for a scalar with $`p` markings, the order-$`j` weights are

$$`S_j=D+p+Mj\qquad\text{and}\qquad S_j=p+Mj`

 respectively, so that $`S_j\ge Mj\ge j` and $`S_j\ge p`. The following four bounds are used repeatedly.

1. Child weights. Let $`i\le j`. The merger child $`\mathbf d^{ij',\ell}` has $`p-1` markings and degree sum $`D+\ell-1`, the nonseparating child $`\mathbf d^{i;u,v}` has $`p+1` markings and degree sum $`D+\ell-2`, and the large child $`(v,\mathbf d_J)` of a separating term has $`p-s` markings and degree sum at most $`D+\ell-2`. In all three cases the order-$`i` weight of the child is at most $`S_j+\ell`. A scalar factor occurring at loss $`r` has at most $`p+r` markings; if it enters at order $`i` with $`i+r\le j`, its weight is at most $`p+r+Mi\le p+Mj\le S_j`, because $`r\le j-i\le M(j-i)`. The dilaton child $`(d,0^p)` of a scalar with $`p` markings has weight at most $`S_j+d+1`, and the children in the KdV and descent rules have weights at most $`S_j+2`.

2. Moment bound. For $`0\le k\le2j` and $`a\ge0`, $`(S_j+a)^k\le S_j^k(1+a/S_j)^{2j}\le S_j^k\mathrm{e}^{2a/M}`, since $`S_j\ge Mj`. Hence, with $`C_1=C_0\sum_{n\ge0}\rho^{-n}\mathrm{e}^{2(n+1)/M}<\infty`,
   $$`\sum_{\ell\ge0}|w_\ell|(S_j+\ell+1)^k\le C_1S_j^k,\qquad
 \sum_{d\ge1}|b_d|(S_j+d+1)^k\le C_1S_j^k\qquad(0\le k\le2j).`


3. Shifts. For integers $`a\ge1`, $`q\ge0` and $`0\le c\le c_0`,
   $$`[t^q](1-ct)^{-a}=\frac{a(a+1)\cdots(a+q-1)c^q}{q!}
 \le\frac{((a+q)c_0)^q}{q!},`
    with the empty product equal to one. For a product $`\prod_k(1-c_kt)^{-a_k}`, taking absolute values if necessary, the coefficient is bounded by that of $`(1-c_0t)^{-a}`, where $`a=\sum_k a_k` and $`c_0\ge\max_k|c_k|`. In an order-$`j` term, a prefactor of order $`r` and coefficients of total order $`i` leave shift degree $`q=j-r-i`. The total denominator exponent is at most $`r+i`, so $`a+q\le j`; also $`c_0\le\max(1,r)\le j`. Thus the coefficient is at most $`j^{2q}/q!\le S_j^{2q}/q!`. The case $`a=0` contributes only $`q=0`. After normalization all shifts are therefore majorized by $`\mathrm{e}^{t}`.

4. Counts. At a profile state, $`\sum_{j'\ne i}(2d_{j'}+1)\le
2D+p\le2S_j`, the number of pairs $`(u,v)` with $`u+v=d_i+\ell-2` is at most $`D+\ell\le S_j+\ell`, and a coordinate path from $`\mathbf0` to $`\mathbf d` has $`D\le S_j` steps. In a separating term of loss $`r=2j_0+s` the number of label subsets is $`\binom{p-1}s\le p^s/s!`, there are at most $`r+1\le2^r` pairs $`(j_0,s)`, and the small component has complexity $`r-1` in the profile rule and $`r` in the KdV rule, so C.21 gives
   $$`\binom{p-1}{s}\,|\mathcal W|\le C_0^{\,r}\frac{p^s\Gamma(r)}{s!}
 \le C_0^{\,r}(p+r)^r\le C_0^{\,r}S_j^{\,r}.`
    Indeed $`\Gamma(r)/s!\le r^{r-1-s}` when $`s\le r-1`, and $`\Gamma(r)/r!\le1` when $`s=r`; and $`p+r\le p+Mj=S_j` because $`r\le j`.

## Bounds for the formal coefficients

:::lemma_ "lem:coefficient-bounds" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:FE1")
%%%
source := { document := "paper-v3", spans := #[{ page := "79", anchor := "lem:coefficient-bounds", citation := "Lemma C.4", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma C.4 — Coefficient bounds.

The rules C.15–C.18 determine coefficients $`e_{p,j}(\mathbf d)`, $`\mathsf C_{p,j}` and $`\mathsf G_{p,j}` that are holomorphic on $`\Omega`, and there are $`C,B_0` such that, on $`\Omega`, for all $`p\ge1`, all degree tuples and all $`j\ge0`,

$$`|e_{p,j}(\mathbf d)|\le CB_0^{\,j}S_j^{2j},\qquad
 |\mathsf C_{p,j}|+|\mathsf G_{p,j}|\le CB_0^{\,j}S_j^{2j},`

 with the weights C.22.
:::



:::proof "lem:coefficient-bounds" (uses := "lem:majorant, lem:terminal, eq:P11")
Define the normalized coefficient sequences

$$`\varepsilon_j=\sup\frac{|e_{p,j}(\mathbf d)|}{S_j^{2j}},\quad
 \gamma_j=\sup\frac{|\mathsf C_{p,j}|}{S_j^{2j}},\quad
 \eta_j=\sup_{p\ge2}\frac{|\mathsf G_{p,j}|}{S_j^{2j}},\quad
 \zeta_j=\sup\frac{|\mathsf G_{1,j}|}{S_j^{2j}},`

 the suprema being taken over $`Y\in\Omega`, all marking counts $`p\ge1` and all degree tuples; $`\varepsilon_0=\gamma_0=\eta_0=\zeta_0=1`. Write $`\varepsilon(t)=\sum_j\varepsilon_jt^j`, and similarly $`\gamma,\eta,\zeta`, and put $`\bar\eta=\max(\eta,\zeta)` coefficientwise, which bounds every genus factor. Each coefficient of order $`j` is a finite combination of coefficients of lower order, summed against $`w_\ell` or $`b_d`; by C.20 and the polynomial growth in $`\ell` or $`d` of the lower-order weights these sums converge absolutely and uniformly on $`\Omega`, so each coefficient is holomorphic on $`\Omega` and each supremum is finite, by induction on $`j`. We bound the order-$`j` coefficients term by term.

Profile. Fix a state $`(\mathbf d,p)` and a direction $`i`. By C.15, $`[t^j]\mathsf A_{p,i}` is the sum over $`j'\ne i`, $`\ell\ge0` and $`i_1+i_2+q=j-1` of

$$`A(2d_{j'}+1)\,w_\ell\;\mathsf C_{p-1,i_1}\;
 e_{p-1,i_2}(\mathbf d^{ij',\ell})\;[t^q](1-t)^{-(1+i_1+i_2)}.`

 By (a) of Subsection C.5 the two coefficients are at most $`\gamma_{i_1}S_j^{2i_1}` and $`\varepsilon_{i_2}(S_j+\ell)^{2i_2}`; by (b) the sum over $`\ell` is at most $`C_1S_j^{2(i_1+i_2)}`; by (c) the shift coefficient is at most $`S_j^{2q}/q!`; and by (d) the merger count is at most $`2S_j`. Hence

$$`|[t^j]\mathsf A_{p,i}|\le2|A|C_1\,S_j^{\,2j-1}\,
 [t^{j-1}]\bigl(\mathrm{e}^{t}\gamma(t)\varepsilon(t)\bigr).`

 The term $`\mathsf N_{p,i}` has in addition one genus coefficient and the pair count $`S_j+\ell`, which C.23 absorbs with $`k=2(i_1+i_2+i_3)+1\le2j`; it is at most $`2|A|C_1S_j^{2j-1}[t^{j-1}](\mathrm{e}^{t}\gamma\bar\eta\varepsilon)`. A separating term of loss $`r\ge2` in C.16 carries the prefactor $`(At)^r`, $`r` cusp coefficients, $`j_0\le r/2` genus coefficients, one profile coefficient, the count C.24, the pair count and the shifts. Since $`\gamma` and $`\bar\eta` have constant term one and nonnegative coefficients, $`\gamma^r\bar\eta^{j_0}\preceq\gamma^{2r}\bar\eta^{2r}`, and the term is at most $`(2|A|C_0)^rC_1S_j^{\,r+1}S_j^{\,2(j-r)}[t^{j-r}](\mathrm{e}^t\gamma^{2r}\bar\eta^{2r}\varepsilon)`, where $`S_j^{r+1}\le S_j^{2r-1}` because $`r\ge2`. Summing the increments along a coordinate path of at most $`S_j` steps supplies one more factor $`S_j`. After division by $`S_j^{2j}` we obtain, for a constant $`b_1` depending only on $`\sup_\Omega|A|`, $`C_0` and $`C_1`,

$$`\varepsilon_j\le\Bigl[b_1\mathrm{e}^{t}\varepsilon(t)
 \Bigl(t\gamma\bar\eta+\sum_{r\ge2}(b_1t)^r\gamma^{2r}\bar\eta^{2r}\Bigr)\Bigr]_j
 \qquad(j\ge1).`



Cusp ratio. By C.17, $`[t^j]\mathsf C_p` is the sum over $`d\ge1` and $`i+q=j` of $`A^{-1}b_d\,e_{p+1,i}(d,0^p)\,[t^q](1+t)^{-i}`. The child weight is at most $`S_j+d+1` by (a), so C.23 and (c) give

$$`\gamma_j\le\bigl[b_2\,\mathrm{e}^{t}\varepsilon(t)\bigr]_j\qquad(j\ge1),
 \qquad b_2=C_1/\inf_\Omega|A|.`



Genus ratio at $`p\ge2`. In C.18 the term $`\mathsf P_p(\mathbf e_1;t)` has weight at most $`S_j+1` and contributes at most $`\mathrm{e}^{2/M}\varepsilon_j`. A separating term of loss $`r\ge1` carries $`3\binom{p-2}s|\mathcal W_{j_0,s+2}(\mathbf0)|\le3C_0^rS_j^r\le3C_0^rS_j^{2r}` by C.24, the prefactor $`(At)^r`, at most $`2r` scalar coefficients and the shifts. Hence

$$`\eta_j\le\Bigl[b_3\varepsilon(t)+b_3\mathrm{e}^{t}
 \sum_{r\ge1}(b_3t)^r\gamma^{2r}\bar\eta^{2r}\Bigr]_j\qquad(j\ge1),`

 for a constant $`b_3` depending only on $`M`, $`\sup_\Omega|A|` and $`C_0`.

Descent. The identity $`\mathsf G_1(h)=\mathsf G_2(h+1)\mathsf C_3(h)/\mathsf C_1(h)` is a product of a genus series with the shift $`t/(1+t)`, a cusp series and the formal inverse of a cusp series; the three weights are at most $`S_j+2`. If $`|\mathsf C_{1,i}|\le\gamma_iS_j^{2i}` for $`i\le j`, then the coefficients of $`1/\mathsf C_1` through order $`j` are bounded by $`S_j^{2i}` times those of $`1/(2-\gamma(t))=\sum_{k\ge0}(\gamma-1)^k`. Therefore

$$`\zeta_j\le\Bigl[b_4\,\mathrm{e}^{t}\frac{\eta(t)\gamma(t)}{2-\gamma(t)}\Bigr]_j
 \qquad(j\ge1),\qquad b_4=\mathrm{e}^{12/M}.`



The majorant system. Put $`b=\max(1,b_1,b_2,b_3,b_4)` and let $`E_*,C_*,H_*,G_*` be the formal solution, with constant terms one, of

$$`\begin{aligned}
 E_*&=1+b\,\mathrm{e}^{t}E_*\Bigl(tC_*G_*+\frac{(btC_*^2G_*^2)^2}{1-btC_*^2G_*^2}\Bigr),&
 C_*&=1+b(\mathrm{e}^{t}E_*-1),\\
 H_*&=1+b(E_*-1)+b\,\mathrm{e}^{t}\frac{btC_*^2G_*^2}{1-btC_*^2G_*^2},&
 G_*&=1+b\Bigl(\mathrm{e}^{t}\frac{H_*C_*}{2-C_*}-1\Bigr).
\end{aligned}`

 Here $`E_*` bounds the profile coefficients after division by their weights, $`C_*` the cusp coefficients, $`H_*` the genus coefficients at $`p\ge2` and $`G_*` the descent. Since $`b\ge1`, $`C_*/(2-C_*)\succeq1` and $`\mathrm{e}^t\succeq1`, the last equation gives $`G_*\succeq H_*`; so $`G_*` majorizes $`\bar\eta` as soon as $`H_*,G_*` majorize $`\eta,\zeta`. Writing $`E_*=1+v_1`, $`C_*=1+v_2`, $`H_*=1+v_3`, $`G_*=1+v_4`, the right-hand sides of C.29 are power series in $`(t,v)` with nonnegative coefficients, convergent near the origin and vanishing there. At $`t=0` the first equation has no linear term, the second and third are linear in $`v_1` only, and the fourth depends only on $`v_2,v_3`; so the Jacobian at the origin is strictly lower triangular, and Lemma {bpref "lem:majorant"}[C.2] shows that the formal solution of C.29 converges near $`t=0`. The inequalities C.25–C.28 now give $`\varepsilon_j\le[E_*]_j`, $`\gamma_j\le[C_*]_j`, $`\eta_j\le[H_*]_j` and $`\zeta_j\le[G_*]_j` for all $`j`, by induction on $`j` in the stage order: at order $`j` the right-hand sides involve $`\bar\eta` only through orders below $`j`, or through $`\eta_j` in the descent, and $`\max(\eta_i,\zeta_i)\le[G_*]_i` as soon as $`\eta_i\le[H_*]_i` and $`\zeta_i\le[G_*]_i`. Cauchy’s estimate for the convergent solution gives $`\varepsilon_j,\gamma_j,\eta_j,\zeta_j\le CB_0^{\,j}` for all $`j`, with $`C,B_0` depending only on the system.
:::



## Tails over topological types and first-order estimates

We next bound the tails of the sums over topological types, before truncating any expansion. In the sums $`S_{g,p}` and $`T_{g,p}` of 6.10, orient the smaller-complexity component. In $`S_{g,p}` of 6.10 its loss is its complexity plus one; in $`T_{g,p}` its loss is its complexity. Write $`S_{g,p}^{[L]}` and $`T_{g,p}^{[L]}` for the parts of these sums in which the loss is at least $`L`; for $`p=1`, $`S_{g,1}` is the one-marking separating sum of 6.18.

:::lemma_ "lem:tails" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:TL9")
%%%
source := { document := "paper-v3", spans := #[{ page := "81", anchor := "lem:tails", citation := "Lemma C.5", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma C.5 — Tails over topological types.

Fix $`M_0>0`. There are $`C_{M_0},B_{M_0}` such that, for all sufficiently large $`h` and all $`1\le p\le M_0\sqrt h`,

$$`\begin{aligned}
 S_{g,p}^{[L]}&\le C_{M_0}\left(\frac{B_{M_0}(p+L)}h\right)^L,
                  &&2\le L\le\sqrt h,\\
 T_{g,p}^{[L]}&\le C_{M_0}\left(\frac{B_{M_0}(p+L)}h\right)^L,
                  &&1\le L\le\sqrt h,
 \end{aligned}`

 the second bound being used only for $`p\ge2`. The ranges of $`L` start at the stability minima two and one respectively.

Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



:::proof "lem:tails" (uses := "prop:harmonic, eq:TL24, eq:TL27")
Note first that, before specializing to fixed markings, Lemmas {bpref "lem:lower"}[5.3] and {bpref "lem:upper"}[5.6], with zero count and marked count both $`p`, give, using the common local limit 4.16,

$$`\log W_{g,p}=\log\Gamma(h)-h\log A
 +O_{M_0}(\sqrt h\log(h+1)+\log^2(h+1)).`

 Indeed the harmonic probability has displacement $`-p/2=O(\sqrt h)` and lies between $`c_{M_0}/\sqrt h` and one; the terminal factors cost $`O(p\log(p+1)+(p+\log(h+1))\log(h+1))`. For losses between $`\varepsilon h` and half the parent complexity, Stirling entropy dominates this error. Both children have comparable complexity and $`O(\sqrt h)` markings. The $`2^p` subsets cost only $`\mathrm{e}^{O(\sqrt h)}`, so their total is $`O(\mathrm{e}^{-c_\varepsilon h})`. For $`r\le\varepsilon h`, 6.8–6.9 give the complementary ratio at most $`(C/h)^r`. If its marking count is one, insert $`2j_0+1` cusps before raising genus $`j_0` times, then the remaining $`s-1` cusps; this uses $`p\ge2` and avoids a one-marking genus comparison. The same subset/Gamma bound gives $`a_r=[C(p+r)/h]^r`, after absorbing the number of types into $`C^r`. Their consecutive ratio satisfies

$$`\frac{a_{r+1}}{a_r}
 \le \frac{eC(p+r+1)}h
 \le eC\left(\frac{M_0}{\sqrt h}+\varepsilon+\frac1h\right).`

 Choose $`\varepsilon` first, and then a lower bound on $`h` depending on $`M_0`, so this is at most $`1/2`. Thus the sum over $`L\le r\le\varepsilon h` is at most $`2a_L`. The macroscopic tail also fits C.30: for $`1\le L\le\sqrt h`,

$$`\left(\frac{p+L}{h}\right)^L
 \ge \exp\{-\sqrt h\log h\},`

 which eventually exceeds $`\mathrm{e}^{-c_\varepsilon h}`. Enlarging the constants covers the bounded remaining complexities and proves the asserted bound. At $`p=1`, compare to $`T_{g,2}`: two uses of 6.8 and the proved fixed-one-marking cusp ratio bound multiply its summand by at most $`C/j_0` for $`j_0\le g/2`. The loss is $`2j_0` in both sums. This proves C.30, including $`p=1`.
:::



:::lemma_ "lem:first-order" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:TL9")
%%%
source := { document := "paper-v3", spans := #[{ page := "81", anchor := "lem:first-order", citation := "Lemma C.6", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma C.6 — First-order estimates.

Fix $`M_0>0`. For all sufficiently large $`h`, all $`1\le p\le M_0\sqrt h` and all degree tuples,

$$`0\le1-c_{g,p}(\mathbf d)
 \le\min\{1,C_{M_0}D(D+p+1)/h\},\qquad
 |\mathsf C_p(h)-1|+|\mathsf G_p(h)-1|\le C_{M_0}(p+1)/h.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



:::proof "lem:first-order" (uses := "lem:tails, lem:monotone, eq:TL12, eq:TL14")
Subtract the recursion at adjacent degrees, as in the proof of {bpref "eq:TL23"}[6.15], and bound its separating part by Lemma {bpref "lem:tails"}[C.5] at the stability minima. For the profile, each increment costs $`C[(D+p+1)/h+(D+1)(p+2)^2/h^2]`; sum the path. Dilaton sums the child bound against absolute $`b_d` moments, KdV uses degree one and $`T^{[1]}`, and the exact descent gives $`p=1`. These estimates concern the true quantities, in a range of marking counts that grows with $`h`.
:::



## Remainder bounds: proof of Proposition {bpref "prop:hierarchy"}[C.3]

:::proof "prop:hierarchy" (uses := "lem:coefficient-bounds, lem:tails, lem:first-order")
The coefficient bounds are Lemma {bpref "lem:coefficient-bounds"}[C.4], with $`S_j^{2j}\le(D+p+Mj)^{2j}`. It remains to prove the remainder bounds C.19, the path independence and the finiteness of the coefficient rules.

For $`L\ge1` define the normalized remainders

$$`\mathscr E_L=\sup\frac{\bigl|c_{g,p}(\mathbf d)-\sum_{j<L}e_{p,j}(\mathbf d)h^{-j}\bigr|}{S_L^{2L}h^{-L}},
 \qquad
 \mathscr C_L=\sup\frac{\bigl|\mathsf C_p(h)-\sum_{j<L}\mathsf C_{p,j}h^{-j}\bigr|}{S_L^{2L}h^{-L}},`

 and $`\mathscr H_L,\mathscr G_L` in the same way for $`\mathsf G_p` with $`p\ge2` and with $`p=1`; the suprema are over real $`Y\in[0,y_0]`, all stable states with $`h\ge1`, $`p\ge1`, and all degree tuples, invalid tuples having profile zero. We prove by induction on $`L`, in the stage order profile, cusp, genus, descent, that these numbers are finite and at most $`CB^L`; this is C.19.

Large weights. Put $`\delta=S_L^2/h` and fix $`\delta_0\in(0,1]` with $`B_0\delta_0<1/2`. The exact quantities are bounded: $`0\le c\le1`, $`|\mathsf C_p(h)|\le C` by 6.8, $`\mathsf G_p(h)\le1` for $`p\ge2` by 6.9, and $`\mathsf G_1(h)\le C` by the case $`p=1` of {bpref "eq:TL27"}[6.19]. If $`\delta\ge\delta_0`, then Lemma {bpref "lem:coefficient-bounds"}[C.4] and $`S_j^{2j}h^{-j}\le\delta^j` ($`j\le L`) bound the normalized remainder by

$$`\delta^{-L}\Bigl(C+\sum_{j<L}CB_0^{\,j}\delta^{j}\Bigr)
 \le C\delta_0^{-L}\Bigl(1+\sum_{j<L}(B_0\delta_0)^j\Bigr)\le2C\delta_0^{-L},`

 since $`\delta^{j-L}\le\delta_0^{j-L}` for $`j<L`. Invalid-degree parents satisfy $`D\ge h`, hence $`\delta\ge h\ge1`, and lie in this region. In the remaining region $`\delta<\delta_0` one has $`p+ML\le S_L<\sqrt h`, so every marking count that occurs, including those of children, is at most $`p+L+2\le4\sqrt h`: Lemmas {bpref "lem:tails"}[C.5] and {bpref "lem:first-order"}[C.6] apply with $`M_0=4`. Also $`h>M^2L^2/\delta_0`, and shrinking $`\delta_0` once makes Lemma {bpref "lem:first-order"}[C.6] give $`\mathsf C_p(h)\ge1/2` wherever a cusp ratio is inverted. From now on $`\delta<\delta_0`.

Products of exact factors. Every term of the exact adjacent difference, of the exact dilaton identity, of the exact KdV identity and of the exact descent is a product of exact factors: a prefactor $`A^r\prod(h-c_k)^{-1}`, cusp and genus ratios at shifted complexities, and profiles of children. Each exact factor $`F` has, for every $`q\ge1`, a decomposition $`F=T_{<q}F^{\mathrm{form}}+R_F(q)` into its truncated formal series and a remainder, and the formal rule at order $`L` is the truncation of the product of the formal series. The product of exact factors and the truncated formal product differ by the finite identity

$$`\prod_kF_k-T_{<q}\prod_kF_k^{\rm form}
 =R_{F_1}(q)\prod_{k>1}F_k
 +\sum_{j<q}f_{1,j}h^{-j}\Bigl(\prod_{k>1}F_k-T_{<q-j}\prod_{k>1}F_k^{\rm form}\Bigr),`

 applied again to the bracket on the right, and so on. Each resulting term contains exactly one remainder $`R_{F_k}(q_k)`, multiplied by known coefficients of the factors before it and by exact factors after it. For an inverse, with known formal inverse coefficients $`d_j`,

$$`\mathsf C\,T_{<q}(1/\mathsf C)-1
 =\sum_{j<q}d_jh^{-j}\bigl(\mathsf C-T_{<q-j}\mathsf C\bigr),`

 so the remainder of $`1/\mathsf C` is $`1/\mathsf C` times a sum of known coefficients against remainders of $`\mathsf C`.

Bounding one term. Normalize by $`S_L^{2L}h^{-L}`. A known coefficient of order $`j'` of a factor with weight $`S'` is at most $`CB_0^{j'}(S')^{2j'}` by Lemma {bpref "lem:coefficient-bounds"}[C.4], where $`S'\le S_L+\ell`, $`S_L+d+1`, $`S_L+2` or $`S_L` by (a) of Subsection C.5, applied with $`j'\le L`. A remainder $`R_{F_k}(q_k)` of a factor at complexity $`h-c`, $`|c|\le L`, is at most $`\mathscr X_{q_k}(S')^{2q_k}(h-c)^{-q_k}`, where $`\mathscr X` is the error sequence of its type, and $`(h-c)^{-q_k}\le h^{-q_k}\mathrm{e}^{2|c|q_k/h}\le\mathrm{e}^{2\delta_0/M^2}h^{-q_k}` because $`q_k\le L` and $`L^2/h\le\delta_0/M^2`. The exact factors after the remainder are bounded by the constants above. The known shift tails are bounded as follows. If the orders of the known coefficients and of the prefactor sum to $`a=L-q` and the first omitted shift degree is $`q`, the elementary inequality

$$`\sum_{n\ge q}\frac{(a)_n}{n!}x^n\le\frac{(a)_q}{q!}x^q(1-x)^{-a-q}
 \qquad(a\ge1,\ 0\le x<1),`

 which follows from $`(a)_{q+k}=(a)_q(a+q)_k` and $`(q+k)!\ge q!k!`, bounds the tail by $`\binom{L-1}{q}(c/h)^q(1-c/h)^{-L}` with $`c\le L`; after division by $`S_L^{2q}h^{-q}` this is at most $`\mathrm{e}^{2\delta_0/M^2}/q!`, since $`c(L-1)\le L^2\le S_L^2` and $`(1-c/h)^{-L}\le\mathrm e^{2cL/h}` in the small-weight region. The counts, kernel moments and path sums are handled exactly as in the proof of Lemma {bpref "lem:coefficient-bounds"}[C.4], with the same powers of $`S_L`: a linear term supplies $`S_L^2` against the prefactor order one, and a separating term of loss $`r` supplies $`S_L^{r+2}\le S_L^{2r}` ($`r\ge2`) in the profile rule and $`S_L^{r}\le S_L^{2r}` ($`r\ge1`) in the KdV rule.

Forcing terms. Three contributions do not involve the error sequences. The exact topological types of loss $`r>L`, which the formal rule omits, have total mass bounded by C.30 with $`L+1` in place of $`L`; after the kernel sum and the coordinate path their profile contribution is at most $`CD(D+1)(B(p+L)/h)^{L}\le CB^LS_L^{L+2}h^{-L}\le CB^LS_L^{2L}h^{-L}` for $`L\ge2`, and the KdV contribution has no path or pair factor. The difference between the exact kernel sum over $`\ell\le m` and the formal sum over all $`\ell`, and the macroscopic cutoffs in the proof of Lemma {bpref "lem:tails"}[C.5], are $`O(\mathrm{e}^{-ch})`, and $`\mathrm{e}^{-ch}\le C^LL!\,h^{-L}\le C^LS_L^{2L}h^{-L}`. At $`L=1` the normalized remainders are bounded by Lemma {bpref "lem:first-order"}[C.6].

The linear majorant system. Let $`F_0=C/(1-B_0t)` be the majorant of the normalized known coefficients from Lemma {bpref "lem:coefficient-bounds"}[C.4], and $`V=C_{\rm ex}+F_0`, where $`C_{\rm ex}\ge1` bounds all exact factors and $`1/\mathsf C` in the region $`\delta<\delta_0`. Collecting the bounds above, the error sequences $`\mathscr E,\mathscr C,\mathscr H,\mathscr G`, regarded as formal series in $`t`, satisfy coefficientwise

$$`\begin{aligned}
 \mathscr E&\preceq F+K_E\mathscr R,&
 \mathscr C&\preceq F+b\mathscr E,\\
 \mathscr H&\preceq F+b\mathscr E+K_H\mathscr R,&
 \mathscr G&\preceq F+b(\mathscr H+\mathscr C)+K_G\mathscr R,
 \qquad \mathscr R=\mathscr E+\mathscr C+\mathscr H+\mathscr G,
\end{aligned}`

 with the zero-constant kernels

$$`K_E=b\,\mathrm{e}^{bt}\Bigl[tV^2+\sum_{r\ge2}(2r+1)(bt)^rV^{2r}\Bigr],\quad
 K_H=b\,\mathrm{e}^{bt}\sum_{r\ge1}2r(bt)^rV^{2r},\quad
 K_G=b\bigl[\mathrm{e}^{bt}V^3-V(0)^3\bigr],`

 and the forcing

$$`F=\frac{bV^3\mathrm{e}^{bt}}{(1-btV^2)^3}+\frac{b}{1-\delta_0^{-1}t},`

 for a constant $`b` depending only on the constants already fixed. The factors $`2r+1` and $`2r` count the possible positions of the single remainder among the factors of a product with $`r` cusp, at most $`r` genus and at most one profile factor; the term $`b\mathscr E` in the second and third lines is the current-order remainder of the profile, which enters the dilaton and KdV rules without a prefactor $`t`, and $`b(\mathscr H+\mathscr C)` plays the same role in the descent. The first summand of $`F` dominates the shift tails, the omitted topology and the cutoff terms, each of which is a product of at most $`2r+1` known or exact factors times $`C^q/q!` or $`C^LL!/S_L^{2L}`; the second summand dominates the region $`\delta\ge\delta_0`.

Induction. Substituting the first line of C.33 into the others gives $`\mathscr R\preceq A_0F+A_0(K_E+K_H+K_G)\mathscr R` for a constant $`A_0`. Since $`K_E+K_H+K_G` has no constant term, the coefficient of $`t^L` on the right involves $`\mathscr R_j` only for $`j<L`. Let $`\mathscr R_*=A_0F/(1-A_0(K_E+K_H+K_G))`, a series with nonnegative coefficients, analytic near $`t=0`. If $`\mathscr R_j\le[\mathscr R_*]_j` for all $`j<L`, then $`\mathscr R_L\le[A_0F+A_0(K_E+K_H+K_G)\mathscr R_*]_L=[\mathscr R_*]_L` by monotonicity of series with nonnegative coefficients; the case $`L=1` is the base estimate. Cauchy’s estimate for $`\mathscr R_*` gives $`\mathscr R_L\le CB^L` and proves C.19; no infinite inverse-complexity series is evaluated. For each fixed degree tuple, two coordinate paths give asymptotic expansions of the same ratio, and uniqueness of asymptotic coefficients as $`g\to\infty` proves the asserted path independence.

Finiteness of the coefficient rules. It remains to justify the finite coefficient rule and polynomial bounds used above. At each fixed order, the degree lattice admits a finite boundary stratification: each coordinate is either one of finitely many low integers or lies above that threshold. The coefficients are polynomial on every stratum. A merger has an exceptional low child degree only when $`d_i+d_j+\ell-1` is bounded; otherwise polynomial summation uses finitely many $`w` moments. For a nonseparating pair, separate bounded $`u`, bounded $`v`, and the interior. The interior sum is a Faulhaber polynomial in $`u+v`; overlap of the two boundary ranges adds finitely many exceptions. In a retained split, dimension bounds $`u` and $`\mathbf d_I` by $`3j+s-2`, so the same argument applies to the large child. Summing the coordinate path preserves this class. One admissible (not optimal) choice of the low-degree thresholds is given by $`b_0^{\rm deg}=0` and $`b_K^{\rm deg}=2b_{K-1}^{\rm deg}+2K+4`. The adjacent coefficient has degree at most $`2K-1`, and its path sum has degree at most $`2K`, proving the claimed growth. The single-degree specialization in dilaton is eventually polynomial; its sum uses finitely many signed $`b_d` moments and low $`b_d`. Exact small amplitudes are finite polynomials in the $`\theta_\ell`. These facts reduce every displayed infinite sum in the coefficient algorithm to finite kernel data. The common analytic disks and removable critical normalization give analyticity of that data throughout $`[0,y_0]`.
:::



## Determining the constants at the pure-ψ endpoint

To integrate the transport equation to all orders, we need the value of every coefficient at the pure-$`\psi` endpoint, with constants controlled as the order grows. This subsection supplies these values from the Painlevé I asymptotics and then proves Theorem {bpref "thm:full-expansion"}[8.2].

Invert the cusp expansion and write, at each fixed order,

$$`\frac1{\mathsf C_p(h)}
 =1+\frac{\beta_p}h+\sum_{j=1}^K\frac{\gamma_{p,j}}{h^{j+1}}
      +O_{p,K}(h^{-K-2}).`

 Here $`\gamma_{p,1}=\gamma_p`. The exact endpoint identity following C.12 gives $`1/\mathsf C_p(h;y_0)=1-p/(5h)`. Uniformity and uniqueness of successive coefficients imply

$$`\gamma_{p,j}(y_0)=0\quad(j\ge1),\qquad
 \gamma_{p,j}/(Ar)\ \hbox{is analytic at }y_0.`

 Analyticity follows from the finite coefficient rules, not from remainder estimates. Division by the simple zero of $`Ar` is a bounded operation on a fixed smaller complex neighborhood: write a vanishing function as $`(Y-y_0)\int_0^1 f'(y_0+t(Y-y_0))\,\mathrm{d}t` and apply Cauchy’s bound once on the larger neighborhood. No successive shrinkage in order occurs.

We need a quantitative version of the pure-$`\psi` endpoint input. Use the conventions of Garoufalidis–Its–Kapaev–Mariño \[27\]: $`-u''/6+u^2=Z`, zero-instanton coefficients $`u_{g,0}`, $`\mathfrak a=8\sqrt3/5`, $`\nu_g=2g-1/2` and $`S_1=-i3^{1/4}/(2\sqrt\pi)`. Put

$$`Z_g=\frac{\pi i}{S_1}
       \frac{\mathfrak a^{\nu_g}u_{g,0}}{\Gamma(\nu_g)}.`

 The Borel representation of Costin–Costin–Huang \[18\] Theorem 2 makes the coefficient formula in \[27\] Section 2.3 quantitative, as follows. Set $`\rho=6^{-1/5}\mathrm{e}^{i\pi/5}`; $`y(Z_c)=\rho^2u(\rho Z_c)` satisfies $`y''=6y^2+Z_c`. Their Boutroux coordinate is $`\xi=\mathfrak a Z^{5/4}`, and the normalized remainder is $`u(Z)/\sqrt Z-1+4/(25\xi^2)`. Their variable $`x` is our $`\xi`, and their unknown $`h(x)` is this normalized remainder. The adjacent GIKM solutions $`u_1,u_0` have sectors $`(-2\pi/5,6\pi/5)` and $`(-6\pi/5,2\pi/5)` respectively. Their normalized remainders are $`O(\xi^{-4})` on $`+i\infty` and $`-i\infty`. Thus the respective lateral constants in the exact Borel representation vanish: multiplying by $`\mathrm{e}^\xi\xi^{1/2}` gives zero on those rays. This identifies the lateral Borel sums with the solutions themselves, not merely with their formal expansions.

The Borel transform at its first positive singularity has the form $`S(1-s)^{-1/2}\alpha(s)+\beta(s)`, where $`\alpha,\beta` are analytic near one and $`\alpha(1)=1` \[18\] Proposition 3(i). Keep its multiplier symbolic and normalize the jump between the two solutions in the convention of \[27\]:

$$`\mathfrak J(\xi)=
 \frac{u_1(Z)-u_0(Z)}{-S_1\mathrm{e}^{-\xi}Z^{-1/8}},\qquad
 \mathfrak J(\xi)\longrightarrow1.`

 Choose a fixed small $`r>0` and angles $`\pm\phi` so $`(1+r)\cos\phi>1+r/2`. Deform only the finite initial parts of the two Laplace rays into a local Hankel contour about $`[1,1+r]` and compact joining arcs on $`|s|=1+r`. The infinite ray tails are kept unchanged. The analytic continuation and weighted $`L^1` estimates of \[18\] Lemma 17(c),(f) bound these outer parts by $`C\mathrm{e}^{-(1+\varepsilon)\xi}`, with constants independent of Taylor order. The local analytic term has no jump. Cauchy’s estimate on $`|s-1|\le2r` bounds the degree-$`L-1` remainder of $`\alpha(1+t)` by $`C(2r)^{-L}t^L`. Its normalized Laplace integral is bounded by $`CB^L\Gamma(L+1/2)\xi^{-L}`. Extending the retained polynomial integrals from $`r` to infinity obeys the same bound; the outer term $`O(\sqrt\xi \mathrm{e}^{-\varepsilon\xi})` is at most $`CB^LL!\xi^{-L}`. Consequently, for all $`L\ge1` and real $`\xi\ge\xi_0`,

$$`\left|\mathfrak J(\xi)-\sum_{j<L}v_j\xi^{-j}\right|
       \le CB^LL!\xi^{-L},\qquad v_j=\mathfrak a^ju_{j,1}.`

 No numerical Stokes multiplier from the other normalization is used.

The first coefficient is $`v_1=-1/8`, and we derive it here because it determines the first correction at the endpoint. The difference $`u_1-u_0` is exponentially small and satisfies the linearization $`(u_1-u_0)''=12u_0(u_1-u_0)` of $`-u''/6+u^2=Z` up to a term quadratic in $`u_1-u_0`, which is $`O(\mathrm{e}^{-2\xi})` and does not affect the coefficients $`v_j`. Here $`12u_0=12Z^{1/2}-Z^{-2}/4+O(Z^{-9/2})`, because $`u_{1,0}=-1/48`. Put $`f=Z^{-1/8}\mathrm{e}^{-\xi}`. Since $`\xi'=2\sqrt3Z^{1/4}` and $`\xi''=(\sqrt3/2)Z^{-3/4}`,

$$`\frac{f''}f=\Bigl(\frac1{8Z}+\xi'\Bigr)^2+\frac1{8Z^2}-\xi''
 =12Z^{1/2}+\frac9{64}Z^{-2};`

 the terms of order $`Z^{-3/4}` cancel, which is why the prefactor is $`Z^{-1/8}`. Writing $`u_1-u_0=-S_1f\mathfrak J` and dividing the linearized equation by $`-S_1f` gives $`(f''/f)\mathfrak J+2(f'/f)\mathfrak J'+\mathfrak J''=12u_0\mathfrak J`. The local Laplace representation above gives the expansion of $`\mathfrak J` in a sector about the positive ray; Cauchy’s estimate therefore permits differentiation of its remainder on a smaller sector. With $`\mathfrak J=1+v_1\xi^{-1}+O(\xi^{-2})` one has $`\mathfrak J'=-v_1\xi'\xi^{-2}+O(Z^{-7/2})=-(2\sqrt3v_1/\mathfrak a^2)Z^{-9/4}+O(Z^{-7/2})`, so $`2(f'/f)\mathfrak J'=-2\xi'\mathfrak J'+O(Z^{-13/4})=(24v_1/\mathfrak a^2)Z^{-2}+O(Z^{-13/4})`, while $`\mathfrak J''=O(Z^{-13/4})`. Comparing the coefficients of $`Z^{-2}` gives $`9/64+24v_1/\mathfrak a^2=-1/4`, that is $`v_1=-25\mathfrak a^2/1536=-1/8`, since $`\mathfrak a^2=192/25`. Equivalently $`u_{1,1}=-5/(64\sqrt3)`.

The exact coefficient contour in \[27\] Section 2.3 expresses $`u_{g,0}` as a circle integral and deforms it onto the five rays $`\arg t=2\pi k/5`, $`k=0,\pm1,\pm2`; the symmetry of the tritronquée solutions reduces their sum to five times the positive ray \[27\] equations (2.25) and (2.29):

$$`u_{g,0}=-\frac5{2\pi i}\int_\rho^\infty t^{5g-2}
        \bigl(u_1(t^2)-u_0(t^2)\bigr)\,\mathrm{d}t+r_g(\rho),
 \qquad |r_g(\rho)|\le C\rho^{5g},`

 for a fixed $`\rho`, large enough for \[27\] and such that $`\xi_0=\mathfrak a\rho^{5/2}` is at least the threshold in the jump expansion above. Put $`\xi=\mathfrak at^{5/2}`, so that $`t^{5g-9/4}\,\mathrm{d}t=\tfrac25\mathfrak a^{-\nu_g}\xi^{\nu_g-1}\,\mathrm{d}\xi`, and write $`u_1-u_0=-S_1\mathrm{e}^{-\xi}t^{-1/4}\mathfrak J(\xi)`. The factor $`5\cdot\tfrac25` cancels the $`2` in $`2\pi i`, and the definition of $`Z_g` gives exactly

$$`Z_g=\frac1{\Gamma(\nu_g)}\int_{\xi_0}^{\infty}
        \mathrm{e}^{-\xi}\xi^{\nu_g-1}\mathfrak J(\xi)\,\mathrm{d}\xi
       +O\!\left(\frac{D^g}{\Gamma(\nu_g)}\right);`

 the error term is $`(\pi i/S_1)\mathfrak a^{\nu_g}r_g(\rho)/\Gamma(\nu_g)`. Applying the jump remainder with $`L=K+1\le g/2` gives $`CB^LL!\Gamma(\nu_g-L)/\Gamma(\nu_g)\le CB^LL!g^{-L}`. The omitted low integrals and inner circle are $`O(\mathrm{e}^{-c g\log g})` uniformly for $`K\le c_0g`, with $`c_0` small. For the low integrals, bound the finite sum by $`C\xi_0^{\nu_g}\sum_{j<L}B^jj!\xi_0^{-j}/\Gamma(\nu_g)` and use Stirling’s lower bound. Thus the finite falling-factorial expansion of $`Z_g` has a Gevrey-1 remainder. Re-expansion in $`g^{-1}` preserves it:

$$`\frac{\Gamma(\nu_g-j)}{\Gamma(\nu_g)}
 =(2g)^{-j}\prod_{a=1}^j\left(1-\frac{a+1/2}{2g}\right)^{-1}.`

 Cauchy on radius $`1/(D(K+1))` for the product, followed by $`j!(K+1)^{K+1-j}\le \mathrm{e}^{K+1}(K+1)!`, bounds the total omitted inverse-genus powers by $`CB^{K+1}(K+1)!g^{-K-1}`.

The exact identity of Itzykson–Zuber \[43\] equation (6.10) is

$$`\langle\tau_2^{3g-3}\rangle_g
 =\frac{2^g(3g-3)!}{(5g-5)(5g-3)}\,\phi_g,\qquad g\ge2,`

 where $`\phi(t)=\sum_{g\ge0}\phi_g t^{(1-5g)/2}`, $`\phi_0=-1`, satisfies $`\phi''/3+\phi^2=t`. The substitution $`\phi(t)=-2^{1/5}u(2^{-2/5}t)` gives exactly $`\phi_g=-2^g u_{g,0}`. Combined with the expansion of $`Z_g` above, this gives, in the normalization of {bpref "eq:H4"}[4.3] and for every fixed $`K`,

$$`\pi C_g(2^{3g-3})=1+\sum_{j=1}^K d_jg^{-j}+O_K(g^{-K-1}).`

 The leading constant is also independently given by \[32\] Theorem 1. More precisely, put $`h_0=2g-2`, $`h=h_0+p`, $`a_*=2/15`, and define the exact normalized endpoint

$$`E_{g,p}=\frac{\pi\overline U_{g,p}(0^p;y_0)}
 {\Gamma(h)4^{-g}a_*^{-h}\sqrt{a_*/(\pi h)}}.`

 For $`p\ge1` this is the limit of $`\pi\Phi_g^{(p)}/\mathcal J_{g,p}`; at $`p=0` it is defined by the same exact pure-$`\psi` expression. String and dilaton give $`E_{g,p+1}/E_{g,p}=(h_0+4p/5)(h_0+p)^{-1}
\sqrt{(h_0+p+1)/(h_0+p)}`. The base conversion gives exactly $`\overline U_{g,0}(y_0)=-108^gu_{g,0}/[27(5g-5)(5g-3)]`. Substitution therefore proves

:::proposition "eq:FE14" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H7")
%%%
source := { document := "paper-v3", spans := #[{ page := "86", anchor := "eq:FE14", citation := "Equation C.37", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition C.37 — Quantitative endpoint normalization.

In the setup and notation of this section, the paper defines or asserts:



$$`\begin{aligned}
 E_{g,p}&=Z_g\,\frac{\Gamma(h_0+3/2)}{\Gamma(h_0)h_0^{3/2}}
             \frac{R_p(h_0)}{1+4/(5h_0)},\\
 R_p(h_0)&=\sqrt{1+p/h_0}\prod_{i=0}^{p-1}
                       \frac{1+4i/(5h_0)}{1+i/h_0}.
 \end{aligned}`


:::



This identity is exact for $`g\ge2,p\ge0`, with the empty product one.

For fixed $`p`, the endpoint value and its logarithm therefore have Gevrey-1 remainders through order $`K\le c_pg`. It remains to treat the Gamma factor; for fixed $`\alpha>0`,

$$`\log\frac{\Gamma(h_0+\alpha)}{\Gamma(h_0)h_0^\alpha}
 =\int_0^\infty \mathrm{e}^{-h_0t}
 \left[\alpha-\frac{1-\mathrm{e}^{-\alpha t}}{1-\mathrm{e}^{-t}}\right]\frac{\mathrm{d}t}{t}.`

 The kernel is analytic at zero on a fixed disk and bounded outside a small positive interval. Its global Taylor remainder is bounded by $`CB^Lt^{L-1}`, giving $`CB^L(L-1)!h_0^{-L}` after integration. The finite insertion factors have convergent expansions at $`h_0^{-1}=0`. Finite shifts from $`h_0` to $`h=h_0+p` preserve the factorial error by the same Cauchy estimate for rational products just used above. For logarithms, exponentials and inverses, take the degree-$`K` polynomial on radius $`1/(D(K+1))`; its unit or zero-constant part stays bounded away from the relevant singularity. Cauchy’s tail and the bounded real derivative of the composed function preserve the remainder bound. This proves the stated endpoint bound, including its log coefficients $`a^*_{p,j}`, defined by $`\log E_{g,p}\sim\sum_{j\ge1}a^*_{p,j}h^{-j}`. At first order, {bpref "eq:FE14"}[C.37], the value $`v_1=-1/8` derived above, and $`\nu_g-1=h_0+1/2` give

$$`a^*_{p,1}=-\frac18+\frac38-\frac45+\frac p2-\frac{p(p-1)}{10}
 =\frac{-2p^2+12p-11}{20}=t_p,`

 the constant in {bpref "eq:ST13"}[8.1]; replacing $`h_0` by $`h=h_0+p` does not change the first-order coefficient.

In particular the first coefficient in C.36 is $`d_1=-2/9`. Indeed, at $`p=0` the definition of $`E_{g,0}` and {bpref "eq:PF13"}[7.14] give

$$`\pi C_g(2^{3g-3})=\frac{E_{g,0}}{N_{h_0}},\qquad
 N_{h_0}=\frac{\mathcal M_{g,0}(y_0)}
          {\Gamma(h_0)4^{-g}a_*^{-h_0}/\sqrt{2\pi h_0v}}
     =\sqrt{2\pi h_0v}\,\Pr(S_{h_0}=3h_0/2),\qquad v=\frac{15}4,`

 where $`S_{h_0}` is the sum of $`h_0` independent copies of the geometric law with generating function $`(2/5)/(1-3w/5)`; this is the normalized negative-binomial coefficient of Theorem {bpref "thm:first-correction"}[8.1] at displacement zero, so $`N_{h_0}=1-19/(180h_0)+O(h_0^{-2})`. On the other side, $`Z_g=1+v_1\Gamma(\nu_g-1)/\Gamma(\nu_g)+O(g^{-2})=1-1/(8h_0)+O(h_0^{-2})`, because $`\nu_g-1=h_0+1/2` and $`v_1=-1/8`; $`\Gamma(h_0+3/2)/(\Gamma(h_0)h_0^{3/2})=1+3/(8h_0)+O(h_0^{-2})`; and $`(1+4/(5h_0))^{-1}=1-4/(5h_0)+O(h_0^{-2})`. Hence, by {bpref "eq:FE14"}[C.37],

$$`\pi C_g(2^{3g-3})
 =1+\frac1{h_0}\Bigl(-\frac18+\frac38-\frac45+\frac{19}{180}\Bigr)+O(h_0^{-2})
 =1-\frac4{9h_0}+O(h_0^{-2})
 =1-\frac2{9g}+O(g^{-2}),`

 since $`h_0=2g-2`. This value agrees with the expansion recorded by Guo, Yang and Zagier \[32\] equation (25), which rests on the same Painlevé I input; it is used in the proof of Theorem {bpref "thm:first-correction"}[8.1].

Define

$$`a_{p,j}(Y)=a^*_{p,j}-\int_Y^{y_0}\frac{\gamma_{p,j}(v)}{A(v)r(v)}\,\mathrm{d}v,
 \qquad
 \mathcal L_{p,j}(Y)=[t^j]\exp\!\left(\sum_{i=1}^j a_{p,i}(Y)t^i\right).`

 Proposition {bpref "prop:hierarchy"}[C.3], inversion and the bounded division and integration above give common-domain bounds $`\|a_{p,j}\|+\|\mathcal L_{p,j}\|\le C_p\mathfrak B_p^j(j!)^2`. For formal exponentiation this follows also by Cauchy on the finite log polynomial at radius $`1/(Dj^2)`. The first coefficient is $`\mathcal L_{p,1}=\mathcal L_p`. These are the coefficients in Theorem {bpref "thm:full-expansion"}[8.2].

:::proof "thm:full-expansion" (uses := "prop:hierarchy, eq:FE14, ext:iz, ext:painleve-contour, ext:painleve-borel")
We first expand the logarithmic derivative, then fix its integration constant near the endpoint. After integration, exponentiation gives the claimed expansion. The extra orders retained below compensate for the error accumulated near the zero of $`Ar`.

Put $`F_g(Y)=\log(\pi\Phi_g^{(p)}/\mathcal J_{g,p})`. For fixed $`p` the inverse cusp ratio is bounded, and the finite inverse identity in Proposition {bpref "prop:hierarchy"}[C.3] transfers its remainder to $`1/\mathsf C_p` with error $`CB^N(N!)^2h^{-N}`, for $`N\le c\sqrt h`. The exact dilaton and 7.11 give

$$`F'_g=\frac{h}{Ar}(1/\mathsf C_p-1-\beta_p/h).`

 For $`L=K+1`, use $`N=L+2=K+3`, retaining $`\gamma_{p,j}` through $`j=L`. Its unknown derivative error is $`CB^{L+2}((L+2)!)^2h^{-L-1}/(Ar)`. Choose $`\delta_*=h^{-L-1}`. The positive comparison 7.16 and the exact first equality of 7.17 change $`F_g` from its endpoint value by at most $`Ch\delta_*=Ch^{-L}` on this strip. The leading harmonic approximation in the second equality of 7.17 is not used. The endpoint expansion proved above supplies the value at the matching point. The bounded coefficient derivatives from C.35 show that the whole retained coefficient sum changes by $`O(\delta_*/h)` there, after choosing the square-root order constant small.

Integrate backwards from $`y_0-\delta_*`. Since $`Ar` has a simple zero, the unknown error costs at most

$$`CB^{L+2}((L+2)!)^2h^{-L-1}[1+(L+1)\log h].`

 Relative to $`(L!)^2h^{-L}`, its extra factor is a fixed exponential base times $`(L+2)^4[1+(L+1)\log h]/h`, bounded by another fixed exponential in $`L`. Indeed $`L\le c\sqrt h` implies $`h\ge c^{-2}L^2`; the decrease of $`\log h/h` for $`h\ge e` bounds this factor by $`C(L+2)^3\log(L+2)\le C D^L`. The bounded exceptional values of $`h,L` are absorbed into $`C`. The known coefficients integrate to C.38. Discarding the last term $`a_{p,L}h^{-L}` proves the asserted log error, on both the strip and its complement. Choose $`c_p` smaller and $`h_p` larger once so that the inverse-cusp remainder estimate remains valid through order $`K+3`. The endpoint range is linear in $`h`.

Finally the finite degree-$`K` log polynomial is uniformly bounded on $`|t|\le1/(D(K+1)^2)`. Cauchy’s exponential tail at $`t=1/h` is $`C[D(K+1)^2/h]^{K+1}\le C(\mathrm{e}^2D)^{K+1}((K+1)!)^2h^{-K-1}`. At the real evaluation point the polynomial is $`O(h^{-1})` and the function $`F_g` itself is bounded by Proposition {bpref "prop:prefactor"}[7.1]. Thus the exponential is Lipschitz on the required bounded interval and transfers the error bound for the logarithm to 8.3. Choosing $`K=\lfloor c'_p\sqrt h\rfloor` after the final error base, with $`\mathfrak B_p(c'_p)^2<1`, gives the exponential upper error.
:::
