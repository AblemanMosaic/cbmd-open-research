# Public verification dossier for the genus-two ECH calculation

Prepared by Adam Ableman Mazurk with AI assistance  
Released as a provisional argument for verification, correction, or disproof  
27 October 2026

## Purpose and present status

This dossier presents a proposed extension of Chen's explicit filtered ECH calculation to genus two, Euler number \(e=-b\) with \(b\ge3\), and torsion representatives \(\Gamma=1,2\), for public verification or disproof. These are the two classes outside the range \(\Gamma=0\) or \(\Gamma>2g-2\) in Chen's stated theorem.

The proposed extension uses explicit monomial representatives for the small symmetric products, retains a triangular cap/fill pairing, and solves for \(U\) without requiring that pairing to be diagonal. A written argument now runs through finite filtered bases, the \(U\)-recurrence, continuation, and the direct limit. Exact computations corroborate the algebra. The geometric application is the central subject of this public verification dossier.

The first question is whether the cap/fill maps and source formulas apply to the chosen low-sector representatives with the asserted signs, filtration, and continuation identifications. If that application is valid, the remaining linear algebra gives a concrete filtered formula. If it fails, a precise missing hypothesis or counterexample would be equally valuable.

The research was developed with substantial AI assistance, including source interpretation, mathematical drafting, and code. It has not received an independent specialist review or proof-assistant verification. The appropriate status is a proposed written proof for criticism. Prior statements in the working notes that the rational line was exhausted describe the extent of the attempted argument; they should not be read as specialist certification of its geometric premises.

## 1 The setting and the proposed contribution

Let \(Y_b\to\Sigma_2\) be the prequantization circle bundle over a closed genus-two surface, with Euler number \(e=-b\), \(b\ge3\). Work over \(\mathbb Q\), and take the standard representative

\[
\Gamma\in\{1,2\}\subset\mathbb Z/b\mathbb Z.
\]

Write

\[
n_d=bd+\Gamma,\qquad d\ge0.
\]

The integer \(d\) labels a multiplicity sector: orbit sets in that sector have total multiplicity \(n_d\).

The proposed contribution is an explicit description of the cap classes and their \(U\)-action at a sequence of action cutoffs containing complete sectors. It is narrower than a formula at every action level, an orbit-by-orbit identification of cap representatives, or a computation of a full persistence module.

The principal proposed statement is:

> For genus two, \(e=-b\), \(b\ge3\), and \(\Gamma=1,2\), the raw cap images of the chosen symmetric-product monomial bases form bases of filtered rational ECH at sufficiently small perturbations and the specified complete-sector cutoffs. In these bases, \(U\) is given by the recurrence in Section 6. The continuation maps preserve these raw classes, so the recurrence extends to the ECH direct limit.

The algebraic direct limit of this recurrence consists of sixteen \(U\)-towers. Its geometric identification and its exact relation to existing Floer computations are included among the questions for review.

## 2 Relationship to the existing literature

Chen's v2 paper is the closest source. Its explicit basis and \(U\)-formula use hypotheses that omit \(\Gamma=1,2\) when \(g=2\). His Remark 1.5 already proposes extending the pairing method beyond the stated range. The general strategy is therefore inherited. His bulk recurrence also agrees, after genus-two specialization, with the stable-sector formula used here. [Chen, Theorem 1, Lemma 5.11, Remark 1.5](https://arxiv.org/html/2608.16625v2).

Nelson and Weiler provide the orbit, grading, and direct-limit framework and credit Farris's dissertation as a foundation. Their direct system treats every \(\Gamma\), while their coefficients are \(\mathbb F_2\). The present rational application follows the formal-properties argument discussed by Chen. [Nelson and Weiler, Proposition 3.2 and Theorem 7.1](https://arxiv.org/html/2007.13883v3).

The symmetric-product rings are classical input. The small-degree case must use the appropriate unstable presentation; Gugnin explains the correction to the usual Macdonald statement in that range. [Gugnin, Theorem 2 and Section 3](https://arxiv.org/html/1502.01862v3).

We have not established priority for the proposed extension. Chen identifies existing Heegaard-Floer computations and equivalences as another route to his stated theorem. That observation alone does not prove the exact sixteen-tower statement for the two excluded classes here. A comparison must match the torsion class, spin-c structure, orientation, coefficient field, and Floer flavor. A pointer to such a comparison would be valuable.

The possible mathematical addition is therefore the explicit treatment of the initial sectors and the resulting filtered formula in these coordinates. The existence of an off-diagonal block, triangular elimination, classical symmetric-product algebra, and the general pairing strategy are not proposed as new invariants or methods.

## 3 Coordinates and the symmetric product algebra

Set

\[
E=\Lambda_{\mathbb Q}(a_1,b_1,a_2,b_2),\qquad
\theta=a_1b_1+a_2b_2,\qquad
\omega=a_1b_1a_2b_2.
\]

The exterior order is \(a_1,b_1,a_2,b_2\), the generators have degree one, and \(\deg u=2\). Thus \(\theta^2=2\omega\).

Let \(H_n=H^*(\operatorname{Sym}^n\Sigma_2;\mathbb Q)\), with chosen normal-form map \(\rho_n\). For \(n\ge3\), use

\[
H_n=E[u]/(R_n),\qquad
R_n=u^{n-1}-\theta u^{n-2}+\omega u^{n-3}.
\]

An additive basis is

\[
B_n=\{u^az:0\le a\le n-2,\ z\text{ an ordered exterior monomial}\}.
\]

Its size is \(16(n-1)\). The two unstable bases are:

\[
B_1=\{1,a_1,b_1,a_2,b_2,u\},
\]

and

\[
\begin{aligned}
B_2=\{&1;\ a_1,b_1,a_2,b_2;\ u;\\
&a_1b_1,a_1a_2,a_1b_2,b_1a_2,b_1b_2,a_2b_2;\\
&ua_1,ub_1,ua_2,ub_2;\ u^2\}.
\end{aligned}
\]

Their sizes are six and seventeen. In \(H_1\), \(a_ib_i=u\), cross pairs vanish, and degrees above two vanish. In \(H_2\), a triple is \(u\) times its unpaired generator, with the exterior sign; \(ua_ib_i=\omega=u^2\); \(u\) times a cross pair vanishes; and degrees above four vanish.

The integration functional has

\[
\int_{H_n}u^{n-k}\prod_{i\in S}a_ib_i=1,
\qquad |S|=k\le\min(2,n),
\]

and is zero on unmatched exterior monomials and outside degree \(2n\). Write \(G_n\) for its Gram matrix on \(B_n\). These are unimodular in the corresponding integral presentations.

There is a crucial distinction between a polynomial insertion and its cohomology normal form. The raw cap construction below acts on selected elements of \(\mathbb A(\Sigma)=\mathbb Q[u]\otimes E\), identifying the source's homological insertion algebra with these generators by the chosen conventions. Writing \(F_d(y)\) for the image of a basis representative does not make \(F_d\) an \(E[u]\)-module map from the quotient \(H_{n_d}\). In an off-diagonal cap/fill pairing, one cannot replace an insertion by a cohomologically equal polynomial without justification.

## 4 The proposed geometric pairing

Use Chen's cap \(X_+\), filling \(X_-\), their perturbations, and the homology orientations of his equation (2.5). In the glued ruled surface, write

\[
F=[S^2],\qquad S=[\Sigma_+],\qquad
F^2=0,\quad F\cdot S=1,\quad S^2=b.
\]

Choose relative classes \(A_\pm(d)\) with

\[
A_\pm(d)\cdot\Sigma_\pm=n_d.
\]

For the chosen polynomial representatives, define

\[
F_d^\varepsilon(y)=
\operatorname{ECH}(X_+,\omega_+^\varepsilon,A_+(d))(y),
\]

\[
\Psi_m^\varepsilon(x\otimes-)=
\operatorname{ECH}(X_-,\omega_-^\varepsilon,A_-(m))(x\otimes-).
\]

The intended application of composition uses a unique glued class

\[
A_{d,m}=(mb+\Gamma)F+(d-m)S,
\]

with

\[
A_{d,m}\cdot F=d-m,
\]

\[
I_{d,m}=(d-m+1)(d+m)b-2(d-m)+2\Gamma(d-m+1).
\]

The proposed raw pairing identity is

\[
\Psi_m^\varepsilon(x\otimes F_d^\varepsilon(y))
=\operatorname{Gr}(X,A_{d,m},xy)
=L_{d-m,I_{d,m}}(xy).                       \tag{1}
\]

Here \(L_{s,I}\) vanishes outside degree \(I\). For \(s\ge0\), its values on a degree-matching ordered monomial are:

| Exterior factor | Value |
|---|---:|
| \(1\) | \((s+1)^2\) |
| \(a_1b_1\) or \(a_2b_2\) | \(s+1\) |
| \(\omega\) | \(1\) |
| An unmatched exterior monomial | \(0\) |

Wedge signs are applied before evaluating the table. For \(s<0\), the proposed geometric justification of zero is the negative intersection \(A_{d,m}\cdot F<0\), rather than a convention imposed by the model.

For finite depth \(D\), define matrices on the chosen bases by

\[
P_{m,d}(x,y)=L_{d-m,I_{d,m}}(xy),\qquad
Q_{m,d}(x,y)=L_{d-m,I_{d,m}}(xuy).
\]

The further geometric claim is

\[
\Psi_m^\varepsilon(x\otimes UF_d^\varepsilon(y))
=Q_{m,d}(x,y).                              \tag{2}
\]

It requires that the \(u\) insertion agrees with the geometric point action, with the same coefficient and orientation conventions.

The source route proposed for (1) and (2) is Chen's Theorem 2.2, Lemma 5.1, and Theorem 4.2. The open question is whether that route applies to all the selected low-sector insertions without an implicit use of the restricted basis theorem.

One foundational dependency deserves explicit attention. Chen's discussion after Theorem 2.2 attributes the filtration and holomorphic-current properties for strong cobordisms to an extension of the exact-cobordism analysis, referring to unpublished work of Hutchings. The present argument accepts that formalism as used by Chen; it does not independently supply that extension. Whether it is an adequate available input here is part of the review. [Chen, discussion following Theorem 2.2](https://arxiv.org/html/2608.16625v2).

## 5 The single off diagonal block

On the finite sum

\[
V_D=\bigoplus_{d=0}^D H_{n_d},
\]

the algebraic pairing matrix \(P_D\) is upper triangular, with diagonal \(G_{n_d}\). Its only nonzero off-diagonal block is

\[
C=P_{0,1}.
\]

Thus, for \(D\ge1\),

\[
P_D=
\begin{pmatrix}
G_\Gamma&C&0&\cdots\\
0&G_{b+\Gamma}&0&\cdots\\
0&0&G_{2b+\Gamma}&\cdots\\
\vdots&\vdots&\vdots&\ddots
\end{pmatrix}.
\]

Put \(h=b+\Gamma-2\). The eight entries of \(C\) are:

| Filling row | Cap column | Coefficient |
|---|---|---:|
| \(u^{\Gamma-1}\) | \(u^h\omega\) | \(1\) |
| \(u^{\Gamma-1}a_1\) | \(u^hb_1a_2b_2\) | \(1\) |
| \(u^{\Gamma-1}b_1\) | \(u^ha_1a_2b_2\) | \(-1\) |
| \(u^{\Gamma-1}a_2\) | \(u^ha_1b_1b_2\) | \(1\) |
| \(u^{\Gamma-1}b_2\) | \(u^ha_1b_1a_2\) | \(-1\) |
| \(u^\Gamma\) | \(u^{h-1}\omega\) | \(1\) |
| \(u^\Gamma\) | \(u^ha_1b_1\) | \(2\) |
| \(u^\Gamma\) | \(u^ha_2b_2\) | \(2\) |

This block has rank six, including after reduction modulo two as an algebraic matrix. Since every diagonal block is invertible, \(P_D\) is invertible at every finite depth.

The location of this block has a structural degree explanation inside the model. When the sector separation (s=d-m\) is at least two, the required pairing index exceeds the largest available product degree. When (s=1\) and (m\ge1\), the stable basis bound still leaves the largest product degree two below the required index. Only (s=1,m=0\) uses the unstable initial bases (B_1,B_2\), where the required degree becomes reachable. A second-reader finite audit confirms exactly this one eight-entry block for (b\in\{3,4,5,6,7,8,10,12\}\), \(\Gamma\in\{1,2\}\), through depth (D=6\). This is a statement about the algebraic model, not the unresolved geometric identification.

The smallest geometric witness proposed in the working notes is

\[
(b,\Gamma,m,d,x,y)=(3,1,0,1,1,u^2\omega).
\]

Its glued class is \(F+S\), its index is eight, and the insertion has degree eight. The proposed specialization gives

\[
\Psi_0^\varepsilon(1\otimes F_1^\varepsilon(u^2\omega))=1.
\]

This single entry is a useful first diagnostic for the source interpretation.

The block \(C\) depends on the raw coordinates. Indeed, let \(R:V_1\to V_0\) have matrix \(G_\Gamma^{-1}C\), extend it by zero, and put \(S_0=I-R\). Then

\[
R^2=0,\qquad P'=PS_0=\operatorname{diag}(G_{n_0},\ldots,G_{n_D}),
\]

\[
Q'=QS_0,\qquad U'=S_0^{-1}US_0.
\]

This is a valid integral change of coordinates. It preserves cumulative multiplicity sectors, though no claim is made that it preserves every finer action level. Deleting \(C\) while keeping \(Q\) fixed is a different operation and gives incorrect columns.

## 6 The proposed formula for U

The algebraic model defines \(U_D\) by

\[
P_DU_D=Q_D.
\]

Invertibility of \(P_D\) makes the solution unique. The written algebraic proof gives, with \(h_d=n_d-2\),

\[
UF_0(x)=F_0(\rho_\Gamma(ux)),
\]

and for \(d\ge1\), \(z\in E\) an exterior monomial, \(0\le a\le h_d\),

\[
UF_d(u^az)=
\begin{cases}
F_d(u^{a+1}z),&a<h_d,\\[2mm]
F_d(u^{h_d}\theta z-u^{h_d-1}\omega z)
+F_{d-1}(\rho_{n_{d-1}}z),&a=h_d.
\end{cases}                                      \tag{3}
\]

The \(F_d\) symbols in this formula are linear labels for the chosen representatives. The relation \(R_{n_d}=0\) in cohomology supplies the same-sector normal form; the preceding-sector term records the extra cap relation. Reducing inside \(H_{n_d}\) and stopping there loses this contribution.

For example, at \(b=3,\Gamma=1\), \(n_1=4\) and \(h_1=2\), so

\[
UF_1(u^2)=F_1(u^2\theta-u\omega)+F_0(1).
\]

Another useful diagnostic is

\[
UF_1(\omega)=F_1(u\omega).
\]

Erasing \(C\) from \(P\) while leaving \(Q\) unchanged falsely adds \(F_0(1)\) to this second expression.

Equation (3) is proved for the specified algebraic model. Its interpretation as the geometric \(U\)-map follows if (1), (2), and the filtered-basis argument below are valid.

## 7 The finite filtered basis argument

Fix a finite \(D\ge0\), put \(N=bD+\Gamma\), and use Chen's normalization in which a fiber has action two. Choose a perfect Morse perturbation with \(\lVert H\rVert_\infty\le1/10\) and a source orbit-classification cutoff \(L_\varepsilon\).

The proposed sufficient conditions are

\[
0<\varepsilon\le
\min\left\{\frac14,\frac{b}{2N+b}\right\},
\qquad L_\varepsilon>3N.
\]

Set

\[
L_D=2(1+\varepsilon)N.
\]

The action estimates give

\[
2(1+\varepsilon/10)N<L_D
<2(1-\varepsilon/10)(N+b),
\qquad L_D<3N<L_\varepsilon.
\]

Thus all classified generators in sectors \(0,\ldots,D\) are included and all higher sectors are excluded.

At multiplicity \(n\), there are two elliptic multiplicities and four binary hyperbolic choices. The generator count is

\[
c(n)=\sum_{k=0}^{\min(4,n)}\binom4k(n-k+1).
\]

It gives

\[
c(1)=6,\qquad c(2)=17,\qquad c(n)=16(n-1)\quad(n\ge3),
\]

matching \(|B_n|\). At \(b=3,D=1\), the counts are \(6+48=54\) for \(\Gamma=1\), and \(17+64=81\) for \(\Gamma=2\).

The geometric support premise is that the filtered cap chain map represents \(F_d^\varepsilon(y)\) at filtration \(3n_d+\delta<L_\varepsilon\), and any output \(\alpha\) has section coefficient

\[
k=d-d(\alpha).
\]

Applying Chen's Lemma 3.7 would give \(d(\alpha)\le d\), placing the entire resulting cycle below \(L_D\). This follows the support part of the proof of Lemma 5.7, while replacing its restricted basis conclusion by the independent triangular argument below.

The rest of the argument is finite-dimensional. A vanishing linear combination of these filtered classes would vanish after inclusion into unfiltered ECH. Applying all filling tests would give \(P_Dv=0\), hence \(v=0\). The number of independent classes equals the full chain dimension, so they form a filtered homology basis, the differential has rank zero, and inclusion into unfiltered ECH is injective.

The review issue is whether the filtered map and its support property apply as asserted to the low-sector insertions. The arithmetic does not establish that premise. The computations use admissible numerical fixtures for \(\varepsilon\), critical values, and a declared cutoff; they do not construct a specific contact form or observe its Reeb dynamics.

## 8 Continuation and the direct limit

The working argument chooses a sequence \(\varepsilon_j\to0\), with valid dynamical cutoffs tending to infinity and sector depths \(D_j\to\infty\), and the exact-cobordism maps followed by filtration inclusions

\[
\iota_j:V^{\varepsilon_j}_{D_j}
\longrightarrow V^{\varepsilon_{j+1}}_{D_{j+1}}.
\]

Once both raw collections are bases, expand

\[
\iota_j(F_d^{\varepsilon_j}(y))
=\sum_{k,z}a_{k,z}F_k^{\varepsilon_{j+1}}(z).
\]

Pairing the right side with all target filling tests gives \(P_{D_{j+1}}a\). The essential geometric claim is that composition of the old cap, continuation cylinder, and new filling has the same closed invariant as the direct target cap/fill gluing:

\[
\Psi_m^{\varepsilon_{j+1}}
\bigl(x\otimes\iota_j(F_d^{\varepsilon_j}(y))\bigr)
=L_{d-m,I_{d,m}}(xy).                            \tag{4}
\]

If (4) holds, then

\[
P_{D_{j+1}}a=P_{D_{j+1}}e_{d,y},
\]

and invertibility gives

\[
\iota_j(F_d^{\varepsilon_j}(y))
=F_d^{\varepsilon_{j+1}}(y).
\]

The candidate justification for (4) follows the deformation and chamber comparison in Chen's Section 6. The points to check are the transported relative class, identification and order of insertions, homology orientations, Taubes chamber, and compatibility of the selected cutoffs. Solving a matrix equation does not establish those geometric identifications.

If this continuation identification and the rational direct-limit comparison are valid, the geometric limit is the algebraic union with recurrence (3). In that union, the written algebraic argument proves that \(U\) is locally nilpotent and surjective and that \(\dim\ker U=16\). Hence it gives

\[
\operatorname{ECH}(Y_b,\xi,\Gamma;\mathbb Q)
\cong\bigoplus_{j=1}^{16}\mathcal T^+,\qquad
\mathcal T^+=\mathbb Q[U,U^{-1}]/U\mathbb Q[U],
\]

as an ungraded \(U\)-module.

## 9 What the verification establishes

The reproducible finite grid is

\[
3\le b\le8,\qquad\Gamma=1,2,\qquad0\le D\le3.
\]

It contains 48 cases and 11,688 raw columns. Exact arithmetic checks the closed recurrence against the solution of \(PU=Q\), covering 3,812,376 scalar equations. The window routines enumerate 22,632 orbit sets, including the first excluded sectors, and check the action inequalities and counts.

Further checks include the diagonal Gram identities, the eight-entry junction, the finite \(U\)-cokernel dimension sixteen at positive depth, and recovery of each unit vector by solving \(Pa=Pe_j\). The latter is a check of triangular back substitution using the same algebraic matrices; it is not an independent test of geometric continuation.

The workbench also distinguishes deliberately incorrect alternatives: removing the raw junction without transforming the other data, removing lower-sector \(U\)-terms, and using an unsafe action window. A valid coordinated change of basis is separately checked.

The junction-sensitive part of that adverse control is concentrated. In every audited case with (3\le b\le8\), \(\Gamma\in\{1,2\}\), and (1\le D\le3\), exactly fifteen sector-one sources reject the invalid deletion. The remaining columns do not distinguish that particular mutant; they test the within-sector recurrence and normal-form reduction. Thus the grid is nonvacuous, but the 3,812,376 scalar equations should not be read as equally independent evidence for the junction. The [second-reader grid audit](../verification/grid-audit/LOW_SECTOR_GRID_AUDIT.md) records the exact scope and replay.

The frozen checkpoint passed eight package gates and 56 regression tests. Those gates establish reproducibility and the scope of the recorded software evidence. They do not certify a theorem about ECH. Finite examples corroborate the parameterized written algebraic proofs; no finite grid proves the universal or geometric statements.

## 10 Questions for verification or disproof

The requests below are ordered so that a short review can still settle the most important issue.

| Priority | Question | What would resolve it |
|---|---|---|
| 1 | Do the raw cap/fill composition and closed-invariant formulas give (1) for the unstable \(n=1,2\) bases and these torsion classes, including the initial diagonal \(G_1,G_2\)? | Confirmation with the needed hypotheses, or the first invalid insertion, sign, class identification, or source application |
| 2 | Does the strong-cobordism formalism used by Chen supply the filtered chain maps and nonnegative-section support property for these insertions? | An applicable established formulation or a precise additional analytic lemma |
| 3 | Does the \(u\) insertion produce the asserted geometric point action, so that (2) holds with these conventions? | Confirmation of the action and orientation identification, or a correction |
| 4 | Does the continuation gluing argument establish (4) for the raw classes and a cofinal compatible system of cutoffs? | A valid deformation, chamber, insertion, and orientation comparison; or the missing condition |
| 5 | Is the rational direct-limit comparison sufficient to identify this union with ECH? | Confirmation of the coefficient and map formalism, or the necessary modification |
| 6 | Does a matched existing Floer computation already give this \(U\)-module, this filtered recurrence, or an equivalent presentation? | A reference with the torsion-to-spin-c and convention correspondence |

If the first three points hold, the finite filtered formula is already a meaningful outcome even if continuation requires further work. If continuation also holds, the full directed-system description follows. A counterexample to an early bridge would narrow the result to the algebraic model and identify the next mathematical obligation.

For a first-pass review, the most useful bounded question is:

> Is the nonzero entry
> \(\Psi_0^\varepsilon(1\otimes F_1^\varepsilon(u^2\omega))=1\)
> correct for \(g=2,e=-3,\Gamma=1\), and does the same composition argument justify the complete triangular raw pairing on the unstable monomial bases?

An answer to that question would test the central source interpretation before asking you to review the entire argument.

## 11 Scope after a successful review

If the rational bridge survives review, coefficient transport becomes a separate next project. The algebra is integral, but that fact alone does not identify integral or mod-two geometric maps. A coefficient-specific comparison would still be needed. This is an unproved transport obligation; no impossibility or counterexample to coefficient extension has been established.

Likewise, the model has a grading by explicitly defined weights, but no absolute ECH grading normalization is asserted here. Nor do the complete-sector bases supply individual orbit representatives, every intermediate action sublevel, a fine-action barcode, or a new ECH capacity computation.

There is no claim of a defect in Chen's theorem: the proposed calculation concerns cases outside its stated range. There is also no claim that the raw eight-entry block is intrinsic. If the formula is already known in other coordinates, identifying that equivalence would be a successful outcome of the review.

## 12 Materials and suggested reading order

This breakdown contains the definitions, formulas, and review questions needed for an initial assessment. The supporting local files are:

| File | Purpose |
|---|---|
| EXCLUDED_GAMMA_RAW_BASIS_EXTENSION.md | The proposed argument through finite windows, continuation, and the direct limit |
| LOW_SECTOR_CAP_FILL_AUDIT.md | The first \(b=3,\Gamma=1,D=1\) specialization and nonzero pairing entry |
| vendor/ech_b1/research/ONE_JUNCTION_THEOREM.md in the Batch 2 checkpoint | The full written algebraic proof of the junction, recurrence, and tower result |
| research/COORDINATE_AWARE_JUNCTION.md in the checkpoint | The coordinated basis change and the distinction between deleting a block and changing coordinates |
| verify_raw_extension.py and EXTENSION_VERIFICATION_RECEIPT.json | Exact finite checks, pinned inputs, counts, and their declared limits |

The verifier expects the pinned Batch 2 extraction in a sibling directory; the script alone is not a portable standalone archive. A computational replay can be arranged if useful, but reviewing code is not part of the primary mathematical request.

For the shortest reading path, start with Sections 1, 4, 5, and 10 here. The decisive entry and the application of the source hypotheses are the first questions. Sections 6 through 8 then explain precisely what would follow from a positive assessment.

## References

1. Guanheng Chen, *Computing the U maps on ECH of prequantization bundles*, arXiv:2608.16625v2, 23 August 2026. Theorem 2.2 and its discussion, equation (2.5), Lemmas 3.7 and 5.1, Theorem 4.2, Lemma 5.11, Remark 1.5, and Section 6. [Versioned primary text](https://arxiv.org/html/2608.16625v2).
2. Jo Nelson and Morgan Weiler, *Embedded contact homology of prequantization bundles*, arXiv:2007.13883v3, 21 May 2024. Proposition 3.2, Theorem 7.1, and the conventions for orbit multiplicities, gradings, and direct limits. [Versioned primary text](https://arxiv.org/html/2007.13883v3).
3. Dmitry V. Gugnin, *On Integral Cohomology Ring of Symmetric Products*, arXiv:1502.01862v3, 13 March 2017. Theorem 2 and Section 3, including the unstable correction to the classical presentation. [Versioned primary text](https://arxiv.org/html/1502.01862v3).
