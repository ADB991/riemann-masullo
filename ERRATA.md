# Errata and gaps found in the paper

Problems found in A. M. Masullo, *The Music of the Primes*, while turning it into Lean. They
refer to the draft of 20 November 2026 (sha256 in [`paper/README.md`](paper/README.md)).

Most entries were first reported by an AI agent. The **Checked** column says whether someone has
since read the passage and agrees: *integrator* means the integrating agent compared the report
with the page; *reported* means nobody has yet. No entry has been reviewed by a specialist. The
dispute over the main theorem is described in the [README](README.md#status), not here.

The author's preface says that he and Brian Conrad know of "several glitches here and there"
still being fixed, and that the draft is unfinished. Everything below so far is in the
appendices and early chapters that recall standard material, and none of it touches the trace
formula.

## False as stated

| # | Where | What the paper says | Why it fails | In the Lean | Found in | Checked |
|---|---|---|---|---|---|---|
| F1 | Lemma A.1.1.2(5), p. 540 | For any partition I = J₁ ⊔ J₂ with J₁ finite, the box ∏_{J₁} Uᵢ × ∏_{J₂} Kⱼ with Uᵢ open is open in the restricted product. | An index with Kᵢ = 1 and Gᵢ not discrete may lie in J₂. With the single group ℝ, K = {0} and J₁ empty, the box is {0}, which is not open. | `restrictedProduct_topology` assumes Kᵢ is open for every i outside J₁ (true when J₁ contains all the exceptional indices). | #40 | integrator |
| F2 | Lemma A.1.5.1, last sentence, p. 543 | "In particular, 𝔸_{F,S}/O_{F,S} is naturally a ℚ-vector space." | For F = ℚ and S = {∞} the group is ℝ/ℤ, which has torsion: the class of 1/2 has order two. | `sAdele_additive_quotient` keeps parts (1)–(3) and omits this consequence. | #40 | integrator |
| F3 | Remark after Theorem C.1.5.11, p. 668 | Each Fréchet stage "is assumed merely to be Schwartz (which implies nuclearity by Example C.1.5.10)". | The direction is reversed: Example C.1.5.10 shows that nuclear spaces are Schwartz, and Schwartz spaces need not be nuclear. | `limitSubspaceTopology_eq_iff_liftsBoundedSets` is stated for Schwartz stages, the more general form. | #41 | integrator |
| F4 | Definition A.2.1.1 with Lemma A.2.1.2, p. 545 | The archimedean part of the fundamental domain is {x = Σ_{1≤i≤r₁+r₂} xᵢaᵢ : \|xᵢ\|_{vᵢ} ∈ [0,1)}, and its translates by nonzero field elements are disjoint from it. | The sum runs over r₁+r₂ of the [F:ℚ] basis vectors, and bounding absolute values gives a symmetric set. For F = ℚ the printed set is (−1,1), which meets its translate by 1. Example A.2.1.3 and the proof of Lemma A.2.4.2 (p. 554) use [0,1)^{[F:ℚ]}. | `infiniteAdeleFundamentalDomain` is the half-open parallelepiped of the whole integral basis. | #113 | integrator |
| F5 | End of §C.2.2.2, p. 674 | "The condition under which the strong-dual topology β(E′,E) agrees with the Mackey topology τ(E′,E) is barreledness of E." | The roles of E and E′ are swapped: barrelledness of E says that E itself carries the strong topology β(E,E′). On the dual, β(E′,E) = τ(E′,E) characterizes semi-reflexive spaces. The Banach space c₀ is barrelled, yet the dual of (ℓ¹, β) is ℓ^∞ while the dual of (ℓ¹, τ(ℓ¹,c₀)) is c₀. | Not stated; `strongDualityTopology_le_mackeyTopology` gives the comparison that does hold. | #147 | integrator |
| F6 | Remark A.2.4.5, p. 555 | For S large enough that Pic(O_{F,S}) = 1, "O_{F,S}^× · E¹_{F,S} = GL₁(𝔸_F)¹". | Both O_{F,S}^× and E¹_{F,S} consist of ideles that are units at every place outside S, so their product cannot contain a norm-one idele that is not. For F = ℚ and a prime p outside S, the principal idele of p is such an idele. The equality holds with F^× in place of O_{F,S}^×, or after passing to idele classes. | `exists_rat_prime_idele_outside` records the counterexample; the identification is stated on idele classes. | #234 | integrator |
| F7 | After (C.2.3.15), p. 679 | "The analog of Lemma C.2.3.5 for projective tensor products holds." Lemma C.2.3.5 says that the injective tensor product of two topological embeddings is an embedding, and of two isometric embeddings an isometry. | The projective tensor product does not respect subspaces. With H the closed span of the Rademacher functions in L¹[0,1], the map H ⊗_π ℓ² → L¹ ⊗_π ℓ² is not an embedding: otherwise the coefficient map H → ℓ² would extend to a bounded map L¹ → ℓ² sending each Rademacher function to a basis vector, which is impossible. The paper's own footnote 10 asks whether the sentence is needed. | Only associativity, compatibility with completion and the quotient results of C.2.3.7 are stated for ⊗_π. | #330 | integrator |

## Imprecise, inconsistent or wrongly justified

| # | Where | Problem | In the Lean | Found in | Checked |
|---|---|---|---|---|---|
| I1 | Definition A.1.1.1 and Lemma A.1.1.2, p. 539 | The index set is written I = I₀ × I₁, but the conditions are then imposed on "i ∈ I₀" and "i ∈ I₁". A disjoint union is meant. | A finite set of exceptional indices and its complement. | #40 | integrator |
| I2 | Opening of §A.1.2, p. 540 | The completion of O_F is taken for the topology generated by I·O_F over all proper ideals I. The zero ideal is proper, which would make the topology discrete; nonzero ideals are meant. | `integralAdelesOutside` uses the product of the local integer rings. | #40 | integrator |
| I3 | Sentence after (A.1.4.2), p. 542 | Compactness of the norm-one idele class group is attributed to Lemma A.1.3.4(3), which only gives a continuous section of the norm. A section does not imply a compact kernel. | Compactness is a separate obligation in `ideleClassGroup_finiteness` (Theorem A.1.4.3). | #40 | integrator |
| I4 | Proof on p. 665 (Lemma C.1.5.4 / Theorem C.1.5.5) | The second Baire category argument is reported to establish only that a union is dense, not that it is everything. | Statements are as in the paper; the proof was not followed. | #41 | reported |
| I5 | Lemma A.2.2.1, p. 546 | The displayed section takes values in the ideles, but the conclusion applies the norm of the idele class group; the quotient map is missing. | Both identities are stated: `ratIdeleNormSection_rightInverse` and `ratIdeleNormSection_class_rightInverse`. | #113 | reported |
| I6 | Lemma A.2.2.9, p. 547 | The hypothesis is "any continuous section s to the idelic norm", but the map (t, g₀) ↦ s(t)g₀ is called a homomorphism and an isomorphism of groups, which needs s to be a homomorphism. | `ideleNormSection_product` assumes a continuous homomorphic section, as in the opening of §A.2.2. | #113 | integrator |
| I7 | Lemma A.2.3.8(3), p. 550 | Equation (A.2.3.18) quantifies over a compact set K but intersects a translate of the closure with the closure itself; the parallel statements A.2.3.10(3) and A.2.4.4(3) use K, and the proof reduces to K equal to the closure. | Stated with K, which contains the printed case. | #234 | reported |
| I8 | Definition A.2.4.3 and Proposition A.2.4.4(4), pp. 554–555 | (A.2.4.4) takes a union over h_{F,S} translates gᵢ yet places the result inside GL₁(𝔸_{F,S})¹ × ∏_{v∉S} O_v^×. An idele that is a unit at every place outside S has trivial image in the class group of the S-integers, so such gᵢ cannot represent nontrivial S-ideal classes (for example the class of (2, 1+√−5) in ℤ[√−5]). The basis in (A.2.4.8) must also be read modulo torsion, since the S-units contain −1. | `sIdele_ideal_class_trivial` states the obstruction; part (4) is stated when the S-class group is trivial. | #234 | integrator |
| I9 | Lemma A.2.3.5, p. 549 | The opening sentence calls F a hyperplane; (A.2.3.5) and (A.2.3.9) use the number field F and put the parallelotope in the hyperplane H_log. | Follows the equations. | #234 | reported |
| I15 | Proof of Lemma A.2.3.8, pp. 550–551 | (A.2.3.20) requires the chosen coordinate to lie on the positive real ray, but at a complex place Definition A.2.3.6 and (A.2.3.21) give a sector. For F = ℚ(i) the archimedean idele e^{iπ/4} has norm one, logarithm zero and argument in [0, π/2), yet is not on the real ray. | `inTorsionSector` uses the sector. | #234 | reported |
| I16 | Proposition A.2.3.9, p. 552 | The first exact sequence gives no formulas for its arrows and describes the units as embedded diagonally. For the multiplication map (x, h) ↦ d(x)h a unit u must embed as (u, d(u)⁻¹); the diagonal embedding maps to d(u)², which is nontrivial for u = 1+√2 in ℚ(√2). | Both arrows are specified. | #234 | reported |
| I10 | After (C.2.1.2), p. 670 | The S-topology is said to be the unique topology with the given neighbourhoods of zero for which "translation by each element of F" is continuous. Translations by all elements of F^E are needed for uniqueness. | `uniformOnFun_zero_basis` states the neighbourhood basis for Mathlib's topology. | #147 | integrator |
| I11 | Remark C.2.3.2, p. 677, after (C.2.3.6) | The description of the image of (C.2.3.5) as all μ-continuous finite-rank operators is reported to fail when E is not complete (finitely supported sequences with the ℓ² norm, F = ℂ). | `tensorDualOperator_finiteRank` and `tensorDualOperator_continuous_mu` state what does hold. | #147, #330 | reported |
| I12 | Inductive tensor topology, p. 682, before (C.2.3.22) | The defining property as printed is satisfied by the finest locally convex topology, so it does not single out the inductive topology; separate continuity of the canonical bilinear map has to be required as well. | `InductiveTensor` is defined with separate continuity. | #147, #330 | reported |
| I17 | Proposition C.2.3.13(2), (C.2.3.27), p. 683 | The map from the limit of the completed stages is reported not to be injective in general, when the limit is the algebraic direct limit of §C.1.5: with stages c₀₀/span(e₁,…,eₙ) under the ℓ² norm and second factor ℂ, the class of (2⁻ᵏ) is nonzero at every completed stage but dies in the completion of the limit, which is zero. | Stated for the span of the stage images with its subspace topology, and density of that span. | #330 | reported |
| I18 | Proposition C.2.3.13(3), p. 683 | Bornologicity of the completed inductive tensor product is reported to fail: with second factor ℂ the claim is that the completion of a bornological space is bornological, and a counterexample is built from continuous functions on a stationary, costationary subset of ω₁. | Not stated. | #330 | reported |
| I19 | Remark C.2.3.3, p. 677 | Refers to an open mapping theorem of Pták without stating its hypotheses. | Only the topology is named. | #330 | reported |
| I13 | After (3.1.2.1), p. 120 | Compactness of the norm-one part of J_{F,S} is cited from Theorem A.1.5.2(1), which is about C_{F,S}; one has to project away the unit factors outside S first. | `SIdeleQuotient` is the quotient of (3.1.2.1); the compactness statement is for it. | #148 | reported |
| I14 | (3.1.2.2), p. 120 | At a finite place the norm has image q^ℤ, so the "section" of the norm exists only over that subgroup and depends on a uniformizer. | The Lean formula keeps both choices and the period 2πi/log q. | #148 | reported |

## Placeholders and missing material

| # | Where | What is missing | Found in | Checked |
|---|---|---|---|---|
| M1 | Chapter 13, pp. 521–522 | §13.1 and §13.2 are headings with no text. Theorem 13.3.1.2, the main theorem on the zeros, reads "Insert statement"; the text before it cites "Theorem ??"; the trace formula as restated in Theorem 13.3.1.1 carries the footnote "Correct statement". | first survey; scout #3 | integrator |
| M2 | Definition C.1.3.1, p. 659 | The reference for constructing the completion by Cauchy nets is "[?]". | #41 | reported |
| M3 | Footnotes 2–4, p. 667 | The explicit Köthe space, the two strong topologies and the justification of the subspace example are left unspecified. | #41 | reported |
| M4 | §B.4, p. 625, footnote 27 | The footnote asks for an explanation of how an identity follows from B.4.2.2. | scout #3 | reported |

## How this file is kept

Digesters and provers mark a problem where they meet it with a comment `-- TODO(paper-gap): …`
in the Lean file and describe it in their report. When the pull request is merged, the integrator
reads the passage and adds an entry here. `grep -rn "TODO(paper-gap)" RiemannMasullo` lists every
mark in the code.
