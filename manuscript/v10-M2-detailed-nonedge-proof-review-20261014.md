# The non-edge proof of M2: detailed English audit

*Successor v10; 14 October 2026. Review-only supplement; the frozen author's proof is unchanged.*

## Statement and reductions

Let \(\mathcal K\) be the class of admissible partial \(L^+\)-types for the normalized finite family \(\mathcal F\) of forbidden \(L\)-structures. The forbidden nontrivial members are irreducible: every pair of distinct vertices is joined by some positive directed \(L\)-atom in at least one direction. Forbidden one-point structures are not the all-negative neutral one-point structure. The auxiliary relation \(E\) does not occur in the forbidden structures.

Fix a genuine shape-preserving map \(F\in\mathcal M\) and consecutive source levels \(n-1,n\), with image levels separated by at least one missing level. Put \(\lambda=\widetilde F\), and let \(m=\lambda(n)-1\). Thus \(\lambda(i)<m\) for every \(i<n\), and \(\lambda(n)=m+1\). The intrinsic deletion construction supplies another genuine shape map \(D\) which agrees with \(F\) below the first affected boundary and deletes the last ordinary coordinate of each image type at that boundary. We must restore its boundary image types by inserting one level at \(m\).

The finite prescription consists of all boundary types \(D(t)\), with prescribed value \(F(t)\), for source nodes \(t\) at level \(n\). Injectivity of \(D\) makes this a function. **B1** follows from the literal equality between deletion of the last coordinate and ordinary prefix restriction. **B2** follows from the reflection of complete ordinary \(L^+\)-compatibility by \(D\) and its preservation by \(F\). This includes all negative directed binary atoms, unary and diagonal information, and ordinary \(E\). By the already formalized compatible-class boring-extension theorem, **B3** is then the sole outstanding finite-age obligation.

## Claim: the prescribed family satisfies CompatibleB3

Fix a prescribed boundary source \(S_0=D(t_0)\). Consider an arbitrary finite \(L\)-structure \(W\) satisfying the three clauses of CompatibleB3:

1. Its initial \(m+1\) vertices, including \(m\), have exactly the full ordinary \(L\)-socle of \(F(t_0)\) (including unary and diagonal atoms).
2. Each upper vertex \(w>m\) has, over the first \(m+1\) vertices, the complete \(L\)-type of some \(F(t_w)\), where the boundary type \(D(t_w)\) is compatible with \(S_0\).
3. \(W\setminus\{m\}\) is \(\mathcal F\)-free, in the induced sense.

Suppose a forbidden \(P\in\mathcal F\) occurs in \(W\), enumerated by a strictly increasing map \(e:\{0,\ldots,r-1\}\to W\). Since \(W\setminus\{m\}\) is free, the copy contains \(m\). For each \(a\) such that \(e(a)>m\), choose the actual admissible source type \(t_a\) whose image provides the upper type of \(e(a)\). (Only these finitely many upper vertices need source types.) B2 reflection, i.e. the \(D\)-then-\(F\) compatibility theorem, gives a common ordinary \(L^+\)-socle for \(t_0\) and all \(t_a\).

### 1. A forbidden-free, finite, dense source \(L\)-model

On the first \(n+r\) numerical positions build \(A\). The *real* positions are \(i<n\) and \(n+a\) for which \(e(a)>m\). Map them, in order, to \(\lambda(i)\) and \(e(a)\), respectively, in \(W\setminus\{m\}\). Copy **every** induced \(L\)-atom, including absent directed binary atoms and singleton/diagonal facts, along this strictly increasing map. At the other (unused) positions, put the completely neutral singleton and no incident positive \(L\)-relations.

The resulting \(A\) is \(\mathcal F\)-free. A forbidden copy on real positions would induce one in \(W\setminus\{m\}\). A new irreducible forbidden copy with at least two vertices cannot meet a dummy vertex because the dummy has no positive binary incident atom. A forbidden singleton cannot meet a dummy because it requires a nonneutral unary or diagonal atom. This argument requires neither an \(E\)-expansion of \(W\) nor a preservation-of-age axiom for \(F\).

### 2. Recover exactly the selected source \(L\)-types

At the genuine source position \(n+a\), extract the complete \(L\)-type of that vertex over the first \(n\) positions. Its ordinary–ordinary atoms come from \(W(\lambda(i),\lambda(j))\), its two directed crossing atoms from \(W(\lambda(i),e(a))\) and \(W(e(a),\lambda(i))\), and its distinguished-vertex singleton and loop atoms from \(W(e(a))\). Because the upper type of \(e(a)\) in \(W\) equals the full \(L\)-reduct of \(F(t_a)\), these are exactly the corresponding atoms of \(F(t_a)\) on the retained indices. The complete retained-record theorem for a genuine ShapeMap says that this pullback equals \(t_a\), atom for atom. In particular, it is **not** enough to check positive edges: reverse directions, nonedges and singleton obstructions are recovered too.

Thus the selected type at \(n+a\) in \(A\) is \(t_a\)'s \(L\)-reduct. The initial \(L\)-socle of \(A\) similarly agrees with the ordinary \(L\)-socle of \(t_0\): compare the initial \(F(t_0)\)-socle of \(W\) at \(\lambda(i),\lambda(j)\) and apply the same retained-record identity.

These selected-type recoveries are checked locally in `M2SelectedCopyType.lean`, using the *actual* shape map and no M2 assumption.

### 3. Add auxiliary \(E\) only after the \(L\)-model is fixed

Choose one genuine finite partial structure witnessing admissibility of \(t_0\). Its first \(n\) ordinary positions supply the shared \(E\)-socle. Since all selected \(t_a\) are ordinarily \(L^+\)-compatible with \(t_0\), they have exactly the same ordinary \(E\)-socle. Apply non-edge padding to \(A\): keep its real–real \(L\)-atoms *unchanged*; insert neutral, unlinked filler positions as needed; and choose \(E\) so that each selected source vertex has free cut at least \(n\), with the correct full prescribed type. All selected \(t_a\) are now realized together in one forbidden-free partial structure \(B\). Unselected filler vertices are deliberately **not** asserted to realize a member of the prescribed source family.

The simultaneous version of this step is checked locally in `M2SelectedCopyPadded.lean`. Both the \(L\)-age argument and the complete \(E\)-type recovery have been checked separately in the established padding library.

### 4. Cap once and apply the genuine map \(F\)

Append two neutral vertices to \(B\), with the final cap vertex \(v\) having free cut \(|B|\). This gives an admissible Kpt node \(u\) whose complete ordinary socle contains **every** vertex of \(B\). The source type of a selected vertex at padded coordinate \(j_a\) over the first \(n\) vertices is precisely \(t_a\), and its free cut is at least \(n>0\).

Apply the actual shape map \(F\) to this *one* node \(u\). The canonical-parameter-prefix transport theorem, with the explicit coordinate version from PR #363, gives the entire ordinary \(L^+\)-type of the selected image vertex at \(\lambda(j_a)\), over **all** first \(\lambda(n)=m+1\) target positions, equal to \(F(t_a)\). This includes the target coordinates omitted by \(\lambda\): it is a parameter statement, not merely a retained-coordinate statement.

The output initial \(m+1\) ordinary socle agrees with \(F(t_0)\): the corresponding source initial \(n\)-socles are compatible, and \(F\) preserves complete ordinary compatibility. Hence this initial output socle agrees with that of \(W\).

Finally, for two distinct real upper source vertices \(j_a,j_b\), ordinary–ordinary pair recovery for \(F\) shows that their **complete directed** \(L\)-pair record in \(F(u)\), at \(\lambda(j_a),\lambda(j_b)\), is exactly the original pair record in \(B\). The padding retained the real pair record from \(A\), which by construction was \(W(e(a),e(b))\). Unary and diagonal atoms of these upper vertices follow either from this full ordinary record recovery or from their complete parameter image types.

### 5. Transfer the forbidden induced copy

Define the candidate copy coordinates in the finite \(L\)-age of \(F(u)\) by

\[
\psi(a)=\begin{cases}
 e(a),&e(a)\le m,\\
 \lambda(j_a),&e(a)>m.
\end{cases}
\]

The coordinates are strictly increasing: the lower part is unchanged; all upper image positions are above \(m\); the padded source positions \(j_a\) strictly increase with \(a\); and \(\lambda\) is strictly increasing. Every candidate belongs to the old ordinary carrier of \(F(u)\).

Every pair and singleton atom of the alleged forbidden copy now agrees, in both truth values, with its counterpart in \(F(u)\). Indeed, lower–lower atoms come from the common initial image socle; lower–upper atoms in both directions, **including the omitted coordinate \(m\)**, come from complete canonical-parameter image transport; and upper–upper atoms come from retained ordinary-pair transport. Unary, diagonal and loop facts are included explicitly. Hence \(\psi\) is an **induced ordered copy** of \(P\) in the age of the admissible node \(F(u)\), a contradiction.

Therefore the finite age witness \(W\) is \(\mathcal F\)-free, establishing CompatibleB3 for the boundary prescription. The existing global boring-extension theorem then constructs the restoring one-gap map, and the previously proved conditional factorization criterion yields M2.

## Formalization checklist and scope

The preceding is a complete mathematical proof *scheme*, with every delicate point identified. It should be read as a proposed proof rather than a claim that the final Lean theorem has already compiled. The following interfaces are currently available:

- Nonedge source age, neutral fillers, full real pair records, and preserved avoidance: `M2BoundedCopySourceAge`, `M2BoundedCopyRecords`.
- Full shape-map retained records and compatibility reflection/preservation: `ShapeMapFullRecovery`, `M2B2Transfer`.
- Simultaneous full L+ source realization: `M2SelectedFamilyPadding` and new `M2SelectedCopyPadded`.
- Complete image parameter transport at its actual \(\lambda(j)\) coordinate: `M2AmbientLevelTransport` (PR #363).
- Strict mixed final copy coordinates and atom-by-atom copy assembly: `M2CopyImageCoordinates`, `M2CopyImageTransfer`.
- Conditional one-gap factorization: `M2CompatibleFactorization`.

**Still requiring Lean integration:** turn the B3 upper-type predicate into exact source-node indices \(t_a\), derive the initial socle comparison of \(A\) from the B3 first clause, package the one-cap image record equalities into the four `M2CopyImageTransfer` atom zones, prove the unconditional `CompatibleB3` theorem, and finally discharge `M2CompatibleFactorization` for the concrete boundary prescription. No statement above may be marked as completely Lean-verified until those last applications are checked with full Lean and a transitive standard-axiom audit.