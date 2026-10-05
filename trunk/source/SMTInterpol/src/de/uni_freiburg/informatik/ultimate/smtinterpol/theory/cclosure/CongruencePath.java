/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * This class generates congruence lemmata and their explanation.
 * It takes the CClosure and extracts from it a path of equalities that
 * connect two equivalent CCTerm.  It also computes the required
 * congruences.  All literals are collected and if proof production
 * is enabled, also the paths are collected and remembered.
 *
 *
 * @author Jochen Hoenicke
 *
 */
public class CongruencePath {

	final CClosure mClosure;

	/**
	 * This is the data structure that remembers an equality path if
	 * proof production is enabled.  It just is a list of ccterms that
	 * are connected by equality edges or congruences.
	 *
	 * This data structure is only in use if proof production is enabled.
	 *
	 * @author Jochen Hoenicke
	 */
	public static class SubPath {
		ArrayList<CCTerm> mTermsOnPath;

		public SubPath(final CCParameter start) {
			this(start, true);
		}

		public SubPath(final CCParameter start, final boolean produceProofs) {
			if (produceProofs) {
				mTermsOnPath = new ArrayList<>();
				mTermsOnPath.add(start.getCCTerm());
			}
		}

		/**
		 * The path nodes as {@link CCParameter}s, offset so that every node has the same value as {@code anchor}:
		 * {@code value(node) + offset == value(anchor) + anchor.getOffset()}. So if {@code x = y+4} and {@code y = z+2},
		 * a path rendered with anchor {@code x+2} reads {@code x+2, y+6, z+8}. The relative offsets are intrinsic
		 * ({@link CCTerm#getOffsetToRep} differences), so the anchor only fixes the absolute base and the result is
		 * stable under {@link #addSubPath} concatenation. The anchor is typically one of the path's own nodes.
		 *
		 * <p>The {@code anchor} is treated as the <em>start</em> of the path: its term must be one of the path's two
		 * endpoints, and the result is oriented so that the anchor's term is first (the stored term list may run either
		 * way, since {@link #mVisited} keys paths by an undirected {@link SymmetricPair}). The anchor's term renders at
		 * {@code anchor.getOffset()} and the other endpoint follows from the intrinsic relative offsets.
		 *
		 * <p>{@link CCTerm#getOffsetToRep} is relative to each node's own representative, so for two nodes in different
		 * classes the difference mixes reference frames and yields garbage offsets — the bug behind several earlier
		 * offset conflicts (a path built over a freshly added, not-yet-united merge bridge). For <em>numeric</em> terms
		 * we therefore assert the anchor shares the representative of every node; the cross-class conflict builder
		 * ({@link #computeMergeConflictCycle}) avoids this by rendering each single-class half separately. The only paths
		 * that genuinely cross classes are non-numeric (weak-array
		 * paths over distinct strong classes), and a non-numeric term can never carry an offset, so the rendering is
		 * trivially correct (offset zero) regardless of frame.
		 */
		public CCParameter[] getParams(final CCParameter anchor) {
			final int n = mTermsOnPath.size();
			assert mTermsOnPath.get(0) == anchor.getCCTerm() || mTermsOnPath.get(n - 1) == anchor.getCCTerm()
					: "getParams anchor must be a path endpoint";
			// Orient the path so the anchor's term is first. The stored term list may run either way (mVisited keys
			// paths undirected), so if the anchor is the stored last node, render in reverse.
			final boolean reversed = mTermsOnPath.get(0) != anchor.getCCTerm();
			final CCParameter[] params = new CCParameter[n];
			for (int i = 0; i < n; i++) {
				final CCTerm t = mTermsOnPath.get(reversed ? n - 1 - i : i);
				assert !t.getFlatTerm().getSort().isNumericSort()
						|| anchor.getRepresentative() == t.getRepresentative()
						: "getParams anchor must share the congruence class of every numeric node";
				params[i] = CCParameter.of(t, anchor.getOffsetToRep().sub(t.getOffsetToRep()));
			}
			return params;
		}

		/** {@link #getParams(CCParameter)} self-anchored at the path's first node (offset 0). */
		public CCParameter[] getParams() {
			return getParams(mTermsOnPath.get(0));
		}

		public void addEntry(final CCTerm term, final CCEquality reason) {
			if (mTermsOnPath != null) {
				mTermsOnPath.add(term);
			}
		}

		public void addSubPath(final SubPath second) {
			if (mTermsOnPath != null && second != null) {
				if (second.mTermsOnPath.get(0)
						== mTermsOnPath.get(mTermsOnPath.size() - 1)) {
					for (int i = 1; i < second.mTermsOnPath.size(); i++) {
						mTermsOnPath.add(second.mTermsOnPath.get(i));
					}
				} else {
					/* sub path is reversed */
					assert (second.mTermsOnPath.get(second.mTermsOnPath.size() - 1)
							== mTermsOnPath.get(mTermsOnPath.size() - 1));
					for (int i = second.mTermsOnPath.size() - 2; i >= 0; i--) {
						mTermsOnPath.add(second.mTermsOnPath.get(i));
					}
				}
			}
		}

		@Override
		public String toString() {
			return mTermsOnPath.toString();
		}
	}

	/**
	 * Visited subpaths, keyed by the <em>offset-free</em> end terms. Two requested paths that differ only by a constant
	 * offset (e.g. {@code x+5 = y+7} and {@code x+7 = y+9}, both for the edge {@code x = y+2}) share one key, so only a
	 * single subpath is built; consumers (e.g. {@link CCProofGenerator}) absorb the per-use constant difference.
	 */
	final HashMap<SymmetricPair<CCTerm>,SubPath> mVisited;
	/**
	 * The already built subpath. These are added in dependency order, i.e. subpaths
	 * depending on other subpaths are added in front of them.
	 */
	final ArrayDeque<SubPath> mAllPaths;
	/**
	 * The Todo deque. This contains all the subpaths that still must be built (can
	 * also contain already built paths as well).
	 */
	final ArrayDeque<SymmetricPair<CCTerm>> mTodo;
	/**
	 * The subpaths already appended to {@link #mAllPaths}. Persistent across
	 * {@link #drainTodo} calls (unlike a per-drain set) so a subpath shared between
	 * several drains is collected exactly once. {@link WeakCongruencePath} drains
	 * once per weak/main path, and {@link #enqueueCongruence} re-enqueues argument
	 * pairs unconditionally, so the same dependency can resurface in a later drain;
	 * this set keeps it from being added twice.
	 */
	final Set<SymmetricPair<CCTerm>> mCollected;
	final Set<Literal> mAllLiterals;

	public CongruencePath(final CClosure closure) {
		mClosure = closure;
		mVisited = new HashMap<>();
		mAllLiterals = new LinkedHashSet<>();
		mTodo = new ArrayDeque<>();
		mAllPaths = new ArrayDeque<>();
		mCollected = new HashSet<>();
	}

	private CCAnnotation createAnnotation(final SymmetricPair<CCParameter> diseq) {
		return new CCAnnotation(diseq, mAllPaths, CCAnnotation.RuleKind.CONG);
	}

	private int computeDepth(CCTerm t) {
		int depth = 0;
		while (t.mEqualEdge != null) {
			t = t.mEqualEdge;
			depth++;
		}
		return depth;
	}

	/**
	 * Enqueue the congruence from start to end. The terms must be congruent
	 * AppTerms, i.e. their func and arg values are congruent.
	 *
	 * @param start one of the function application terms.
	 * @param end   the other function application term.
	 */
	private void enqueueCongruence(CCAppTerm start, CCAppTerm end) {
		// Pair the argument values (CCParameters), so the recorded subpath for each argument is anchored at the
		// argument's offset, e.g. f(x+2) congruent f(z+8) yields a subpath from x+2 to z+8. This only enqueues the
		// argument pairs; the surrounding drain loop (drainTodo) builds them.
		for (int i = 0; i < start.getArgCount(); i++) {
			mTodo.addFirst(new SymmetricPair<>(start.getArgParam(i).getCCTerm(), end.getArgParam(i).getCCTerm()));
		}
	}

	/**
	 * Compute the path from start to end, where end must be on the path from start
	 * to the representative, i.e. end is reachable from start by repeatedly
	 * following the equalEdge field. The last equalEdge must be induced by a
	 * equality literal not a congruence edge.
	 *
	 * @param start the first term in the path.
	 * @param end   the last term in the path.
	 * @return the sub path from start to end.
	 */
	private SubPath computePathTo(final CCTerm start, final CCTerm end) {
		final SubPath path =
				new SubPath(start, mClosure.isProofGenerationEnabled());
		CCTerm t = start;
		CCTerm startCongruence = t;
		while (t != end) {
			if (t.mOldRep.mReasonLiteral != null) {
				if (startCongruence != t) {
					/* We have a congruence:  The terms startCongruence and t are congruent.
					 * Compute the paths for the func and arg parts and merge into the
					 * interpolation info.
					 */
					enqueueCongruence((CCAppTerm) startCongruence, (CCAppTerm) t);
					path.addEntry(t, null);
				}
				/* Add the equality literal to conflict set */
				path.addEntry(t.mEqualEdge, t.mOldRep.mReasonLiteral);
				mAllLiterals.add(t.mOldRep.mReasonLiteral);
				startCongruence = t.mEqualEdge;
			}
			t = t.mEqualEdge;
		}
		assert (startCongruence == t);
		return path;
	}

	/**
	 * Compute the conflict set and interpolation information for the congruence
	 * path from term left to right.
	 *
	 * <p>
	 * This is a pure builder: it does not consult or update the {@link #mVisited}
	 * cache. {@link #drainTodo} owns the cache — it looks up {@link #mVisited}
	 * before calling and stores the result afterwards, so a path requested as a
	 * standalone subpath is built once and collected through the re-enqueue
	 * discipline. Inline grafts (built directly, outside the drain, to be spliced
	 * into a weak/store path) call this without caching: a later standalone request
	 * for the same edge therefore rebuilds it through the drain rather than
	 * short-circuiting to the already-visited branch of {@link #drainTodo} (which
	 * would collect it ahead of its still-pending congruence dependencies). The
	 * graft's dependencies are enqueued either way, so the inlined congruences are
	 * still explained.
	 *
	 * @param left  the left end of the congruence chain that should be evaluated.
	 * @param right the right end of the congruence chain that should be evaluated.
	 * @return the built path, or {@code null} for a trivial path ({@code left} and
	 *         {@code right} share the same term).
	 */
	SubPath computePath(final CCTerm left, final CCTerm right) {
		/* check for and ignore trivial paths */
		if (left == right) {
			return null;
		}

		int leftDepth = computeDepth(left);
		int rightDepth = computeDepth(right);
		CCTerm ll = left;
		CCTerm rr = right;
		CCTerm llWithReason = ll, rrWithReason = rr;
		while (leftDepth > rightDepth) {
			if (ll.mOldRep.mReasonLiteral != null) {
				llWithReason = ll.mEqualEdge;
			}
			ll = ll.mEqualEdge;
			leftDepth--;
		}
		while (rightDepth > leftDepth) {
			if (rr.mOldRep.mReasonLiteral != null) {
				rrWithReason = rr.mEqualEdge;
			}
			rr = rr.mEqualEdge;
			rightDepth--;
		}
		while (ll != rr) {
			if (ll.mOldRep.mReasonLiteral != null) {
				llWithReason = ll.mEqualEdge;
			}
			if (rr.mOldRep.mReasonLiteral != null) {
				rrWithReason = rr.mEqualEdge;
			}
			ll = ll.mEqualEdge;
			rr = rr.mEqualEdge;
		}
		assert (ll != null);
		final SubPath path = computePathTo(left, llWithReason);
		if (llWithReason != rrWithReason) {
			enqueueCongruence((CCAppTerm)llWithReason, (CCAppTerm)rrWithReason);
			path.addEntry(rrWithReason, null);
		}
		final SubPath pathBack = computePathTo(right, rrWithReason);
		path.addSubPath(pathBack);
		return path;
	}

	/**
	 * Enqueue the congruence path from left to right as a depending sub path. The
	 * path will be computed only when drainTodo() is called. The caller needs to
	 * call drainTodo() to add the path and its dependencies to the list
	 * {@link #mAllPaths}.
	 *
	 * @param left  the left end of the congruence chain that should be evaluated.
	 * @param right the right end of the congruence chain that should be evaluated.
	 */
	public void enqueuePath(final CCParameter left, final CCParameter right) {
		mTodo.add(new SymmetricPair<>(left.getCCTerm(), right.getCCTerm()));
	}

	/**
	 * Process the work list {@link #mTodo} of (sub)paths to compute, building each
	 * one and collecting it into {@link #mAllPaths} (and its literals into
	 * {@link #mAllLiterals}). The top-level compute*Cycle/Lemma methods seed the
	 * work list via {@link #enqueuePath} (a single pair) and
	 * {@link #enqueueCongruence} (argument pairs), then call this once. Partial
	 * subpaths (like the paths concatenated in {@link #computeMergeConflictCycle}
	 * or the strong subpaths of {@link WeakCongruencePath}) are instead built
	 * directly via {@link #computePath} and they will also enqueue subpaths using
	 * {@link #enqueueCongruence}. They must call this function before the
	 * concatenated path is added to ensure all dependent subpaths are computed
	 * before. The function uses a persistent {@link #mCollected} set so that every
	 * path is only added once.
	 *
	 * <p>
	 * Ordering invariant: a path is collected (appended to {@link #mAllPaths}) only
	 * after its congruence dependencies, so it precedes the paths explaining its
	 * congruences (as the proof generator requires). This holds because a freshly
	 * seen path takes the {@code path == null} branch: it re-enqueues itself
	 * <em>behind</em> the dependencies that {@link #computePath} pushes to the
	 * front, so those are collected first. Since there cannot be cyclic
	 * dependencies between congruences, it is guaranteed that the next time the
	 * path is collected, the dependencies were already added.
	 */
	protected void drainTodo() {
		while (!mTodo.isEmpty()) {
			final SymmetricPair<CCTerm> pathEnds = mTodo.removeFirst();

			// don't do anything for trivial paths
			if (pathEnds.getFirst().getCCTerm() == pathEnds.getSecond().getCCTerm()) {
				continue;
			}

			// check if we already visited this path (keyed offset-free, so offset variants share one subpath)
			final SubPath path = mVisited.get(pathEnds);
			if (path == null) {
				// if we did not visit it yet, enqueue again for later, build the path and cache it. drainTodo owns the
				// mVisited cache; computePath is a pure builder. The pair is non-trivial (checked above), so
				// the build never returns null here.
				mTodo.addFirst(pathEnds);
				mVisited.put(pathEnds, computePath(pathEnds.getFirst(), pathEnds.getSecond()));
			} else {
				// already visited it, so we just add the path now unless we did this earlier
				if (mCollected.add(pathEnds)) {
					mAllPaths.addFirst(path);
				}
			}
		}
	}

	public Clause computeCycle(final CCEquality eq, final boolean produceProofs) {
		final CCTerm lhs = eq.getLhs();
		final CCTerm rhs = eq.getRhs();
		enqueuePath(eq.getLhs(), eq.getRhs());
		drainTodo();
		final Literal[] cycle = new Literal[mAllLiterals.size() + 1];
		int i = 0;
		cycle[i++] = eq;
		for (final Literal l: mAllLiterals) {
			cycle[i++] = l.negate();
		}
		final Clause c = new Clause(cycle);
		if (produceProofs) {
			// The disequality being violated is eq, which states value(lhs) == value(rhs) + eq.getOffset(); carry that
			// offset on the main diseq so the proof matches the (offset-aware) literal eq instead of a bare lhs == rhs.
			final SymmetricPair<CCParameter> diseq = new SymmetricPair<>(lhs, CCParameter.of(rhs, eq.getOffset()));
			c.setProof(new LeafNode(LeafNode.THEORY_CC, createAnnotation(diseq)));
		}
		return c;
	}

	/**
	 * The single conflict explainer for an offset cycle: a bridge equality
	 * {@code lhs = rhs + offset} together with the existing congruence-class
	 * path(s) implies a contradiction to a known disequality
	 * {@code lhsDiseq != rhsDiseq + k}. The bridge is justified by a real equality
	 * literal {@code equality} or, congruence ({@code equality == null}), by the
	 * argument equalities; {@code offset} is the bridge's offset, {@code 0} for a
	 * congruence). The disequality can stem from two sources:
	 * <ul>
	 * <li><b>Disequality clash</b> ({@code diseq != null}): a registered
	 * disequality {@code diseq} forbids exactly the offset at which the bridge
	 * would unite. The disequality is between {@code lhsDiseq} and {@code rhsDiseq}
	 * with exactly the right offset. The clause carries {@code diseq} as its
	 * positive literal.</li>
	 * <li><b>Trivial clash</b> ({@code diseqLit == null}):
	 * {@code lhsDiseq}/{@code rhsDiseq} are provable distinct by integer reasoning
	 * (an integer shared term forced to a non-integer value,
	 * {@code to_real a == 1/2}), or — in the same-class case — the same term at two
	 * offsets. The contradiction is a trivial axiom; the clause contains no
	 * positive literal.</li>
	 * </ul>
	 *
	 * <p>
	 * This covers both the cross-class and same-class shapes uniformly.
	 * <ul>
	 * <li><b>Cross-class</b>
	 * ({@code lhs.getRepresentative() != rhs.getRepresentative()}): this is most
	 * likely caused by a disequality (diseq != null), but it could also be an
	 * integer conflict.</li>
	 * <li><b>Same-class</b> in that case most likely lhsDiseq=rhsDiseq = lhs (or
	 * rhs). and the equality closes a cycle within one class against the existing
	 * path from {@code rhs} back to {@code lhs} with a mismatched offset. The
	 * source half is empty and the trivial diseq is
	 * {@code lhs != lhs + (bridgeOff − pathOffset)}. The diseq is null.</li>
	 * </ul>
	 *
	 * @param lhs           one side of equality.
	 * @param rhs           one side of equality.
	 * @param offset        offset for rhs in the equality.
	 * @param equality      the equality that caused the conflicting merge (null for
	 *                      congruence).
	 * @param lhsDiseq      the side of the diseq that matches lhs (not necessarily
	 *                      the diseq's lhs).
	 * @param rhsDiseq      the side of the diseq that matches rhs.
	 * @param diseq         the disequality (null if trivial arithmetic
	 *                      disequality).
	 * @param produceProofs true if proof production is enabled.
	 */
	public Clause computeMergeConflictCycle(final CCTerm lhs, final CCTerm rhs, final Rational offset,
			final CCEquality equality, final CCTerm lhsDiseq, final CCTerm rhsDiseq, final CCEquality diseq,
			final boolean produceProofs) {
		assert lhs.getRepresentative() == lhsDiseq.getRepresentative();
		assert rhs.getRepresentative() == rhsDiseq.getRepresentative();
		// Justify the bridge edge lhs = rhs + offset.
		if (equality != null) {
			mAllLiterals.add(equality);
		} else {
			// Congruence bridge: the argument equalities justify lhs == rhs (and build the
			// subpaths that the proof generator uses to resolve the bridge step).
			assert offset.equals(Rational.ZERO);
			enqueueCongruence((CCAppTerm) lhs, (CCAppTerm) rhs);
		}
		// Two single-class paths for lhs and rhs, each offset-correct on its own. These are merged later by hand into a
		// single main path, so they are not standalone subpaths: computePath builds them without caching in
		// mVisited, so they neither enter mAllPaths nor short-circuit a later standalone request for the same edge
		// (their congruence dependencies are still enqueued and collected through the drain below).
		final SubPath segSrc = computePath(lhsDiseq, lhs);
		final SubPath segDest = computePath(rhs, rhsDiseq);
		drainTodo();
		final Literal[] clause = new Literal[mAllLiterals.size() + (diseq != null ? 1 : 0)];
		int i = 0;
		// The separating disequality (if any) is the cycle's only positive literal; the merge falsifies it.
		if (diseq != null) {
			clause[i++] = diseq;
		}
		for (final Literal l : mAllLiterals) {
			clause[i++] = l.negate();
		}
		final Clause c = new Clause(clause);
		if (produceProofs) {
			// paramsSrc = [srcEnd@0, ..., lhs@offLhs] (anchored and oriented at srcEnd). Shift the destination half into
			// the source half's frame: after the bridge edge (value(lhs) == value(rhsTerm) + bridgeOff), rhsTerm sits at
			// lhs's offset plus bridgeOff; rendering the dest half anchored there yields it already shifted, so the main
			// path is a plain concatenation.
			final CCParameter[] paramsSrc = segSrc != null ? segSrc.getParams(lhsDiseq) : new CCParameter[] { lhsDiseq };
			assert paramsSrc[paramsSrc.length - 1].getCCTerm() == lhs : "src path must end at lhs + offset";
			final CCParameter destAnchor =
					CCParameter.of(rhs, paramsSrc[paramsSrc.length - 1].getOffset().add(offset));
			final CCParameter[] paramsDest =
					segDest != null ? segDest.getParams(destAnchor) : new CCParameter[] { destAnchor };
			final CCParameter[] mainPath = new CCParameter[paramsSrc.length + paramsDest.length];
			System.arraycopy(paramsSrc, 0, mainPath, 0, paramsSrc.length);
			System.arraycopy(paramsDest, 0, mainPath, paramsSrc.length, paramsDest.length);
			assert mainPath[0].getCCTerm() == lhsDiseq : "main path must start at lhs of diseq";
			assert mainPath[mainPath.length - 1].getCCTerm() == rhsDiseq : "main path must end at rhs of diseq";
			// The remaining subpaths (congruences within either half, plus the bridge's argument subpaths) keep deriving
			// their offsets the usual way. segSrc/segDest were built off the work list and never entered mAllPaths, so
			// mAllPaths is exactly the other paths (the constructor only iterates it, so no copy is needed).
			// The clashing equality: a concrete disequality discharged against diseqLit, or (shared case) the trivially
			// distinct shared values discharged by an EQ/LA lemma.
			final SymmetricPair<CCParameter> diseqPair = new SymmetricPair<>(mainPath[0],
					mainPath[mainPath.length - 1]);
			c.setProof(new LeafNode(LeafNode.THEORY_CC,
					new CCAnnotation(diseqPair, mainPath, mAllPaths, CCAnnotation.RuleKind.CONG)));
		}
		return c;
	}

	public Clause computeDTLemma(final CCEquality propagatedEq, final DataTypeLemma lemma,
			final boolean produceProofs) {
		for (final SymmetricPair<CCTerm> reason : lemma.getReason()) {
			enqueuePath(reason.getFirst(), reason.getSecond());
		}
		drainTodo();

		final Literal[] negLits = new Literal[mAllLiterals.size() + (propagatedEq != null ? 1 : 0)];
		int i = 0;
		if (propagatedEq != null) {
			negLits[i++] = propagatedEq;
		}
		for (final Literal l : mAllLiterals) {
			negLits[i++] = l.negate();
		}
		final Clause c = new Clause(negLits);
		if (produceProofs) {
			// the main equality carries the offset of a numeric constructor field.
			c.setProof(new LeafNode(LeafNode.THEORY_DT, new CCAnnotation(lemma.getMainEquality(), mAllPaths, lemma)));
		}
		return c;
	}

	/**
	 * Compute the earliest decide level at which the path between lhs and rhs exists. There must be a path, i.e.
	 * {@code lhs.getRepresentative() == rhs.getRepresentative()}.
	 *
	 * @param lhs
	 *            the start of the path
	 * @param rhs
	 *            the end of the path
	 * @return the earliest decide level.
	 */
	public int computeDecideLevel(final CCTerm lhs, final CCTerm rhs) {
		enqueuePath(lhs, rhs);
		drainTodo();
		int depth = 0;
		for (final Literal l : mAllLiterals) {
			depth = Math.max(depth, l.getAtom().getDecideLevel());
		}
		return depth;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("CongruencePath[");
		sb.append(mAllLiterals.toString());
		sb.append(']');
		return sb.toString();
	}
}
