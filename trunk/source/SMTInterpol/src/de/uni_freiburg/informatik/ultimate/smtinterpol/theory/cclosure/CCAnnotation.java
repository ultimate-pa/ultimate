/*
 * Copyright (C) 2014-2016 University of Freiburg
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

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CongruencePath.SubPath;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.WeakCongruencePath.WeakSubPath;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * Annotations for congruence-closure theory lemmas and array theory lemmas.
 *
 * A cc theory lemma is annotated with a set of paths and literals on these path. A special role plays the diseq
 * literal, which is the only positive literal in a cc clause. In the negated clause this is the disequality that is in
 * conflict with the other equalities.
 *
 * The main path (index 0) starts and ends with one side of the diseq literal. Every step must either be explained by a
 * literal from the clause (litsOnPaths != null), or by a congruence, i.e., there two consecutive function applications
 * on a path and for each argument where they differ there is another path explaining the equality Trivial paths for
 * equal func or arg terms are omitted.
 *
 * Like cc lemmas an array lemma proofs an equality from other equalities, but unlike a CC lemma it may also require
 * disequalities, to prove that store terms didn't change the value of the array at some index. We distinguish two array
 * lemmas.
 * <ul>
 * <li>{@code read-over-weakeq}: Here diseq is an equality of the form {@code (select a i) == (select b j)}. The main
 * paths of the proof are a strong path for the indices {@code i == j} and a weak path for the arrays {@code a == j} for
 * index {@code i}.</li>
 * <li>{@code weakeq-ext}: Here diseq is an equality between arrays {@code a == b}}. The main path is a store path (like
 * a weak path but without an index). This path proves that the arrays can at most differ at the store indices occuring
 * in that path. For every store index used in the main path, there is another weak path between the same arrays for
 * that store index to prove that the arrays do not differ at that store index.</li>
 * </ul>
 *
 * A strong path (a1 ... an) proves the equality between a1 and an. For every intermediate step ai to ai+1, there must
 * be either an equality {@code ai == ai+1} in the conflict (the negated clause), or it is a congruence
 * {@code f(x1,...,xn) == f(y1,...,yn)}, i.e. ai and ai+1 are application terms with the same function symbol and for
 * each pair {@code (xi,yi)}, either xi and yi are the same term, or there is an equality between them, or there is
 * another strong path (xi ... yi) proving their equality.
 *
 * A weak path i (a1 ... an) proves that the arrays a1 and an do not differ on index i. Every intermediate step can
 * either be an equality step (same cases as for strong path), a store edge, i.e. ai is the term
 * {@code (store ai+1 j v)} or {@code ai+1} is the term {@code (store ai j v)} and the literal {@code i != j} appears in
 * the negated clause, or there exists another strong path ((select ai j) ... (select ai+1 k)), and there are proofs for
 * {@code i==j} and {@code i==k} (like in the congruence case these can be explicit equalities, strong paths or j/k is
 * identical to i).
 *
 * A store path is like a weak path without an index and without the last select case. The store indices are the indices
 * j occcuring for a store step, e.g., if {@code ai+1} is {@code (store ai j v)}.
 *
 * When converting the ArrayAnnotation to a lemma, we out-source the auxiliary strong paths into separate lemmas. So
 * whenever a strong path or a weak paths uses another strong path as explanation, we include an equality literal and
 * proof the equality in a separate CC lemma. The same is done for congruences, i.e., we include an equality literal for
 * the congruence and prove the congruence in a separate lemma.
 *
 * @author hoenicke, schindler
 */

public class CCAnnotation implements IAnnotation {

	/**
	 * The kind of the array axiom. We support two kinds, read-over-weakeq and weakeq-ext.
	 */
	enum RuleKind {
		/**
		 * Congruence closure lemma, i.e., congruence or transitivity.
		 */
		CC(":CC"),
		/**
		 * Read over weak equivalence lemma.
		 */
		READ_OVER_WEAKEQ(":read-over-weakeq"),
		/**
		 * Extensionality lemma.
		 */
		WEAKEQ_EXT(":weakeq-ext"),
		/**
		 * read over weak equivalence with const lemma.
		 */
		READ_CONST_WEAKEQ(":read-const-weakeq"),
		/**
		 * Constant array extensionality.
		 */
		CONST_WEAKEQ(":const-weakeq");

		/**
		 * The annotation key used in the array lemma.
		 */
		String mKind;

		private RuleKind(final String kind) {
			mKind = kind;
		}

		/**
		 * Get the name of rule. This can be used in an annotation for the lemma.
		 *
		 * @return the annotation key for the array lemma.
		 */
		public String getKind() {
			return mKind;
		}
	}

	/**
	 * The kind of rule. This is CC for all congruence lemmas (transitivity, congruence); for array lemmas this is the
	 * kind of array lemma.
	 */
	final RuleKind mRule;

	/**
	 * The disequality of the theory lemma. This is the only positive atom in the generated theory clause. If this is
	 * null, then the first and last element in the main paths are distinct terms.
	 */
	final SymmetricPair<CCTerm> mDiseq;

	/**
	 * A sequence of paths. The main path with index 0 must always exist and explain the diseq. The other paths must be
	 * in such an order that later paths explain congruences on earlier.
	 */
	final CCTerm[][] mPaths;

	final CCTerm[] mWeakIndices;

	public CCAnnotation(final SymmetricPair<CCTerm> diseq, final Collection<SubPath> paths, final RuleKind rule) {
		super();
		mDiseq = diseq;
		mPaths = new CCTerm[paths.size()][];
		mWeakIndices = new CCTerm[mPaths.length];
		int i = 0;
		for (final SubPath p : paths) {
			mPaths[i] = p.getTerms();
			mWeakIndices[i] = p instanceof WeakSubPath ? ((WeakSubPath) p).getIndex() : null;
			i++;
		}
		mRule = rule;
	}

	public SymmetricPair<CCTerm> getDiseq() {
		return mDiseq;
	}

	public CCTerm[][] getPaths() {
		return mPaths;
	}

	public CCTerm[] getWeakIndices() {
		return mWeakIndices;
	}

	/**
	 * Convert the annotation into a term suitable to add to the proof tree. The output is a lemma where all congruences
	 * are explained by auxiliary CC lemmas in a hyper-resolution step.
	 *
	 * @param clause
	 *            The clause containing this annotation.
	 * @param theory
	 *            The term unifier.
	 * @return the proof term in form of a resolution step of the central lemma and the auxiliary lemmas which are
	 *         obtained from subpaths explaining congruences in the main lemma - or, if there are no congruences, just
	 *         the central lemma.
	 */
	@Override
	public Term toTerm(final Clause clause, final Theory theory) {
		return new CCProofGenerator(this).toTerm(clause, theory);
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append('(');
		sb.append(mDiseq);
		for (int i = 0; i < mPaths.length; i++) {
			if (mWeakIndices[i] != null) {
				sb.append(" :weak ").append(mWeakIndices[i]).append(' ');
			} else {
				sb.append(" :strong ");
			}
			sb.append("(");
			String comma = "";
			for (final CCTerm term : mPaths[i]) {
				sb.append(comma).append(term);
				comma = " ";
			}
			sb.append(")");
		}
		sb.append(')');
		return sb.toString();
	}
}
