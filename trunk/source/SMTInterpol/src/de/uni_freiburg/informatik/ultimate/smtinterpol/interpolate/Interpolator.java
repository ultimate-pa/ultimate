/*
 * Copyright (C) 2009-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.InterpolatorClauseInfo.ClauseKind;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitesimalNumber;

/**
 * This interpolator computes the interpolants of a refutation for the partitions specified by the user. It works in a
 * non-recursive way on the proof tree generated during SMT solving.
 *
 * @author Jochen Hoenicke, Tanja Schindler
 */
public class Interpolator extends NonRecursive {

	/**
	 * The name of the auxiliary EQ predicate used for CC interpolation.
	 */
	public static final String EQ = "@EQ";

	private final TerminationRequest mCancel;

	InterpolantChecker mChecker;
	final Collection<Term> mAllAssertions;

	LogProxy mLogger;
	Theory mTheory;
	int mNumInterpolants;

	Occurrence mFullOccurrence;

	/**
	 * Array encoding the tree-structure for tree interpolants. The interpolants are always required to be in post-order
	 * tree traversal. The i-th element of this array contains the lowest index occuring in the sub-tree with the i-th
	 * element as root node. This is the index of the lower left-most node in the sub-tree. The nodes between
	 * m_startOfSubtrees[i] and i form the sub-tree with the root i. To traverse the children of a node the following
	 * pattern can be used:
	 *
	 * <pre>
	 * for (int child = node-1; child >= m_startOfSubtrees[node];
	 *      child = m_startOfSubtrees[child] - 1) {
	 *      ...
	 * }
	 * </pre>
	 *
	 * To find the parent of a node do:
	 *
	 * <pre>
	 * int parent = node + 1;
	 * while (m_startOfSubtrees[parent] > node)
	 * 	parent++;
	 * </pre>
	 */
	int[] mStartOfSubtrees;
	HashMap<Term, Occurrence> mSymbolPartition;
	HashMap<String, Integer> mPartitions;
	HashMap<Term, LitInfo> mAtomOccurenceInfos;
	HashMap<Term, Term[]> mInterpolants;
	HashMap<Term, InterpolatorClauseInfo> mClauseTermInfos;
	HashMap<Term, InterpolatorAtomInfo> mLiteralTermInfos;
	HashMap<FunctionSymbol, Occurrence> mFunctionSymbolOccurrenceInfos;
	HashMap<Term, TermVariable> mMixedTermAuxEq;
	HashMap<TermVariable, Term> mPurifyDefinitions;

	private final HashMap<Term, Term[]> mProvedClauses = new HashMap<>();
	private final ArrayDeque<Term[]> mProvedClauseStack = new ArrayDeque<>();

	/**
	 * The interpolants which have already been computed. Used to store the interpolants preceding a resolution before
	 * combining them. In the end of the interpolation, it contains only the interpolants for the refutation,
	 * corresponding to the specified partitions.
	 */
	private final ArrayDeque<Term[]> mInterpolated = new ArrayDeque<>();

	/**
	 * This class goes through the proof terms of the proof tree for the input clause. It checks if the interpolant for
	 * a term already exists, and if not, it enqueues new walkers depending on the node type.
	 *
	 * @param proofTerm
	 *            the proof term to interpolate
	 */
	public static class ProofTreeWalker implements Walker {
		private final Term mProofTerm;

		public ProofTreeWalker(final Term proofTerm) {
			mProofTerm = proofTerm;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final Interpolator proofTreeWalker = (Interpolator) engine;
			if (proofTreeWalker.checkCacheForInterpolants(mProofTerm)) {
				return;
			}
			final InterpolatorClauseInfo proofTermInfo = ((Interpolator) engine).getClauseTermInfo(mProofTerm);
			if (proofTermInfo.isResolution()) {
				((Interpolator) engine).walkResolutionNode(mProofTerm);
			} else {
				((Interpolator) engine).walkLeafNode(mProofTerm);
			}
		}
	}

	/**
	 * This class combines the interpolants preceding a resolution step and adds the interpolant of the resolvent to the
	 * Interpolated stack.
	 *
	 * @param the
	 *            pivot of the resolution step
	 */
	public static class CombineInterpolants implements Walker {
		private final Term mPivot;

		public CombineInterpolants(final Term pivot) {
			mPivot = pivot;
		}

		@Override
		public void walk(final NonRecursive engine) {
			((Interpolator) engine).combine(mPivot);
		}
	}

	/**
	 * This class summarizes a hyper-resolution step by adding the interpolants to the cache, checking for inductivity,
	 * and providing debug messages.
	 */
	public static class SummarizeResolution implements Walker {
		private final Term mProofTerm;

		public SummarizeResolution(final Term proofTerm) {
			mProofTerm = proofTerm;
		}

		@Override
		public void walk(final NonRecursive engine) {
			((Interpolator) engine).summarize(mProofTerm);
		}
	}

	public Interpolator(final LogProxy logger, final Script checkingSolver, final Collection<Term> allAssertions,
			final Theory theory, final Set<String>[] partitions, final int[] startOfSubTrees,
			final TerminationRequest cancel) {
		assert partitions.length == startOfSubTrees.length;
		mPartitions = new HashMap<>();
		for (int i = 0; i < partitions.length; i++) {
			final Integer part = i;
			for (final String name : partitions[i]) {
				mPartitions.put(name, part);
			}
		}
		mLogger = logger;
		mCancel = cancel;
		if (checkingSolver != null) {
			mChecker = new InterpolantChecker(this, checkingSolver);
			mChecker.assertUnpartitionedFormulas(allAssertions, mPartitions.keySet());
		}
		mAllAssertions = allAssertions;
		mTheory = theory;
		mNumInterpolants = partitions.length - 1;
		mFullOccurrence = new Occurrence();
		mFullOccurrence.occursIn(-1);

		mStartOfSubtrees = startOfSubTrees;
		mSymbolPartition = new HashMap<>();
		mAtomOccurenceInfos = new HashMap<>();
		mInterpolants = new HashMap<>();
		mClauseTermInfos = new HashMap<>();
		mLiteralTermInfos = new HashMap<>();
		mFunctionSymbolOccurrenceInfos = new HashMap<>();
		mMixedTermAuxEq = new HashMap<>();
		mPurifyDefinitions = new HashMap<>();
	}

	public LogProxy getLogger() {
		return mLogger;
	}

	public Term[] getInterpolants(final Term proofTree) {
		colorTermsInAssertions();
		colorLiterals(proofTree);
		final Term[] interpolants = interpolate(proofTree);
		for (int i = 0; i < interpolants.length; i++) {
			interpolants[i] = unfoldLAs(interpolants[i]);
		}
		if (mChecker != null) {
			if (!mChecker.checkFinalInterpolants(mPartitions, interpolants)) {
				throw new SMTLIBException("generated interpolants did not pass sanity check");
			}
		}
		return interpolants;
	}

	public Term[] interpolate(final Term proofTerm) {
		if (mInterpolants.containsKey(proofTerm)) {
			mLogger.debug("Proof term %s has been interpolated before.", proofTerm.hashCode());
			return mInterpolants.get(proofTerm);
		}
		if (mCancel.isTerminationRequested()) {
			throw new SMTLIBException("Termination requested (timeout or resource limit)");
		}

		Term[] interpolants = null;

		run(new ProofTreeWalker(proofTerm));

		// collect the final interpolants from the Interpolated stack
		interpolants = collectInterpolated();
		return interpolants;
	}

	/**
	 * Enqueue walkers for the single steps in a hyper-resolution step.
	 *
	 * @param clause
	 *            the resolvent clause
	 */
	private void walkResolutionNode(final Term proofTerm) {
		if (mCancel.isTerminationRequested()) {
			throw new SMTLIBException("Termination requested (timeout or resource limit)");
		}
		// get primary and antecedents
		final Term resolutionTerm = proofTerm instanceof AnnotatedTerm ? ((AnnotatedTerm) proofTerm).getSubterm()
				: proofTerm;
		final Term[] resArgs = ((ApplicationTerm) resolutionTerm).getParameters();
		final Term pivot = resArgs[0];
		final Term prim = resArgs[1];
		final Term antecedent = resArgs[2];

		if (proofTerm instanceof AnnotatedTerm) {
			enqueueWalker(new SummarizeResolution(proofTerm));
		}
		// enqueue walkers for primary and antecedents in reverse order
		// alternating with Combine walkers
		enqueueWalker(new CombineInterpolants(pivot));
		enqueueWalker(new ProofTreeWalker(antecedent));
		enqueueWalker(new ProofTreeWalker(prim));
	}

	/**
	 * Interpolate a proof tree leaf depending on its type.
	 *
	 * @param clause
	 *            the clause to interpolate
	 */
	@SuppressWarnings("unused")
	private void walkLeafNode(final Term leaf) {
		if (mCancel.isTerminationRequested()) {
			throw new SMTLIBException("Termination requested (timeout or resource limit)");
		}
		final InterpolatorClauseInfo leafTermInfo = getClauseTermInfo(leaf);
		final Term[] clause = leafTermInfo.getLiterals();
		Term[] interpolants;
		if (leafTermInfo.getLeafKind() == ClauseKind.INPUT) {
			if (isSkolemizedFormula(leaf)) {
				throw new UnsupportedOperationException("Interpolation not supported for quantified formulae.");
			}
			final String source = leafTermInfo.getSource();
			final int partition = mPartitions.containsKey(source) ? mPartitions.get(source) : 0;
			interpolants = new Term[mNumInterpolants];
			for (int i = 0; i < mNumInterpolants; i++) {
				interpolants[i] = mStartOfSubtrees[i] <= partition && partition <= i ? mTheory.mFalse : mTheory.mTrue;
			}
		} else if (leafTermInfo.getLeafKind() == ClauseKind.LEMMA) {
			switch (leafTermInfo.getLemmaType()) {
			case ":EQ":
				interpolants = new EQInterpolator(this).computeInterpolants(leafTermInfo);
				break;
			case ":cong":
			case ":trans": {
				final CCInterpolator ipolator = new CCInterpolator(this);
				interpolants = ipolator.computeInterpolants(leafTermInfo);
				// Replace non-shared symbols in interpolant.
				final InterpolantPurifier purifier = new InterpolantPurifier(this);
				for (int i = 0; i < interpolants.length; i++) {
					interpolants[i] = purifier.purify(interpolants[i], i);
				}
				break;
			}
			case ":LA": {
				final LAInterpolator ipolator = new LAInterpolator(this);
				interpolants = ipolator.computeInterpolants(leafTermInfo);
				break;
			}
			case ":trichotomy": {
				final LAInterpolator ipolator = new LAInterpolator(this);
				interpolants = ipolator.computeTrichotomyInterpolants(leafTermInfo);
				break;
			}
			case ":read-over-weakeq":
			case ":weakeq-ext":
			case ":const-weakeq":
			case ":read-const-weakeq": {
				final ArrayInterpolator ipolator = new ArrayInterpolator(this);
				interpolants = ipolator.computeInterpolants(leafTermInfo);
				break;
			}
			case ":inst": {
				final CCInterpolator ipolator = new CCInterpolator(this);
				interpolants = ipolator.interpolateInstantiation(leafTermInfo);
				// Replace non-shared symbols in interpolant.
				final InterpolantPurifier purifier = new InterpolantPurifier(this);
				for (int i = 0; i < interpolants.length; i++) {
					interpolants[i] = purifier.purify(interpolants[i], i);
					// Check for unsupported variables and add quantifiers if necessary.
					interpolants[i] = addQuantifier(interpolants[i], i, clause);
				}
				break;
			}
			case ":dt-project":
			case ":dt-cases":
			case ":dt-cycle":
			case ":dt-disjoint":
			case ":dt-injective": 
			case ":dt-constructor":
			case ":dt-tester":
			case ":dt-unique": {
				final DatatypeInterpolator ipolator = new DatatypeInterpolator(this);
				interpolants = ipolator.computeDatatypeInterpolants(leafTermInfo);
				break;
			}
			default:
				throw new UnsupportedOperationException("Unknown lemma type!");
			}
		} else {
			throw new UnsupportedOperationException("Cannot interpolate " + leaf);
		}

		// add the interpolants to the stack and the cache
		mInterpolated.add(interpolants);
		mProvedClauseStack.add(clause);
		mInterpolants.put(leaf, interpolants);
		mProvedClauses.put(leaf, clause);
		mLogger.debug("Interpolating leaf %s %s yields ...", leaf.hashCode(), leaf);
		for (int i = 0; i <= mNumInterpolants - 1; i++) {
			mLogger.debug(interpolants[i]);
		}

		if ((true || Config.DEEP_CHECK_INTERPOLANTS) && mChecker != null) {
			mChecker.checkInductivity(leafTermInfo.getLiterals(), interpolants);
		}
	}

	private Term[] computeResolution(Term[] primary, Term[] antecedent, Term pivot) {
		final HashSet<Term> newClause = new LinkedHashSet<>(antecedent.length + primary.length);
		for (final Term lit : primary) {
			if (lit != pivot) {
				newClause.add(lit);
			}
		}
		final Term negPivot = pivot.getTheory().not(pivot);
		for (final Term lit : antecedent) {
			if (lit != negPivot) {
				newClause.add(lit);
			}
		}
		return newClause.toArray(new Term[newClause.size()]);
	}

	/**
	 * Combine the interpolants preceding a resolution step depending on the type of the pivot.
	 *
	 * @param pivot
	 *            the pivot of the resolution step
	 */
	private void combine(final Term pivotAtom) {
		final LitInfo pivInfo = mAtomOccurenceInfos.get(pivotAtom);

		final Term[] antecedentInterp = collectInterpolated();
		final Term[] primInterp = collectInterpolated();
		final Term[] interp = new Term[mNumInterpolants];

		final Term[] antecedentClause = mProvedClauseStack.removeLast();
		final Term[] primClause = mProvedClauseStack.removeLast();
		final Term[] provedClause = computeResolution(primClause, antecedentClause, pivotAtom);

		final InterpolantPurifier purifier = new InterpolantPurifier(this);
		for (int i = 0; i < mNumInterpolants; i++) {
			mLogger.debug("Pivot %3$s%4$s on interpolants %1$s and %2$s gives...", primInterp[i], antecedentInterp[i],
					pivotAtom, pivInfo);
			if (pivInfo.isALocal(i)) {
				interp[i] = mTheory.or(primInterp[i], antecedentInterp[i]);
			} else if (pivInfo.isBLocal(i)) {
				interp[i] = mTheory.and(primInterp[i], antecedentInterp[i]);
			} else if (pivInfo.isAB(i)) {
				interp[i] = mTheory.ifthenelse(pivotAtom, antecedentInterp[i], primInterp[i]);
			} else {
				final InterpolatorAtomInfo pivotTermInfo = getAtomTermInfo(pivotAtom);
				if (pivotTermInfo.isCCEquality() || pivotTermInfo.isLAEquality()) {
					// pivot is eq and occurs in primary,
					final Term eqIpol = primInterp[i];
					final Term neqIpol = antecedentInterp[i];
					interp[i] = mixedEqInterpolate(eqIpol, neqIpol, pivInfo.mMixedVar);
				} else if (pivotTermInfo.isBoundConstraint()) {
					interp[i] = mixedPivotLA(antecedentInterp[i], primInterp[i], pivInfo.mMixedVar);
				} else {
					throw new UnsupportedOperationException("Cannot handle mixed literal " + pivotAtom);
				}
			}
			interp[i] = purifier.purify(interp[i], i);
			interp[i] = addQuantifier(interp[i], i, provedClause);
			mLogger.debug(interp[i]);
		}

		// add the interpolants and the proved clause to the stack
		mProvedClauseStack.add(provedClause);
		mInterpolated.add(interp);
	}

	/**
	 * Summarize the results of a hyper-resolution step. Introduce quantifiers if
	 * necessary.
	 *
	 * @param clause the interpolated clause
	 */
	@SuppressWarnings("unused")
	private void summarize(final Term proofTerm) {
		Term[] interpolants = null;
		interpolants = mInterpolated.getLast();

		if (Config.DEEP_CHECK_INTERPOLANTS && mChecker != null) {
			mChecker.checkInductivity(mProvedClauseStack.getLast(), interpolants);
		}

		mInterpolants.put(proofTerm, interpolants);
		mProvedClauses.put(proofTerm, mProvedClauseStack.getLast());
		mLogger.debug("...which is the resulting interpolant for Term %s ", proofTerm.hashCode());

	}

	/**
	 * Get the last interpolant array from the Interpolated stack.
	 */
	protected final Term[] collectInterpolated() {
		return mInterpolated.removeLast();
	}

	/**
	 * Check if a clause has been interpolated before. If so, add the interpolant array to the Interpolated stack.
	 *
	 * @param clause
	 *            the clause to interpolate
	 * @return true iff clause has been interpolated before
	 */
	public boolean checkCacheForInterpolants(final Term proofTerm) {
		final Term[] interpolants = mInterpolants.get(proofTerm);
		if (interpolants != null) {
			// add the interpolant to the interpolated stack
			mInterpolated.add(interpolants);
			mProvedClauseStack.add(mProvedClauses.get(proofTerm));
			return true;
		}
		return false;
	}

	class Occurrence {
		BitSet mInA;
		BitSet mInB;

		public Occurrence() {
			mInA = new BitSet(mNumInterpolants + 1);
			mInA.set(mNumInterpolants);
			mInB = new BitSet(mNumInterpolants + 1);
		}

		public Occurrence(final BitSet inA, final BitSet inB) {
			mInA = inA;
			mInB = inB;
		}

		public void occursIn(final int partition) {
			for (int i = 0; i <= mNumInterpolants; i++) {
				if (partition == -1) {
					mInA.set(i);
					if (i != mNumInterpolants) { // All literals are in A in the root
						mInB.set(i);
					}
				} else if (i < partition || mStartOfSubtrees[i] > partition) {
					mInB.set(i);
				} else {
					mInA.set(i);
				}
			}
		}

		public boolean isALocalInSomeChild(final int partition) {
			for (int i = partition - 1; i >= mStartOfSubtrees[partition];) {
				if (mInA.get(i)) {
					return true;
				}
				i = mStartOfSubtrees[i] - 1;
			}
			return false;
		}

		public boolean contains(final int partition) {
			if (partition == -1) {
				for (int i = 0; i <= mNumInterpolants; i++) {
					if (!mInA.get(i) || !mInB.get(i)) {
						return false;
					}
				}
				return true;
			}
			if (!mInA.get(partition)) {
				return false;
			}
			if (mInB.get(partition)) {
				return true;
			}
			for (int i = partition - 1; i >= mStartOfSubtrees[partition];) {
				if (!mInB.get(i)) {
					return false;
				}
				i = mStartOfSubtrees[i] - 1;
			}
			return true;
		}

		public Occurrence intersect(final Occurrence other) {
			final BitSet inA = (BitSet) mInA.clone();
			final BitSet inB = (BitSet) mInB.clone();
			inA.and(other.mInA);
			inB.and(other.mInB);
			return new Occurrence(inA, inB);
		}

		public boolean isAorShared(final int partition) {
			return mInA.get(partition);
		}

		public boolean isBorShared(final int partition) {
			return mInB.get(partition);
		}

		public boolean isALocal(final int partition) {
			return mInA.get(partition) && !mInB.get(partition);
		}

		public boolean isBLocal(final int partition) {
			return mInB.get(partition) && !mInA.get(partition);
		}

		public boolean isAB(final int partition) {
			return mInA.get(partition) && mInB.get(partition);
		}

		public boolean isMixed(final int partition) {
			return !mInA.get(partition) && !mInB.get(partition);
		}

		@Override
		public String toString() {
			return "[" + mInA + "|" + mInB + "]";
		}

		/**
		 * Find the first A-local colored node. Every occurrence has a A-local chain from such a node to the root node
		 * and all other nodes are not A-local.
		 *
		 * @return the first A-local colored node.
		 */
		public int getALocalColor() {
			int color = mInA.nextSetBit(0);
			if (mInB.get(color)) {
				color = mInB.nextClearBit(color);
			}
			return color;
		}
	}

	class LitInfo extends Occurrence {
		/**
		 * The mixed variable for mixed literals (in at least one partition).
		 */
		TermVariable mMixedVar;
		/**
		 * Tells for an equality whether the A part is the Lhs or the Rhs.
		 */
		Occurrence mLhsOccur;
		/**
		 * Gives for an inequality the A part.
		 */
		InterpolatorAffineTerm[] mAPart;

		public LitInfo() {
			super();
		}

		public LitInfo(final BitSet inA, final BitSet inB) {
			super(inA, inB);
		}

		public TermVariable getMixedVar() {
			return mMixedVar;
		}

		public Occurrence getLhsOccur() {
			return mLhsOccur;
		}

		public InterpolatorAffineTerm getAPart(final int p) {
			return mAPart[p];
		}
	}

	Term unfoldLAs(final Term interpolant) {
		final TermTransformer substitutor = new TermTransformer() {
			@Override
			public void convert(Term term) {
				if (LAInterpolator.isLATerm(term)) {
					term = ((AnnotatedTerm) term).getSubterm();
				}
				super.convert(term);
			}
		};
		return substitutor.transform(interpolant);
	}

	private void colorTermsInAssertions() {
		for (final Term a : mAllAssertions) {
			int part = -1;
			Term subTerm = a;
			if (a instanceof AnnotatedTerm) {
				final AnnotatedTerm annTerm = (AnnotatedTerm) a;
				for (final Annotation an : annTerm.getAnnotations()) {
					if (SMTLIBConstants.NAMED.equals(an.getKey()) && mPartitions.containsKey(an.getValue())) {
						part = mPartitions.get(an.getValue());
					}
				}
				subTerm = annTerm.getSubterm();
			}
			new ColorAssertion().color(subTerm, part);
		}
	}

	private class ColorAssertion extends NonRecursive {
		private HashSet<Term> mSeen;

		void color(final Term term, final int part) {
			mSeen = new HashSet<>();
			run(new ColorTerm(term, part));
		}

		/**
		 * Color all ground terms occurring in a given term according to the given partition.
		 */
		private class ColorTerm extends NonRecursive.TermWalker {

			final int mPart;

			public ColorTerm(final Term term, final int part) {
				super(term);
				mPart = part;
			}

			@Override
			public void walk(final NonRecursive walker) {
				if (mSeen.add(mTerm)) {
					super.walk(walker);
				}
			}

			@Override
			public void walk(final NonRecursive walker, final ConstantTerm term) {
				// Nothing to do
			}

			@Override
			public void walk(final NonRecursive walker, final AnnotatedTerm term) {
				walker.enqueueWalker(new ColorTerm(term.getSubterm(), mPart));
			}

			@Override
			public void walk(final NonRecursive walker, final ApplicationTerm term) {
				final FunctionSymbol fsym = term.getFunction();
				final Term def = fsym.getDefinition();
				if (def != null) {
					final Term[] params = term.getParameters();
					final HashMap<TermVariable, Term> subs = new HashMap<>();
					for (int i = 0; i < params.length; i++) {
						subs.put(term.getFunction().getDefinitionVars()[i], params[i]);
					}
					final FormulaUnLet unletter = new FormulaUnLet();
					unletter.addSubstitutions(subs);
					final Term expanded = unletter.unlet(def);
					walker.enqueueWalker(new ColorTerm(expanded, mPart));
				} else {
					if (!term.getFunction().isIntern()) {
						if (term.getFreeVars().length == 0) {
							addOccurrence(term, mPart);
						}
						// Color function symbol for quantified interpolation
						addOccurrence(fsym, mPart);
					}
					for (final Term param : ((ApplicationTerm) mTerm).getParameters()) {
						walker.enqueueWalker(new ColorTerm(param, mPart));
					}
				}
			}

			@Override
			public void walk(final NonRecursive walker, final LetTerm term) {
				walker.enqueueWalker(new ColorTerm(new FormulaUnLet().unlet(term), mPart));
			}

			@Override
			public void walk(final NonRecursive walker, final LambdaTerm term) {
				walker.enqueueWalker(new ColorTerm(term.getSubterm(), mPart));
			}

			@Override
			public void walk(final NonRecursive walker, final QuantifiedFormula term) {
				walker.enqueueWalker(new ColorTerm(term.getSubformula(), mPart));
			}

			@Override
			public void walk(final NonRecursive walker, final TermVariable term) {
				// Nothing to do
			}

			@Override
			public void walk(final NonRecursive walker, final MatchTerm term) {
				walker.enqueueWalker(new ColorTerm(term.getDataTerm(), mPart));
				for (final Term t : term.getCases()) {
					walker.enqueueWalker(new ColorTerm(t, mPart));
				}
			}
		}
	}

	/**
	 * Color the input literals. This gets the source for the literals from the LeafNodes.
	 */
	private void colorLiterals(final Term proofTree) {

		final Set<Term> seen = new HashSet<>();
		final Deque<Term> todoStack = new ArrayDeque<>();
		todoStack.add(proofTree);

		while (!todoStack.isEmpty()) {
			if (mCancel.isTerminationRequested()) {
				throw new SMTLIBException("Termination requested (timeout or resource limit)");
			}
			final Term proofTerm = todoStack.pop();
			if (!seen.add(proofTerm)) {
				continue;
			}
			final InterpolatorClauseInfo proofTermInfo = getClauseTermInfo(proofTerm);
			if (proofTermInfo.isResolution()) {
				final Term resolutionTerm = proofTerm instanceof AnnotatedTerm
						? ((AnnotatedTerm) proofTerm).getSubterm()
						: proofTerm;
				final Term[] resArgs = ((ApplicationTerm) resolutionTerm).getParameters();
				// recursively go through the sub proofs
				todoStack.add(resArgs[1]);
				todoStack.add(resArgs[2]);
			} else {
				assert proofTermInfo.isLeaf();
				if (proofTermInfo.getLeafKind() == ClauseKind.INPUT) {
					// Color the literals
					final String source = proofTermInfo.getSource();
					final Term[] lits = proofTermInfo.getLiterals();
					final int partition = mPartitions.containsKey(source) ? mPartitions.get(source) : -1;

					for (int i = 0; i < lits.length; i++) {
						final Term atom = getAtom(lits[i]);
						LitInfo info = mAtomOccurenceInfos.get(atom);
						if (info == null) {
							info = new LitInfo();
							mAtomOccurenceInfos.put(atom, info);
						}
						if (!info.contains(partition)) {
							info.occursIn(partition);
							addOccurrence(atom, partition);
						}

						// Color all symbols occurring in the literal.
						colorSymbols(atom, partition);
					}
				}
			}
		}
	}

	Occurrence getOccurrence(final FunctionSymbol func) {
		if (func.isIntern() && !func.getName().startsWith("@AUX") && !func.getName().startsWith("@skolem")) {
			return mFullOccurrence;
		}
		return mFunctionSymbolOccurrenceInfos.get(func);
	}

	Occurrence getOccurrence(final Term term) {
		if (term instanceof ConstantTerm) {
			return mFullOccurrence;
		}

		Occurrence result = mSymbolPartition.get(term);
		if (result == null) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final FunctionSymbol func = appTerm.getFunction();
			final Occurrence fsymOccurrence = getOccurrence(func);
			result = fsymOccurrence;
			for (final Term param : appTerm.getParameters()) {
				// TODO make non-recursive
				result = result.intersect(getOccurrence(param));
			}
			final BitSet veryMixed = new BitSet();
			veryMixed.set(0, mNumInterpolants + 1);
			veryMixed.andNot(result.mInA);
			veryMixed.andNot(result.mInB);
			if (veryMixed.nextSetBit(0) >= 0) {
				// this is a very mixed term. The color in the veryMixed partition will
				// be set to that of the function symbol.
				final BitSet litInA = (BitSet) result.mInA.clone();
				final BitSet litInB = (BitSet) result.mInB.clone();
				litInA.or(veryMixed);
				litInA.and(fsymOccurrence.mInA);
				litInB.or(veryMixed);
				litInB.and(fsymOccurrence.mInB);
				result = new Occurrence(litInA, litInB);
			}
			mSymbolPartition.put(term, result);
		}
		return result;
	}

	void addOccurrence(final Term term, final int part) {
		if (term instanceof ConstantTerm) {
			/* Constant terms are always implicitly shared. */
			return;
		}
		Occurrence occ = mSymbolPartition.get(term);
		if (occ != null && occ.contains(part)) {
			/* Already colored correctly */
			return;
		}
		/* Recursively color subterms */
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm at = (ApplicationTerm) term;
			for (final Term p : at.getParameters()) {
				addOccurrence(p, part);
			}
			/* AUX and skolem functions must be colored for the quantifier interpolation */
			final FunctionSymbol fsym = at.getFunction();
			if (!fsym.isIntern() || fsym.getName().startsWith("@AUX") || fsym.getName().contains("skolem")) {
				addOccurrence(fsym, part);
			}
			return;
		}
		/* Create occurrence if it is *not* an internal function and if it does not exists yet */
		if (occ == null) {
			occ = new Occurrence();
			mSymbolPartition.put(term, occ);
		}
		occ.occursIn(part);
	}

	/**
	 * Add the occurrence of non-intern function symbols and of the intern AUX and
	 * skolem function symbols, needed for quantifier interpolation.
	 */
	void addOccurrence(final FunctionSymbol symbol, final int part) {
		Occurrence occ = mFunctionSymbolOccurrenceInfos.get(symbol);
		/* Create occurrence if it does not exist yet */
		if (occ == null) {
			occ = new Occurrence();
			mFunctionSymbolOccurrenceInfos.put(symbol, occ);
		} else if (occ.contains(part)) {
			/* Already colored correctly */
			return;
		}
		occ.occursIn(part);
	}

	HashSet<Term> getSubTerms(final Term literal) {
		final HashSet<Term> subTerms = new HashSet<>();
		final ArrayDeque<Term> todo = new ArrayDeque<>();
		todo.addLast(literal);
		while (!todo.isEmpty()) {
			final Term term = todo.removeLast();
			if (subTerms.add(term)) {
				if (term instanceof ApplicationTerm) {
					final ApplicationTerm appTerm = (ApplicationTerm) term;
					for (final Term sub : appTerm.getParameters()) {
						todo.addLast(sub);
					}
				}
			}
		}
		return subTerms;
	}

	// Collect all subterms in a literal. This function ignores annotations while
	// looking for subterms.
	HashSet<Term> getAllSubTerms(final Term literal) {
		final HashSet<Term> subTerms = new HashSet<>();
		final ArrayDeque<Term> todo = new ArrayDeque<>();

		todo.addLast(literal);
		while (!todo.isEmpty()) {
			final Term term = todo.removeLast();
			if (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				// TODO: Not intern and not @EQ @AUX
				if (!appTerm.getFunction().equals(mTheory.mNot)) {
					subTerms.add(appTerm);
				}
				for (final Term sub : appTerm.getParameters()) {
					todo.addLast(sub);
				}
			}
			if (term instanceof AnnotatedTerm) {
				todo.add(((AnnotatedTerm) term).getSubterm());
			}
		}
		return subTerms;
	}

	LitInfo getAtomOccurenceInfo(final Term atom) {
		assert !isNegatedTerm(atom);
		LitInfo result = mAtomOccurenceInfos.get(atom);
		if (result == null) {
			mLogger.info("colorLiteral: " + atom);
			result = colorMixedLiteral(atom);
		}
		return result;
	}

	public List<Term> getSubTermsForAtom(final Term atom) {
		final InterpolatorAtomInfo atomInfo = getAtomTermInfo(atom);
		/*
		 * The sort of the auxiliary variable created for this atom. We need this since we internally represent integral
		 * constants in LIRA logics as Int even if they should have sort Real.
		 */
		if (atomInfo.isCCEquality()) {
			final ApplicationTerm eq = atomInfo.getEquality();
			return Arrays.asList(eq.getParameters());
		} else {
			assert atomInfo.isLAEquality() || atomInfo.isBoundConstraint();
			final List<Term> subterms = new ArrayList<>();
			subterms.addAll(atomInfo.getAffineTerm().getSummands().keySet());
			return subterms;
		}
	}

	/**
	 * Compute the LitInfo for a mixed Literal.
	 */
	public LitInfo colorMixedLiteral(final Term atom) {
		assert !isNegatedTerm(atom);
		assert !mAtomOccurenceInfos.containsKey(atom);

		final InterpolatorAtomInfo atomInfo = getAtomTermInfo(atom);

		final List<Term> subterms = getSubTermsForAtom(atom);
		final LitInfo info = computeMixedOccurrence(subterms);
		mAtomOccurenceInfos.put(atom, info);

		final BitSet shared = new BitSet();
		shared.or(info.mInA);
		shared.or(info.mInB);
		if (shared.nextClearBit(0) >= mNumInterpolants) {
			return info;
		}

		info.mMixedVar = mTheory.createFreshTermVariable("litaux", subterms.get(0).getSort());

		if (atomInfo.isCCEquality()) {
			final ApplicationTerm eq = atomInfo.getEquality();
			info.mLhsOccur = getOccurrence(eq.getParameters()[0]);
		} else if (atomInfo.isBoundConstraint() || atomInfo.isLAEquality()) {
			final InterpolatorAffineTerm lv = atomInfo.getAffineTerm();
			assert lv.getSummands().size() > 1 : "Mixed Literal with only one subterm: " + lv + " atom: " + atom;

			info.mAPart = new InterpolatorAffineTerm[mNumInterpolants];
			for (int part = 0; part < mNumInterpolants; part++) {
				if (!info.isMixed(part)) {
					continue;
				}

				final InterpolatorAffineTerm sumApart = new InterpolatorAffineTerm();
				for (final Entry<Term, Rational> en : lv.getSummands().entrySet()) {
					final Term var = en.getKey();
					final Occurrence occ = getOccurrence(var);
					if (occ.isALocal(part)) {
						final Rational coeff = en.getValue();
						sumApart.add(coeff, var);
					}
				}

				info.mAPart[part] = sumApart;
			}
		}
		return info;
	}

	private LitInfo computeMixedOccurrence(final List<Term> subterms) {
		LitInfo info;
		final BitSet inA = new BitSet(mNumInterpolants + 1);
		inA.set(0, mNumInterpolants + 1);
		final BitSet inB = new BitSet(mNumInterpolants + 1);
		inB.set(0, mNumInterpolants);
		for (final Term st : subterms) {
			final Occurrence occInfo = getOccurrence(st);
			inA.and(occInfo.mInA);
			inB.and(occInfo.mInB);
		}
		info = new LitInfo(inA, inB);
		return info;
	}

	/**
	 * This term transformer substitutes an auxiliary variable by an arbitrary term. This is used for the LA and UF
	 * resolution rule. For the UF resolution rule, it will replace the auxiliary variable by the term that must be
	 * equal to it due to an EQ(x,s) term in the other interpolant. For the LA resolution rule, this will replace the
	 * auxiliary variable by -s1/c1 - i in F1/F2 (see paper). The replacement term may contain other auxiliary variables
	 * that will be replaced later. It may only contain auxiliary variables for equalities with the negated equality in
	 * the clause or auxiliary variables for LA literals that are bound by a surrounding LATerm.
	 *
	 * @author hoenicke
	 */
	public static class Substitutor extends TermTransformer {
		TermVariable mTermVar;
		Term mReplacement;

		public Substitutor(final TermVariable termVar, final Term replacement) {
			mTermVar = termVar;
			mReplacement = replacement;
		}

		private static boolean isSMTAffineTerm(final Term term) {
			if (!term.getSort().isNumericSort()) {
				return false;
			}
			if (term instanceof ApplicationTerm) {
				final FunctionSymbol fsym = ((ApplicationTerm) term).getFunction();
				return fsym.isIntern() && (fsym.getName() == "+" || fsym.getName() == "-" || fsym.getName() == "*"
						|| fsym.getName() == "to_real");
			} else if (term instanceof ConstantTerm) {
				return true;
			}
			return false;
		}

		@Override
		public void convert(final Term oldTerm) {
			if (isSMTAffineTerm(oldTerm)) {
				final SMTAffineTerm oldAffine = new SMTAffineTerm(oldTerm);
				final Term[] oldSummands =
						oldAffine.getSummands().keySet().toArray(new Term[oldAffine.getSummands().size()]);
				/* recurse into LA term */
				enqueueWalker(new Walker() {
					@Override
					public void walk(final NonRecursive engine) {
						final Substitutor me = (Substitutor) engine;
						final Term[] newSummands = me.getConverted(oldSummands);
						// did we change something?
						if (newSummands == oldSummands) {
							me.setResult(oldTerm);
							return;
						}
						// create new SMTAffineTerm from newSummands and old coefficients
						final SMTAffineTerm newAffine = new SMTAffineTerm();
						for (int i = 0; i < oldSummands.length; i++) {
							newAffine.add(oldAffine.getSummands().get(oldSummands[i]), newSummands[i]);
						}
						newAffine.add(oldAffine.getConstant());
						// create the new LA term
						me.setResult(newAffine.toTerm(oldTerm.getSort()));
					}
				});
				pushTerms(oldSummands);
				return;
			} else if (LAInterpolator.isLATerm(oldTerm)) {
				final InterpolatorAffineTerm oldS = LAInterpolator.getS(oldTerm);
				final InfinitesimalNumber oldK = LAInterpolator.getK(oldTerm);
				final Term oldF = LAInterpolator.getF(oldTerm);
				final Term[] oldSummands =
						oldS.getSummands().keySet().toArray(new Term[oldS.getSummands().size()]);
				/* recurse into LA term */
				enqueueWalker(new Walker() {
					@Override
					public void walk(final NonRecursive engine) {
						final Substitutor me = (Substitutor) engine;
						final Term newF = me.getConverted();
						final Term[] newSummands = me.getConverted(oldSummands);
						// did we change something?
						if (newF == oldF && newSummands == oldSummands) {
							me.setResult(oldTerm);
							return;
						}
						// create newS term from newSummands and old coefficients
						final InterpolatorAffineTerm newS = new InterpolatorAffineTerm();
						for (int i = 0; i < oldSummands.length; i++) {
							newS.add(oldS.getSummands().get(oldSummands[i]), newSummands[i]);
						}
						newS.add(oldS.getConstant());
						// create the new LA term
						me.setResult(LAInterpolator.createLATerm(newS, oldK, newF));
					}
				});
				pushTerm(oldF);
				pushTerms(oldSummands);
				return;
			} else if (oldTerm.equals(mTermVar)) {
				setResult(mReplacement);
			} else {
				super.convert(oldTerm);
			}
		}
	}

	/**
	 * Substitute termVar by replacement in mainTerm. This will also work correctly with LATerms.
	 *
	 * @param mainTerm
	 *            the term where the replacement is done.
	 * @param termVar
	 *            the variable to replace.
	 * @param replacement
	 *            the replacement term.
	 * @return the substituted term.
	 */
	Term substitute(final Term mainTerm, final TermVariable termVar, final Term replacement) {
		return new Substitutor(termVar, replacement).transform(mainTerm);
	}

	class EQSubstitutor extends TermTransformer {
		Term mI2;
		TermVariable mAuxVar;

		EQSubstitutor(final Term i2, final TermVariable auxVar) {
			mI2 = i2;
			mAuxVar = auxVar;
		}

		@Override
		public void convert(final Term term) {
			assert term != mAuxVar;
			if (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				final FunctionSymbol func = appTerm.getFunction();
				final Term[] params = appTerm.getParameters();
				if (func.isIntern() && func.getName().equals(EQ) && params[0] == mAuxVar) {
					assert params.length == 2;
					setResult(substitute(mI2, mAuxVar, params[1]));
					return;
				}
			}
			super.convert(term);
		}
	}

	/**
	 * This term transformer substitutes a given term by another term. It is used to
	 * remove non-shared symbols from a provisional interpolant.
	 */
	class TermSubstitutor extends TermTransformer {
		Term mTerm;
		Term mReplacement;

		TermSubstitutor(final Term term, final Term replacement) {
			mTerm = term;
			mReplacement = replacement;
		}

		@Override
		public void convert(final Term oldTerm) {
			// assert oldTerm != mReplacement;

			if (oldTerm == mTerm) {
				setResult(mReplacement);
			} else if (oldTerm instanceof ApplicationTerm) {
				final Term[] oldParams = ((ApplicationTerm) oldTerm).getParameters();
				enqueueWalker(new Walker() {
					@Override
					public void walk(final NonRecursive engine) {
						final TermSubstitutor ts = (TermSubstitutor) engine;
						final String funName = ((ApplicationTerm) oldTerm).getFunction().getName();
						final Term[] newParams = ts.getConverted(oldParams);

						if (newParams == oldParams) {
							// Nothing changed.
							ts.setResult(oldTerm);
							return;
						}
						// Create a new Term from newParams and the function symbol
						final Term newTerm = mTheory.term(funName, newParams);
						ts.setResult(newTerm);
					}
				});
				pushTerms(oldParams);
				return;
			} else {
				super.convert(oldTerm);
			}
		}
	}

	/**
	 * Compute the interpolant for the resolution rule with a mixed equality as pivot. This is I1[I2(s_i)] for
	 * I1[EQ(x,s_i)] and I2(x).
	 *
	 * @param eqIpol
	 *            the interpolant I1[EQ(x,s_i)].
	 * @param neqIpol
	 *            the interpolant I2(x).
	 * @param mixedVar
	 *            the auxiliary variable x.
	 * @return the resulting interpolant.
	 */
	private Term mixedEqInterpolate(final Term eqIpol, final Term neqIpol,
			final TermVariable mixedVar) {
		final TermTransformer ipolator = new EQSubstitutor(neqIpol, mixedVar);
		return ipolator.transform(eqIpol);
	}

	static abstract class MixedLAInterpolator extends TermTransformer {
		TermVariable mMixedVar;
		Term mI2;
		AnnotatedTerm mLA1;

		public MixedLAInterpolator(final Term i2, final TermVariable mixed) {
			mMixedVar = mixed;
			mLA1 = null;
			mI2 = i2;
		}

		abstract Term interpolate(AnnotatedTerm la1, AnnotatedTerm la2);

		@Override
		public void convert(final Term term) {
			assert term != mMixedVar;
			if (LAInterpolator.isLATerm(term)) {
				final AnnotatedTerm laTerm = (AnnotatedTerm) term;
				final InterpolatorAffineTerm s2 = LAInterpolator.getS(term);
				if (s2.getSummands().get(mMixedVar) != null) { // NOPMD
					if (mLA1 == null) {
						/*
						 * We are inside I1. Remember the lainfo and push I2 on the convert stack. Also enqueue a walker
						 * that will remove m_LA1 once we are finished with I2.
						 */
						beginScope(new TermVariable[] { mMixedVar });
						mLA1 = laTerm;
						enqueueWalker(new Walker() {
							@Override
							public void walk(final NonRecursive engine) {
								((MixedLAInterpolator) engine).mLA1 = null;
								((MixedLAInterpolator) engine).endScope();
							}
						});
						pushTerm(mI2);
						return;
					} else {
						/*
						 * We are inside I2. Interpolate the LAInfos.
						 */
						setResult(interpolate(mLA1, laTerm));
						return;
					}
				}
			}
			super.convert(term);
		}
	}

	class RealInterpolator extends MixedLAInterpolator {
		public RealInterpolator(final Term i2, final TermVariable mixedVar) {
			super(i2, mixedVar);
		}

		@Override
		public Term interpolate(final AnnotatedTerm la1, final AnnotatedTerm la2) {
			// retrieve c1,c2,s2,s2
			final InterpolatorAffineTerm s1 = LAInterpolator.getS(la1);
			final Rational c1 = s1.getSummands().get(mMixedVar);
			final InfinitesimalNumber k1 = LAInterpolator.getK(la1);
			final InterpolatorAffineTerm s2 = LAInterpolator.getS(la2);
			final Rational c2 = s2.getSummands().get(mMixedVar);
			final InfinitesimalNumber k2 = LAInterpolator.getK(la2);
			assert c1.signum() * c2.signum() == -1;
			InfinitesimalNumber newK = k1.mul(c2.abs()).add(k2.mul(c1.abs()));

			// compute c1s2 + c2s1
			final InterpolatorAffineTerm c1s2c2s1 = new InterpolatorAffineTerm();
			c1s2c2s1.add(c1.abs(), s2);
			c1s2c2s1.add(c2.abs(), s1);
			assert !c1s2c2s1.getSummands().containsKey(mMixedVar);

			Term newF;
			if (s1.getConstant().mEps > 0 || s2.getConstant().mEps > 0) {
				// One of the inequalities is strict. In this case
				// c1s2c2s1 must also be a strict inequality and it is not
				// possible that c1s2c2s1 == 0 holds. Hence, we do not need
				// to substitute a shared term.
				newF = c1s2c2s1.toLeq0(mTheory);
				newK = InfinitesimalNumber.EPSILON.negate();
			} else if (k1.less(InfinitesimalNumber.ZERO)) {
				// compute -s1/c1
				final InterpolatorAffineTerm s1divc1 = new InterpolatorAffineTerm(s1);
				s1divc1.getSummands().remove(mMixedVar);
				s1divc1.mul(c1.inverse().negate());
				final Term s1DivByc1 = s1divc1.toSMTLib(mTheory, false);
				newF = substitute(la2.getSubterm(), mMixedVar, s1DivByc1);
				newK = k2;
			} else if (k2.less(InfinitesimalNumber.ZERO)) {
				// compute s2/c2
				final InterpolatorAffineTerm s2divc2 = new InterpolatorAffineTerm(s2);
				s2divc2.getSummands().remove(mMixedVar);
				s2divc2.mul(c2.inverse().negate());
				final Term s2DivByc2 = s2divc2.toSMTLib(mTheory, false);
				newF = substitute(la1.getSubterm(), mMixedVar, s2DivByc2);
				newK = k1;
			} else {
				final InterpolatorAffineTerm s1divc1 = new InterpolatorAffineTerm(s1);
				s1divc1.getSummands().remove(mMixedVar);
				s1divc1.mul(c1.inverse().negate());
				final Term s1DivByc1 = s1divc1.toSMTLib(mTheory, false);
				final Term f1 = substitute(la1.getSubterm(), mMixedVar, s1DivByc1);
				final Term f2 = substitute(la2.getSubterm(), mMixedVar, s1DivByc1);
				newF = mTheory.and(f1, f2);
				if (c1s2c2s1.isConstant()) {
					if (c1s2c2s1.getConstant().less(InfinitesimalNumber.ZERO)) {
						newF = mTheory.mTrue;
					}
				} else {
					final InterpolatorAffineTerm s3 = new InterpolatorAffineTerm(c1s2c2s1);
					s3.add(InfinitesimalNumber.EPSILON);
					newF = mTheory.or(s3.toLeq0(mTheory), newF);
				}
				newK = InfinitesimalNumber.ZERO;
			}
			return LAInterpolator.createLATerm(c1s2c2s1, newK, newF);
		}
	}

	class IntegerInterpolator extends MixedLAInterpolator {

		public IntegerInterpolator(final Term i2, final TermVariable mixedVar) {
			super(i2, mixedVar);
		}

		@Override
		public Term interpolate(final AnnotatedTerm la1, final AnnotatedTerm la2) {
			// retrieve c1,c2,s1,s2
			final InterpolatorAffineTerm s1 = LAInterpolator.getS(la1);
			final Rational c1 = s1.getSummands().get(mMixedVar);
			final InfinitesimalNumber k1 = LAInterpolator.getK(la1);
			final InterpolatorAffineTerm s2 = LAInterpolator.getS(la2);
			final Rational c2 = s2.getSummands().get(mMixedVar);
			final InfinitesimalNumber k2 = LAInterpolator.getK(la2);
			assert c1.isIntegral() && c2.isIntegral();
			assert c1.signum() * c2.signum() == -1;
			final Rational absc1 = c1.abs();
			final Rational absc2 = c2.abs();

			// compute c1s2 + c2s1
			final InterpolatorAffineTerm c1s2c2s1 = new InterpolatorAffineTerm();
			c1s2c2s1.add(absc1, s2);
			c1s2c2s1.add(absc2, s1);
			assert !c1s2c2s1.getSummands().containsKey(mMixedVar);

			// compute newk = c2k1 + c1k2 + c1c2;
			final Rational c1c2 = absc1.mul(absc2);
			final InfinitesimalNumber newK = k1.mul(absc2).add(k2.mul(absc1)).add(new InfinitesimalNumber(c1c2, 0));
			assert newK.isIntegral();

			final Rational k1c1 = k1.mReal.add(Rational.ONE).div(absc1).ceil();
			final Rational k2c2 = k2.mReal.add(Rational.ONE).div(absc2).ceil();
			Rational kc;
			Rational theC;
			InterpolatorAffineTerm theS;
			if (k1c1.compareTo(k2c2) < 0) {
				theC = c1;
				theS = s1;
				kc = k1c1;
			} else {
				theC = c2;
				theS = s2;
				kc = k2c2;
			}
			Term newF = mTheory.mFalse;
			// Use -s/c as start value.
			final InterpolatorAffineTerm sPlusOffset = new InterpolatorAffineTerm();
			sPlusOffset.add(theC.signum() > 0 ? Rational.MONE : Rational.ONE, theS);
			sPlusOffset.getSummands().remove(mMixedVar);
			Rational offset = Rational.ZERO;
			final Rational theCabs = theC.abs();
			if (theC.signum() < 0) {
				sPlusOffset.add(theCabs.add(Rational.MONE));
			}
			while (offset.compareTo(kc) <= 0) {
				Term x;
				if (mCancel.isTerminationRequested()) {
					throw new SMTLIBException("Termination requested (timeout or resource limit)");
				}
				x = sPlusOffset.toSMTLib(mTheory, true);
				if (theCabs != Rational.ONE) {
					x = mTheory.term("div", x, theCabs.toTerm(mTheory.getNumericSort()));
				}
				Term F1 = substitute(la1.getSubterm(), mMixedVar, x);
				Term F2 = substitute(la2.getSubterm(), mMixedVar, x);

				if (offset.compareTo(kc) == 0) {
					if (theS == s1) {
						F1 = mTheory.mTrue;
					} else {
						F2 = mTheory.mTrue;
					}
				}
				newF = mTheory.or(newF, mTheory.and(F1, F2));
				sPlusOffset.add(theC.negate());
				offset = offset.add(Rational.ONE);
			}
			return LAInterpolator.createLATerm(c1s2c2s1, newK, newF);
		}

	}

	/**
	 * Compute the interpolant for the resolution rule with a mixed inequality as pivot. This is I1[I2(LA3)] for I1[LA1]
	 * and I2[LA2]. Note that we use only one auxiliary variable, which corresponds to x_1 and -x_2 in the paper.
	 *
	 * @param leqItp
	 *            the interpolant I1[LA1].
	 * @param sgItp
	 *            the interpolant I2[LA2].
	 * @param mixedVar
	 *            the auxiliary variable x used in the la term.
	 * @return the resulting interpolant.
	 */
	public Term mixedPivotLA(final Term leqItp, final Term sgItp, final TermVariable mixedVar) {
		final MixedLAInterpolator ipolator;

		if (mixedVar.getSort().getName().equals("Real")) {
			ipolator = new RealInterpolator(sgItp, mixedVar);
		} else {
			ipolator = new IntegerInterpolator(sgItp, mixedVar);
		}
		final Term newI = ipolator.transform(leqItp);
		return newI;
	}

	/**
	 * Get all the information the interpolator needs for this term. Known InterpolatorTermInfos are stored in a HashMap
	 * to avoid recalculating them. This can be used for complex proof terms such as complete resolution steps or
	 * lemmata, but also for single literals.
	 */
	InterpolatorClauseInfo getClauseTermInfo(final Term term) {
		if (mClauseTermInfos.containsKey(term)) {
			return mClauseTermInfos.get(term);
		}
		final InterpolatorClauseInfo info = new InterpolatorClauseInfo(term);
		mClauseTermInfos.put(term, info);
		return info;
	}

	InterpolatorAtomInfo getAtomTermInfo(final Term term) {
		assert !isNegatedTerm(term);
		if (mLiteralTermInfos.containsKey(term)) {
			return mLiteralTermInfos.get(term);
		}
		final InterpolatorAtomInfo info = new InterpolatorAtomInfo(term);
		mLiteralTermInfos.put(term, info);
		return info;
	}

	/**
	 * Collect all non-logical symbols in a term.
	 */
	public HashSet<FunctionSymbol> getSymbols(final Term term) {
		assert term != null;

		final HashSet<FunctionSymbol> result = new HashSet<>();
		final HashSet<Term> visited = new HashSet<>();
		final Deque<Term> todoStack = new ArrayDeque<>();
		todoStack.add(term);

		while (!todoStack.isEmpty()) {
			Term t = todoStack.pop();
			while ((t instanceof AnnotatedTerm || t instanceof QuantifiedFormula)) {
				if (t instanceof QuantifiedFormula) {
					t = ((QuantifiedFormula) t).getSubformula();
				}
				if (t instanceof AnnotatedTerm) {
					t = ((AnnotatedTerm) t).getSubterm();
				}
			}

			if (t instanceof TermVariable || t instanceof ConstantTerm) {
				continue;
			}
			if (!visited.add(t)) {
				continue;
			}

			// Add symbol if it is not an internal symbol
			final ApplicationTerm at = (ApplicationTerm) t;
			final FunctionSymbol funSymbol = at.getFunction();
			if (!funSymbol.isIntern() || funSymbol.getName().startsWith("@AUX") || funSymbol.getName().contains("skolem")) {
				result.add(funSymbol);
			}
			// visit all children
			todoStack.addAll(Arrays.asList(at.getParameters()));
		}
		return result;
	}

	/**
	 * Return the depth of nested functions for a term with given depth.
	 */
	int getNestingDepth(final ApplicationTerm term, int n) {
		if (term.getParameters().length == 0) {
			return n;
		} else {
			int nMax = n;
			for (int i = 0; i < term.getParameters().length; i++) {
				if (term.getParameters()[i] instanceof TermVariable) {
					continue;
				}
				final int j = getNestingDepth((ApplicationTerm) term.getParameters()[i], n + 1);
				nMax = (j > nMax) ? j : nMax;
			}
			return nMax;
		}
	}

	/**
	 * Return a list of terms with descending number of nested function depth.
	 */
	ArrayList<Term> orderTerms(final HashSet<Term> terms) {
		final ArrayList<Term> ordered = new ArrayList<>();
		final HashMap<Term, Integer> info = new HashMap<>();

		// Collect nested function depth for all terms.
		for (final Term t : terms) {
			final ApplicationTerm at = (ApplicationTerm) t;

			if (info.get(at) == null) {
				info.put(at, getNestingDepth(at, 0));
			}
		}
		// Order terms in descending order of nested function depth.
		for (final Term t : terms) {
			final ApplicationTerm at = (ApplicationTerm) t;
			int n = 0;
			for (int i = 0; i < ordered.size(); i++) {
				if (info.get(at) > info.get(ordered.get(i))) {
					n = i;
					break;
				}
			}
			ordered.add(n, at);
		}
		return ordered;
	}

	/**
	 * Update the color of all non-logical symbols in a given term according to the
	 * given partition.
	 */
	public void colorSymbols(final Term literal, final int partition) {
		assert literal != null;

		final HashSet<FunctionSymbol> symbols = getSymbols(literal);
		for (final FunctionSymbol symbol : symbols) {
			Occurrence funOcc = new Occurrence();
			if (mFunctionSymbolOccurrenceInfos.containsKey(symbol)) {
				funOcc = mFunctionSymbolOccurrenceInfos.get(symbol);
			}
			funOcc.occursIn(partition);
			mFunctionSymbolOccurrenceInfos.put(symbol, funOcc);
		}
	}

	/**
	 * Get the purification variable for a term. This also creates the variable if
	 * it doesn't already exists.
	 *
	 * @param term the term to replace by a variable
	 * @return the term variable.
	 */
	public TermVariable getOrCreatePurificationVariable(Term term) {
		TermVariable auxVar = mMixedTermAuxEq.get(term);
		if (auxVar == null) {
			// Create fresh variable if it didn't exists.
			auxVar = mTheory.createFreshTermVariable("purAux", term.getSort());
			mMixedTermAuxEq.put(term, auxVar);
			mPurifyDefinitions.put(auxVar, term);
		}
		return auxVar;
	}

	/**
	 * Collect the set of supported variables relative to a given clause from a list
	 * of variables .
	 *
	 * @param clause The clause against which the variables are checked
	 * @return Set of TermVariables that are not supported by the clause
	 */
	private HashSet<TermVariable> getSupportedVariables(Term[] clause, int partition) {
		final HashSet<ApplicationTerm> visitedSupported = new HashSet<>();
		// first collect the top-level supported terms in the clause
		for (final Term lit : clause) {
			final Term atom = getAtom(lit);
			final LitInfo atomOccurrence = getAtomOccurenceInfo(atom);
			if (atomOccurrence.isMixed(partition)) {
				for (final Term term : getSubTermsForAtom(atom)) {
					addMixedSubTerms(term, getOccurrence(term), partition, visitedSupported);
				}
			} else {
				addMixedSubTerms(atom, atomOccurrence, partition, visitedSupported);
			}
		}

		// now mark all subterms of supported terms as supported as well and collect
		// their variables.
		final HashSet<TermVariable> supportedVars = new HashSet<>();
		final ArrayList<ApplicationTerm> todo = new ArrayList<>();
		todo.addAll(visitedSupported);
		while (!todo.isEmpty()) {
			final ApplicationTerm appTerm = todo.remove(todo.size() - 1);
			if (supportedVars.add(mMixedTermAuxEq.get(appTerm))) {
				for (final Term subTerm : Arrays.asList(appTerm.getParameters())) {
					if (subTerm instanceof ApplicationTerm) {
						todo.add((ApplicationTerm) subTerm);
					}
				}
			}
		}
		return supportedVars;
	}

	private void addMixedSubTerms(Term atom, Occurrence atomOccurrence, int partition,
			HashSet<ApplicationTerm> visitedSupported) {
		final HashSet<Term> visited = new HashSet<>();
		final ArrayList<Term> todo = new ArrayList<>();
		todo.add(atom);
		while (!todo.isEmpty()) {
			final Term term = todo.remove(todo.size() - 1);
			if (term instanceof ApplicationTerm) {
				if (visited.add(term)) {
					final ApplicationTerm appTerm = (ApplicationTerm) term;
					final Occurrence fsymOccurrence = getOccurrence(appTerm.getFunction());
					// check if function symbol is local to the wrong partition.
					if ((fsymOccurrence.isALocal(partition) && atomOccurrence.isBorShared(partition))
							|| (fsymOccurrence.isBLocal(partition) && atomOccurrence.isAorShared(partition))) {
						visitedSupported.add(appTerm);
					} else {
						todo.addAll(Arrays.asList(appTerm.getParameters()));
					}
				}
			}
		}

	}

	/**
	 * For a given set of variables and their mapping to the terms they replace,
	 * return a list where the given variables are ordered according to their
	 * dependencies, i.e. For v1, v2 with dependency v1=f(v2), we return [v2,v1].
	 * Only works if variable dependencies do not contain cycles.
	 *
	 * @param unsupported    Set of variables to be sorted.
	 * @param variableToTerm Set containing mapping between variables and the terms
	 *                       that they replaced.
	 * @return List of variables in dependency order.
	 */
	private List<TermVariable> sortVariables(Map<TermVariable, Term> map) {
		final HashMap<TermVariable, HashSet<TermVariable>> dependencies = new HashMap<>();

		// Build dependency map.
		for (final Entry<TermVariable, Term> e1 : map.entrySet()) {
			final Term t1 = e1.getValue();
			final HashSet<TermVariable> deps = new HashSet<>();
			for (final Entry<TermVariable, Term> e2 : map.entrySet()) {
				if (e1.equals(e2)) {
					continue;
				}
				final Term t2 = e2.getValue();
				// check if v2 is subTerm of v1
				final HashSet<Term> sub = getAllSubTerms(t1);
				if (sub.contains(t2)) {
					deps.add(e2.getKey());
				}
			}
			dependencies.put(e1.getKey(), deps);
		}

		final Deque<TermVariable> todoStack = new ArrayDeque<>(map.keySet());
		final List<TermVariable> ordered = new ArrayList<>();
		TermVariable seen = null;
		Boolean reset = true;

		// Compute dependency ordered list.
		while (!todoStack.isEmpty()) {
			final TermVariable tv = todoStack.pop();
			if (tv == seen) {
				throw new IllegalArgumentException("Variable dependencies must not contain cycles.");
			}
			// Only add a variable to the ordered list if all variables on which it depends
			// are already present.
			if (dependencies.get(tv).isEmpty() || ordered.containsAll(dependencies.get(tv))) {
				ordered.add(tv);
				reset = true;
				seen = tv;
			} else {
				todoStack.add(tv);
				if (reset) {
					seen = tv;
					reset = false;
				}
			}
		}
		return ordered;
	}

	/**
	 * Add quantifiers to the provisional interpolants for a given clause if the
	 * provisional interpolant contains auxiliary variables that are not supported
	 * by the clause.
	 *
	 * @param interpolants Set of provisional interpolants for the clause
	 * @param clause       The clause for which the interpolants should be computed
	 * @return The modified interpolant.
	 */
	private Term addQuantifier(Term interpolant, int partition, Term[] clause) {
		// Sort unsupported variables in dependency order.

		// Insert quantifiers for unsupported variables in inverse dependency order.
		final Set<TermVariable> supported = getSupportedVariables(clause, partition);
		final Map<TermVariable, Term> unsupportedFreeVars = new LinkedHashMap<>();
		for (final TermVariable freeVar : interpolant.getFreeVars()) {
			final Term definition = mPurifyDefinitions.get(freeVar);
			if (definition != null) {
				// this is a purified variable. Check whether it's in supported or a dependent
				// var is in supported
				boolean foundDependent = false;
				final HashSet<Term> visited = new HashSet<>();
				final ArrayList<Term> todo = new ArrayList<>();
				todo.add(definition);
				while (!todo.isEmpty()) {
					final Term term = todo.remove(todo.size() - 1);
					if (supported.contains(mMixedTermAuxEq.get(term))) {
						foundDependent = true;
						break;
					}
					if (term instanceof ApplicationTerm && visited.add(term)) {
						todo.addAll(Arrays.asList(((ApplicationTerm) term).getParameters()));
					}
				}
				if (!foundDependent) {
					unsupportedFreeVars.put(freeVar, definition);
				}
			}
		}
		final List<TermVariable> ordered = sortVariables(unsupportedFreeVars);
		Collections.reverse(ordered);
		for (final TermVariable var : ordered) {
			final FunctionSymbol outermost = ((ApplicationTerm) mPurifyDefinitions.get(var)).getFunction();
			if (mFunctionSymbolOccurrenceInfos.get(outermost).isALocal(partition)) {
				interpolant = mTheory.exists(new TermVariable[] { var }, interpolant);
			} else {
				interpolant = mTheory.forall(new TermVariable[] { var }, interpolant);
			}
		}
		return interpolant;
	}

	public boolean isNegatedTerm(final Term literal) {
		return literal instanceof ApplicationTerm && ((ApplicationTerm) literal).getFunction().getName().equals("not");
	}

	public Term getAtom(final Term literal) {
		return isNegatedTerm(literal) ? ((ApplicationTerm) literal).getParameters()[0] : literal;
	}

	private boolean isSkolemizedFormula(final Term leaf) {
		final InterpolatorClauseInfo info = getClauseTermInfo(leaf);
		for (final Term lit : info.getLiterals()) {
			if (containsSkolemVar(lit)) {
				return true;
			}
		}
		return false;
	}

	private boolean containsSkolemVar(final Term t) {
		if (t instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) t;
			final String f = appTerm.getFunction().getName();
			if (f.matches("@.*skolem.*")) {
				return true;
			}
			for (final Term arg : appTerm.getParameters()) {
				if (containsSkolemVar(arg)) {
					return true;
				}
			}
		}
		return false;
	}
}
