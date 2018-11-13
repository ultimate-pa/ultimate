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
import java.util.BitSet;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SolverOptions;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitNumber;

/**
 * This interpolator computes the interpolants of a refutation for the partitions specified by the user. It works in a
 * non-recursive way on the proof tree generated during SMT solving.
 *
 * @author Jochen Hoenicke, Tanja Schindler
 */
public class Interpolator extends NonRecursive {

	SMTInterpol mSmtSolver;
	Script mCheckingSolver;

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
	HashMap<Term, LitInfo> mLiteralInfos;
	HashMap<Term, Interpolant[]> mInterpolants;
	HashMap<Term, InterpolatorClauseTermInfo> mClauseTermInfos;
	HashMap<Term, InterpolatorLiteralTermInfo> mLiteralTermInfos;

	/**
	 * The interpolants which have already been computed. Used to store the interpolants preceding a resolution before
	 * combining them. In the end of the interpolation, it contains only the interpolants for the refutation,
	 * corresponding to the specified partitions.
	 */
	private final ArrayDeque<Interpolant[]> mInterpolated = new ArrayDeque<>();

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
			final InterpolatorClauseTermInfo proofTermInfo = ((Interpolator) engine).getClauseTermInfo(mProofTerm);
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

	public Interpolator(final LogProxy logger, final SMTInterpol smtSolver, final Script checkingSolver,
			final Theory theory, final Set<String>[] partitions, final int[] startOfSubTrees) {
		mPartitions = new HashMap<>();
		for (int i = 0; i < partitions.length; i++) {
			final Integer part = i;
			for (final String name : partitions[i]) {
				mPartitions.put(name, part);
			}
		}
		mLogger = logger;
		mSmtSolver = smtSolver;
		mCheckingSolver = checkingSolver;
		mTheory = theory;
		mNumInterpolants = partitions.length - 1;
		mFullOccurrence = new Occurrence();
		mFullOccurrence.occursIn(-1);

		mStartOfSubtrees = startOfSubTrees;
		mSymbolPartition = new HashMap<>();
		mLiteralInfos = new HashMap<>();
		mInterpolants = new HashMap<>();
		mClauseTermInfos = new HashMap<>();
		mLiteralTermInfos = new HashMap<>();
	}

	public Term[] getInterpolants(final Term proofTree) {
		colorLiterals();
		final Interpolant[] eqitps = interpolate(proofTree);
		final Term[] itpTerms = new Term[eqitps.length];
		for (int i = 0; i < eqitps.length; i++) {
			itpTerms[i] = unfoldLAs(eqitps[i]);
		}
		return itpTerms;
	}

	public Interpolant[] interpolate(final Term proofTerm) {
		if (mInterpolants.containsKey(proofTerm)) {
			mLogger.debug("Proof term %s has been interpolated before.", proofTerm.hashCode());
			return mInterpolants.get(proofTerm);
		}
		if (mSmtSolver.isTerminationRequested()) {
			throw new SMTLIBException("Timeout exceeded");
		}

		Interpolant[] interpolants = null;

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
		if (mSmtSolver.isTerminationRequested()) {
			throw new SMTLIBException("Timeout exceeded");
		}
		final InterpolatorClauseTermInfo proofTermInfo = getClauseTermInfo(proofTerm);
		// get primary and antecedents
		final Term prim = proofTermInfo.getPrimary();

		final AnnotatedTerm[] antecedents = proofTermInfo.getAntecedents();
		final int antNumber = antecedents.length;

		enqueueWalker(new SummarizeResolution(proofTerm));
		// enqueue walkers for primary and antecedents in reverse order
		// alternating with Combine walkers
		for (int i = antNumber - 1; i >= 0; i--) {
			final Term pivot = (Term) antecedents[i].getAnnotations()[0].getValue();
			final Term antecedent = antecedents[i].getSubterm();

			enqueueWalker(new CombineInterpolants(pivot));
			enqueueWalker(new ProofTreeWalker(antecedent));
		}
		enqueueWalker(new ProofTreeWalker(prim));
	}

	/**
	 * Interpolate a proof tree leaf depending on its type.
	 *
	 * @param clause
	 *            the clause to interpolate
	 */
	private void walkLeafNode(final Term leaf) {
		if (mSmtSolver.isTerminationRequested()) {
			throw new SMTLIBException("Timeout exceeded");
		}
		Interpolant[] interpolants = new Interpolant[mNumInterpolants];
		final InterpolatorClauseTermInfo leafTermInfo = getClauseTermInfo(leaf);
		if (leafTermInfo.getLeafKind().equals("@clause")) {
			final String source = leafTermInfo.getSource();
			final int partition = mPartitions.containsKey(source) ? mPartitions.get(source) : 0;
			interpolants = new Interpolant[mNumInterpolants];
			for (int i = 0; i < mNumInterpolants; i++) {
				interpolants[i] = new Interpolant(
						mStartOfSubtrees[i] <= partition && partition <= i ? mTheory.mFalse : mTheory.mTrue);
			}
		} else if (leafTermInfo.getLeafKind().equals("@lemma")) {
			if (leafTermInfo.getLemmaType().equals(":EQ")) {
				interpolants = computeEQInterpolant(leaf);
			} else if (leafTermInfo.getLemmaType().equals(":CC")) {
				final CCInterpolator ipolator = new CCInterpolator(this);
				final Term[] interpolantTerms = ipolator.computeInterpolants(leaf);
				interpolants = new Interpolant[mNumInterpolants];
				for (int j = 0; j < mNumInterpolants; j++) {
					interpolants[j] = new Interpolant(interpolantTerms[j]);
				}
			} else if (leafTermInfo.getLemmaType().equals(":LA") || leafTermInfo.getLemmaType().equals(":trichotomy")) {
				final LAInterpolator ipolator = new LAInterpolator(this);
				interpolants = ipolator.computeInterpolants(leaf);
			} else if ((Boolean) mSmtSolver.getOption(SolverOptions.ARRAY_INTERPOLATION)
					&& (leafTermInfo.getLemmaType().equals(":read-over-weakeq")
							|| leafTermInfo.getLemmaType().equals(":weakeq-ext")
							|| leafTermInfo.getLemmaType().equals(":const-weakeq")
							|| leafTermInfo.getLemmaType().equals(":read-const-weakeq"))) {
				final ArrayInterpolator ipolator = new ArrayInterpolator(this);
				final Term[] interpolantTerms = ipolator.computeInterpolants(leaf);
				for (int j = 0; j < mNumInterpolants; j++) {
					interpolants[j] = new Interpolant(interpolantTerms[j]);
				}
			} else {
				throw new UnsupportedOperationException("Unknown lemma type!");
			}
		} else {
			throw new UnsupportedOperationException("Cannot interpolate " + leaf);
		}

		if (Config.DEEP_CHECK_INTERPOLANTS && mCheckingSolver != null) {
			final HashSet<Term> lits = new HashSet<>();
			lits.addAll(leafTermInfo.getLiterals());
			checkInductivity(lits, interpolants);
		}

		// add the interpolants to the stack and the cache
		mInterpolated.add(interpolants);
		mInterpolants.put(leaf, interpolants);
		mLogger.debug("Interpolating leaf %s %s yields ...", leaf.hashCode(), leaf);
		for (int i = 0; i <= mNumInterpolants - 1; i++) {
			mLogger.debug(interpolants[i]);
		}
	}

	/**
	 * Combine the interpolants preceding a resolution step depending on the type of the pivot.
	 *
	 * @param pivot
	 *            the pivot of the resolution step
	 */
	private void combine(final Term pivot) {
		final InterpolatorLiteralTermInfo pivotTermInfo = getLiteralTermInfo(pivot);
		final Term pivotAtom = pivotTermInfo.getAtom();
		final LitInfo pivInfo = mLiteralInfos.get(pivotAtom);

		final Interpolant[] assInterp = collectInterpolated();
		final Interpolant[] primInterp = collectInterpolated();
		final Interpolant[] interp = new Interpolant[mNumInterpolants];

		for (int i = 0; i < mNumInterpolants; i++) {
			mLogger.debug("Pivot %3$s%4$s on interpolants %1$s and %2$s gives...", primInterp[i], assInterp[i],
					unquote(pivot), pivInfo);
			if (pivInfo.isALocal(i)) {
				interp[i] = new Interpolant(mTheory.or(primInterp[i].mTerm, assInterp[i].mTerm));
			} else if (pivInfo.isBLocal(i)) {
				interp[i] = new Interpolant(mTheory.and(primInterp[i].mTerm, assInterp[i].mTerm));
			} else if (pivInfo.isAB(i)) {
				interp[i] =
						new Interpolant(mTheory.ifthenelse(unquote(pivot), primInterp[i].mTerm, assInterp[i].mTerm));
			} else {
				if (pivotTermInfo.isCCEquality() || pivotTermInfo.isLAEquality()) {
					Interpolant eqIpol, neqIpol;
					if (!pivotTermInfo.isNegated()) {
						eqIpol = assInterp[i];
						neqIpol = primInterp[i];
					} else {
						eqIpol = primInterp[i];
						neqIpol = assInterp[i];
					}
					interp[i] = mixedEqInterpolate(eqIpol, neqIpol, pivInfo.mMixedVar);
				} else if (pivotTermInfo.isBoundConstraint()) {
					interp[i] = mixedPivotLA(assInterp[i], primInterp[i], pivInfo.mMixedVar);
				} else {
					throw new UnsupportedOperationException("Cannot handle mixed literal " + unquote(pivot));
				}
			}
			mLogger.debug(interp[i]);
		}
		// add the interpolants to the Interpolated stack
		mInterpolated.add(interp);
	}

	/**
	 * Summarize the results of a hyper-resolution step.
	 *
	 * @param clause
	 *            the interpolated clause
	 */
	private void summarize(final Term proofTerm) {
		Interpolant[] interpolants = null;
		interpolants = mInterpolated.getLast();
		final InterpolatorClauseTermInfo proofTermInfo = getClauseTermInfo(proofTerm);

		if (Config.DEEP_CHECK_INTERPOLANTS && mCheckingSolver != null) {
			final HashSet<Term> lits = new HashSet<>();
			if (proofTermInfo.getLiterals().isEmpty()) {
				proofTermInfo.computeResolutionLiterals(this);
			}
			lits.addAll(proofTermInfo.getLiterals());
			checkInductivity(lits, interpolants);
		}

		mInterpolants.put(proofTerm, interpolants);
		mLogger.debug("...which is the resulting interpolant for Term %s ", proofTerm.hashCode());

	}

	/**
	 * Get the last interpolant array from the Interpolated stack.
	 */
	protected final Interpolant[] collectInterpolated() {
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
		Interpolant[] interpolants = new Interpolant[mNumInterpolants];
		if (mInterpolants.containsKey(proofTerm)) {
			interpolants = mInterpolants.get(proofTerm);
			// add the interpolant to the interpolated stack
			mInterpolated.add(interpolants);
			return true;
		}
		return false;
	}

	class Occurrence {
		BitSet mInA;
		BitSet mInB;

		public Occurrence() {
			mInA = new BitSet(mNumInterpolants + 1);
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

	private Term unfoldLAs(final Interpolant interpolant) {
		final TermTransformer substitutor = new TermTransformer() {
			@Override
			public void convert(Term term) {
				if (term instanceof LATerm) {
					term = ((LATerm) term).mF;
				}
				super.convert(term);
			}
		};
		return substitutor.transform(interpolant.mTerm);
	}

	private void checkInductivity(final HashSet<Term> literals, final Interpolant[] ipls) {
		final int old = mLogger.getLoglevel();// NOPMD
		mLogger.setLoglevel(LogProxy.LOGLEVEL_ERROR);

		mCheckingSolver.push(1);

		/*
		 * initialize auxMaps, which maps for each partition the auxiliary variables for mixed literals to a new fresh
		 * constant.
		 */
		@SuppressWarnings("unchecked") // because Java Generics are broken :(
		final HashMap<TermVariable, Term>[] auxMaps = new HashMap[ipls.length];

		for (final Term lit : literals) {
			final InterpolatorLiteralTermInfo litTermInfo = getLiteralTermInfo(lit);
			final LitInfo info = getLiteralInfo(litTermInfo.getAtom());
			for (int part = 0; part < ipls.length; part++) {
				if (info.isMixed(part)) {
					final TermVariable tv = info.mMixedVar;
					final String name = ".check" + part + "." + tv.getName();
					mCheckingSolver.declareFun(name, new Sort[0], tv.getSort());
					final Term term = mCheckingSolver.term(name);
					if (auxMaps[part] == null) {
						auxMaps[part] = new HashMap<>();
					}
					auxMaps[part].put(tv, term);
				}
			}
		}
		final Term[] interpolants = new Term[ipls.length];
		for (int part = 0; part < ipls.length; part++) {
			final Term ipl = unfoldLAs(ipls[part]);
			if (auxMaps[part] == null) {
				interpolants[part] = ipl;
			} else {
				final TermVariable[] tvs = new TermVariable[auxMaps[part].size()];
				final Term[] values = new Term[auxMaps[part].size()];
				int i = 0;
				for (final Entry<TermVariable, Term> entry : auxMaps[part].entrySet()) {
					tvs[i] = entry.getKey();
					values[i] = entry.getValue();
					i++;
				}
				interpolants[part] = mTheory.let(tvs, values, ipl);
			}
		}

		for (int part = 0; part < ipls.length + 1; part++) {
			mCheckingSolver.push(1);
			for (final Entry<String, Integer> entry : mPartitions.entrySet()) {
				if (entry.getValue() == part) {
					mCheckingSolver.assertTerm(mTheory.term(entry.getKey()));
				}
			}
			for (Term lit : literals) {
				lit = mTheory.not(lit);
				final InterpolatorLiteralTermInfo litTermInfo = getLiteralTermInfo(lit);
				final LitInfo info = mLiteralInfos.get(litTermInfo.getAtom());
				if (info.contains(part)) {
					mCheckingSolver.assertTerm(lit);
				} else if (info.isBLocal(part)) {
					// nothing to do, literal cannot be mixed in sub-tree.
				} else if (info.isALocalInSomeChild(part)) {
					// nothing to do, literal cannot be mixed in node
					// or some direct children
				} else if (litTermInfo.isCCEquality()) {
					// handle mixed (dis)equalities.
					final ApplicationTerm cceq = litTermInfo.getEquality();
					Term lhs = cceq.getParameters()[0];
					Term rhs = cceq.getParameters()[1];
					for (int child = part - 1; child >= mStartOfSubtrees[part]; child = mStartOfSubtrees[child] - 1) {
						if (info.isMixed(child)) {
							if (info.getLhsOccur().isALocal(child)) {
								lhs = auxMaps[child].get(info.mMixedVar);
							} else {
								assert info.getLhsOccur().isBLocal(child);
								rhs = auxMaps[child].get(info.mMixedVar);
							}
						}
					}
					if (info.isMixed(part)) {
						if (info.getLhsOccur().isALocal(part)) {
							rhs = auxMaps[part].get(info.mMixedVar);
						} else {
							assert info.getLhsOccur().isBLocal(part);
							lhs = auxMaps[part].get(info.mMixedVar);
						}
						mCheckingSolver.assertTerm(mTheory.term("=", lhs, rhs));
					} else {
						if (litTermInfo.isNegated()) {
							mCheckingSolver.assertTerm(mTheory.not(mTheory.equals(lhs, rhs)));
						} else {
							mCheckingSolver.assertTerm(mTheory.equals(lhs, rhs));
						}
					}
				} else if (litTermInfo.isLAEquality() && litTermInfo.isNegated()) {
					// handle mixed LA disequalities.
					final InterpolatorAffineTerm at = new InterpolatorAffineTerm();
					final Term eq = mTheory.not(lit);
					final InterpolatorLiteralTermInfo eqTermInfo = getLiteralTermInfo(eq);
					for (int child = part - 1; child >= mStartOfSubtrees[part]; child = mStartOfSubtrees[child] - 1) {
						if (info.isMixed(child)) {
							// child and node are A-local.
							at.add(Rational.MONE, info.getAPart(child));
							at.add(Rational.ONE, auxMaps[child].get(info.mMixedVar));
						}
					}
					if (info.isMixed(part)) {
						assert info.mMixedVar != null;
						at.add(Rational.ONE, info.getAPart(part));
						at.add(Rational.MONE, auxMaps[part].get(info.mMixedVar));
						final boolean isInt = eqTermInfo.isInt();
						final Sort sort = mTheory.getSort(isInt ? "Int" : "Real");
						final Term t = at.toSMTLib(mTheory, isInt);
						final Term zero = Rational.ZERO.toTerm(sort);
						mCheckingSolver.assertTerm(mTheory.term("=", t, zero));
					} else {
						assert !at.isConstant();
						at.add(Rational.ONE, eqTermInfo.getLinVar());
						at.add(eqTermInfo.getBound().negate());
						final boolean isInt = eqTermInfo.isInt();
						final Sort sort = mTheory.getSort(isInt ? "Int" : "Real");
						final Term t = at.toSMTLib(mTheory, isInt);
						final Term zero = Rational.ZERO.toTerm(sort);
						mCheckingSolver.assertTerm(mTheory.not(mTheory.equals(t, zero)));
					}
				} else {
					// handle mixed LA inequalities and equalities.
					InterpolatorAffineTerm lv;
					InfinitNumber bound;
					if (litTermInfo.isBoundConstraint()) {
						bound = new InfinitNumber(litTermInfo.getBound(), 0);
						// adapt the bound for strict inequalities
						if (litTermInfo.isStrict()) {
							bound = bound.sub(litTermInfo.getEpsilon());
						}
						// get the inverse bound for negated literals
						if (litTermInfo.isNegated()) {
							bound = bound.add(litTermInfo.getEpsilon());
						}
						lv = litTermInfo.getLinVar();
					} else {
						assert litTermInfo.isLAEquality();
						lv = litTermInfo.getLinVar();
						bound = new InfinitNumber(litTermInfo.getBound(), 0);
					}

					// check if literal is mixed in part or some child partition.
					final InterpolatorAffineTerm at = new InterpolatorAffineTerm();
					for (int child = part - 1; child >= mStartOfSubtrees[part]; child = mStartOfSubtrees[child] - 1) {
						if (info.isMixed(child)) {
							// child and node are A-local.
							at.add(Rational.MONE, info.getAPart(child));
							at.add(Rational.ONE, auxMaps[child].get(info.mMixedVar));
						}
					}
					if (info.isMixed(part)) {
						assert info.mMixedVar != null;
						at.add(Rational.ONE, info.getAPart(part));
						at.add(Rational.MONE, auxMaps[part].get(info.mMixedVar));
					} else {

						at.add(Rational.ONE, lv);
						at.add(bound.negate());
					}
					if (litTermInfo.isBoundConstraint()) {
						if (litTermInfo.isNegated()) {
							at.negate();
						}
						mCheckingSolver.assertTerm(at.toLeq0(mTheory));
					} else {
						final boolean isInt = at.isInt();
						final Sort sort = mTheory.getSort(isInt ? "Int" : "Real");
						final Term t = at.toSMTLib(mTheory, isInt);
						final Term zero = Rational.ZERO.toTerm(sort);
						Term eqTerm = mTheory.term("=", t, zero);
						if (!info.isMixed(part) && litTermInfo.isNegated()) {
							eqTerm = mTheory.term("not", eqTerm);
						}
						mCheckingSolver.assertTerm(eqTerm);
					}
				}
			}
			for (int child = part - 1; child >= mStartOfSubtrees[part]; child = mStartOfSubtrees[child] - 1) {
				mCheckingSolver.assertTerm(interpolants[child]);
			}
			if (part < interpolants.length) {
				mCheckingSolver.assertTerm(mTheory.term("not", interpolants[part]));
			}
			if (mCheckingSolver.checkSat() != LBool.UNSAT) {
				throw new AssertionError();
			}
			mCheckingSolver.pop(1);
		}
		mCheckingSolver.pop(1);
		mLogger.setLoglevel(old);
	}

	/**
	 * Compute the interpolant for a Nelson-Oppen equality clause. This is a theory lemma of the form equality implies
	 * equality, where one equality is congruence closure and one is linear arithmetic.
	 *
	 * @param ccEq
	 *            the congruence closure equality atom
	 * @param laEq
	 *            the linear arithmetic equality atom
	 * @param sign
	 *            the sign of l1 in the conflict clause. This is -1 if l1 implies l2, and +1 if l2 implies l1.
	 */
	private Interpolant[] computeEQInterpolant(final Term eqLemma) {
		Interpolant[] interpolants = null;

		final InterpolatorClauseTermInfo lemmaTermInfo = getClauseTermInfo(eqLemma);
		final Term ccEq = lemmaTermInfo.getCCEq();
		final Term laEq = lemmaTermInfo.getLAEq();
		final InterpolatorLiteralTermInfo ccTermInfo = getLiteralTermInfo(ccEq);
		final InterpolatorLiteralTermInfo laTermInfo = getLiteralTermInfo(laEq);
		final boolean ccIsNeg = ccTermInfo.isNegated();

		final LitInfo ccInfo = getLiteralInfo(ccTermInfo.getAtom());
		final LitInfo laInfo = getLiteralInfo(laTermInfo.getAtom());

		interpolants = new Interpolant[mNumInterpolants];
		for (int p = 0; p < mNumInterpolants; p++) {
			Term interpolant;
			if (ccInfo.isAorShared(p) && laInfo.isAorShared(p)) {
				interpolant = mTheory.mFalse; // both literals in A.
			} else if (ccInfo.isBorShared(p) && laInfo.isBorShared(p)) {
				interpolant = mTheory.mTrue; // both literals in B.
			} else {
				final InterpolatorAffineTerm iat = new InterpolatorAffineTerm();
				final Rational factor = lemmaTermInfo.getLAFactor();
				TermVariable mixed = null;
				boolean negate = false;
				// Get A part of ccEq:
				final ApplicationTerm ccEqApp = ccTermInfo.getEquality();
				if (ccInfo.isALocal(p)) {
					iat.add(factor, termToAffine(ccEqApp.getParameters()[0]));
					iat.add(factor.negate(), termToAffine(ccEqApp.getParameters()[1]));
					if (!ccIsNeg) {
						negate = true;
					}
				} else if (ccInfo.isMixed(p)) {
					// mixed;
					if (!ccIsNeg) {
						mixed = ccInfo.getMixedVar();
					}
					if (ccInfo.mLhsOccur.isALocal(p)) {
						iat.add(factor, termToAffine(ccEqApp.getParameters()[0]));
						iat.add(factor.negate(), ccInfo.getMixedVar());
					} else {
						iat.add(factor, ccInfo.getMixedVar());
						iat.add(factor.negate(), termToAffine(ccEqApp.getParameters()[1]));
					}
				} else {
					// both sides in B, A part is empty
				}

				// Get A part of laEq:
				if (laInfo.isALocal(p)) {
					iat.add(Rational.MONE, laTermInfo.getLinVar());
					iat.add(laTermInfo.getBound());
					if (ccIsNeg) {
						negate = true;
					}
				} else if (laInfo.isMixed(p)) {
					if (ccIsNeg) {
						mixed = laInfo.getMixedVar();
					}
					iat.add(Rational.MONE, laInfo.getAPart(p));
					iat.add(Rational.ONE, laInfo.getMixedVar());
				} else {
					// both sides in B, A part is empty
				}
				iat.mul(iat.getGCD().inverse());

				// Now solve it.
				if (mixed != null) { // NOPMD
					final Rational mixedFactor = iat.getSummands().remove(mixed);
					assert mixedFactor.isIntegral();
					final boolean isInt = mixed.getSort().getName().equals("Int");
					if (isInt && mixedFactor.abs() != Rational.ONE) { // NOPMD
						if (mixedFactor.signum() > 0) {
							iat.negate();
						}
						final Term sharedTerm = iat.toSMTLib(mTheory, isInt);
						final Term divisor = mixedFactor.abs().toTerm(mixed.getSort());
						// We need to divide sharedTerm by mixedFactor and check that it doesn't produce a remainder.
						//
						// Interpolant is: (and (= mixed (div sharedTerm mixedFactor))
						// (= (mod sharedTerm mixedFactor) 0))
						interpolant = mTheory.and(mTheory.equals(mixed, mTheory.term("div", sharedTerm, divisor)),
								mTheory.term("=", mTheory.term("mod", sharedTerm, divisor),
										Rational.ZERO.toTerm(mixed.getSort())));
					} else {
						iat.mul(mixedFactor.negate().inverse());
						final Term sharedTerm = iat.toSMTLib(mTheory, isInt);
						interpolant = mTheory.equals(mixed, sharedTerm);
					}
				} else {
					if (iat.isConstant()) {
						if (iat.getConstant() != InfinitNumber.ZERO) {
							negate ^= true;
						}
						interpolant = negate ? mTheory.mFalse : mTheory.mTrue;
					} else {
						final boolean isInt = iat.isInt();
						final Sort sort = mTheory.getSort(isInt ? "Int" : "Real");
						final Term term = iat.toSMTLib(mTheory, isInt);
						final Term zero = Rational.ZERO.toTerm(sort);
						interpolant = negate ? mTheory.not(mTheory.equals(term, zero)) : mTheory.equals(term, zero);
					}
				}
			}
			interpolants[p] = new Interpolant(interpolant);
		}
		return interpolants;
	}

	/**
	 * Color the input literals. This gets the source for the literals from the LeafNodes.
	 */
	public void colorLiterals() {

		for (final Clause clause : mSmtSolver.getEngine().getClauses()) {
			final ProofNode pn = clause.getProof();
			assert pn instanceof LeafNode;
			final LeafNode ln = (LeafNode) pn;
			assert ((LeafNode) pn).hasSourceAnnotation();
			final String source = ((SourceAnnotation) ln.getTheoryAnnotation()).getAnnotation();
			final int partition = mPartitions.containsKey(source) ? mPartitions.get(source) : -1;
			for (int i = 0; i < clause.getSize(); i++) {
				// Take the quoted literal!
				final Term literal = clause.getLiteral(i).getSMTFormula(mTheory, true);

				final InterpolatorLiteralTermInfo litTermInfo = getLiteralTermInfo(literal);
				final Term atom = litTermInfo.getAtom();
				LitInfo info = mLiteralInfos.get(atom);
				if (info == null) {
					info = new LitInfo();
					mLiteralInfos.put(atom, info);
				}
				if (!info.contains(partition)) {
					info.occursIn(partition);
					Term unquoted = atom;
					if (unquoted instanceof AnnotatedTerm) {
						unquoted = ((AnnotatedTerm) unquoted).getSubterm();
					}
					addOccurrence(unquoted, partition);
				}
			}
		}
	}

	Occurrence getOccurrence(final Term term) {
		if (term instanceof ConstantTerm) {
			return mFullOccurrence;
		}
		Occurrence result = mSymbolPartition.get(term);
		if (result == null) {
			if (term instanceof ApplicationTerm && ((ApplicationTerm) term).getFunction().isIntern()) {
				final Term[] subTerms = ((ApplicationTerm) term).getParameters();
				result = mFullOccurrence;
				if (subTerms.length == 0)
					return result;
				for (final Term p : subTerms) {
					final Occurrence occ = getOccurrence(p);
					result = result.intersect(occ);
				}
			} else {
				result = new Occurrence();
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
			if (at.getFunction().isIntern()) {
				return;
			}
		}
		/* Create occurrence if it is *not* an internal function and if it does not exists yet */
		if (occ == null) {
			occ = getOccurrence(term);
		}
		occ.occursIn(part);
	}

	HashSet<Term> getSubTerms(final Term literal) {
		final HashSet<Term> subTerms = new HashSet<>();
		final ArrayDeque<Term> todo = new ArrayDeque<Term>();
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

	LitInfo getLiteralInfo(final Term lit) {
		assert lit == getLiteralTermInfo(lit).getAtom();
		LitInfo result = mLiteralInfos.get(lit);
		if (result == null) {
			mLogger.info("colorLiteral: " + lit);
			result = colorMixedLiteral(lit);
		}
		return result;
	}

	/**
	 * Compute the LitInfo for a mixed Literal.
	 */
	public LitInfo colorMixedLiteral(final Term atom) {
		LitInfo info = mLiteralInfos.get(atom);

		assert info == null;

		final InterpolatorLiteralTermInfo atomInfo = getLiteralTermInfo(atom);

		final ArrayList<Term> subterms = new ArrayList<>();
		/*
		 * The sort of the auxiliary variable created for this atom. We need this since we internally represent integral
		 * constants in LIRA logics as Int even if they should have sort Real.
		 */
		Sort auxSort;
		if (atomInfo.isCCEquality()) {
			final ApplicationTerm eq = atomInfo.getEquality();
			final Term l = eq.getParameters()[0];
			final Term r = eq.getParameters()[1];
			subterms.add(l);
			subterms.add(r);
			if (l.getSort() == r.getSort()) {
				auxSort = l.getSort();
			} else {
				assert mTheory.getLogic().isIRA();
				// IRA-Hack
				auxSort = mTheory.getRealSort();
			}
		} else {
			assert atomInfo.isLAEquality() || atomInfo.isBoundConstraint();
			final InterpolatorAffineTerm lv = atomInfo.getLinVar();
			assert lv != null;
			final Collection<Term> components = lv.getSummands().keySet();
			boolean allInt = true;
			for (final Term c : components) {
				// IRA-Hack
				allInt &= c.getSort().getName().equals("Int");
				subterms.add(c);
			}
			auxSort = allInt ? mTheory.getNumericSort() : mTheory.getRealSort();
		}
		info = computeMixedOccurrence(subterms);
		mLiteralInfos.put(atom, info);

		final BitSet shared = new BitSet();
		shared.or(info.mInA);
		shared.or(info.mInB);
		if (shared.nextClearBit(0) >= mNumInterpolants) {
			return info;
		}

		info.mMixedVar = mTheory.createFreshTermVariable("litaux", auxSort);

		if (atomInfo.isCCEquality()) {
			final ApplicationTerm eq = atomInfo.getEquality();
			info.mLhsOccur = getOccurrence(eq.getParameters()[0]);
		} else if (atomInfo.isBoundConstraint() || atomInfo.isLAEquality()) {
			final InterpolatorAffineTerm lv = atomInfo.getLinVar();
			assert lv.getSummands().size() > 1 : "Not initially basic: " + lv + " atom: " + atom;

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

	private LitInfo computeMixedOccurrence(final ArrayList<Term> subterms) {
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

		@Override
		public void convert(final Term term) {
			if (term instanceof LATerm) {
				final LATerm laTerm = (LATerm) term;
				final Term[] oldTerms =
						laTerm.mS.getSummands().keySet().toArray(new Term[laTerm.mS.getSummands().size()]);
				/* recurse into LA term */
				enqueueWalker(new Walker() {
					@Override
					public void walk(final NonRecursive engine) {
						final Substitutor me = (Substitutor) engine;
						final Term result = me.getConverted();
						final Term[] newTerms = me.getConverted(oldTerms);
						if (result == laTerm.mF && newTerms == oldTerms) {
							me.setResult(laTerm);
							return;
						}
						final InterpolatorAffineTerm newS = new InterpolatorAffineTerm();
						for (int i = 0; i < oldTerms.length; i++) {
							newS.add(laTerm.mS.getSummands().get(oldTerms[i]), newTerms[i]);
						}
						newS.add(laTerm.mS.getConstant());
						me.setResult(new LATerm(newS, laTerm.mK, result));
					}
				});
				pushTerm(laTerm.mF);
				pushTerms(oldTerms);
				return;
			} else if (term.equals(mTermVar)) {
				setResult(mReplacement);
			} else {
				super.convert(term);
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

	class EQInterpolator extends TermTransformer {
		Interpolant mI2;
		TermVariable mAuxVar;

		EQInterpolator(final Interpolant i2, final TermVariable auxVar) {
			mI2 = i2;
			mAuxVar = auxVar;
		}

		@Override
		public void convert(final Term term) {
			assert term != mAuxVar;
			if (term instanceof LATerm) {
				final LATerm laTerm = (LATerm) term;
				/* recurse into LA term */
				enqueueWalker(new Walker() {
					@Override
					public void walk(final NonRecursive engine) {
						final EQInterpolator me = (EQInterpolator) engine;
						final Term result = me.getConverted();
						if (result == laTerm.mF) {
							me.setResult(laTerm);
						} else {
							me.setResult(new LATerm(laTerm.mS, laTerm.mK, result));
						}
					}
				});
				pushTerm(laTerm.mF);
				return;
			} else if (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getParameters().length == 2
						&& (appTerm.getParameters()[0] == mAuxVar || appTerm.getParameters()[1] == mAuxVar)) {
					assert appTerm.getFunction().isIntern() && appTerm.getFunction().getName().equals("=")
							&& appTerm.getParameters().length == 2;

					Term s = appTerm.getParameters()[1];
					if (s == mAuxVar) {
						s = appTerm.getParameters()[0];
					}
					setResult(substitute(mI2.mTerm, mAuxVar, s));
					return;
				}
			}
			super.convert(term);
		}
	}

	/**
	 * Compute the interpolant for the resolution rule with a mixed equality as pivot. This is I1[I2(s_i)] for I1[x=s_i]
	 * and I2(x).
	 *
	 * @param eqIpol
	 *            the interpolant I1[x=s_i].
	 * @param neqIpol
	 *            the interpolant I2(x).
	 * @param mixedVar
	 *            the auxiliary variable x.
	 * @return the resulting interpolant.
	 */
	private Interpolant mixedEqInterpolate(final Interpolant eqIpol, final Interpolant neqIpol,
			final TermVariable mixedVar) {
		final TermTransformer ipolator = new EQInterpolator(neqIpol, mixedVar);
		return new Interpolant(ipolator.transform(eqIpol.mTerm));
	}

	static abstract class MixedLAInterpolator extends TermTransformer {
		TermVariable mMixedVar;
		Term mI2;
		LATerm mLA1;

		public MixedLAInterpolator(final Term i2, final TermVariable mixed) {
			mMixedVar = mixed;
			mLA1 = null;
			mI2 = i2;
		}

		abstract Term interpolate(LATerm la1, LATerm la2);

		@Override
		public void convert(final Term term) {
			assert term != mMixedVar;
			if (term instanceof LATerm) {
				final LATerm laTerm = (LATerm) term;
				if (laTerm.mS.getSummands().get(mMixedVar) != null) { // NOPMD
					if (mLA1 == null) {
						/*
						 * We are inside I1. Remember the lainfo and push I2 on the convert stack. Also enqueue a walker
						 * that will remove m_LA1 once we are finished with I2.
						 */
						beginScope();
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
					}
					/*
					 * We are inside I2. Interpolate the LAInfos.
					 */
					setResult(interpolate(mLA1, (LATerm) term));
					return;
				}
				/* this is a LA term not involving the mixed variable */
				enqueueWalker(new Walker() {

					@Override
					public void walk(final NonRecursive engine) {
						final MixedLAInterpolator me = (MixedLAInterpolator) engine;
						final Term result = me.getConverted();
						if (result == laTerm.mF) {
							me.setResult(laTerm);
						} else {
							me.setResult(new LATerm(laTerm.mS, laTerm.mK, result));
						}
					}
				});

				pushTerm(laTerm.mF);
				return;
			}
			super.convert(term);
		}
	}

	class RealInterpolator extends MixedLAInterpolator {
		public RealInterpolator(final Term i2, final TermVariable mixedVar) {
			super(i2, mixedVar);
		}

		@Override
		public Term interpolate(final LATerm la1, final LATerm la2) {
			// retrieve c1,c2,s2,s2
			final InterpolatorAffineTerm s1 = new InterpolatorAffineTerm(la1.mS);
			final Rational c1 = s1.getSummands().remove(mMixedVar);
			final InterpolatorAffineTerm s2 = new InterpolatorAffineTerm(la2.mS);
			final Rational c2 = s2.getSummands().remove(mMixedVar);
			assert c1.signum() * c2.signum() == -1;
			InfinitNumber newK = la1.mK.mul(c2.abs()).add(la2.mK.mul(c1.abs()));

			// compute c1s2 + c2s1
			final InterpolatorAffineTerm c1s2c2s1 = new InterpolatorAffineTerm();
			c1s2c2s1.add(c1.abs(), s2);
			c1s2c2s1.add(c2.abs(), s1);

			Term newF;
			if (s1.getConstant().mEps > 0 || s2.getConstant().mEps > 0) {
				// One of the inequalities is strict. In this case
				// c1s2c2s1 must also be a strict inequality and it is not
				// possible that c1s2c2s1 == 0 holds. Hence, we do not need
				// to substitute a shared term.
				newF = c1s2c2s1.toLeq0(mTheory);
				newK = InfinitNumber.EPSILON.negate();
			} else if (la1.mK.less(InfinitNumber.ZERO)) {
				// compute -s1/c1
				final InterpolatorAffineTerm s1divc1 = new InterpolatorAffineTerm(s1);
				s1divc1.mul(c1.inverse().negate());
				final Term s1DivByc1 = s1divc1.toSMTLib(mTheory, false);
				newF = substitute(la2.mF, mMixedVar, s1DivByc1);
				newK = la2.mK;
			} else if (la2.mK.less(InfinitNumber.ZERO)) {
				// compute s2/c2
				final InterpolatorAffineTerm s2divc2 = new InterpolatorAffineTerm(s2);
				s2divc2.mul(c2.inverse().negate());
				final Term s2DivByc2 = s2divc2.toSMTLib(mTheory, false);
				newF = substitute(la1.mF, mMixedVar, s2DivByc2);
				newK = la1.mK;
			} else {
				final InterpolatorAffineTerm s1divc1 = new InterpolatorAffineTerm(s1);
				s1divc1.mul(c1.inverse().negate());
				final Term s1DivByc1 = s1divc1.toSMTLib(mTheory, false);
				final Term f1 = substitute(la1.mF, mMixedVar, s1DivByc1);
				final Term f2 = substitute(la2.mF, mMixedVar, s1DivByc1);
				newF = mTheory.and(f1, f2);
				if (c1s2c2s1.isConstant()) {
					if (c1s2c2s1.getConstant().less(InfinitNumber.ZERO)) {
						newF = mTheory.mTrue;
					}
				} else {
					final InterpolatorAffineTerm s3 = new InterpolatorAffineTerm(c1s2c2s1);
					s3.add(InfinitNumber.EPSILON);
					newF = mTheory.or(s3.toLeq0(mTheory), newF);
				}
				newK = InfinitNumber.ZERO;
			}
			final LATerm la3 = new LATerm(c1s2c2s1, newK, newF);
			return la3;
		}
	}

	class IntegerInterpolator extends MixedLAInterpolator {

		public IntegerInterpolator(final Term i2, final TermVariable mixedVar) {
			super(i2, mixedVar);
		}

		@Override
		public Term interpolate(final LATerm la1, final LATerm la2) {
			// retrieve c1,c2,s1,s2
			final InterpolatorAffineTerm s1 = new InterpolatorAffineTerm(la1.mS);
			final Rational c1 = s1.getSummands().remove(mMixedVar);
			final InterpolatorAffineTerm s2 = new InterpolatorAffineTerm(la2.mS);
			final Rational c2 = s2.getSummands().remove(mMixedVar);
			assert c1.isIntegral() && c2.isIntegral();
			assert c1.signum() * c2.signum() == -1;
			final Rational absc1 = c1.abs();
			final Rational absc2 = c2.abs();

			// compute c1s2 + c2s1
			final InterpolatorAffineTerm c1s2c2s1 = new InterpolatorAffineTerm();
			c1s2c2s1.add(absc1, s2);
			c1s2c2s1.add(absc2, s1);

			// compute newk = c2k1 + c1k2 + c1c2;
			final Rational c1c2 = absc1.mul(absc2);
			final InfinitNumber newK = la1.mK.mul(absc2).add(la2.mK.mul(absc1)).add(new InfinitNumber(c1c2, 0));
			assert newK.isIntegral();

			final Rational k1c1 = la1.mK.mA.add(Rational.ONE).div(absc1).ceil();
			final Rational k2c2 = la2.mK.mA.add(Rational.ONE).div(absc2).ceil();
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
			InterpolatorAffineTerm sPlusOffset = new InterpolatorAffineTerm();
			sPlusOffset.add(theC.signum() > 0 ? Rational.MONE : Rational.ONE, theS);
			Rational offset = Rational.ZERO;
			final Rational theCabs = theC.abs();
			if (theC.signum() < 0) {
				sPlusOffset.add(theCabs.add(Rational.MONE));
			}
			while (offset.compareTo(kc) <= 0) {
				Term x;
				if (mSmtSolver.isTerminationRequested()) {
					throw new SMTLIBException("Timeout exceeded");
				}
				x = sPlusOffset.toSMTLib(mTheory, true);
				if (theCabs != Rational.ONE) {
					x = mTheory.term("div", x, theCabs.toTerm(mTheory.getNumericSort()));
				}
				Term F1 = substitute(la1.mF, mMixedVar, x);
				Term F2 = substitute(la2.mF, mMixedVar, x);

				if (offset.compareTo(kc) == 0) {
					if (theS == s1) {
						F1 = mTheory.mTrue;
					} else {
						F2 = mTheory.mTrue;
					}
				}
				newF = mTheory.or(newF, mTheory.and(F1, F2));
				sPlusOffset = sPlusOffset.add(theC.negate());
				offset = offset.add(Rational.ONE);
			}
			final LATerm la3 = new LATerm(c1s2c2s1, newK, newF);
			return la3;
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
	public Interpolant mixedPivotLA(final Interpolant leqItp, final Interpolant sgItp, final TermVariable mixedVar) {
		final MixedLAInterpolator ipolator;

		if (mixedVar.getSort().getName().equals("Real")) {
			ipolator = new RealInterpolator(sgItp.mTerm, mixedVar);
		} else {
			ipolator = new IntegerInterpolator(sgItp.mTerm, mixedVar);
		}
		final Interpolant newI = new Interpolant(ipolator.transform(leqItp.mTerm));
		return newI;
	}

	/**
	 * Get all the information the interpolator needs for this term. Known InterpolatorTermInfos are stored in a HashMap
	 * to avoid recalculating them. This can be used for complex proof terms such as complete resolution steps or
	 * lemmata, but also for single literals.
	 */
	InterpolatorClauseTermInfo getClauseTermInfo(final Term term) {
		if (mClauseTermInfos.containsKey(term)) {
			return mClauseTermInfos.get(term);
		}
		final InterpolatorClauseTermInfo info = new InterpolatorClauseTermInfo();
		info.computeClauseTermInfo(term);
		mClauseTermInfos.put(term, info);
		return info;
	}

	InterpolatorLiteralTermInfo getLiteralTermInfo(final Term term) {
		if (mLiteralTermInfos.containsKey(term)) {
			return mLiteralTermInfos.get(term);
		}
		final InterpolatorLiteralTermInfo info = new InterpolatorLiteralTermInfo();
		info.computeLiteralTermInfo(term);
		mLiteralTermInfos.put(term, info);
		return info;
	}

	/**
	 * Convert this term to an InterpolatorAffineTerm
	 */
	static InterpolatorAffineTerm termToAffine(Term term) {
		if (term instanceof AnnotatedTerm) {
			term = ((AnnotatedTerm) term).getSubterm();
		}
		final SMTAffineTerm affine = new SMTAffineTerm(term);
		return new InterpolatorAffineTerm(affine);
	}

	/**
	 * Get the unquoted literal. The main problem here is that the quote annotation is inside the negation for negated
	 * literals.
	 *
	 * @param literal
	 * @return the literal without the quoted annotation
	 */
	Term unquote(final Term literal) {
		final InterpolatorLiteralTermInfo termInfo = getLiteralTermInfo(literal);
		Term unquoted = termInfo.getAtom();
		if (unquoted instanceof AnnotatedTerm) {
			assert ((AnnotatedTerm) unquoted).getAnnotations()[0].getKey().startsWith(":quoted");
			unquoted = ((AnnotatedTerm) unquoted).getSubterm();
		}
		if (termInfo.isNegated()) {
			unquoted = mTheory.term("not", unquoted);
		}
		return unquoted;
	}
}