/*
 * Copyright (C) 2023 University of Freiburg
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

import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * The interpolator for the cycle lemma of the theory of datatypes.
 *
 * @author Leon Cacace, Jochen Hoenicke
 */
public class DatatypeCycleInterpolator {

	private final Interpolator mInterpolator;
	private final Theory mTheory;
	private final int mNumInterpolants;
	/**
	 * a set for each Interpolant, to be filled with the literals of the
	 * interpolant.
	 */
	private final Set<Term>[] mInterpolants;
	/** the equalities of the lemma. */
	private final HashMap<SymmetricPair<Term>, LitInfo> mEqualityInfos;
	/** the testers as a map from their inner Term to their Occurrence. */
	private final HashMap<Term, LitInfo> mTestersOccurrence;
	/** the testers as a map from their inner Term to their function name. */
	private final HashMap<Term, FunctionSymbol> mTestersFunctions;
	/** the ordered terms of the lemma building the cycle */
	private Term[] mPath;

	/** The partitions for which every literal so far is in A. */
	BitSet mAllInA;

	/**
	 * The target partition of the last considered term in the path. Only for
	 * ancestors of this partition (including lastColor itself) an A path can be
	 * open. For all other nodes, the current term is considered as B-local.
	 */
	private int mLastColor;

	/** for each partition, the boundary terms thats start the A Path. */
	private final Term[] mStart;
	/**
	 * for each partition, the end of the first A-Path, if it was never started
	 * before.
	 */
	private final Term[] mHead;
	/**
	 * for each partition, the indices of the literals where the current A-path
	 * started (-1 if there is none for that partition)
	 */
	private final int[] mStartIndices;
	/**
	 * for each partition, the ending index of the first A-Path, if it was never
	 * started before.
	 */
	private final int[] mHeadIndices;

	/** array to store select functions later applied to the start of the a path. */
	private FunctionSymbol[] mSelectorOnPath;
	/** array to store tester functions. */
	private FunctionSymbol[] mTesterOnPath;

	@SuppressWarnings("unchecked")
	public DatatypeCycleInterpolator(final Interpolator interpolator,
			final HashMap<SymmetricPair<Term>, LitInfo> equalityInfos) {
		mInterpolator = interpolator;
		mTheory = interpolator.mTheory;
		mNumInterpolants = interpolator.mNumInterpolants;
		mInterpolants = new Set[mNumInterpolants];
		for (int i = 0; i < mNumInterpolants; i++) {
			mInterpolants[i] = new HashSet<>();
		}
		mStart = new Term[mNumInterpolants];
		mHead = new Term[mNumInterpolants];
		mStartIndices = new int[mNumInterpolants];
		mHeadIndices = new int[mNumInterpolants];
		mAllInA = new BitSet(mNumInterpolants);
		mEqualityInfos = equalityInfos;
		mTestersOccurrence = new HashMap<>();
		mTestersFunctions = new HashMap<>();
		collectTesterInfo(equalityInfos);
	}

	/**
	 * Collect all the info for all testers in the current conflict clause.
	 *
	 * @param atomInfo the map containing all infos for the equality literals of the
	 *                 clause.
	 */
	private void collectTesterInfo(Map<SymmetricPair<Term>, LitInfo> atomInfo) {
		for (final Map.Entry<SymmetricPair<Term>, LitInfo> entry : atomInfo.entrySet()) {
			final SymmetricPair<Term> key = entry.getKey();
			final LitInfo atomOccurrenceInfo = entry.getValue();
			final Term left = key.getFirst();
			final Term right = key.getSecond();
			collectSingleTesterInfo(left, atomOccurrenceInfo);
			collectSingleTesterInfo(right, atomOccurrenceInfo);

		}
	}

	private void collectSingleTesterInfo(Term term, LitInfo atomOccurrenceInfo) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm testerTerm = (ApplicationTerm) term;
			if (testerTerm.getFunction().getName().equals(SMTLIBConstants.IS)) {
				final Term testerArg = testerTerm.getParameters()[0];
				mTestersFunctions.put(testerArg, testerTerm.getFunction());
				mTestersOccurrence.put(testerArg, atomOccurrenceInfo);
			}
		}
	}

	/**
	 * Interpolate a datatype dt-cycle conflict. The lemma is annotated with a cycle
	 * {@code a1,b1,a2,b2,..,an} that shows that {@code a1} is equal to a
	 * constructor call on itself. The conflict must contain {@code ai == bi} (if it
	 * is not trivial) and {@code a(i+1)} is a child of {@code bi} in the sense that
	 * either {@code bi} is a term {@code cons(..,a(i+1),...)}, or that
	 * {@code a(i+1)} is a term {@code sel(bi)} and for the corresponding
	 * constructor {@code is_cons(bi) = true} occurs negated in the lemma.
	 *
	 * @param annot the argument of the :dt-cycle annotation. It has the form
	 *              {@code :cycle a1 b1 a2 b2 ... an} where a1 == an.
	 * @return The array of interpolants.
	 */
	public Term[] interpolateCycle(Term[] path) {
		mPath = path;
		mLastColor = mNumInterpolants;
		mAllInA.set(0, mNumInterpolants);
		mSelectorOnPath = new FunctionSymbol[mPath.length];
		mTesterOnPath = new FunctionSymbol[mPath.length];

		traverseCycleLemma();
		collectCycleInterpolants();

		final Term[] interpolants = new Term[mNumInterpolants];
		for (int color = 0; color < mNumInterpolants; color++) {
			interpolants[color] = mTheory.and(mInterpolants[color].toArray(new Term[mInterpolants[color].size()]));
		}
		return interpolants;
	}

	/**
	 * Traverse the path of the cycle lemma and collect all A-paths. As soon as an
	 * A-path is closed the corresponding interpolant is computed and added to the
	 * interpolants arrays.
	 */
	private void traverseCycleLemma() {
		final Occurrence firstOccurrence = mInterpolator.getOccurrence(mPath[0]);
		closeAPaths(firstOccurrence, mPath[0], 0);
		openAPaths(firstOccurrence, mPath[0], 0);
		for (int i = 0; i < mPath.length - 2; i += 2) {
			final Term left = mPath[i];
			final Term right = mPath[i + 1];
			if (!left.equals(right)) {
				final LitInfo literalInfo = mEqualityInfos.get(new SymmetricPair<>(left, right));

				// close and open A-paths before the literal when switches happen
				closeAPaths(literalInfo, mPath[i], i);
				openAPaths(literalInfo, mPath[i], i);
				// close and open A-paths in the middle of mixed literals
				if (literalInfo.getMixedVar() != null) {
					final Occurrence rightOccurrence = mInterpolator.getOccurrence(right);
					closeAPaths(rightOccurrence, literalInfo.getMixedVar(), i);
					openAPaths(rightOccurrence, literalInfo.getMixedVar(), i);
				}
			}

			final Term nextTerm = mPath[i + 2];
			if (isConsParentOf(right, nextTerm)) {
				// generate selector for child step
				addConsToAPath((ApplicationTerm) right, nextTerm, i + 1);
			} else {
				assert(isSelParentOf(right, nextTerm));
				// close and open A-paths after the literal where the tester occurrence forces a switch
				final Occurrence testerOccurrence = mTestersOccurrence.get(right);
				closeAPaths(testerOccurrence, right, i + 1);
				openAPaths(testerOccurrence, right, i + 1);
				// generate selector for child step
				addSelToAPath(right, (ApplicationTerm) nextTerm, i + 1);
			}
		}
	}

	/**
	 * Handle all unclosed paths at the beginning or the end of the path. Also adds
	 * the false interpolants for A-local conflicts.
	 */
	private void collectCycleInterpolants() {
		for (int color = 0; color < mNumInterpolants; color++) {
			if (mAllInA.get(color)) {
				// For this partition the conflict is completely in A.
				assert(mInterpolants[color].isEmpty());
				mInterpolants[color].add(mTheory.mFalse);
			} else if (mHead[color] != null) {
				// The APath was closed at the beginning and needs to be connected to the start
				// of the APath. If it didn't start, the index 0 is the boundaryTerm.
				if (mStart[color] == null) {
					mStart[color] = mPath[0];
					mStartIndices[color] = 0;
				}
				addCompletedAPath(color, mHead[color], mHeadIndices[color]);
			} else if (mStart[color] != null) {
				// APath was opened before but still needs to be closed
				addCompletedAPath(color, mPath[0], 0);
			}
		}

	}

	/**
	 * Add the selector/tester for a cons step ({@code parent = cons(...child...)}).
	 *
	 * @param consTerm  the parent term.
	 * @param childTerm the child term.
	 * @param litIndex  the index into the path.
	 */
	private void addConsToAPath(final ApplicationTerm consTerm, Term childTerm, int litIndex) {
		// store the corresponding selector and tester function
		final FunctionSymbol functionSymbol = consTerm.getFunction();
		assert(functionSymbol.isConstructor());
		final String selectorName = getSelector(consTerm, childTerm);
		mSelectorOnPath[litIndex] = mTheory.getFunction(selectorName, consTerm.getSort());
		mTesterOnPath[litIndex] = mTheory.getFunctionWithResult(SMTLIBConstants.IS,
				new String[] { functionSymbol.getName() }, null, consTerm.getSort());
	}

	/**
	 * Add the selector/tester for a selector step
	 * ({@code selector(parent) = child}).
	 *
	 * @param parentTerm the parent term.
	 * @param childTerm  the child term.
	 * @param litIndex   the index into the path.
	 */
	private void addSelToAPath(final Term parentTerm, final ApplicationTerm childTerm, int litIndex) {
		final FunctionSymbol functionSymbol = childTerm.getFunction();
		// store the selector and tester function
		assert(functionSymbol.isSelector());
		mSelectorOnPath[litIndex] = functionSymbol;
		final FunctionSymbol testerFunction = mTestersFunctions.get(parentTerm);
		mTesterOnPath[litIndex] = testerFunction;
	}


	/**
	 * Closes all A paths and goes up the tree until the occurrence is in A or
	 * mixed.
	 *
	 * @param occurence    the occurrence of the term/literal that we use
	 * @param boundaryTerm the boundary term
	 * @param litIndex     the index into the mPath.
	 */
	private void closeAPaths(Occurrence occurrence, Term boundaryTerm, int litIndex) {
		mAllInA.and(occurrence.mInA);
		int color = mLastColor;
		final int top = mNumInterpolants;

		// increase the color to go up the Tree, while the occurrence is in B, and close the A-Paths for those partitions
		while (color < top && occurrence.isBLocal(color)) {
			// switch from shared (open A path) to B
			if (mStart[color] != null) {
				addCompletedAPath(color, boundaryTerm, litIndex);
			} else {
				mHead[color] = boundaryTerm;
				mHeadIndices[color] = litIndex;
			}
			color = getParent(color);
			mLastColor = color;
		}
	}

	/**
	 * Open A-paths (or close B-Paths) with the boundary term until there is no
	 * A-local child for occur. This means that we go down the tree until the
	 * corresponding literal/term occurs in this partition. For mixed literals we do
	 * nothing, since we are already at the occurrence of one of the literals.
	 *
	 * @param occurence    the occurrence of the term/literal that we use
	 * @param boundaryTerm the boundary term
	 * @param litIndex     the index into the mPath.
	 */
	private void openAPaths(Occurrence occurrence, Term boundaryTerm, int litIndex) {

		int color = mLastColor;
		color = getALocalChild(color, occurrence);
		// decrease the color to go down the Tree, while the occurrence is in A, and open the A Paths for those partitions
		while (color >= 0) {
			assert occurrence.isALocal(color);
			if (!mAllInA.get(color)) {
				// stop on the partition that doesn't see a switch anymore
				// switch from B to A
				mStart[color] = boundaryTerm;
				mStartIndices[color] = litIndex;
			}
			mLastColor = color;
			color = getALocalChild(color, occurrence);
		}
	}

	/**
	 * Compute the interpolant for a commpleted A-Path and adds them to the set of
	 * interpolants for the given partition.
	 *
	 * @param color    The index into the interpolation partition.
	 * @param right    The right boundary term of the A-Path (the left is stored in
	 *                 mStart).
	 * @param endIndex The end index (the start index is stored in mStartIndices).
	 */
	private void addCompletedAPath(int color, Term right, int endIndex) {
		Term left = mStart[color];
		for (int i = mStartIndices[color]; i != endIndex; i = (i + 1) % mTesterOnPath.length) {
			if (mTesterOnPath[i] != null) {
				mInterpolants[color].add(mTheory.term(mTesterOnPath[i], left));
			}
			if (mSelectorOnPath[i] != null) {
				left = mTheory.term(mSelectorOnPath[i], left);
			}
		}
		if (left != right) {
			mInterpolants[color].add(mTheory.term(SMTLIBConstants.EQUALS, left, right));
		}

		mStartIndices[color] = -1;
		mStart[color] = null;
	}


	/**
	 * Checks if the child term is a selector application on the parent term.
	 *
	 * @param parent the parent term.
	 * @param child  the child term.
	 * @return true if child term is a selector application on the parent term.
	 */
	private boolean isSelParentOf(Term parent, Term child) {
		if (!(child instanceof ApplicationTerm)) {
			return false;
		}
		if (((ApplicationTerm) child).getFunction().isSelector()) {
			if (((ApplicationTerm) child).getParameters()[0] == parent) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Checks if the parent term is a constructor application, that includes the
	 * child term.
	 *
	 * @param parent the parent term.
	 * @param child  the child term.
	 * @return true if parent is constructor and child one of its arguments.
	 */
	private boolean isConsParentOf(Term parent, Term child) {
		if (!(parent instanceof ApplicationTerm)) {
			return false;
		}
		if (((ApplicationTerm) parent).getFunction().isConstructor()) {
			for (final Term term : ((ApplicationTerm) parent).getParameters()) {
				if (child == term) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Computes the selector that would give the childTerm when applied to the
	 * consTerm
	 *
	 * @param consTerm  The parent term, which must be a cons term.
	 * @param childTerm The child term, which must be a parameter of consTerm.
	 * @return The name of the selector to apply.
	 */
	private String getSelector(ApplicationTerm consTerm, Term childTerm) {
		final FunctionSymbol constructorSymbol = consTerm.getFunction();
		assert(constructorSymbol.getReturnSort().getSortSymbol().isDatatype());
		final DataType datatype = (DataType) consTerm.getSort().getSortSymbol();
		final Constructor cons = datatype.findConstructor(constructorSymbol.getName());
		final String[] s = cons.getSelectors();
		final Term[] terms = consTerm.getParameters();
		for (int i = 0; i < terms.length; i++) {
			if (childTerm.equals(terms[i])) {
				return s[i];
			}
		}
		throw new AssertionError("child term not found in constructors");
	}

	/**
	 * Compute the parent partition. This is the next partition, whose subtree
	 * includes color.
	 */
	private int getParent(int color) {
		int parent = color + 1;
		while (mInterpolator.mStartOfSubtrees[parent] > color) {
			parent++;
		}
		return parent;
	}

	/**
	 * Compute the A-local child partition. This is the child, that is A-local to
	 * the occurrence. This function returns -1 if all children are in B.
	 */
	private int getALocalChild(int color, Occurrence occ) {
		int child = color - 1;
		while (child >= mInterpolator.mStartOfSubtrees[color]) {
			if (occ.isALocal(child)) {
				return child;
			}
			child = mInterpolator.mStartOfSubtrees[child] - 1;
		}
		return -1;
	}
}
