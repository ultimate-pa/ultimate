/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the Es of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the Es of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.LexicographicCounter;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.SymmetricHashRelation;

/**
 *
 *
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 TODO do not always rebuild relation, but store relation on stack and make copy for modifications
 *
 */
public class EquivalenceRelationIterator<E> implements Iterable<Set<Doubleton<E>>> {

	private final IUltimateServiceProvider mServices;
	private final List<Set<Doubleton<E>>> mResult = new ArrayList<>();

	private final LinkedList<Boolean> mStack = new LinkedList<>();
	private SymmetricHashRelation<E> mCurrentRelation;
	private final List<Doubleton<E>> mNonDisjointDoubletons;

	private final ThreeValuedEquivalenceRelation<E> mEqualityInformation;
	private final IExternalOracle<E> mExternalOracle;

	public EquivalenceRelationIterator(final IUltimateServiceProvider services,
			final Collection<E> indices, final ThreeValuedEquivalenceRelation<E> equalityInformation, final IExternalOracle<E> externalOracle, final List<Doubleton<E>> relevant) {
		super();
		mServices = services;
		mNonDisjointDoubletons = relevant;
		mEqualityInformation = equalityInformation;
		mExternalOracle = externalOracle;
		mCurrentRelation = new SymmetricHashRelation<>();

		while (true) {
			if (mStack.size() == mNonDisjointDoubletons.size()) {
				addRelationToResult();
				if (mCurrentRelation.isEmpty()) {
					break;
				}
			}
			final boolean failedToPushOnEmptyStack = advance();
			if (failedToPushOnEmptyStack) {
				break;
			}
		}
//		assert checkResultWithOldCombinationIterator(indices,
//				equalityInformation) : "result of CombinationIterator and CombinationIterator2 is different";
	}
	
	public EquivalenceRelationIterator(final IUltimateServiceProvider services,
			final Collection<E> indices, final ThreeValuedEquivalenceRelation<E> equalityInformation, final IExternalOracle<E> externalOracle) {
		this(services, indices, equalityInformation, externalOracle, buildListOfNonDisjointDoubletons(indices, equalityInformation));

	}

	private boolean checkResultWithOldCombinationIterator(final Collection<E> indices,
			final ThreeValuedEquivalenceRelation<E> equalityInformation) {
		final Set<Set<Doubleton<E>>> newResult = new HashSet<>(mResult);
		final Set<Set<Doubleton<E>>> oldResult = new HashSet<>();
		final EquivalenceRelationIterator2 ci = new EquivalenceRelationIterator2(indices, equalityInformation);
		for (final Set<Doubleton<E>> e : ci) {
			oldResult.add(e);
		}
		assert newResult.equals(oldResult) : "result of CombinationIterator and CombinationIterator2 is different "
				+ newResult.size() + " vs. " + oldResult.size();
		return newResult.equals(oldResult);
	}

	private boolean advance() {
		if (mStack.size() == mNonDisjointDoubletons.size()) {
			final boolean finished = remove1true();
			if (finished) {
				return true;
			} else {
				rebuildCurrentRelation();
				return tryToPush1False();
			}
		} else {
			return tryToPush1True();
		}

	}

	/**
	 * Try to push 'false' on the stack. If the relation becomes inconsistent,
	 * backtrack to the last 'true' (i.e., remove elements until we reached the
	 * last 'true', including the last 'true') and push 'false'. Continue until
	 * we reached a consistent stack. Note that there has is at least one
	 * consistent stack, namely the one that contains only 'false' elements.
	 * @return true iff we removed false and obtained an empty stack (which
	 * means we are done because we tried all combinations).
	 */
	private boolean tryToPush1False() {
		final Doubleton<E> d = mNonDisjointDoubletons.get(mStack.size());
		if (mCurrentRelation.containsPair(d.getOneElement(), d.getOtherElement())) {
			// we cannot add false
			final boolean finished = remove1true();
			if (finished) {
				return true;
			} else {
				rebuildCurrentRelation();
				return tryToPush1False();
			}
		} else {
			mStack.add(false);
			if (!mExternalOracle.isConsistent(mStack, mNonDisjointDoubletons)) {
				// we cannot add false
				mStack.removeLast();
				if (mStack.isEmpty()) {
					return true;
				} else {
					final boolean finished = remove1true();
					if (finished) {
						return true;
					} else {
						rebuildCurrentRelation();
						return tryToPush1False();
					}
				}
			} else {
				return false;
			}
		}
	}

	/**
	 * Push 'true' on the stack. If the relation becomes inconsistent remove the
	 * 'true' and call the {@link EquivalenceRelationIterator#tryToPush1False()}
	 * method which iterates until it was able to push 'false' to the stack.
	 * @return true iff we removed false and obtained an empty stack (which
	 * means we are done because we tried all combinations).
	 */
	private boolean tryToPush1True() {
		final Doubleton<E> d = mNonDisjointDoubletons.get(mStack.size());
		if (mEqualityInformation.getEqualityStatus(d.getOneElement(), d.getOtherElement()) == EqualityStatus.NOT_EQUAL) {
			// we cannot add true
			return false;
		} else {
			mStack.add(true);
			mCurrentRelation.addPair(d.getOneElement(), d.getOtherElement());
			final Set<Doubleton<E>> newPairs = mCurrentRelation.makeTransitive();
			final boolean containsDisjointPair = containsNotEqualsPair(newPairs);
			if (containsDisjointPair || !mExternalOracle.isConsistent(mStack, mNonDisjointDoubletons)) {
				final boolean finished = remove1true();
				if (finished) {
					return true;
				} else {
					rebuildCurrentRelation();
					return tryToPush1False();
				}
			} else {
				return false;
			}
		}
	}

	private boolean containsNotEqualsPair(final Set<Doubleton<E>> pairs1) {
		for (final Doubleton<E> pairFrom1 : pairs1) {
			if (mEqualityInformation.getEqualityStatus(pairFrom1.getOneElement(),
					pairFrom1.getOtherElement()) == EqualityStatus.NOT_EQUAL) {
				return true;
			}
		}
		return false;
	}

	private void rebuildCurrentRelation() {
		mCurrentRelation = new SymmetricHashRelation<>();
		int offset = 0;
		for (final Boolean bool : mStack) {
			if (bool) {
				final Doubleton<E> doubleton = mNonDisjointDoubletons.get(offset);
				mCurrentRelation.addPair(doubleton.getOneElement(), doubleton.getOtherElement());
			}
			offset++;
		}
		mCurrentRelation.makeTransitive();
	}

	/**
	 * Remove elements from the stack until one 'true' element was removed.
	 * @return true iff we removed false and obtained an empty stack (which
	 * means we are done because we tried all combinations).
	 */
	private boolean remove1true() {
		while (!mStack.peekLast()) {
			mStack.removeLast();
			if (mStack.isEmpty()) {
				return true;
			}
		}
		mStack.removeLast();
		return false;
	}

	private void addRelationToResult() {
		mResult.add(mCurrentRelation.buildSetOfNonSymmetricDoubletons());
	}

	public int size() {
		return mResult.size();
	}

	@Override
	public Iterator<Set<Doubleton<E>>> iterator() {
		return mResult.iterator();
	}
	
	
	
	
	

	static <E> List<Doubleton<E>> buildListOfNonDisjointDoubletons(final Collection<E> indices,
			final ThreeValuedEquivalenceRelation<E> equalityInformation) {
		final List<Doubleton<E>> doubeltons = new ArrayList<>();
		final List<E> indexList = new ArrayList<>(indices);
		for (int i = 0; i < indexList.size(); i++) {
			if (!equalityInformation.isRepresentative(indexList.get(i))) {
				continue;
			}
			for (int j = i + 1; j < indexList.size(); j++) {
				if (!equalityInformation.isRepresentative(indexList.get(j))) {
					continue;
				}
				if (equalityInformation.getEqualityStatus(indexList.get(i), indexList.get(j)) == EqualityStatus.NOT_EQUAL) {
					// do nothing
				} else {
					doubeltons.add(new Doubleton<>(indexList.get(i), indexList.get(j)));
				}
			}
		}
		return doubeltons;
	}
	
	
	private class EquivalenceRelationIterator2 implements Iterable<Set<Doubleton<E>>> {

		private final List<Set<Doubleton<E>>> mResult = new ArrayList<>();

		public EquivalenceRelationIterator2(final Collection<E> indices,
				final ThreeValuedEquivalenceRelation<E> equalityInformation) {
			super();
			final List<Doubleton<E>> doubeltons = buildListOfNonDisjointDoubletons(indices, equalityInformation);

			final int[] numberOfValues = new int[doubeltons.size()];
			Arrays.fill(numberOfValues, 2);
			final LexicographicCounter lc = new LexicographicCounter(numberOfValues);

			do {
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(this.getClass(), "iterating over LexicographicCounter " + lc);
				}
				final HashRelation<E, E> relationCandidate = new HashRelation<>();
				for (final E index : indices) {
					if (equalityInformation.isRepresentative(index)) {
						relationCandidate.addPair(index, index);
					}
				}
				final Set<Doubleton<E>> resultCandidate = new HashSet<>();
				for (int i = 0; i < doubeltons.size(); i++) {
					if (lc.getCurrentValue()[i] == 1) {
						final Doubleton<E> doubleton = doubeltons.get(i);
						relationCandidate.addPair(doubleton.getOneElement(), doubleton.getOtherElement());
						relationCandidate.addPair(doubleton.getOtherElement(), doubleton.getOneElement());
						resultCandidate.add(doubleton);
					}
				}
				if (isClosedUnderTransitivity(relationCandidate)) {
					mResult.add(resultCandidate);
				}

				lc.increment();
			} while (!lc.isZero());
		}

		public int size() {
			return mResult.size();
		}

		@Override
		public Iterator<Set<Doubleton<E>>> iterator() {
			return mResult.iterator();
		}

	}
	
	public static <E> boolean isClosedUnderTransitivity(final HashRelation<E, E> relation) {
		for (final Entry<E, E> entry : relation.entrySet()) {
			for (final E image : relation.getImage(entry.getValue())) {
				if (!relation.containsPair(entry.getKey(), image)) {
					return false;
				}
			}
		}
		return true;
	}

	public interface IExternalOracle<E> {

		public abstract boolean isConsistent(LinkedList<Boolean> stack, List<Doubleton<E>> nonDisjointDoubletons);

	}

	public static class DefaultExternalOracle<E> implements IExternalOracle<E> {

		@Override
		public boolean isConsistent(final LinkedList<Boolean> stack,
				final List<Doubleton<E>> nonDisjointDoubletons) {
			return true;
		}

	}
	
	


}