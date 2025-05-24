/*
 * Copyright (C) 2017 Yong Li (liyong@ios.ac.cn)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.complement;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.Options;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IBuchiNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.StateNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntIterator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;
import gnu.trove.map.TIntObjectMap;
import gnu.trove.map.hash.TIntObjectHashMap;

public class StateNwaNCSB extends StateNwa implements IStateNwaComplement {

	private final BuchiNwaComplement mComplement;
	private final IBuchiNwa mOperand;
	private final NCSB mNCSB;

	public StateNwaNCSB(final BuchiNwaComplement complement, final int id, final NCSB ncsb) {
		super(complement, id);
		mComplement = complement;
		mOperand = complement.getOperand();
		mNCSB = ncsb;
	}

	public NCSB getNCSB() {
		return mNCSB;
	}

	@Override
	public IBuchiNwa getOperand() {
		return mOperand;
	}

	@Override
	public IBuchiNwa getComplement() {
		return mComplement;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || getClass() != obj.getClass()) {
			return false;
		}
		final StateNwaNCSB state = (StateNwaNCSB) obj;
		return mNCSB.equals(state.mNCSB);
	}

	// private IntSet visitedLetters = UtilIntSet.newIntSet();

	/**
	 * compute the successor deckers for internal/call transition
	 */
	private SuccessorResult computeSuccDoubleDeckers_CallOrInternal(final IntSet predDoubleDeckers, final int letter,
			final boolean testTrans) {
		final IntIterator iter = predDoubleDeckers.iterator();
		final SuccessorResult resultSucc = new SuccessorResult();
		while (iter.hasNext()) {
			final int doubleDecker = iter.next();
			final int downState = mComplement.getDownState(doubleDecker);
			final int upState = mComplement.getUpState(doubleDecker);
			IntSet upStateSuccs = null;
			IntSet succDeckers = null;

			final boolean isInternalLetter = mComplement.getAlphabetInternal().get(letter);
			// generate all deckers (down, succ)
			if (isInternalLetter) {
				// internal (x, y) - l -> (x, d)
				upStateSuccs = mOperand.getSuccessorsInternal(upState, letter);
				succDeckers = mComplement.generateDeckers(downState, upStateSuccs);
			} else {
				// call (x, y) - l -> (y, d)
				upStateSuccs = mOperand.getSuccessorsCall(upState, letter);
				succDeckers = mComplement.generateDeckers(upState, upStateSuccs);
			}

			if (testTrans && noTransitionAssertion_MinusF(upState, upStateSuccs)) {
				resultSucc.hasSuccessor = false;
				return resultSucc;
			}

			resultSucc.mSuccs.or(succDeckers);
			if (testTrans) {
				if (mOperand.isFinal(upState)) {
					resultSucc.mInterFSuccs.or(succDeckers);
				} else {
					resultSucc.mMinusFSuccs.or(succDeckers);
				}
			}
		}
		return resultSucc;
	}

	private IntSet computeSuccessors(final NCSB succNCSB, final IntSet minusFSuccs, final IntSet interFSuccs,
			final int hier, final int letter) {
		// d_a(S) /\ F and d_a(S) /\ must-in states should be empty
		if (succNCSB.getSSet().overlap(mComplement.getFinalDeckers()) || minusFSuccs.overlap(succNCSB.getSSet())) {
			return UtilIntSet.newIntSet();
		}

		final SuccessorGenerator generator = new SuccessorGenerator(mNCSB.getBSet().isEmpty(), succNCSB, minusFSuccs,
				interFSuccs, mComplement.getFinalDeckers());
		final IntSet succs = UtilIntSet.newIntSet();
		while (generator.hasNext()) {
			final NCSB ncsb = generator.next();
			if (ncsb == null) {
				continue;
			}
			final StateNwaNCSB succ = mComplement.addState(ncsb);
			if (mComplement.getAlphabetInternal().get(letter)) {
				super.addSuccessorInternal(letter, succ.getId());
			} else if (mComplement.getAlphabetCall().get(letter)) {
				super.addSuccessorCall(letter, succ.getId());
			} else {
				super.addSuccessorReturn(hier, letter, succ.getId());
			}
			succs.set(succ.getId());
		}

		return succs;
	}

	private IntSet computeSuccCallOrInternal(final int letter) {

		final IntSet minusFSuccs = UtilIntSet.newIntSet();
		final IntSet interFSuccs = UtilIntSet.newIntSet();

		// Compute the successors of B
		SuccessorResult succResult = computeSuccDoubleDeckers_CallOrInternal(mNCSB.getBSet(), letter, true);
		if (!succResult.hasSuccessor) {
			return UtilIntSet.newIntSet();
		}
		final IntSet BSuccs = succResult.mSuccs;
		minusFSuccs.or(succResult.mMinusFSuccs);
		interFSuccs.or(succResult.mInterFSuccs);

		// First compute the successors of C
		final IntSet CMinusB = mNCSB.copyCSet();
		CMinusB.andNot(mNCSB.getBSet()); // C\B
		succResult = computeSuccDoubleDeckers_CallOrInternal(CMinusB, letter, !Options.lazyS);
		if (!succResult.hasSuccessor) {
			return UtilIntSet.newIntSet();
		}
		final IntSet CSuccs = succResult.mSuccs;
		CSuccs.or(BSuccs);
		minusFSuccs.or(succResult.mMinusFSuccs);
		interFSuccs.or(succResult.mInterFSuccs);

		// Compute the successors of N
		succResult = computeSuccDoubleDeckers_CallOrInternal(mNCSB.getNSet(), letter, false);
		final IntSet NSuccs = succResult.mSuccs;

		// Compute the successors of S
		succResult = computeSuccDoubleDeckers_CallOrInternal(mNCSB.getSSet(), letter, false);
		final IntSet SSuccs = succResult.mSuccs;

		return computeSuccessors(new NCSB(NSuccs, CSuccs, SSuccs, BSuccs), minusFSuccs, interFSuccs, -1, letter);
	}

	@Override
	public IntSet getSuccessorsInternal(final int letter) {
		assert mComplement.getAlphabetInternal().get(letter);
		if (super.getEnabledLettersInternal().contains(letter)) {
			return super.getSuccessorsInternal(letter);
		}
		return computeSuccCallOrInternal(letter);
	}

	/**
	 * If q in C\F or (B\F), then tr(q, a) should not be not empty
	 */
	private boolean noTransitionAssertion_MinusF(final int upState, final IntSet succs) {
		return !mOperand.isFinal(upState) && succs.isEmpty();
	}

	@Override
	public IntSet getSuccessorsCall(final int letter) {
		assert mComplement.getAlphabetCall().get(letter);
		if (super.getEnabledLettersCall().contains(letter)) {
			return super.getSuccessorsCall(letter);
		}
		return computeSuccCallOrInternal(letter);
	}

	private IntSet computeSuccReturn(final int hier, final int letter) {

		final StateNwaNCSB hierState = (StateNwaNCSB) mComplement.getState(hier);
		final NCSB hierNCSB = hierState.getNCSB();

		final IntSet minusFSuccs = UtilIntSet.newIntSet();
		final IntSet interFSuccs = UtilIntSet.newIntSet();
		// Compute the successors of B
		final TIntObjectMap<List<Integer>> hierDoubleDeckers = doubleDeckerSetToMap(hierNCSB);
		SuccessorResult succResult = computeSuccDoubleDeckers_Return(mNCSB.getBSet(), hierDoubleDeckers, letter, true);
		if (!succResult.hasSuccessor) {
			return UtilIntSet.newIntSet();
		}
		final IntSet BSuccs = succResult.mSuccs;
		minusFSuccs.or(succResult.mMinusFSuccs);
		interFSuccs.or(succResult.mInterFSuccs);

		// First compute the successors of C
		final IntSet CMinusB = mNCSB.getCSet().clone();
		CMinusB.andNot(mNCSB.getBSet()); // C\B

		succResult = computeSuccDoubleDeckers_Return(CMinusB, hierDoubleDeckers, letter, !Options.lazyS);
		if (!succResult.hasSuccessor) {
			return UtilIntSet.newIntSet();
		}
		final IntSet CSuccs = succResult.mSuccs;
		CSuccs.or(BSuccs); // add successors of B
		minusFSuccs.or(succResult.mMinusFSuccs);
		interFSuccs.or(succResult.mInterFSuccs);

		// Compute the successors of N
		succResult = computeSuccDoubleDeckers_Return(mNCSB.getNSet(), hierDoubleDeckers, letter, false);
		if (!succResult.hasSuccessor) {
			return UtilIntSet.newIntSet();
		}
		final IntSet NSuccs = succResult.mSuccs;

		// Compute the successors of S
		succResult = computeSuccDoubleDeckers_Return(mNCSB.getSSet(), hierDoubleDeckers, letter, false);
		if (!succResult.hasSuccessor) {
			return UtilIntSet.newIntSet();
		}
		final IntSet SSuccs = succResult.mSuccs;

		return computeSuccessors(new NCSB(NSuccs, CSuccs, SSuccs, BSuccs), minusFSuccs, interFSuccs, hier, letter);
	}

	@Override
	public IntSet getSuccessorsReturn(final int hier, final int letter) {
		assert mComplement.getAlphabetReturn().get(letter);
		if (super.getEnabledLettersReturn().contains(letter) && super.getEnabledHiersReturn(letter).contains(hier)) {
			return super.getSuccessorsReturn(hier, letter);
		}
		return computeSuccReturn(hier, letter);
	}

	private SuccessorResult computeSuccDoubleDeckers_Return(final IntSet predDoubleDecker,
			final TIntObjectMap<List<Integer>> predHierDoubleDeckerMap, final int letter,
			final boolean testTransition) {
		final SuccessorResult succResult = new SuccessorResult();
		for (final int doubleDecker : predDoubleDecker.iterable()) {
			final int downState = mComplement.getDownState(doubleDecker);
			final int upState = mComplement.getUpState(doubleDecker);
			// predHier should contain all downState as its upState
			if (!predHierDoubleDeckerMap.containsKey(downState)) {
				succResult.hasSuccessor = false;
				return succResult;
			}
			// compute successors of return
			final IntSet upStateSuccs = mOperand.getSuccessorsReturn(upState, downState, letter);
			if (testTransition && noTransitionAssertion_MinusF(upState, upStateSuccs)) {
				succResult.hasSuccessor = false;
				return succResult;
			}

			final List<Integer> downHiers = predHierDoubleDeckerMap.get(downState);
			// put (upHier, succ)
			for (final Integer downHier : downHiers) {
				final IntSet succDeckers = mComplement.generateDeckers(downHier, upStateSuccs);
				succResult.mSuccs.or(succDeckers);
				if (testTransition) {
					if (mOperand.isFinal(upState)) {
						succResult.mInterFSuccs.or(succDeckers);
					} else {
						succResult.mMinusFSuccs.or(succDeckers);
					}
				}
			}
		}
		return succResult;
	}

	private TIntObjectMap<List<Integer>> doubleDeckerSetToMap(final NCSB hierNCSB) {
		final IntSet ncsb = hierNCSB.copyNSet();
		ncsb.or(hierNCSB.getCSet());
		ncsb.or(hierNCSB.getSSet());
		return doubleDeckerSetToMap(ncsb, false);
	}

	private TIntObjectMap<List<Integer>> doubleDeckerSetToMap(final IntSet doubleDeckerSet,
			final boolean keyIsDownState) {
		final TIntObjectMap<List<Integer>> doubleDeckerMap = new TIntObjectHashMap<>();
		for (final int doubleDecker : doubleDeckerSet.iterable()) {
			final int downState = mComplement.getDownState(doubleDecker);
			final int upState = mComplement.getUpState(doubleDecker);
			List<Integer> temp = null;
			final int key = keyIsDownState ? downState : upState;
			final int value = !keyIsDownState ? downState : upState;
			if (doubleDeckerMap.containsKey(key)) {
				temp = doubleDeckerMap.get(key);
			} else {
				temp = new ArrayList<>();
			}
			temp.add(value);
			doubleDeckerMap.put(key, temp);
		}
		return doubleDeckerMap;
	}

	@Override
	public String toString() {

		return "(" + outputSet(mNCSB.getNSet()) + "," + outputSet(mNCSB.getCSet()) + "," + outputSet(mNCSB.getSSet())
				+ "," + outputSet(mNCSB.getBSet()) + ")";
	}

	private String outputSet(final IntSet set) {
		final IntIterator iter = set.iterator();
		final StringBuilder builder = new StringBuilder();
		builder.append("{");
		boolean first = true;
		while (iter.hasNext()) {
			if (!first) {
				builder.append(",");
			}
			first = false;
			builder.append(mComplement.getDoubleDecker(iter.next()).toString());
		}
		builder.append("}");
		return builder.toString();
	}

	@Override
	public int hashCode() {
		return mNCSB.hashCode();
	}

}
