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

package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata;

import java.io.PrintStream;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;

/**
 * State class for Buchi Nested Word Automata
 */
public class StateNwa implements IStateNwa, Comparable<StateNwa> {

	private final IBuchiNwa mBuchi;
	private final int mId;

	private final Map<Integer, IntSet> mSuccessorsInternal;
	private final Map<Integer, IntSet> mSuccessorsCall;
	// letter * hier -> succ
	private final Map<Integer, Map<Integer, IntSet>> mSuccessorsReturn;

	public StateNwa(final IBuchiNwa buchi, final int id) {
		mBuchi = buchi;
		mId = id;
		mSuccessorsCall = new HashMap<>();
		mSuccessorsInternal = new HashMap<>();
		mSuccessorsReturn = new HashMap<>();
	}

	@Override
	public int getId() {
		return mId;
	}

	private void addSuccessors(final Map<Integer, IntSet> succMap, final int letterOrHier, final int state) {
		IntSet succs = succMap.get(letterOrHier);
		if (succs == null) {
			succs = UtilIntSet.newIntSet();
		}
		succs.set(state);
		succMap.put(letterOrHier, succs);
	}

	@Override
	public void addSuccessorInternal(final int letter, final int state) {
		assert mBuchi.getAlphabetInternal().get(letter);
		addSuccessors(mSuccessorsInternal, letter, state);
	}

	@Override
	public void addSuccessorCall(final int letter, final int state) {
		assert mBuchi.getAlphabetCall().get(letter);
		addSuccessors(mSuccessorsCall, letter, state);
	}

	@Override
	public void addSuccessorReturn(final int hier, final int letter, final int state) {
		assert mBuchi.getAlphabetReturn().get(letter);
		Map<Integer, IntSet> succMap = mSuccessorsReturn.get(letter);
		if (succMap == null) {
			succMap = new HashMap<>();
		}
		addSuccessors(succMap, hier, state);
		mSuccessorsReturn.put(letter, succMap);
	}

	private IntSet getSuccessors(final Map<Integer, IntSet> succMap, final int letter) {
		final IntSet succs = succMap.get(letter);
		if (succs == null) { // transition function may not be complete
			return UtilIntSet.newIntSet();
		}
		return succs.clone();
	}

	@Override
	public IntSet getSuccessorsInternal(final int letter) {
		assert mBuchi.getAlphabetInternal().get(letter);
		return getSuccessors(mSuccessorsInternal, letter);
	}

	@Override
	public IntSet getSuccessorsCall(final int letter) {
		assert mBuchi.getAlphabetCall().get(letter);
		return getSuccessors(mSuccessorsCall, letter);
	}

	@Override
	public IntSet getSuccessorsReturn(final int hier, final int letter) {
		assert mBuchi.getAlphabetReturn().get(letter);
		final Map<Integer, IntSet> succMap = mSuccessorsReturn.get(letter);
		if (succMap == null) {
			return UtilIntSet.newIntSet();
		}
		return getSuccessors(succMap, hier);
	}

	@Override
	public Set<Integer> getEnabledLettersInternal() {
		return mSuccessorsInternal.keySet();
	}

	@Override
	public Set<Integer> getEnabledLettersCall() {
		return mSuccessorsCall.keySet();
	}

	@Override
	public Set<Integer> getEnabledLettersReturn() {
		return mSuccessorsReturn.keySet();
	}

	@Override
	public Set<Integer> getEnabledHiersReturn(final int letter) {
		final Map<Integer, IntSet> succMap = mSuccessorsReturn.get(letter);
		if (succMap == null) {
			return Collections.emptySet();
		}
		return succMap.keySet();
	}

	@Override
	public int compareTo(final StateNwa other) {
		return mId - other.mId;
	}

	@Override
	public boolean equals(final Object other) {
		if (this == other) {
			return true;
		}
		if (other == null || getClass() != other.getClass()) {
			return false;
		}

		final StateNwa otherState = (StateNwa) other;
		return otherState.mId == mId;
	}

	@Override
	public int hashCode() {
		return mId;
	}

	@Override
	public String toString() {
		return "s" + mId;
	}

	@Override
	public void toDot(final PrintStream printer, final List<String> alphabet) {
		final Set<Integer> callLetters = getEnabledLettersCall();
		for (final Integer letter : callLetters) {
			final IntSet succs = getSuccessorsCall(letter);
			transToDot(printer, alphabet, succs, alphabet.get(letter) + "<");
		}

		final Set<Integer> internalLetters = getEnabledLettersInternal();
		for (final Integer letter : internalLetters) {
			final IntSet succs = getSuccessorsInternal(letter);
			transToDot(printer, alphabet, succs, alphabet.get(letter).toString());
		}

		final Set<Integer> returnLetters = getEnabledLettersReturn();
		for (final Integer letter : returnLetters) {
			final Set<Integer> predHiers = getEnabledHiersReturn(letter);
			for (final Integer predHier : predHiers) {
				final IntSet succs = getSuccessorsReturn(predHier, letter);
				transToDot(printer, alphabet, succs, predHier + ",>" + alphabet.get(letter));
			}
		}
	}

	private void transToDot(final PrintStream printer, final List<String> alphabet, final IntSet succs,
			final String letter) {
		for (final Integer succ : succs.iterable()) {
			printer.print("  " + getId() + " -> " + succ + " [label=\"" + letter.replace("\"", "") + "\"];\n");
		}
	}

}
