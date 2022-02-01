/*
 * Copyright (C) 2015 Carl Kuesters
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.alternating;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.alternating.visualization.AAToUltimateModel;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

public class AlternatingAutomaton<LETTER, STATE> implements IAutomaton<LETTER, STATE> {
	private final Set<LETTER> mAlphabet;
	private final ArrayList<STATE> mStates = new ArrayList<>();
	private final HashMap<STATE, Integer> mStatesIndices = new HashMap<>();
	private final HashMap<LETTER, BooleanExpression[]> mTransitionFunction = new HashMap<>();
	private BooleanExpression mAcceptingFunction;
	private final BitSet mFinalStatesBitVector = new BitSet();
	private boolean mIsReversed;

	/**
	 * @param alphabet
	 *            alphabet.
	 * @param stateFactory
	 *            state factory
	 */
	public AlternatingAutomaton(final Set<LETTER> alphabet) {
		mAlphabet = alphabet;
	}

	public void addState(final STATE state) {
		if (!mStates.contains(state)) {
			final int stateIndex = mStates.size();
			mStates.add(state);
			mStatesIndices.put(state, stateIndex);
		}
	}

	public void addTransition(final LETTER letter, final STATE state, final BooleanExpression booleanExpression) {
		BooleanExpression[] letterTransitions = mTransitionFunction.get(letter);
		if (letterTransitions == null) {
			letterTransitions = new BooleanExpression[64];
			mTransitionFunction.put(letter, letterTransitions);
		}
		final int stateIndex = getStateIndex(state);
		if (letterTransitions[stateIndex] == null) {
			letterTransitions[stateIndex] = booleanExpression;
		} else {
			letterTransitions[stateIndex].addConjunction(booleanExpression);
		}
	}

	public void addAcceptingConjunction(final BooleanExpression booleanExpression) {
		if (mAcceptingFunction == null) {
			mAcceptingFunction = booleanExpression;
		} else {
			mAcceptingFunction.addConjunction(booleanExpression);
		}
	}

	public BooleanExpression generateCube(final STATE[] resultStates, final STATE[] negatedResultStates) {
		final BitSet alpha = new BitSet(mStates.size());
		final BitSet beta = new BitSet(mStates.size());
		for (final STATE resultState : resultStates) {
			final int stateIndex = getStateIndex(resultState);
			alpha.set(stateIndex);
			beta.set(stateIndex);
		}
		for (final STATE resultState : negatedResultStates) {
			final int stateIndex = getStateIndex(resultState);
			alpha.set(stateIndex);
		}
		return new BooleanExpression(alpha, beta);
	}

	public void setStateFinal(final STATE state) {
		final int stateIndex = getStateIndex(state);
		mFinalStatesBitVector.set(stateIndex);
	}

	public boolean isStateFinal(final STATE state) {
		final int stateIndex = getStateIndex(state);
		return mFinalStatesBitVector.get(stateIndex);
	}

	public boolean accepts(final Word<LETTER> word) {
		final BitSet resultingStates = (BitSet) mFinalStatesBitVector.clone();
		if (mIsReversed) {
			for (int i = 0; i < word.length(); i++) {
				resolveLetter(word.getSymbol(i), resultingStates);
			}
		} else {
			for (int i = (word.length() - 1); i >= 0; i--) {
				resolveLetter(word.getSymbol(i), resultingStates);
			}
		}
		return mAcceptingFunction.getResult(resultingStates);
	}

	public void resolveLetter(final LETTER letter, final BitSet currentStates) {
		final BooleanExpression[] letterTransitions = mTransitionFunction.get(letter);
		if (letterTransitions != null) {
			final BitSet tmpCurrentStates = (BitSet) currentStates.clone();
			for (int i = 0; i < mStates.size(); i++) {
				final boolean result =
						((letterTransitions[i] != null) ? letterTransitions[i].getResult(tmpCurrentStates) : false);
				currentStates.set(i, result);
			}
		} else {
			currentStates.clear();
		}
	}

	public ArrayList<STATE> getStates() {
		return mStates;
	}

	public int getStateIndex(final STATE state) {
		return mStatesIndices.get(state);
	}

	public HashMap<LETTER, BooleanExpression[]> getTransitionFunction() {
		return mTransitionFunction;
	}

	public BooleanExpression getAcceptingFunction() {
		return mAcceptingFunction;
	}

	public BitSet getFinalStatesBitVector() {
		return mFinalStatesBitVector;
	}

	public void setReversed(final boolean isReversed) {
		mIsReversed = isReversed;
	}

	public boolean isReversed() {
		return mIsReversed;
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mAlphabet;
	}

	@Override
	public int size() {
		return mStates.size();
	}

	@Override
	public String sizeInformation() {
		return "Number of states";
	}

	@Override
	public String toString() {
		String text = "[AlternatingAutomaton\n\tAlphabet = {";
		final Iterator<LETTER> letterIterator = mAlphabet.iterator();
		int r = 0;
		while (letterIterator.hasNext()) {
			if (r != 0) {
				text += ", ";
			}
			text += letterIterator.next();
			r++;
		}
		text += "}\n\tStates = {";
		for (int i = 0; i < mStates.size(); i++) {
			if (i != 0) {
				text += ", ";
			}
			text += mStates.get(i);
		}
		text += "}\n\tFinalStates = {";
		r = 0;
		for (int i = 0; i < mStates.size(); i++) {
			if (mFinalStatesBitVector.get(i)) {
				if (r != 0) {
					text += ", ";
				}
				text += mStates.get(i);
				r++;
			}
		}
		text += "}\n\tAcceptingFunction = " + mAcceptingFunction.toString(mStates) + "\n\tTransistions = {\n";
		r = 0;
		for (final Entry<LETTER, BooleanExpression[]> entry : mTransitionFunction.entrySet()) {
			text += "\t\t" + entry.getKey() + " => {\n";
			int z = 0;
			for (int i = 0; i < mStates.size(); i++) {
				if (entry.getValue()[i] != null) {
					if (z != 0) {
						text += ",\n";
					}
					text += "\t\t\t" + mStates.get(i) + " => " + entry.getValue()[i].toString(mStates);
					z++;
				}
			}
			text += "\n\t\t}";
			if (r != (mTransitionFunction.size() - 1)) {
				text += ",";
			}
			text += "\n";
			r++;
		}
		text += "\t}\n]";
		return text;
	}

	@Override
	public IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		return new AAToUltimateModel<LETTER, STATE>().transformToUltimateModel(this);
	}
}
