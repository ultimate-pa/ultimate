/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoWord;

/**
 * Generate random nested words.
 * TODO: Avoid construction of nested words with pending returns
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 */
public class GetRandomNestedWord<LETTER, STATE> implements IOperation<LETTER, STATE> {
	
	private final Random mRandom;
	private final List<LETTER> mInternalAlphabet;
	private final List<LETTER> mCallAlphabet;
	private final List<LETTER> mReturnAlphabet;
	
	private final static int s_TemporaryPendingCall = -7;
	
	private final NestedWord<LETTER> mResult;
	
	@Override
	public String operationName() {
		return "complement";
	}
	
	
	@Override
	public String startMessage() {
		return MessageFormat.format("Start {0}. Internal alphabet has {1}" +
				" letters, call alphabet has {2} letters, return alphabet" +
				" has {3} letters", 
				operationName(), 
				mInternalAlphabet.size(),
				mCallAlphabet.size(),
				mReturnAlphabet.size());
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ".";
	}
	
	@Override
	public NestedWord<LETTER> getResult() throws AutomataLibraryException {
		return mResult;
	}


	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException, AutomataLibraryException {
		return true;
	}
	
	
	
	public GetRandomNestedWord(INestedWordAutomatonSimple<LETTER, STATE> nwa, int length) {
		super();
		mInternalAlphabet = new ArrayList<LETTER>(nwa.getInternalAlphabet());
		mCallAlphabet = new ArrayList<LETTER>(nwa.getCallAlphabet());
		mReturnAlphabet = new ArrayList<LETTER>(nwa.getReturnAlphabet());
		mRandom = new Random();
		
		int sum = mInternalAlphabet.size() + mCallAlphabet.size() + mReturnAlphabet.size();
		double probabilityCall = ((double) mCallAlphabet.size()) / sum;
		double probabilityReturn = ((double) mReturnAlphabet.size()) / sum;
		
		mResult = generateNestedWord(length, probabilityCall, probabilityReturn);
	}
	
	
	private NestedWord<LETTER> generateNestedWord(int length, 
							double probabilityCall, double probabilityReturn) {
		String errorMessage = 
				"probability for call and return both have to between 0 and 1"
				+ " also the sum has to be between 0 and 1";
		if (probabilityCall < 0) {
			throw new IllegalArgumentException(errorMessage);
		}
		if (probabilityCall > 1) {
			throw new IllegalArgumentException(errorMessage);
		}
		if (probabilityReturn < 0) {
			throw new IllegalArgumentException(errorMessage);
		}
		if (probabilityReturn > 1) {
			throw new IllegalArgumentException(errorMessage);
		}
		if (probabilityCall + probabilityReturn > 1) {
			throw new IllegalArgumentException(errorMessage);
		}

		LETTER[] word = (LETTER[]) new Object[length];
		int[] nestingRelation = new int[length];
		Stack<Integer> callPositionStack = new Stack<Integer>();
		int pendingCalls = 0;
		for (int i=0; i<length; i++) {
			double inORcaORre = mRandom.nextDouble();
			if (inORcaORre < probabilityCall) {
				word[i] = getRandomLetter(mCallAlphabet);
				nestingRelation[i] = s_TemporaryPendingCall;
				callPositionStack.push(i);
				pendingCalls++;
			} else if (pendingCalls > 0 && inORcaORre < probabilityCall + probabilityReturn ) {
				word[i] = getRandomLetter(mReturnAlphabet);
				int correspondingCallPosition = callPositionStack.pop();
				nestingRelation[i] = correspondingCallPosition;
				nestingRelation[correspondingCallPosition] = i;
				pendingCalls--;
			} else {
				if (mInternalAlphabet.isEmpty()) {
					// if internal alphabet is empty we use a call instead
					word[i] = getRandomLetter(mCallAlphabet);
					nestingRelation[i] = s_TemporaryPendingCall;
					callPositionStack.push(i);
					pendingCalls++;
				} else {
					word[i] = getRandomLetter(mInternalAlphabet);
					nestingRelation[i] = NestedWord.INTERNAL_POSITION;
				}
			}
		}
		while (!callPositionStack.isEmpty()) {
			int pendingCallPosition = callPositionStack.pop();
			nestingRelation[pendingCallPosition] = NestedWord.PLUS_INFINITY;
		}
		NestedWord<LETTER> result = new NestedWord<LETTER>(word, nestingRelation);
		return result;
	}
	
	private NestedWord<LETTER> internalSingleton() {
		LETTER letter = getRandomLetter(mInternalAlphabet);
		int nestingRelation = NestedWord.INTERNAL_POSITION;
		return new NestedWord<LETTER>(letter, nestingRelation);
	}
	
	private NestedWord<LETTER> pendingCallSingleton() {
		LETTER letter = getRandomLetter(mCallAlphabet);
		int nestingRelation = NestedWord.PLUS_INFINITY;
		return new NestedWord<LETTER>(letter, nestingRelation);
	}
	
	private NestedWord<LETTER> pendingReturnSingleton() {
		LETTER letter = getRandomLetter(mReturnAlphabet);
		int nestingRelation = NestedWord.MINUS_INFINITY;
		return new NestedWord<LETTER>(letter, nestingRelation);
	}
	
	private LETTER getRandomLetter(List<LETTER> list) {
		int numberOfLetters = list.size();
		assert numberOfLetters > 0;
		LETTER letter = list.get(mRandom.nextInt(numberOfLetters));
		return letter;
	}
	
	public NestedLassoWord<LETTER> generateNestedLassoWord(int lengthStem, 
			int lengthLoop, double probabilityCall, double probabilityReturn) {
		NestedLassoWord<LETTER> result;
		NestedWord<LETTER> stem = generateNestedWord(
							lengthStem, probabilityCall, probabilityReturn);
		NestedWord<LETTER> loop = generateNestedWord(
							lengthLoop, probabilityCall, probabilityReturn);
		result = new NestedLassoWord<LETTER>(stem, loop);
		return result;
	}
	
	public NestedLassoWord<LETTER> generateNestedLassoWord(int lengthStemAndLoop, 
			double probabilityCall, double probabilityReturn) {
		int lengthStem = mRandom.nextInt(lengthStemAndLoop);
		int lengthLoop = lengthStemAndLoop - lengthStem + 1;
		NestedLassoWord<LETTER> result;
		NestedWord<LETTER> stem = generateNestedWord(
							lengthStem, probabilityCall, probabilityReturn);
		NestedWord<LETTER> loop = generateNestedWord(
							lengthLoop, probabilityCall, probabilityReturn);
		result = new NestedLassoWord<LETTER>(stem, loop);
		return result;
	}



	
}
