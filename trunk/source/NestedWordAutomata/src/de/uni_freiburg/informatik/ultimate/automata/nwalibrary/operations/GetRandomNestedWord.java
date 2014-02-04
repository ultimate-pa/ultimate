/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
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
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
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
	
	private final Random m_Random;
	private final List<LETTER> m_InternalAlphabet;
	private final List<LETTER> m_CallAlphabet;
	private final List<LETTER> m_ReturnAlphabet;
	
	private final static int s_TemporaryPendingCall = -7;
	
	private final NestedWord<LETTER> m_Result;
	
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
				m_InternalAlphabet.size(),
				m_CallAlphabet.size(),
				m_ReturnAlphabet.size());
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ".";
	}
	
	@Override
	public NestedWord<LETTER> getResult() throws OperationCanceledException {
		return m_Result;
	}


	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException, AutomataLibraryException {
		return true;
	}
	
	
	
	public GetRandomNestedWord(INestedWordAutomatonSimple<LETTER, STATE> nwa, int length) {
		super();
		m_InternalAlphabet = new ArrayList<LETTER>(nwa.getInternalAlphabet());
		m_CallAlphabet = new ArrayList<LETTER>(nwa.getCallAlphabet());
		m_ReturnAlphabet = new ArrayList<LETTER>(nwa.getReturnAlphabet());
		m_Random = new Random();
		
		int sum = m_InternalAlphabet.size() + m_CallAlphabet.size() + m_ReturnAlphabet.size();
		double probabilityCall = ((double) m_CallAlphabet.size()) / sum;
		double probabilityReturn = ((double) m_ReturnAlphabet.size()) / sum;
		
		m_Result = generateNestedWord(length, probabilityCall, probabilityReturn);
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
			double inORcaORre = m_Random.nextDouble();
			if (inORcaORre < probabilityCall) {
				word[i] = getRandomLetter(m_CallAlphabet);
				nestingRelation[i] = s_TemporaryPendingCall;
				callPositionStack.push(i);
				pendingCalls++;
			} else if (pendingCalls > 0 && inORcaORre < probabilityCall + probabilityReturn ) {
				word[i] = getRandomLetter(m_ReturnAlphabet);
				int correspondingCallPosition = callPositionStack.pop();
				nestingRelation[i] = correspondingCallPosition;
				nestingRelation[correspondingCallPosition] = i;
				pendingCalls--;
			} else {
				if (m_InternalAlphabet.isEmpty()) {
					// if internal alphabet is empty we use a call instead
					word[i] = getRandomLetter(m_CallAlphabet);
					nestingRelation[i] = s_TemporaryPendingCall;
					callPositionStack.push(i);
					pendingCalls++;
				} else {
					word[i] = getRandomLetter(m_InternalAlphabet);
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
		LETTER letter = getRandomLetter(m_InternalAlphabet);
		int nestingRelation = NestedWord.INTERNAL_POSITION;
		return new NestedWord<LETTER>(letter, nestingRelation);
	}
	
	private NestedWord<LETTER> pendingCallSingleton() {
		LETTER letter = getRandomLetter(m_CallAlphabet);
		int nestingRelation = NestedWord.PLUS_INFINITY;
		return new NestedWord<LETTER>(letter, nestingRelation);
	}
	
	private NestedWord<LETTER> pendingReturnSingleton() {
		LETTER letter = getRandomLetter(m_ReturnAlphabet);
		int nestingRelation = NestedWord.MINUS_INFINITY;
		return new NestedWord<LETTER>(letter, nestingRelation);
	}
	
	private LETTER getRandomLetter(List<LETTER> list) {
		int numberOfLetters = list.size();
		assert numberOfLetters > 0;
		LETTER letter = list.get(m_Random.nextInt(numberOfLetters));
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
		int lengthStem = m_Random.nextInt(lengthStemAndLoop);
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
