package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Random;

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

		NestedWord<LETTER> result = new NestedWord<LETTER>();
		int pendingCalls = 0;
		for (int i=0; i<length; i++) {
			NestedWord<LETTER> singletonAtPosi;
			double inORcaORre = m_Random.nextDouble();
			if (inORcaORre < probabilityCall) {
				pendingCalls++;
				singletonAtPosi = pendingCallSingleton();
			} else if (pendingCalls > 0 && inORcaORre < probabilityCall + probabilityReturn ) {
				pendingCalls--;
				singletonAtPosi = pendingReturnSingleton();
			} else {
				singletonAtPosi = internalSingleton();
			}
			result = result.concatenate(singletonAtPosi);
		}
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
