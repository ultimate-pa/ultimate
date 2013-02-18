package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Random;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoWord;

/**
 * Generate random nested words.
 * TODO: Avoid construction of nested words with pending returns
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 */
public class NestedWordGenerator<LETTER> {
	
	private final Random m_Random;
	
	private final List<LETTER> m_InternalAlphabet;
	private final List<LETTER> m_CallAlphabet;
	private final List<LETTER> m_ReturnAlphabet;
	
	
	public NestedWordGenerator(Collection<LETTER> internalAlphabet,
			Collection<LETTER> callAlphabet, Collection<LETTER> returnAlphabet) {
		super();
		m_InternalAlphabet = new ArrayList<LETTER>(internalAlphabet);
		m_CallAlphabet = new ArrayList<LETTER>(callAlphabet);
		m_ReturnAlphabet = new ArrayList<LETTER>(returnAlphabet);
		m_Random = new Random();
	}
	
	
	public NestedWord<LETTER> generateNestedWord(int length, 
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
		for (int i=0; i<length; i++) {
			NestedWord<LETTER> singletonAtPosi;
			double inORcaORre = m_Random.nextDouble();
			if (inORcaORre < probabilityCall) {
				singletonAtPosi = pendingCallSingleton();
			} else if (inORcaORre < probabilityCall + probabilityReturn ) {
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
