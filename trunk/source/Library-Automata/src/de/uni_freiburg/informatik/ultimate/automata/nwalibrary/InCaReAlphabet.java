package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;

/**
 * Alphabet consisting of three not necessarily disjoint sets.
 * For visibly pushdown automata a (disjoint) partition into internal, call, and
 * return alphabet is necessary. For our NestedWordAutomata this segmentation
 * can increase the performance of operations but is not necessary.
 * @author Matthias Heizmann
 *
 * @param <LETTER> Type of the Objects that can be used as letters.
 */
public class InCaReAlphabet<LETTER> {
	private final Set<LETTER> m_InternalAlphabet;
	private final Set<LETTER> m_CallAlphabet;
	private final Set<LETTER> m_ReturnAlphabet;
	public InCaReAlphabet(Set<LETTER> internalAlphabet,
			Set<LETTER> callAlphabet, Set<LETTER> returnAlphabet) {
		super();
		m_InternalAlphabet = internalAlphabet;
		m_CallAlphabet = callAlphabet;
		m_ReturnAlphabet = returnAlphabet;
	}
	
	public InCaReAlphabet(IAutomaton<LETTER, ?> automaton) {
		if (automaton instanceof INestedWordAutomaton) {
			INestedWordAutomaton<LETTER, ?> nwa = 
					(INestedWordAutomaton<LETTER, ?>) automaton;
			m_InternalAlphabet = nwa.getInternalAlphabet();
			m_CallAlphabet = nwa.getCallAlphabet();
			m_ReturnAlphabet = nwa.getReturnAlphabet();
		} else {
			m_InternalAlphabet = automaton.getAlphabet();
			m_CallAlphabet = Collections.emptySet();
			m_ReturnAlphabet = Collections.emptySet();
		}
	}
	
	public Set<LETTER> getInternalAlphabet() {
		return m_InternalAlphabet;
	}
	public Set<LETTER> getCallAlphabet() {
		return m_CallAlphabet;
	}
	public Set<LETTER> getReturnAlphabet() {
		return m_ReturnAlphabet;
	}
	
	

}
