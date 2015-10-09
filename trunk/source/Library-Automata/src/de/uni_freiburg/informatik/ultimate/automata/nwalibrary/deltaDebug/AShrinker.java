package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.deltaDebug;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;

/**
 * Shrinks an automaton according to a certain criterion while still producing
 * the same error.
 * 
 * A shrinker can be seen as a rule according to which the debugger tries to
 * shrink an automaton.
 * For this purpose the shrinker defines a list of objects which are to be
 * removed and then applies binary search on this list.
 * 
 * Implementing subclasses should make certain that no exception is thrown
 * during construction of shrunk automata.
 * Otherwise this might lead to unwanted behavior, namely the debugger might
 * return an automaton object which has crashed during construction (e.g., a
 * transition was inserted whose state or letter was not present).
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 * @param <T> type of objects to be removed, e.g., states
 */
public abstract class AShrinker<T, LETTER, STATE> {
	INestedWordAutomaton<LETTER, STATE> m_automaton;
	AAutomatonFactory<LETTER, STATE> m_factory;
	INestedWordAutomaton<LETTER, STATE> m_prevAutomaton;
	
	/**
	 * Creates an automaton.
	 * 
	 * NOTE: Implementing subclasses must store the automaton.
	 * 
	 * @param list list of objects to be removed
	 * @return automaton according to (complement of the) list
	 */
	public abstract INestedWordAutomaton<LETTER, STATE> createAutomaton(
			final List<T> list);
	
	/**
	 * Extracts a list of objects containing all respective objects of the
	 * current automaton.
	 * 
	 * @return list of objects to be removed
	 */
	public abstract List<T> extractList();
	
	/**
	 * Called when the error still occurs for a shrunk automaton (-> success).
	 */
	public void error(final List<T> list) {
		assert (m_prevAutomaton != null) :
			"The previous automaton should have been stored.";
		m_automaton = m_prevAutomaton;
		m_prevAutomaton = null;
	}
	
	/**
	 * Called when no error occurs for a shrunk automaton (-> failure).
	 */
	public void noError(final List<T> list) {
		m_prevAutomaton = null;
	}
	
	/**
	 * Runs a binary search according to the shrinking rule implemented by this
	 * shrinker.
	 * 
	 * @param automaton automaton
	 * @param tester tester
	 * @param factory automaton factory
	 * @return new automaton iff automaton could be shrunk
	 */
	public INestedWordAutomaton<LETTER, STATE> runBinarySearch(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final ATester<LETTER, STATE> tester,
			final AAutomatonFactory<LETTER, STATE> factory) {
		m_automaton = automaton;
		m_factory = factory;
		m_prevAutomaton = automaton;
		final BinaryDebug<T, LETTER, STATE> binSearch =
				new BinaryDebug<T, LETTER, STATE>(tester, this);
		final boolean isReduced = binSearch.run();
		return isReduced ? m_automaton : null;
	}
	
	@Override
	public String toString() {
		return this.getClass().getSimpleName();
	}
}