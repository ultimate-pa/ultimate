package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.deltaDebug;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;

/**
 * Delta debugger for automaton-related methods.
 * 
 * This is the main class to run the delta debugger.
 * To run it, the user needs the following ingredients:
 * 1) an initial {@link INestedWordAutomaton} object
 * 2) a {@link AAutomatonFactory} which can create new automaton objects
 * 3) a {@link ATester} which executes the method under consideration on
 *    automaton objects and checks whether the same type of error as in the
 *    original (unshrunk) problem still occurs.
 * 
 * At 2)
 * It is advised that the factory returns objects of the same type as the
 * initial automaton in 1) to exclude the possibility that the bug comes from
 * different sources.
 * This is, however, not a constraint of the class.
 * 
 * At 3)
 * It is possible to check for any type of {@link Throwable} as an error.
 * However, in order to prevent misinterpretation by more than one possible
 * sources of the error, it is advised that the error is of a unique type.
 * For instance, if the method code under consideration is available, the
 * {@link DebuggerException} could be thrown at the place where the designated
 * error occurs.
 * Example: If the user wants to find the cause for an
 * {@link AutomataLibraryException}, this might be introduced during the process
 * of shrinking the automaton as well.
 * 
 * For further explanations see
 * {@link #shrink(List, List)}.
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public class AutomatonDebugger<LETTER, STATE> {
	INestedWordAutomaton<LETTER, STATE> m_automaton;
	final AAutomatonFactory<LETTER, STATE> m_factory;
	final ATester<LETTER, STATE> m_tester;

	public AutomatonDebugger(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final AAutomatonFactory<LETTER, STATE> factory,
			final ATester<LETTER, STATE> tester) {
		this.m_automaton = automaton;
		this.m_factory = factory;
		this.m_tester = tester;
	}
	
	/**
	 * Shrinks an automaton according to given rules.
	 * 
	 * Given a set of rules to shrink the automaton, we apply binary search on
	 * the respective automaton objects (e.g., states).
	 * As long as one shrinking process was successful, we repeat this
	 * procedure.
	 * Finally, we apply a second set of shrinking rules which make sense only
	 * once (e.g., shrinking the alphabet).
	 * 
	 * @see BinaryDebug
	 * @param shrinkersLoop list of shrinkers (shrinking rules) applied in loop
	 * @param shrinkersEnd list of shrinkers (shrinking rules) applied once
	 * @return shrunk automaton
	 */
	public INestedWordAutomaton<LETTER, STATE> shrink(
			final List<AShrinker<?, LETTER, STATE>> shrinkersLoop,
			final List<AShrinker<?, LETTER, STATE>> shrinkersEnd) {
		// loop through shrinkers until nothing has changed
		boolean isReduced = true;
		while (isReduced) {
			isReduced = applyShrinker(shrinkersLoop);
		}
		// final shrinkers (apply only once)
		applyShrinker(shrinkersEnd);
		return m_automaton;
	}
	
	/**
	 * Runs a binary search for each shrinkers in a list.
	 * 
	 * @see BinaryDebug
	 * @param shrinkers list of shrinkers (shrinking rules)
	 * @return true iff at least one shrinker was successful
	 */
	private boolean applyShrinker(
			final List<AShrinker<?, LETTER, STATE>> shrinkers) {
		boolean isReduced = false;
		for (final AShrinker<?, LETTER, STATE> shrinker : shrinkers) {
			final INestedWordAutomaton<LETTER, STATE> newAutomaton =
					shrinker.runBinarySearch(m_automaton, m_tester, m_factory);
			if (newAutomaton != null) {
				// store shrunk automaton
				m_automaton = newAutomaton;
				isReduced = true;
			}
		}
		return isReduced;
	}

	@Override
	public String toString() {
		final StringBuilder b = new StringBuilder();
		b.append("<debugger with ");
		b.append(m_factory);
		b.append(" and ");
		b.append(m_tester);
		b.append(", currently considering the following automaton:\n");
		b.append(m_automaton);
		b.append(">");
		return b.toString();
	}
}