package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Determinize;

/**
 * This class implements Brzozowski's minimization algorithm.
 * 
 * The key idea is to reverse and determinize the automaton twice.
 * After each reversal the resulting DFA is minimal wrt. its language
 * (i.e., the reversed DFA minimally accepts the reverse language and the
 * twice reversed DFA minimally accepts the original language).
 * 
 * Reversal means that
 * - the transitions are turned around,
 * - the final states become the initial states,
 * - the initial states become the final states.
 * 
 * NOTE: The implementation is naive in the sense that both a new automaton is
 * created after each operation and the reversal and determinization do not
 * know each other (potentially they may .
 * 
 * @author Christian
 */
public class MinimizeBrzozowski<LETTER, STATE>
		extends AMinimizeNwa<LETTER, STATE>
		implements IOperation<LETTER, STATE>{
	/**
	 * The result automaton.
	 * 
	 * NOTE: All intermediate results are also stored here.
	 */
	private final INestedWordAutomaton<LETTER, STATE> m_result;
	
	/**
	 * Constructor.
	 * 
	 * @param operand input (finite, possibly nondeterministic) automaton
	 * @throws OperationCanceledException 
	 */
	public MinimizeBrzozowski(INestedWordAutomaton<LETTER, STATE> operand)
			throws OperationCanceledException {
		super("MinimizeBrzozowski", operand);
		
		assert super.checkForFiniteAutomaton() :
			"The input automaton contains call or return transitions.";
		
		m_result = minimize();
		s_logger.info(exitMessage());
	}
	
	/**
	 * This method simply reverses and determinizes the automaton twice, which
	 * results in the minimal DFA.
	 * 
	 * @return the minimal DFA
	 * @throws OperationCanceledException thrown when 
	 */
	private INestedWordAutomaton<LETTER, STATE> minimize()
			throws OperationCanceledException {
		INestedWordAutomaton<LETTER, STATE> automaton = m_operand;
		for (int i = 0; i < 2; ++i) {
			super.checkForContinuation();
			automaton = reverse(automaton);
			
			super.checkForContinuation();
			automaton = determinize(automaton);
		}
		return automaton;
	}
	
	/**
	 * This method reverses the automaton.
	 * 
	 * Reversal means that
     * - the transitions are turned around,
     * - the final states become the initial states,
     * - the initial states become the final states.
     * 
	 * @param automaton automaton
	 * @return the reversed automaton
	 */
	private INestedWordAutomaton<LETTER, STATE> reverse(
			final INestedWordAutomaton<LETTER, STATE> automaton) {
		NestedWordAutomaton<LETTER, STATE> reversed =
				new NestedWordAutomaton<>(automaton.getInternalAlphabet(),
						automaton.getCallAlphabet(),
						automaton.getReturnAlphabet(),
						automaton.getStateFactory());
		
		// add states
		for (final STATE state : automaton.getStates()) {
			reversed.addState(automaton.isFinal(state),
					automaton.isInitial(state), state);
		}
		// add (only internal) transitions
		for (final STATE state : automaton.getStates()) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans :
					automaton.internalSuccessors(state)) {
				reversed.addInternalTransition(
						state, trans.getLetter(), trans.getSucc());
			}
		}
		
		return reversed;
	}
	
	/**
	 * This method determinizes the automaton.
	 * 
	 * @param automaton automaton
	 * @return the determinized automaton
	 * @throws OperationCanceledException 
	 */
	private INestedWordAutomaton<LETTER, STATE> determinize(
			final INestedWordAutomaton<LETTER, STATE> automaton) {
		try {
			return new Determinize<LETTER, STATE>(automaton).getResult();
		}
		// this case cannot occur
		catch (OperationCanceledException e) {
			e.printStackTrace();
			return automaton;
		}
	}
	
	@Override
	public INestedWordAutomatonSimple<LETTER, STATE> getResult() {
		return m_result;
	}
}
