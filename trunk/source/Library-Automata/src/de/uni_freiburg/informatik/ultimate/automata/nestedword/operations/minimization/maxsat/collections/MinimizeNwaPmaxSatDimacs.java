package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaPmaxSatDoubleton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Nested word automaton minimization using a partial Max-SAT reduction.
 * The problem instance is solved using an external solver.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class MinimizeNwaPmaxSatDimacs<LETTER, STATE> extends MinimizeNwaPmaxSatDoubleton<LETTER, STATE> {
	/**
	 * @param services
	 *            Ultimate services.
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public MinimizeNwaPmaxSatDimacs(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		super(services, stateFactory, operand, Collections.singleton(operand.getStates()),
				new Settings<STATE>().setFinalStateConstraints(true).setSolverModeExternal());
	}
}
