package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.function.BiPredicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.NwaApproximateXsimulation.SimulationType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.AbstractMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.IAssignmentCheckerAndGenerator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.InteractiveMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedConsistencyGeneratorDelayedSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGeneratorDoubleton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.VariableFactory.MergeDoubleton;
import de.uni_freiburg.informatik.ultimate.automata.util.ISetOfPairs;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;


/**
 * Partial Max-SAT based minimization of NWA using {@link MergeDoubleton} as variable type. 
 * Minimization is done using delayed simulation.
 * 
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @see MinimizeNwaMaxSat2
 */

public class MinimizeNwaPmaxSatDelayed<LETTER, STATE> extends MinimizeNwaPmaxSat<LETTER, STATE>{
	
	protected ScopedConsistencyGeneratorDelayedSimulation<Doubleton<STATE>, LETTER, STATE> mConsistencyGenerator;

	/**
	 * Constructor that should be called by the automata script interpreter.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input nested word automaton
	 * @throws AutomataOperationCanceledException
	 *             thrown by cancel request
	 */
	
	public MinimizeNwaPmaxSatDelayed(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
				this(services, stateFactory, operand, new NwaApproximateBisimulation<>(services, operand, SimulationType.DIRECT).getResult(), new Settings<STATE>().setLibraryMode(false));
	}
	
	/**
	 * Full constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input nested word automaton
	 * @param initialPartition
	 *            We only try to merge states that are in one of the blocks.
	 * @param settings
	 *            settings wrapper
	 * @param applyInitialPartitionPreprocessing
	 *            {@code true} iff preprocessing of the initial partition should be applied
	 * @param libraryMode
	 *            {@code true} iff solver is called by another operation
	 * @throws AutomataOperationCanceledException
	 *             thrown by cancel request
	 */
	
	public MinimizeNwaPmaxSatDelayed(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final ISetOfPairs<STATE, Collection<Set<STATE>>> initialPartition, final Settings<STATE> settings)
			throws AutomataOperationCanceledException {
			super(services, stateFactory, operand, initialPartition, settings);
	}
	
	@Override
	protected void generateVariablesHelper(final STATE[] states) {
		if (states.length <= 1) {
			return;
		}

		final BiPredicate<STATE, STATE> finalNonfinalConstraintPredicate =
				mSettings.getFinalNonfinalConstraintPredicate();

		for (int i = 0; i < states.length; i++) {
			final STATE stateI = states[i];

			// add to transitivity generator
			if (mTransitivityGenerator != null) {
				mTransitivityGenerator.addContent(stateI);
			}
			
			// add to consistency generator
			if (mConsistencyGenerator != null) {
				mConsistencyGenerator.addContent(stateI);
			}

			for (int j = 0; j < i; j++) {
				final STATE stateJ = states[j];
				final Doubleton<STATE> doubleton = new Doubleton<>(stateI, stateJ);
				mStatePair2Var.put(stateI, stateJ, doubleton);
				mStatePair2Var.put(stateJ, stateI, doubleton);
				mSolver.addVariable(doubleton);

				if (mOperand.isFinal(stateI) ^ mOperand.isFinal(stateJ)
						&& finalNonfinalConstraintPredicate.test(stateI, stateJ)) {
					setStatesDifferent(doubleton);
				}
			}
		}
	}
	
	@Override
	protected AbstractMaxSatSolver<Doubleton<STATE>> createTransitivitySolver() {
		mTransitivityGenerator = new ScopedTransitivityGeneratorDoubleton<>(mSettings.isUsePathCompression());
		mConsistencyGenerator = new ScopedConsistencyGeneratorDelayedSimulation<Doubleton<STATE>, LETTER, STATE>(mSettings.isUsePathCompression(), mServices, mOperand);
		final List<IAssignmentCheckerAndGenerator<Doubleton<STATE>>> assignmentCheckerAndGeneratorList =
				new ArrayList<>();
		assignmentCheckerAndGeneratorList.add(mTransitivityGenerator);
		assignmentCheckerAndGeneratorList.add(mConsistencyGenerator);
		return new InteractiveMaxSatSolver<>(mServices, assignmentCheckerAndGeneratorList);
	}

}
