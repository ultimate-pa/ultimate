package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.BiPredicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.AbstractMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.IAssignmentCheckerAndGenerator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.InteractiveMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.NwaApproximateDelayedSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedConsistencyGeneratorDelayedSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedConsistencyGeneratorDelayedSimulationDoubleton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGeneratorDoubleton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.VariableFactory.MergeDoubleton;
import de.uni_freiburg.informatik.ultimate.automata.util.ISetOfPairs;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Partial Max-SAT based minimization of NWA using {@link MergeDoubleton} as variable type. Minimization is done using
 * delayed simulation.
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @see MinimizeNwaMaxSat2
 */
public class MinimizeNwaPmaxSatDelayedBi<LETTER, STATE> extends MinimizeNwaPmaxSat<LETTER, STATE> {
	protected ScopedConsistencyGeneratorDelayedSimulation<Doubleton<STATE>, LETTER, STATE> mConsistencyGenerator;
	final ISetOfPairs<STATE, ?> mSpoilerWinnings;
	final ISetOfPairs<STATE, ?> mDuplicatorFollowing;
	final ISetOfPairs<STATE, ?> mSimulation;

	final BiPredicate<STATE, STATE> nothingMergedYet = new BiPredicate<STATE, STATE>() {
		@Override
		public boolean test(final STATE t, final STATE u) {
			return false;
		}
	};

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
	public MinimizeNwaPmaxSatDelayedBi(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, new Settings<STATE>().setLibraryMode(false));
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

	public MinimizeNwaPmaxSatDelayedBi(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final Settings<STATE> settings) throws AutomataOperationCanceledException {
		super(services, stateFactory, operand, settings, null);

		printStartMessage();

		mSettings.setUseInternalCallConstraints(false);
		final NwaApproximateDelayedSimulation<LETTER, STATE> approximateSimulation =
				new NwaApproximateDelayedSimulation<>(mServices, mOperand, nothingMergedYet);
		mSpoilerWinnings = approximateSimulation.getSpoilerWinningStates();
		mDuplicatorFollowing = approximateSimulation.getDuplicatorEventuallyAcceptingStates();
		mSimulation = approximateSimulation.computeOrdinarySimulation();

		run();

		printExitMessage();
	}

	@Override
	public void addStatistics(final AutomataOperationStatistics statistics) {
		super.addStatistics(statistics);
	}

	@Override
	protected String createTaskDescription() {
		return null;
	}

	@Override
	protected void generateVariablesAndAcceptingConstraints() throws AutomataOperationCanceledException {
		final Set<STATE> stateSet = computeDuplicatorComplement(mDuplicatorFollowing, mSimulation);
		final STATE[] states = constructStateArray(stateSet);
		generateVariablesHelper(states);
		checkTimeout(GENERATING_VARIABLES);
	}

	@Override
	protected void generateTransitionAndTransitivityConstraints(final boolean addTransitivityConstraints)
			throws AutomataOperationCanceledException {
		final Set<STATE> stateSet = computeDuplicatorComplement(mDuplicatorFollowing, mSimulation);
		final STATE[] states = constructStateArray(stateSet);

		for (int i = 0; i < states.length; i++) {
			generateTransitionConstraints(states, i);
			checkTimeout(ADDING_TRANSITION_CONSTRAINTS);
		}

		if (addTransitivityConstraints) {
			generateTransitivityConstraints(states);
		}
	}

	@Override
	protected void generateVariablesHelper(final STATE[] states) {
		if (states.length <= 1) {
			return;
		}

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

				if (!mSpoilerWinnings.containsPair(stateI, stateJ) || !mSpoilerWinnings.containsPair(stateJ, stateI)) {
					setVariableFalse(doubleton);
				}
			}
		}
	}

	@Override
	protected AbstractMaxSatSolver<Doubleton<STATE>> createTransitivitySolver() {
		mTransitivityGenerator = new ScopedTransitivityGeneratorDoubleton<>(mSettings.isUsePathCompression());
		mConsistencyGenerator = new ScopedConsistencyGeneratorDelayedSimulationDoubleton<>(
				mSettings.isUsePathCompression(), mServices, mOperand);
		final List<IAssignmentCheckerAndGenerator<Doubleton<STATE>>> assignmentCheckerAndGeneratorList =
				new ArrayList<>();
		assignmentCheckerAndGeneratorList.add(mConsistencyGenerator);
		assignmentCheckerAndGeneratorList.add(mTransitivityGenerator);
		return new InteractiveMaxSatSolver<>(mServices, assignmentCheckerAndGeneratorList);
	}

	@Override
	protected boolean isInitialPair(final STATE state1, final STATE state2) {
		if (mSpoilerWinnings.containsPair(state1, state2) && mSpoilerWinnings.containsPair(state2, state1)) {
			return true;
		}
		return false;
	}

	private Set<STATE> computeDuplicatorComplement(final ISetOfPairs<STATE, ?> duplicatorFollowing,
			final ISetOfPairs<STATE, ?> allPairs) {
		final Set<STATE> complement = new HashSet<>();
		for (final Pair<STATE, STATE> pair : allPairs) {
			if (!duplicatorFollowing.containsPair(pair.getFirst(), pair.getSecond())) {
				complement.add(pair.getFirst());
				complement.add(pair.getSecond());
			}
		}
		return complement;
	}
}
