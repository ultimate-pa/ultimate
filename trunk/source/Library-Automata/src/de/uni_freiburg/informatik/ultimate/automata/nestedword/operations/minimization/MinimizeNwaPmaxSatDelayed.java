package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.BiPredicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.AbstractMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.IAssignmentCheckerAndGenerator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.InteractiveMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.NwaApproximateDelayedSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedConsistencyGeneratorDelayedSimulationPair;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGeneratorPair;
import de.uni_freiburg.informatik.ultimate.automata.util.ISetOfPairs;
import de.uni_freiburg.informatik.ultimate.util.datastructures.IPartition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class MinimizeNwaPmaxSatDelayed<LETTER, STATE> extends MinimizeNwaMaxSat2<LETTER, STATE, Pair<STATE, STATE>> {
	public enum PreprocessingMode {
		/**
		 * Initial partition.
		 */
		PARTITION,
		/**
		 * Initial pairs.
		 */
		PAIRS,
		/**
		 * No preprocessing.
		 */
		NONE
	}

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
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             thrown by cancel request
	 */
	public MinimizeNwaPmaxSatDelayed(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, createAtsInitialPairs(services, operand),
				new Settings<STATE>().setLibraryMode(false));
	}

	/**
	 * Constructor with initial pairs.
	 *
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input nested word automaton
	 * @param initialPairs
	 *            allowed pairs of states
	 * @param settings
	 *            settings wrapper
	 * @throws AutomataOperationCanceledException
	 *             thrown by cancel request
	 */
	public MinimizeNwaPmaxSatDelayed(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final Iterable<Pair<STATE, STATE>> initialPairs, final Settings<STATE> settings)
			throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, createNestedMapWithInitialPairs(initialPairs), settings);
	}

	public MinimizeNwaPmaxSatDelayed(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final NestedMap2<STATE, STATE, Pair<STATE, STATE>> statePair2Var, final Settings<STATE> settings)
			throws AutomataOperationCanceledException {
		super(services, stateFactory, operand, settings, statePair2Var, null);

		mEmptyStackState = mOperand.getEmptyStackState();

		mSettings.setUseInternalCallConstraints(false);
		final NwaApproximateDelayedSimulation<LETTER, STATE> approximateSimulation =
				new NwaApproximateDelayedSimulation<>(mServices, mOperand, nothingMergedYet);
		mSpoilerWinnings = approximateSimulation.getSpoilerWinningStates();
		mDuplicatorFollowing = approximateSimulation.getDuplicatorEventuallyAcceptingStates();
		mSimulation = approximateSimulation.computeOrdinarySimulation();

		printStartMessage();

		run();

		printExitMessage();
	}

	private static final PreprocessingMode PREPROCESSING_STANDALONE = PreprocessingMode.PAIRS;
	private static final boolean USE_FULL_PREPROCESSING = false;

	@SuppressWarnings("rawtypes")
	private static final Pair[] EMPTY_LITERALS = new Pair[0];
	private STATE mEmptyStackState;
	private ScopedConsistencyGeneratorDelayedSimulationPair<STATE, LETTER, STATE> mConsistencyGenerator;

	final ISetOfPairs<STATE, ?> mSpoilerWinnings;
	final ISetOfPairs<STATE, ?> mDuplicatorFollowing;
	final ISetOfPairs<STATE, ?> mSimulation;

	private static <LETTER, STATE> Iterable<Pair<STATE, STATE>> createAtsInitialPairs(
			final AutomataLibraryServices services, final IDoubleDeckerAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		switch (PREPROCESSING_STANDALONE) {
			//FIXME: The partition part should probably look different
			case PARTITION:
				return createPairs(operand.getStates());
			case PAIRS:
				return createPairs(operand.getStates());
			case NONE:
				return createPairs(operand.getStates());
			default:
				throw new IllegalArgumentException("Unknown mode: " + PREPROCESSING_STANDALONE);
		}

	}

	//FIXME: This should be used for pair creation, but the static reference to mSpoilerWinnings is an issue
/*
	private static <STATE, LETTER> Iterable<Pair<STATE, STATE>> createPairsWithSpoilerWinning(final AutomataLibraryServices services, IDoubleDeckerAutomaton<LETTER, STATE> operand) {
		Set<STATE> states = operand.getStates();
		final List<Pair<STATE, STATE>> result = new ArrayList<>(states.size() * states.size());

		for (final STATE state1 : states) {
			for (final STATE state2 : states) {
				if(mSpoilerWinnings.containsPair(state1, state2)) {
					result.add(new Pair<>(state1, state2));
				}
			}
		}

		return result;
	}
*/

	@Override
	protected AbstractMaxSatSolver<Pair<STATE, STATE>> createTransitivitySolver() {
		mTransitivityGenerator = new ScopedTransitivityGeneratorPair<>(mSettings.isUsePathCompression());
		mConsistencyGenerator = new ScopedConsistencyGeneratorDelayedSimulationPair<>(mSettings.isUsePathCompression(),
				mServices, mOperand);
		final List<IAssignmentCheckerAndGenerator<Pair<STATE, STATE>>> assignmentCheckerAndGeneratorList =
				new ArrayList<>();
		assignmentCheckerAndGeneratorList.add(mTransitivityGenerator);
		assignmentCheckerAndGeneratorList.add(mConsistencyGenerator);
		return new InteractiveMaxSatSolver<>(mServices, assignmentCheckerAndGeneratorList);
	}

	@Override
	protected void generateVariablesAndAcceptingConstraints() throws AutomataOperationCanceledException {
		final Set<STATE> stateSet = computeDuplicatorComplement(mDuplicatorFollowing, mSimulation);
		final STATE[] states = constructStateArray(stateSet);
		generateVariablesHelper(states);
		checkTimeout(GENERATING_VARIABLES);
	}

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
				final Pair<STATE, STATE> pair1 = new Pair<>(stateI, stateJ);
				final Pair<STATE, STATE> pair2 = new Pair<>(stateJ, stateI);
				mStatePair2Var.put(stateI, stateJ, pair1);
				mStatePair2Var.put(stateJ, stateI, pair2);
				mSolver.addVariable(pair1);
				mSolver.addVariable(pair2);

				if (!mSpoilerWinnings.containsPair(stateI, stateJ)) {
					setVariableFalse(pair1);
				}

				if (!mSpoilerWinnings.containsPair(stateJ, stateI)) {
					setVariableFalse(pair2);
				}
			}
		}
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

	@Override
	protected boolean isInitialPair(final STATE state1, final STATE state2) {
		if (state1.equals(mEmptyStackState) || state2.equals(mEmptyStackState)) {
			return false;
		}

		final Map<STATE, Pair<STATE, STATE>> rhsStates = mStatePair2Var.get(state1);
		if (rhsStates == null) {
			// no state was in relation to state1
			return false;
		}

		return rhsStates.containsKey(state2);
	}

	//TODO: All methods below are identical in MinimizeNwaPmaxSatDirect, so there could be a common superclass

	private static <STATE> NestedMap2<STATE, STATE, Pair<STATE, STATE>>
			createNestedMapWithInitialPairs(final Iterable<Pair<STATE, STATE>> initialPairs) {
		final NestedMap2<STATE, STATE, Pair<STATE, STATE>> result = new NestedMap2<>();
		for (final Pair<STATE, STATE> pair : initialPairs) {
			if (!pair.getFirst().equals(pair.getSecond())) {
				// only include non-reflexive pairs
				result.put(pair.getFirst(), pair.getSecond(), pair);
			}
		}
		return result;
	}

	@Override
	protected void generateTransitionAndTransitivityConstraints(final boolean addTransitivityConstraints)
			throws AutomataOperationCanceledException {
		for (final Triple<STATE, STATE, Pair<STATE, STATE>> triple : mStatePair2Var.entrySet()) {
			checkTimeout(ADDING_TRANSITION_CONSTRAINTS);

			final Pair<STATE, STATE> pair = triple.getThird();

			// add transition constraints
			generateTransitionConstraintsHelper(triple.getFirst(), triple.getSecond(), pair);

			// add transitivity constraints
			if (addTransitivityConstraints) {
				generateTransitivityConstraints(pair);
			}
		}

		// add constraints for reflexive pairs; those are not considered above
		for (final STATE state : mOperand.getStates()) {
			checkTimeout(ADDING_TRANSITION_CONSTRAINTS);

			generateTransitionConstraintsHelperReturnSameLinPred(state, getDownStatesArray(state));
		}
	}

	private void generateTransitivityConstraints(final Pair<STATE, STATE> pair12) {
		final Map<STATE, Pair<STATE, STATE>> state2to3s = mStatePair2Var.get(pair12.getSecond());
		if (state2to3s == null) {
			return;
		}
		for (final Entry<STATE, Pair<STATE, STATE>> state3toPair : state2to3s.entrySet()) {
			final STATE state3 = state3toPair.getKey();
			final Pair<STATE, STATE> pair23 = state3toPair.getValue();
			final Pair<STATE, STATE> pair13 = mStatePair2Var.get(pair12.getFirst(), state3);
			if (pair13 == null) {
				continue;
			}

			addTransitivityClausesToSolver(pair12, pair23, pair13);
		}
	}

	@Override
	protected IPartition<STATE> constructResultEquivalenceClasses() throws AssertionError {
		final Map<STATE, Set<STATE>> positivePairs = new HashMap<>();
		final UnionFind<STATE> resultingEquivalenceClasses = new UnionFind<>();
		for (final STATE state : mOperand.getStates()) {
			resultingEquivalenceClasses.makeEquivalenceClass(state);
		}
		for (final Entry<Pair<STATE, STATE>, Boolean> entry : mSolver.getValues().entrySet()) {
			if (entry.getValue() == null) {
				throw new AssertionError("value not determined " + entry.getKey());
			}
			if (!entry.getValue()) {
				continue;
			}

			final STATE state1 = entry.getKey().getFirst();
			final STATE state2 = entry.getKey().getSecond();
			final Set<STATE> setOfRhs2to1 = positivePairs.get(state2);
			if (setOfRhs2to1 != null && setOfRhs2to1.remove(state1)) {
				// symmetric positive pairs, merge states
				final STATE rep1 = resultingEquivalenceClasses.findAndConstructEquivalenceClassIfNeeded(state1);
				final STATE rep2 = resultingEquivalenceClasses.findAndConstructEquivalenceClassIfNeeded(state2);
				resultingEquivalenceClasses.union(rep1, rep2);
			} else if (isInitialPair(state2, state1)) {
				// other (symmetric) pair not seen yet (but will potentially come)
				Set<STATE> setOfRhs1to2 = positivePairs.get(state1);
				if (setOfRhs1to2 == null) {
					setOfRhs1to2 = new HashSet<>();
					positivePairs.put(state1, setOfRhs1to2);
				}
				setOfRhs1to2.add(state2);
			}
		}
		return resultingEquivalenceClasses;
	}

	@Override
	protected boolean isInitialPair(final Pair<STATE, STATE> pair) {
		return isInitialPair(pair.getFirst(), pair.getSecond());
	}

	@Override
	protected Pair<STATE, STATE>[] getEmptyVariableArray() {
		return EMPTY_LITERALS;
	}

	@Override
	protected String createTaskDescription() {
		return "minimizing NWA with " + mOperand.size() + " states";
	}

	@Override
	protected void generateTransitionConstraintGeneralInternalCallHelper(final Pair<STATE, STATE> predPair,
			final Set<STATE> succs1, final Set<STATE> succs2) {
		generateTransitionConstraintGeneralInternalCallHelperOneSide(predPair, succs1, succs2, null);
	}

	@Override
	protected void generateTransitionConstraintGeneralReturnHelper(final Pair<STATE, STATE> linPredPair,
			final Pair<STATE, STATE> hierPredPair, final Set<STATE> succs1, final Set<STATE> succs2) {
		generateTransitionConstraintGeneralReturnHelperOneSide(linPredPair, hierPredPair, succs1, succs2, null);
	}

	@Override
	protected boolean testOutgoingSymbols(final Set<LETTER> letters1, final Set<LETTER> letters2) {
		return letters2.containsAll(letters1);
	}

	private static <STATE> Iterable<Pair<STATE, STATE>> createPairs(final Set<STATE> states) {
		final List<Pair<STATE, STATE>> result = new ArrayList<>(states.size() * states.size());
		for (final STATE state1 : states) {
			for (final STATE state2 : states) {
				result.add(new Pair<>(state1, state2));
			}
		}
		return result;
	}

}
