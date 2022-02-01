/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.BiPredicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.NwaApproximateXsimulation.SimulationType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.AbstractMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.IAssignmentCheckerAndGenerator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.InteractiveMaxSatSolver;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections.ScopedTransitivityGeneratorPair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.IPartition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Partial Max-SAT based minimization of NWA using (asymmetric) {@link Pair}s of states as variable type.<br>
 * In contrast to {@link MinimizeNwaPmaxSat}, this class works for simulation rather than bisimulation. Accrodingly, a
 * pair (q0, q1) means that the state q1 simulates the state q0.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @see MinimizeNwaMaxSat2
 */
public class MinimizeNwaPmaxSatDirect<LETTER, STATE> extends MinimizeNwaMaxSat2<LETTER, STATE, Pair<STATE, STATE>> {
	/**
	 * Preprocessing mode.
	 *
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
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

	private static final PreprocessingMode PREPROCESSING_STANDALONE = PreprocessingMode.PAIRS;
	private static final boolean USE_FULL_PREPROCESSING = false;

	@SuppressWarnings("rawtypes")
	private static final Pair[] EMPTY_LITERALS = new Pair[0];
	private STATE mEmptyStackState;
	private final int mNumberOfInitialPairs;

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
	public MinimizeNwaPmaxSatDirect(final AutomataLibraryServices services,
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
	public MinimizeNwaPmaxSatDirect(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final Iterable<Pair<STATE, STATE>> initialPairs, final Settings<STATE> settings)
			throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, createNestedMapWithInitialPairs(initialPairs), settings);
	}

	/**
	 * Constructor with initial pairs in internal data structure (publicly available for efficiency reasons).
	 *
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input nested word automaton
	 * @param initialPairs
	 *            internal data structure for initial pairs of states
	 * @param settings
	 *            settings wrapper
	 * @throws AutomataOperationCanceledException
	 *             thrown by cancel request
	 */
	public MinimizeNwaPmaxSatDirect(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final NestedMap2<STATE, STATE, Pair<STATE, STATE>> initialPairs, final Settings<STATE> settings)
			throws AutomataOperationCanceledException {
		super(services, stateFactory, operand, settings.setSolverModeGeneral(), removeReflexivePairs(initialPairs), null);
		mEmptyStackState = mOperand.getEmptyStackState();

		// statistics
		int numberOfInitialPairs = 0;
		for (final Iterator<Triple<STATE, STATE, Pair<STATE, STATE>>> iterator =
				initialPairs.entrySet().iterator(); iterator.hasNext(); iterator.next()) {
			numberOfInitialPairs++;
		}
		mNumberOfInitialPairs = numberOfInitialPairs;

		printStartMessage();

		run();

		printExitMessage();
	}

	@Override
	public void addStatistics(final AutomataOperationStatistics statistics) {
		super.addStatistics(statistics);

		statistics.addKeyValuePair(
				mSettings.getLibraryMode()
						? StatisticsType.NUMBER_INITIAL_PAIRS_PMAXSAT
						: StatisticsType.NUMBER_INITIAL_PAIRS,
				mNumberOfInitialPairs);
	}

	/**
	 * Creates the initial pairs for the automata script interpreter constructor.
	 * <p>
	 * The method allows for fast policy switching.
	 *
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	private static <LETTER, STATE> Iterable<Pair<STATE, STATE>> createAtsInitialPairs(
			final AutomataLibraryServices services, final IDoubleDeckerAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		switch (PREPROCESSING_STANDALONE) {
			case PARTITION:
				return createPairsWithInitialPartition(new NwaApproximateBisimulation<>(services, operand,
						SimulationType.DIRECT, USE_FULL_PREPROCESSING).getResult().getRelation());
			case PAIRS:
				return new NwaApproximateSimulation<>(services, operand, SimulationType.DIRECT, USE_FULL_PREPROCESSING)
						.getResult();
			case NONE:
				return createPairs(operand.getStates());
			default:
				throw new IllegalArgumentException("Unknown mode: " + PREPROCESSING_STANDALONE);
		}
	}

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

	private static <STATE> NestedMap2<STATE, STATE, Pair<STATE, STATE>>
			removeReflexivePairs(final NestedMap2<STATE, STATE, Pair<STATE, STATE>> initialPairs) {
		final List<Pair<STATE, STATE>> pairsThatShouldBeRemoved = new ArrayList<>();
		for (final Triple<STATE, STATE, Pair<STATE, STATE>> entry : initialPairs.entrySet()) {
			if (entry.getFirst().equals(entry.getSecond())) {
				pairsThatShouldBeRemoved.add(new Pair<>(entry.getFirst(), entry.getSecond()));
			}
		}
		for (final Pair<STATE, STATE> pair : pairsThatShouldBeRemoved) {
			initialPairs.remove(pair.getFirst(), pair.getSecond());
		}
		return initialPairs;
	}

	private static <STATE> Iterable<Pair<STATE, STATE>>
			createPairsWithInitialPartition(final Collection<Set<STATE>> partition) {
		final List<Pair<STATE, STATE>> result = new ArrayList<>();
		for (final Set<STATE> block : partition) {
			final ArrayList<STATE> blockAsArray = new ArrayList<>(block);
			for (int i = 0; i < blockAsArray.size(); ++i) {
				final STATE stateI = blockAsArray.get(i);
				for (int j = i + 1; j < blockAsArray.size(); ++j) {
					final STATE stateJ = blockAsArray.get(j);
					result.add(new Pair<>(stateI, stateJ));
					result.add(new Pair<>(stateJ, stateI));
				}
			}
		}
		return result;
	}

	@Override
	protected AbstractMaxSatSolver<Pair<STATE, STATE>> createTransitivitySolver() {
		mTransitivityGenerator = new ScopedTransitivityGeneratorPair<>(mSettings.isUsePathCompression());
		final List<IAssignmentCheckerAndGenerator<Pair<STATE, STATE>>> assignmentCheckerAndGeneratorList =
				new ArrayList<>();
		assignmentCheckerAndGeneratorList.add(mTransitivityGenerator);
		return new InteractiveMaxSatSolver<>(mServices, assignmentCheckerAndGeneratorList);
	}

	@Override
	protected void generateVariablesAndAcceptingConstraints() throws AutomataOperationCanceledException {
		final BiPredicate<STATE, STATE> finalNonfinalConstraintPredicate =
				mSettings.getFinalNonfinalConstraintPredicate();

		for (final Triple<STATE, STATE, Pair<STATE, STATE>> triple : mStatePair2Var.entrySet()) {
			checkTimeout(GENERATING_VARIABLES);

			final Pair<STATE, STATE> pair = triple.getThird();
			final STATE state1 = triple.getFirst();
			final STATE state2 = triple.getSecond();

			addStateToTransitivityGeneratorIfNotPresent(state1);
			addStateToTransitivityGeneratorIfNotPresent(state2);

			mSolver.addVariable(pair);

			if (mOperand.isFinal(state1) && !mOperand.isFinal(state2)
					&& finalNonfinalConstraintPredicate.test(state1, state2)) {
				setStatesDifferent(pair);
			}
		}
	}

	private void addStateToTransitivityGeneratorIfNotPresent(final STATE state) {
		if (mTransitivityGenerator != null) {
			mTransitivityGenerator.addContentIfNotPresent(state);
		}
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

	@Override
	protected boolean testOutgoingSymbols(final Set<LETTER> letters1, final Set<LETTER> letters2) {
		return letters2.containsAll(letters1);
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
	protected String createTaskDescription() {
		return "minimizing NWA with " + mOperand.size() + " states";
	}

	@SuppressWarnings("unchecked")
	@Override
	protected Pair<STATE, STATE>[] getEmptyVariableArray() {
		return EMPTY_LITERALS;
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

	@Override
	protected boolean isInitialPair(final Pair<STATE, STATE> pair) {
		return isInitialPair(pair.getFirst(), pair.getSecond());
	}
}
