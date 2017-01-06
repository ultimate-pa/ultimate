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

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

/**
 * Partial Max-SAT based minimization of NWA using {@link Doubleton}s (symmetric pairs) of states as variable type.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @see MinimizeNwaMaxSat2
 */
public class MinimizeNwaPmaxSat<LETTER, STATE> extends MinimizeNwaMaxSat2<LETTER, STATE, Doubleton<STATE>> {
	@SuppressWarnings("rawtypes")
	private static final Doubleton[] EMPTY_LITERALS = new Doubleton[0];
	
	private final Map<STATE, Set<STATE>> mState2EquivalenceClass;
	private final Iterable<Set<STATE>> mInitialPartition;
	private final int mLargestBlockInitialPartition;
	private final int mInitialPartitionSize;
	
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
	public MinimizeNwaPmaxSat(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, Collections.singleton(operand.getStates()), new Settings<>());
	}
	
	/**
	 * Constructor with an initial partition.
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
	 * @throws AutomataOperationCanceledException
	 *             thrown by cancel request
	 */
	public MinimizeNwaPmaxSat(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand, final Collection<Set<STATE>> initialPartition,
			final Settings<STATE> settings) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, initialPartition, settings, true);
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
	 * @throws AutomataOperationCanceledException
	 *             thrown by cancel request
	 */
	public MinimizeNwaPmaxSat(final AutomataLibraryServices services, final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand, final Collection<Set<STATE>> initialPartition,
			final Settings<STATE> settings, final boolean applyInitialPartitionPreprocessing)
			throws AutomataOperationCanceledException {
		super(services, stateFactory, "MinimizeNwaPmaxSat", operand, settings);
		
		mInitialPartition = applyInitialPartitionPreprocessing
				? new LookaheadPartitionConstructor<>(services, operand, initialPartition,
						mSettings.getFinalStateConstraints()).getPartition()
				: initialPartition;
		mState2EquivalenceClass = new HashMap<>();
		int largestBlockInitialPartition = 0;
		int initialPartitionSize = 0;
		for (final Set<STATE> equivalenceClass : mInitialPartition) {
			for (final STATE state : equivalenceClass) {
				mState2EquivalenceClass.put(state, equivalenceClass);
			}
			largestBlockInitialPartition = Math.max(largestBlockInitialPartition, equivalenceClass.size());
			++initialPartitionSize;
		}
		mLargestBlockInitialPartition = largestBlockInitialPartition;
		mInitialPartitionSize = initialPartitionSize;
		mLogger.info("Initial partition has " + initialPartitionSize + " blocks, largest block has "
				+ largestBlockInitialPartition + " states");
		
		run();
	}
	
	@Override
	protected String createTaskDescription() {
		return NestedWordAutomataUtils.generateGenericMinimizationRunningTaskDescription(
				mOperand, mInitialPartitionSize, mLargestBlockInitialPartition);
	}
	
	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics statistics = super.getAutomataOperationStatistics();
		if (mLargestBlockInitialPartition != 0) {
			statistics.addKeyValuePair(StatisticsType.SIZE_MAXIMAL_INITIAL_EQUIVALENCE_CLASS,
					mLargestBlockInitialPartition);
		}
		return statistics;
	}
	
	@Override
	protected void generateVariablesAndAcceptingConstraints() throws AutomataOperationCanceledException {
		for (final Set<STATE> equivalenceClass : mInitialPartition) {
			final STATE[] states = constructStateArray(equivalenceClass);
			generateVariablesHelper(states);
			checkTimeout(GENERATING_VARIABLES);
		}
	}
	
	private void generateVariablesHelper(final STATE[] states) {
		if (states.length <= 1) {
			return;
		}
		
		final boolean separateFinalAndNonfinalStates = mSettings.getFinalStateConstraints();
		
		for (int i = 0; i < states.length; i++) {
			final STATE stateI = states[i];
			
			// add to transitivity generator
			if (mTransitivityGenerator != null) {
				mTransitivityGenerator.addContent(stateI);
			}
			
			for (int j = 0; j < i; j++) {
				final STATE stateJ = states[j];
				final Doubleton<STATE> doubleton = new Doubleton<>(stateI, stateJ);
				mStatePairs.put(stateI, stateJ, doubleton);
				mStatePairs.put(stateJ, stateI, doubleton);
				mSolver.addVariable(doubleton);
				
				// separate final and nonfinal states
				if (separateFinalAndNonfinalStates && (mOperand.isFinal(stateI) ^ mOperand.isFinal(stateJ))) {
					setStatesDifferent(doubleton);
				}
			}
		}
	}
	
	@Override
	protected void generateTransitionAndTransitivityConstraints(final boolean addTransitivityConstraints)
			throws AutomataOperationCanceledException {
		for (final Set<STATE> equivalenceClass : mInitialPartition) {
			final STATE[] states = constructStateArray(equivalenceClass);
			for (int i = 0; i < states.length; i++) {
				generateTransitionConstraints(states, i);
				checkTimeout(ADDING_TRANSITION_CONSTRAINTS);
			}
			
			if (addTransitivityConstraints) {
				generateTransitivityConstraints(states);
			}
		}
	}
	
	private void generateTransitionConstraints(final STATE[] states, final int firstStateIndex) {
		final STATE state1 = states[firstStateIndex];
		final STATE[] downStates1 = getDownStatesArray(state1);
		for (int j = 0; j < firstStateIndex; j++) {
			final STATE state2 = states[j];
			
			// add transition constraints
			generateTransitionConstraintsHelper(state1, state2, getVariable(state1, state2, false));
		}
		generateTransitionConstraintsHelperReturn2(state1, downStates1);
	}
	
	private void generateTransitivityConstraints(final STATE[] states) throws AutomataOperationCanceledException {
		for (int i = 0; i < states.length; i++) {
			for (int j = 0; j < i; j++) {
				for (int k = 0; k < j; k++) {
					final Doubleton<STATE> doubletonIj = mStatePairs.get(states[i], states[j]);
					final Doubleton<STATE> doubletonJk = mStatePairs.get(states[j], states[k]);
					final Doubleton<STATE> doubletonIk = mStatePairs.get(states[i], states[k]);
					
					addTransitivityClausesToSolver(doubletonIj, doubletonJk, doubletonIk);
				}
				checkTimeout(ADDING_TRANSITIVITY_CONSTRAINTS);
			}
		}
	}
	
	@SuppressWarnings("unchecked")
	@Override
	protected Doubleton<STATE>[] getEmptyVariableArray() {
		return EMPTY_LITERALS;
	}
	
	@Override
	@SuppressWarnings("squid:S1698")
	protected boolean isInitialPair(final STATE state1, final STATE state2) {
		// equality intended here
		return mState2EquivalenceClass.get(state1) == mState2EquivalenceClass.get(state2);
	}

	@Override
	protected boolean isInitialPair(final Doubleton<STATE> pair) {
		return isInitialPair(pair.getOneElement(), pair.getOtherElement());
	}
	
	@Override
	protected UnionFind<STATE> constructResultEquivalenceClasses() throws AssertionError {
		final UnionFind<STATE> resultingEquivalenceClasses = new UnionFind<>();
		for (final Entry<Doubleton<STATE>, Boolean> entry : mSolver.getValues().entrySet()) {
			if (entry.getValue() == null) {
				throw new AssertionError("value not determined " + entry.getKey());
			}
			if (entry.getValue()) {
				final STATE rep1 = resultingEquivalenceClasses
						.findAndConstructEquivalenceClassIfNeeded(entry.getKey().getOneElement());
				final STATE rep2 = resultingEquivalenceClasses
						.findAndConstructEquivalenceClassIfNeeded(entry.getKey().getOtherElement());
				resultingEquivalenceClasses.union(rep1, rep2);
			}
		}
		return resultingEquivalenceClasses;
	}
}
