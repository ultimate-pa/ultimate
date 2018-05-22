/*
 * Copyright (C) 2016-2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiPredicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaPmaxSat;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;

/**
 * Nested word automaton minimization using a partial Max-SAT reduction. The problem instance is solved using an
 * external solver.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class MinimizeNwaPmaxSatDimacs<LETTER, STATE> extends MinimizeNwaPmaxSat<LETTER, STATE> {
	private final Iterable<Set<STATE>> mInitialPartition;
	private final int mLargestBlockInitialPartition;
	private final int mInitialPartitionSize;
	private final long mNumberOfInitialPairs;
	private final Map<STATE, Set<STATE>> mState2EquivalenceClass;

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
	public MinimizeNwaPmaxSatDimacs(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final String filename) throws AutomataOperationCanceledException {
		super(services, stateFactory, operand, new Settings<STATE>().setSolverModeExternal(), filename);

		printStartMessage();

		mInitialPartition = Collections.singleton(operand.getStates());
		mState2EquivalenceClass = new HashMap<>();
		int largestBlockInitialPartition = 0;
		int initialPartitionSize = 0;
		long initialPairsSize = 0;
		for (final Set<STATE> block : mInitialPartition) {
			for (final STATE state : block) {
				mState2EquivalenceClass.put(state, block);
			}
			largestBlockInitialPartition = Math.max(largestBlockInitialPartition, block.size());
			initialPairsSize += ((long) block.size()) * ((long) block.size()) - block.size();
			++initialPartitionSize;
		}
		mLargestBlockInitialPartition = largestBlockInitialPartition;
		mInitialPartitionSize = initialPartitionSize;
		mNumberOfInitialPairs = initialPairsSize;
		mLogger.info("Initial partition has " + initialPartitionSize + " blocks, largest block has "
				+ largestBlockInitialPartition + " states");

		run();

		printExitMessage();
	}

	@Override
	protected String createTaskDescription() {
		return NestedWordAutomataUtils.generateGenericMinimizationRunningTaskDescription(getOperationName(), mOperand,
				mInitialPartitionSize, mLargestBlockInitialPartition);
	}

	@Override
	protected void generateVariablesAndAcceptingConstraints() throws AutomataOperationCanceledException {
		for (final Set<STATE> equivalenceClass : mInitialPartition) {
			final STATE[] states = constructStateArray(equivalenceClass);
			generateVariablesHelper(states);
			checkTimeout(GENERATING_VARIABLES);
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

	@Override
	@SuppressWarnings("squid:S1698")
	protected boolean isInitialPair(final STATE state1, final STATE state2) {
		// equality intended here
		return mState2EquivalenceClass.get(state1) == mState2EquivalenceClass.get(state2);
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
		final List<IAssignmentCheckerAndGenerator<Doubleton<STATE>>> assignmentCheckerAndGeneratorList =
				new ArrayList<>();
		assignmentCheckerAndGeneratorList.add(mTransitivityGenerator);
		return new InteractiveMaxSatSolver<>(mServices, assignmentCheckerAndGeneratorList);
	}
}
