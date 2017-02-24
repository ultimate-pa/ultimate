/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 3 of the License,
 * or (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be
 * useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see
 * <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automata Library, or any covered work, by linking or combining it
 * with Eclipse RCP (or a modified version of Eclipse RCP), containing parts
 * covered by the terms of the Eclipse Public License, the licensors of the
 * ULTIMATE Automata Library grant you additional permission to convey the
 * resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.util.PartitionBackedSetOfPairs;

/**
 * Minimization of nested word automata which can be used in a loop. It just calls the next minimization method
 * <ul>
 * <li>according to a fixed pattern (which is finite and repeated), or</li>
 * <li>according to the iteration (intended to be used in an outer loop).</li>
 * </ul>
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class MinimizeNwaPattern<LETTER, STATE> extends MinimizeNwaCombinator<LETTER, STATE> {
	// minimization algorithms executed from left to right
	private final MinimizationMethods[] mPattern;

	/**
	 * AutomataScript constructor with default settings.
	 * <ul>
	 * <li>no initial partition</li>
	 * <li>no mapping 'old state -> new state'</li>
	 * <li>default pattern</li>
	 * </ul>
	 * <p>
	 * NOTE: It makes little sense to use this operation from the AutomataScript interface as only the first operation
	 * is executed.
	 * 
	 * @param services
	 *            services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input automaton
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public MinimizeNwaPattern(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, null, false, 0);
	}

	/**
	 * Constructor with default pattern.
	 * 
	 * @param services
	 *            services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input automaton
	 * @param partition
	 *            pre-defined partition of states
	 * @param addMapOldState2newState
	 *            add map old state 2 new state?
	 * @param iteration
	 *            index in the pattern
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public MinimizeNwaPattern(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final PartitionBackedSetOfPairs<STATE> partition, final boolean addMapOldState2newState,
			final int iteration) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, partition, addMapOldState2newState, getDefaultPattern(), iteration);
	}

	/**
	 * Constructor using only one minimization operation every {@code k}th iteration.
	 * 
	 * @param services
	 *            services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input automaton
	 * @param partition
	 *            pre-defined partition of states
	 * @param addMapOldState2newState
	 *            add map old state 2 new state?
	 * @param indexForMinimization
	 *            iteration index at which minimization should be used
	 * @param iteration
	 *            index in the pattern
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public MinimizeNwaPattern(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final PartitionBackedSetOfPairs<STATE> partition, final boolean addMapOldState2newState,
			final int indexForMinimization, final int iteration) throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, partition, addMapOldState2newState,
				getEveryNthPattern(indexForMinimization), iteration);
	}

	/**
	 * Constructor with user-defined pattern.
	 * 
	 * @param services
	 *            services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input automaton
	 * @param partition
	 *            pre-defined partition of states
	 * @param addMapOldState2newState
	 *            add map old state 2 new state?
	 * @param pattern
	 *            minimization methods pattern
	 * @param iteration
	 *            index in the pattern
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public MinimizeNwaPattern(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory, final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final PartitionBackedSetOfPairs<STATE> partition, final boolean addMapOldState2newState,
			final MinimizationMethods[] pattern, final int iteration) throws AutomataOperationCanceledException {
		super(services, stateFactory, operand);
		mPattern = Arrays.copyOf(pattern, pattern.length);
		final int counter = iteration % mPattern.length;
		mMode = mPattern[counter];
		super.run(partition, addMapOldState2newState);
	}

	/**
	 * Creates a pattern where minimization is only used in each {@code k}th iteration.
	 * 
	 * @param indexForMinimization
	 *            index at which the minimization should actually be used
	 * @return pattern
	 */
	private static MinimizationMethods[] getEveryNthPattern(final int indexForMinimization) {
		if (indexForMinimization <= 0) {
			throw new IllegalArgumentException("The minimization index must be strictly positive.");
		}

		final MinimizationMethods[] pattern = new MinimizationMethods[indexForMinimization];
		pattern[indexForMinimization - 1] = MinimizationMethods.SEVPA;
		for (int i = indexForMinimization - 2; i >= 0; --i) {
			pattern[i] = MinimizationMethods.NONE;
		}
		return pattern;
	}

	/**
	 * @return The default pattern.
	 */
	private static MinimizationMethods[] getDefaultPattern() {
		return new MinimizationMethods[] { MinimizationMethods.NONE, MinimizationMethods.SEVPA,
				MinimizationMethods.NONE, MinimizationMethods.SEVPA, MinimizationMethods.NONE,
				MinimizationMethods.SHRINK_NWA };
	}
}
